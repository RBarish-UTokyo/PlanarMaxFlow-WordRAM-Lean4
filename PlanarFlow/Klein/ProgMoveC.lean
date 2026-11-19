module

public import PlanarFlow.Klein.ProgMove
public import PlanarFlow.Klein.ProgPivotC

/-!
# The pivot loop of a move on the machine, with bounded comparisons

The proofs of `PlanarFlow/Klein/ProgMove.lean` replayed as runs whose real comparisons are
bounded (`DynTree.ORunC`): `mvBody_orunC`, `mv_orunC`, `mv_orunAC`. Besides the invariant
`MvInv`, the loop keeps **the bound `A - Lo` of the values of the forest** (`DynTree.VBnd`,
`Lo` the lower bound of the values at the nodes of the faces of `Stored`, lowered by `|c|` at a
pivot of value `c`) and `Lo ≤ Lo₀`. With `|wt| ≤ Wt`, `|φ| ≤ W`,
`Wt + W + |L - 2B| ≤ A - Lo₀` and `30 (A - (L - 2B)) ≤ H` (`B = #V W`):

* the query `min2` (`regMin2S`, the comparison bit `bitS` against the threshold `L - 2B` in the
  real `r100`) compares the least second value on the root path (at most `A - Lo` by
  `DynTree.pathMin_bound`) with `L - 2B`;
* the pivot selects a dart of value `c` with `|c| ≤ A - Lo` (the least value is a value of the
  forest), the new values of the two edges changing trees are at most `Wt + W + |c| ≤ A - Lo + |c|`,
  so `piv_orunC` applies with `U = A - Lo` and leaves the bound `A - (Lo - |c|)`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {u v : V} {φ wt : D → ℤ} {e : D}
  {W L : ℤ} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {nD : ℕ}
  {σ : D ≃ Fin nD} {B : ℕ} {Fo₀ : Forest} {T₀ : DTree M.dual} {val₀ : D → ℤ} {Lo₀ : ℝ}
  {c₀ : Config} {Wd : ℕ}

section
variable {P : Input} {Hc : ℕ}

theorem mvBody_orunC (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (H : MoveHyp (pieceGraph M S ℓ) u v) (hU : UniqTight (pieceGraph M S ℓ))
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d)
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach (pieceGraph M S ℓ) v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach (pieceGraph M S ℓ) v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) (hLay : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {A Wt : ℝ} (hwtb : ∀ d, |(wt d : ℝ)| ≤ Wt)
    (hTA : Wt + W + |((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)| ≤ A - Lo₀)
    (hHA : 30 * (A - ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)) ≤ Hc)
    (x : MvG M) (hs : List EOp) (G : List VT)
    (c : Config)
    (hI : MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c₀ Wd x hs G c)
    (hV : VBnd (A - x.Lo) n (runOpsE n Fo₀ hs).1) (hLo0 : x.Lo ≤ Lo₀)
    (ht : c.nreg 102 < c.nreg 103) :
    ∃ x' c' os G' j h, ORunC P Wd Hc B n (mvBodyS B nD) c (runOpsE n Fo₀ hs).1 G c' os G' j h ∧
      MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c₀ Wd x' (hs ++ os) G' c' ∧
      x'.cnt = x.cnt + j ∧ x'.ext S ℓ u v + h + 2 ≤ x.ext S ℓ u v ∧ 1 ≤ j ∧ h ≤ 99 ∧
      VBnd (A - x'.Lo) n (runOpsE n Fo₀ (hs ++ os)).1 ∧ x'.Lo ≤ Lo₀ := by
  classical
  have hdone : x.done = false := by
    cases hd : x.done
    · rfl
    · rw [hI.r103, hd, hI.r102] at ht; simp at ht
  set z : ℤ := L - 2 * (Fintype.card V * W) with hz
  set K : ℝ := (driftK L W (Fintype.card V) : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have : (0 : ℤ) ≤ driftK L W (Fintype.card V) := by simp only [driftK]; positivity
    rw [hKdef]; exact_mod_cast this
  have hzLo : (z : ℝ) ≤ x.Lo := by
    have := hI.red
    have : (0 : ℝ) ≤ ((redSet M S ℓ u v (selForest M S (tpar (pieceGraph M S ℓ) u) x.d
      x.i)).card : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK0
    linarith
  obtain ⟨hpiv, hstop⟩ := stored_min2v hM hLay hI.st hzLo
  -- the bounds of the compared values
  set U : ℝ := A - x.Lo with hUdef
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hV _ (hLay.dual.f_lt (M.face e))).1
  have hWt0 : 0 ≤ Wt := (abs_nonneg _).trans (hwtb e)
  have hW0 : (0 : ℝ) ≤ W := by have := hW e; exact_mod_cast (abs_nonneg _).trans this
  have hUz : U ≤ A - (z : ℝ) := by rw [hUdef]; linarith
  have hTU : Wt + W + |(z : ℝ)| ≤ U := by rw [hUdef]; linarith
  have hH2 : 2 * U ≤ Hc := by linarith
  have hpm := (pathMin_bound hV (hLay.dual.f_lt (M.face (M.rev e)))).2
  obtain ⟨c₁, G₁, o₁, a196, a195, a198, -, m₁, f₁⟩ := regMin2_orunC (P := P) hWW hI.wb hI.lcte
    hV hH2 (ra := 100) (rz := 100) hI.r100 (hLay.dual.f_lt _) (by
      rw [hI.q100]
      exact (abs_sub _ _).trans (by linarith [abs_nonneg (W : ℝ)]))
  rw [hI.q100] at a198
  have e₂ := Exec.copyN (P := P) o₁.1.2.wb 103 198
  set c₂ := { c₁ with nreg := upd c₁.nreg 103 (c₁.nreg 198) } with hc₂
  have g₂ : GFr 103 104 c₁ c₂ := by rw [hc₂]; gfr_tac
  have o₂ := ORunC.ofGFr (H := Hc) e₂ o₁.1.2.lcte g₂ (by omega) (by rfl)
  have b102 : c₂.nreg 102 = 0 := by
    rw [(g₂.1 102 (by omega)).1, f₁.1 102 (by omega), hI.r102]
  have hKM₂ := hI.kmem.congr (m₁.trans B n g₂.memFrame) hB hLay
  have fr₂ : MvFr B n c₀ c₂ := by
    obtain ⟨h1, h2, h3, h4⟩ := hI.fr
    have hm := m₁.trans B n g₂.memFrame
    refine ⟨fun r hr => ?_, ?_, fun a ha => ?_, fun a ha han => ?_⟩
    · rw [(g₂.1 r (by omega)).1, (g₂.1 r (by omega)).2, f₁.1 r (by omega),
        f₁.2.1 r (by omega)]
      exact h1 r hr
    · rw [g₂.2.2.2, f₁.2.2]; exact h2
    · exact ((hm a ha).2).trans (h3 a ha)
    · exact ((hm a ha).1).trans (h4 a ha han)
  by_cases hlt : (pathMin2 (runOpsE n Fo₀ hs).1 n (ιf (M.face (M.rev e)))).1 < (z : ℝ)
  · -- a pivot
    obtain ⟨d₀, hd196, hd195, hdpar, hdfb, hdchi, hdlt, hdmin⟩ := hpiv hlt
    obtain ⟨hdS, hy, hna, hnT, hI', hC', hV', hred, hcK⟩ := move_step hM H hU heS hrS hφ hW
      hwt hwL hL hI.rinv hI.compat hI.vinv hdchi hdlt hdmin
    have b103 : c₂.nreg 103 = 1 := by rw [hc₂]; config_simp; rw [a198, ite_eq_left hlt]
    have hcU : |((x.val x.i d₀ : ℤ) : ℝ)| ≤ U := by rw [← hd195]; exact hpm
    have hφb : ∀ d, |(φ d : ℝ)| ≤ W := fun d => by exact_mod_cast hW d
    have tb1 : ∀ p q r : ℝ, |p| ≤ Wt → |q| ≤ W → |p - q - r| ≤ Wt + W + |r| :=
      fun p q r hp hq => by
        have h1 := abs_sub p q; have h2 := abs_sub (p - q) r; linarith
    have tb2 : ∀ p q r : ℝ, |p| ≤ Wt → |q| ≤ W → |p + q + r| ≤ Wt + W + |r| :=
      fun p q r hp hq => by
        have h1 := abs_add_le p q; have h2 := abs_add_le (p + q) r; linarith
    obtain ⟨c₃, G₃, os, o₃, -, hlen, hout, hSt', hVB, hKM₃, lf₃, rm₃, nm₃⟩ := piv_orunC (P := P)
      hWW hWa hB hP hM hLay hK o₂.1.2.wb o₂.1.2.lcte hI.st hKM₂
      (by rw [(g₂.1 101 (by omega)).1, f₁.1 101 (by omega), hI.r101]) (b := d₀)
      (by rw [(g₂.1 196 (by omega)).1, a196, hd196])
      (by rw [(g₂.1 195 (by omega)).2, a195, hd195]) hdpar hdfb hy hna hnT
      (Tb := Wt + W + |((x.val x.i d₀ : ℤ) : ℝ)|) hV
      (by push_cast; exact tb1 _ _ _ (hwtb _) (hφb _))
      (by push_cast; exact tb2 _ _ _ (hwtb _) (hφb _))
      ((hφb d₀).trans (by linarith [abs_nonneg ((x.val x.i d₀ : ℤ) : ℝ)]))
      ((hφb (M.rev d₀)).trans (by linarith [abs_nonneg ((x.val x.i d₀ : ℤ) : ℝ)]))
      (by linarith [abs_nonneg (z : ℝ)])
    have o := o₁.seq (o₂.seq (ORunC.ifLtN_true (a := 102) (b := 103) (e := .skip)
      (by rw [b102, b103]; omega) o₃))
    simp only [List.nil_append] at o
    set T' := (x.T x.i).reparent (M.head d₀) d₀ hy (dual_face_rev d₀) hna with hT'
    set val' := pivotVal (x.T x.i) φ wt (x.val x.i) (M.head d₀) (x.val x.i d₀) with hval'
    have hsel' : selForest M S (tpar (pieceGraph M S ℓ) u) (Function.update x.d x.i d₀)
        (x.i + 1) = Function.update (selForest M S (tpar (pieceGraph M S ℓ) u) x.d x.i)
          (M.head d₀) (some ⟨d₀, hdS⟩) := by
      rw [selForest_succ _ _ _ (by rw [Function.update_self]; exact hdS)]
      simp only [Function.update_self]
      rw [selForest_update _ _ _ x.i le_rfl]
    refine ⟨⟨Function.update x.T (x.i + 1) T', Function.update x.val (x.i + 1) val',
      Function.update x.d x.i d₀, x.i + 1, false, x.Lo - |((x.val x.i d₀ : ℤ) : ℝ)|⟩, c₃, os,
      G₃, 1 + (0 + 26), 0 + (1 + (97 + 1)), o, ?_, ?_, ?_, by norm_num, by norm_num,
      by rw [runOpsE_append]
         exact hVB.mono (max_le (by show U + _ ≤ A - (x.Lo - _); rw [hUdef]; linarith)
           (by show _ ≤ A - (x.Lo - _); linarith [abs_nonneg (z : ℝ)])),
      by show x.Lo - _ ≤ Lo₀; linarith [abs_nonneg ((x.val x.i d₀ : ℤ) : ℝ)]⟩
    · have hT1 : Function.update x.T (x.i + 1) T' (x.i + 1) = T' := Function.update_self ..
      have hv1 : Function.update x.val (x.i + 1) val' (x.i + 1) = val' :=
        Function.update_self ..
      have hTj : ∀ j ≤ x.i, Function.update x.T (x.i + 1) T' j = x.T j := fun j hj =>
        Function.update_of_ne (by omega) _ _
      have hvj : ∀ j ≤ x.i, Function.update x.val (x.i + 1) val' j = x.val j := fun j hj =>
        Function.update_of_ne (by omega) _ _
      have hdj : ∀ j < x.i, Function.update x.d x.i d₀ j = x.d j := fun j hj =>
        Function.update_of_ne (by omega) _ _
      have hdi : Function.update x.d x.i d₀ x.i = d₀ := Function.update_self ..
      refine ⟨?_, o₃.1.2.wb, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun h => absurd h (by simp), ?_⟩
      · rw [runOpsE_fst_append]; exact o₃.1.2.lcte
      · dsimp only; rw [hT1, hv1, runOpsE_fst_append]
        exact hSt'
      · rw [runOpsE_append, hI.out, List.nil_append]; exact hout
      · rw [List.length_append, hI.len, hlen]; ring
      · dsimp only; rw [hTj 0 (by omega)]; exact hI.T0
      · dsimp only; rw [hvj 0 (by omega)]; exact hI.v0
      · dsimp only at hj ⊢
        rcases Nat.lt_or_ge j x.i with h | h
        · rw [hTj j h.le, hdj j h, hvj j h.le]; exact hI.sel j h
        · obtain rfl : j = x.i := by omega
          rw [hTj _ le_rfl, hdi, hvj _ le_rfl]; exact ⟨hdchi, hdmin⟩
      · dsimp only at hj ⊢
        rcases Nat.lt_or_ge j x.i with h | h
        · rw [hdj j h, hvj j h.le]; exact hI.low j h
        · obtain rfl : j = x.i := by omega
          rw [hdi, hvj _ le_rfl]; exact hdlt
      · dsimp only at hj ⊢
        rcases Nat.lt_or_ge j x.i with h | h
        · rw [hTj (j + 1) h, hTj j h.le, hdj j h]; exact hI.Ts j h
        · obtain rfl : j = x.i := by omega
          rw [hT1, hTj _ le_rfl, hdi]
          refine ⟨rfl, funext fun w => ?_⟩
          rw [DTree.reparent_par]
          by_cases hw : w = M.head d₀
          · rw [ite_eq_left hw, hw, Function.update_self]
          · rw [ite_eq_right hw, Function.update_of_ne hw]
      · dsimp only at hj ⊢
        rcases Nat.lt_or_ge j x.i with h | h
        · rw [hvj (j + 1) h, hvj j h.le, hTj j h.le, hdj j h]; exact hI.vals j h
        · obtain rfl : j = x.i := by omega
          rw [hv1, hvj _ le_rfl, hTj _ le_rfl, hdi]
      · dsimp only; rw [hsel']; exact hI'
      · dsimp only; rw [hsel', hT1]; exact hC'
      · dsimp only; rw [hT1, hv1]; exact hV'
      · dsimp only; rw [hsel']
        have h1 := hI.red
        have h2 : (((redSet M S ℓ u v (Function.update (selForest M S (tpar (pieceGraph M S ℓ) u)
            x.d x.i) (M.head d₀) (some ⟨d₀, hdS⟩))).card : ℕ) : ℝ) + 1 ≤
            ((redSet M S ℓ u v (selForest M S (tpar (pieceGraph M S ℓ) u) x.d x.i)).card : ℝ) := by
          exact_mod_cast hred
        have h3 : |((x.val x.i d₀ : ℤ) : ℝ)| ≤ K := by
          rw [hKdef, ← Int.cast_abs]; exact_mod_cast hcK
        nlinarith
      · dsimp only
        have h1 := hI.lo
        have h3 : |((x.val x.i d₀ : ℤ) : ℝ)| ≤ K := by
          rw [hKdef, ← Int.cast_abs]; exact_mod_cast hcK
        push_cast
        nlinarith
      · dsimp only; rw [hsel']
        have := hI.cntb
        omega
      · dsimp only; rw [hT1]; exact hKM₃
      · rw [(lf₃.1 100 (by omega)).1, (g₂.1 100 (by omega)).1, f₁.1 100 (by omega)]
        exact hI.r100
      · rw [(lf₃.1 101 (by omega)).1, (g₂.1 101 (by omega)).1, f₁.1 101 (by omega)]
        exact hI.r101
      · rw [(lf₃.1 100 (by omega)).2, (g₂.1 100 (by omega)).2, f₁.2.1 100 (by omega)]
        exact hI.q100
      · rw [(lf₃.1 102 (by omega)).1, b102]
      · rw [(lf₃.1 103 (by omega)).1, b103]; rfl
      · obtain ⟨h1, h2, h3, h4⟩ := fr₂
        refine ⟨fun r hr => ?_, ?_, fun a ha => ?_, fun a ha han => ?_⟩
        · rw [(lf₃.1 r (by omega)).1, (lf₃.1 r (by omega)).2]; exact h1 r hr
        · rw [lf₃.2]; exact h2
        · rw [rm₃ a ha]; exact h3 a ha
        · rw [nm₃ a ha (by have := hLay.prim.f_lt (M.head d₀); unfold aTP; omega)]
          exact h4 a ha han
    · simp only [MvG.cnt, hdone]; simp; ring
    · simp only [MvG.ext, hdone, Bool.false_eq_true, ite_false]
      rw [hsel']
      have := hred
      omega
  · -- the end of the loop
    have b103 : c₂.nreg 103 = 0 := by rw [hc₂]; config_simp; rw [a198, ite_eq_right hlt]
    have o₃ : ORunC P Wd Hc B n .skip c₂ (runOpsE n Fo₀ hs).1 G₁ c₂ [] G₁ 0 0 :=
      ORunC.skip o₂.1.2.wb o₂.1.2.lcte
    have o := o₁.seq (o₂.seq (ORunC.ifLtN_false (a := 102) (b := 103) (t := pivS B nD)
      (by rw [b102, b103]; omega) o₃))
    simp only [List.nil_append] at o
    refine ⟨{ x with done := true }, c₂, [], G₁, 1 + (0 + 0), 0 + (1 + (0 + 2)), o, ?_, ?_, ?_,
      by norm_num, by norm_num, by rw [List.append_nil]; exact hV, hLo0⟩
    · refine ⟨by rw [List.append_nil]; exact o₂.1.2.lcte, o₂.1.2.wb, ?_, ?_, ?_, hI.T0, hI.v0, hI.sel,
        hI.low, hI.Ts, hI.vals,
        hI.rinv, hI.compat, hI.vinv, hI.red, hI.lo, hI.cntb, hKM₂, ?_, ?_, ?_, b102, ?_,
        fun _ => hstop hlt, fr₂⟩
      · rw [List.append_nil]; exact hI.st
      · rw [List.append_nil]; exact hI.out
      · rw [List.append_nil]; exact hI.len
      · rw [(g₂.1 100 (by omega)).1, f₁.1 100 (by omega)]; exact hI.r100
      · rw [(g₂.1 101 (by omega)).1, f₁.1 101 (by omega)]; exact hI.r101
      · rw [(g₂.1 100 (by omega)).2, f₁.2.1 100 (by omega)]; exact hI.q100
      · rw [b103]; rfl
    · simp only [MvG.cnt, hdone]; simp
    · simp only [MvG.ext, hdone]; simp; omega

theorem mv_orunC (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (H : MoveHyp (pieceGraph M S ℓ) u v) (hU : UniqTight (pieceGraph M S ℓ))
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d)
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach (pieceGraph M S ℓ) v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach (pieceGraph M S ℓ) v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) (hLay : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {A Wt : ℝ} (hwtb : ∀ d, |(wt d : ℝ)| ≤ Wt)
    (hTA : Wt + W + |((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)| ≤ A - Lo₀)
    (hHA : 30 * (A - ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)) ≤ Hc)
    (hC₀ : Compat T₀ u v e (tpar (pieceGraph M S ℓ) u)) (hV₀ : VInv T₀ φ wt val₀)
    (hS₀ : Stored M n ιv ιg ιf ιe φ (M.face e) Lo₀ Fo₀ T₀ val₀)
    (hLo : ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ) +
      Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo₀)
    {c : Config} (hc : WordsBounded Wd c) {G : List VT} (hS : LCTE B n Fo₀ G c)
    (hVB₀ : VBnd (A - Lo₀) n Fo₀)
    (hKM : KMem M σ ιv T₀ wt φ c) (h100 : c.nreg 100 = ιf (M.face (M.rev e)))
    (h101 : c.nreg 101 = ιf (M.face e))
    (q100 : c.rreg 100 = ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)) (h102 : c.nreg 102 = 0)
    (h103 : c.nreg 103 = 1) :
    ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (d : ℕ → D) (m : ℕ) (os : List EOp)
      (c' : Config) (G' : List VT) (Lo : ℝ),
      ORunC P Wd Hc B n (mvLoopS B nD) c Fo₀ G c' os G' (27 * m + 1)
        (101 * (Fintype.card V + 1) + 2) ∧
      T 0 = T₀ ∧ val 0 = val₀ ∧
      DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val
        (selForest M S (tpar (pieceGraph M S ℓ) u) d) d m ∧
      (∀ i < m, (T (i + 1)).root = (T i).root ∧
        (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i)) ∧
      os.length = 16 * m ∧ (runOpsE n Fo₀ os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ (M.face e) Lo (runOpsE n Fo₀ os).1 (T m) (val m) ∧
      Lo₀ - Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo ∧
      KMem M σ ιv (T m) wt φ c' ∧ MvFr B n c c' ∧ c'.nreg 100 = c.nreg 100 ∧
      c'.nreg 101 = c.nreg 101 ∧ c'.rreg 100 = c.rreg 100 ∧ c'.nreg 102 = 0 ∧
      VBnd (A - Lo) n (runOpsE n Fo₀ os).1 ∧ Lo ≤ Lo₀ := by
  classical
  set K : ℝ := (driftK L W (Fintype.card V) : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have : (0 : ℤ) ≤ driftK L W (Fintype.card V) := by simp only [driftK]; positivity
    rw [hKdef]; exact_mod_cast this
  have hr0 := card_le_univ (redSet M S ℓ u v (tpar (pieceGraph M S ℓ) u))
  have hr0' : (((redSet M S ℓ u v (tpar (pieceGraph M S ℓ) u)).card : ℕ) : ℝ) ≤
      Fintype.card V := by exact_mod_cast hr0
  let x₀ : MvG M := ⟨fun _ => T₀, fun _ => val₀, fun _ => e, 0, false, Lo₀⟩
  have hI₀ : MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c Wd x₀ [] G c :=
    ⟨hS, hc, hS₀, rfl, rfl, rfl, rfl, fun j hj => absurd hj (by simp [x₀]),
      fun j hj => absurd hj (by simp [x₀]), fun j hj => absurd hj (by simp [x₀]),
      fun j hj => absurd hj (by simp [x₀]), rInv_init H, hC₀, hV₀,
      by simp only [x₀, selForest]; nlinarith, by simp [x₀], by simpa [x₀, selForest] using hr0,
      hKM, h100, h101, q100, h102, by simp [x₀, h103], fun h => absurd h (by simp [x₀]),
      MvFr.refl B n c⟩
  obtain ⟨x', os, c', G', hrun, hI', ht', -, -⟩ := ORunC.whileLtN (α := MvG M) (P := P) (W := Wd) (H := Hc)
    (B := B) (n := n) (a := 102) (b := 103) (body := mvBodyS B nD) Fo₀
    (fun y hs₁ G₁ c₁ =>
      MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c Wd y hs₁ G₁ c₁ ∧
        VBnd (A - y.Lo) n (runOpsE n Fo₀ hs₁).1 ∧ y.Lo ≤ Lo₀)
    MvG.cnt (MvG.ext S ℓ u v) (fun _ _ _ _ h _ => ⟨h.1.lcte, h.1.wb⟩)
    (fun y hs₁ G₁ c₁ h _ ht => by
      obtain ⟨x', c', os, G', j, h', o, hI', hc', he', -, -, hV', hL'⟩ := mvBody_orunC hWW hWa hB
        hP hM H hU heS hrS hφ hW hwt hwL hL hLay hK hwtb hTA hHA y hs₁ G₁ c₁ h.1 h.2.1 h.2.2 ht
      exact ⟨x', c', os, G', j, h', o, ⟨hI', hV', hL'⟩, hc', he'⟩) (x := x₀) (hs := [])
    ⟨hI₀, hVB₀, le_rfl⟩ trivial
  simp only [List.nil_append] at hI'
  obtain ⟨hI', hVf, hLf⟩ := hI'
  have hdone : x'.done = true := by
    cases hd : x'.done
    · exfalso; apply ht'; rw [hI'.r102, hI'.r103, hd]; simp
    · rfl
  have hcnt : x'.cnt - x₀.cnt = 27 * x'.i + 1 := by
    simp [MvG.cnt, hdone, x₀]
  have hext : x₀.ext S ℓ u v + 2 - x'.ext S ℓ u v ≤ 101 * (Fintype.card V + 1) + 2 := by
    simp only [MvG.ext, hdone, x₀, selForest, ite_true, Bool.false_eq_true, ite_false]
    omega
  rw [hcnt] at hrun
  refine ⟨x'.T, x'.val, x'.d, x'.i, os, c', G', x'.Lo, hrun.mono le_rfl hext, hI'.T0, hI'.v0,
    ?_, hI'.Ts, by simpa using hI'.len, hI'.out, hI'.st, ?_, hI'.kmem, hI'.fr, by
      rw [hI'.r100, h100], by rw [hI'.r101, h101], by rw [hI'.q100, q100], hI'.r102, hVf, hLf⟩
  · have hC := hC₀; rw [← hI'.T0] at hC
    have hV := hV₀; rw [← hI'.T0, ← hI'.v0] at hV
    exact dataRun_of_steps hM H hU heS hrS hφ hW hwt hwL hL hC hV hI'.sel hI'.low hI'.Ts
      hI'.vals (hI'.stop hdone)
  · have h1 := hI'.lo
    have h2 := hI'.cntb
    have h3 : (x'.i : ℝ) ≤ Fintype.card V := by exact_mod_cast (by omega : x'.i ≤ Fintype.card V)
    nlinarith

theorem mv_orunAC (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (H : MoveHyp (pieceGraph M S ℓ) u v) (hU : UniqTight (pieceGraph M S ℓ))
    (heS : e ∉ S) (hrS : M.rev e ∉ S) (hφ : ∀ d ∈ S, φ d = ℓ d)
    (hW : ∀ d, |φ d| ≤ W) (hwt : ∀ d ∈ S, Reach (pieceGraph M S ℓ) v (M.tail d) → wt d = ℓ d)
    (hwL : ∀ d, (d ∈ S → ¬ Reach (pieceGraph M S ℓ) v (M.tail d)) → L ≤ wt d)
    (hL : ∀ d ∈ S, ℓ d + 4 * (Fintype.card V * W) < L) (hLay : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {A Wt : ℝ} (hwtb : ∀ d, |(wt d : ℝ)| ≤ Wt)
    (hTA : Wt + W + |((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)| ≤ A - Lo₀)
    (hHA : 30 * (A - ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)) ≤ Hc)
    (hC₀ : Compat T₀ u v e (tpar (pieceGraph M S ℓ) u)) (hV₀ : VInv T₀ φ wt val₀)
    (hS₀ : Stored M n ιv ιg ιf ιe φ (M.face e) Lo₀ Fo₀ T₀ val₀)
    (hLo : ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ) +
      Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo₀)
    {c : Config} (hc : WordsBounded Wd c) {G : List VT} (hS : LCTE B n Fo₀ G c)
    (hVB₀ : VBnd (A - Lo₀) n Fo₀)
    (hKM : KMem M σ ιv T₀ wt φ c) (h100 : c.nreg 100 = ιf (M.face (M.rev e)))
    (h101 : c.nreg 101 = ιf (M.face e))
    (q100 : c.rreg 100 = ((L - 2 * (Fintype.card V * W) : ℤ) : ℝ)) (h102 : c.nreg 102 = 0)
    (h103 : c.nreg 103 = 1) :
    ∃ (T : ℕ → DTree M.dual) (val : ℕ → D → ℤ) (d : ℕ → D) (m : ℕ) (os : List EOp)
      (c' : Config) (G' : List VT) (Lo : ℝ),
      ORunC P Wd Hc B n (mvLoopS B nD) c Fo₀ G c' os G' (2 * (27 * m + 1)) 2 ∧
      T 0 = T₀ ∧ val 0 = val₀ ∧
      DataRun S ℓ u v φ wt e (Fintype.card V * W) L T val
        (selForest M S (tpar (pieceGraph M S ℓ) u) d) d m ∧
      (∀ i < m, (T (i + 1)).root = (T i).root ∧
        (T (i + 1)).par = Function.update (T i).par (M.head (d i)) (d i)) ∧
      os.length = 16 * m ∧ (runOpsE n Fo₀ os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ (M.face e) Lo (runOpsE n Fo₀ os).1 (T m) (val m) ∧
      Lo₀ - Fintype.card V * (driftK L W (Fintype.card V) : ℝ) ≤ Lo ∧
      KMem M σ ιv (T m) wt φ c' ∧ MvFr B n c c' ∧ c'.nreg 100 = c.nreg 100 ∧
      c'.nreg 101 = c.nreg 101 ∧ c'.rreg 100 = c.rreg 100 ∧ c'.nreg 102 = 0 ∧
      VBnd (A - Lo) n (runOpsE n Fo₀ os).1 ∧ Lo ≤ Lo₀ := by
  classical
  set K : ℝ := (driftK L W (Fintype.card V) : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    have : (0 : ℤ) ≤ driftK L W (Fintype.card V) := by simp only [driftK]; positivity
    rw [hKdef]; exact_mod_cast this
  have hr0 := card_le_univ (redSet M S ℓ u v (tpar (pieceGraph M S ℓ) u))
  have hr0' : (((redSet M S ℓ u v (tpar (pieceGraph M S ℓ) u)).card : ℕ) : ℝ) ≤
      Fintype.card V := by exact_mod_cast hr0
  let x₀ : MvG M := ⟨fun _ => T₀, fun _ => val₀, fun _ => e, 0, false, Lo₀⟩
  have hI₀ : MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c Wd x₀ [] G c :=
    ⟨hS, hc, hS₀, rfl, rfl, rfl, rfl, fun j hj => absurd hj (by simp [x₀]),
      fun j hj => absurd hj (by simp [x₀]), fun j hj => absurd hj (by simp [x₀]),
      fun j hj => absurd hj (by simp [x₀]), rInv_init H, hC₀, hV₀,
      by simp only [x₀, selForest]; nlinarith, by simp [x₀], by simpa [x₀, selForest] using hr0,
      hKM, h100, h101, q100, h102, by simp [x₀, h103], fun h => absurd h (by simp [x₀]),
      MvFr.refl B n c⟩
  obtain ⟨x', os, c', G', hrun, hI', ht', -⟩ := ORunC.whileLtN_abs (α := MvG M) (P := P) (W := Wd) (H := Hc)
    (B := B) (n := n) (a := 102) (b := 103) (body := mvBodyS B nD) Fo₀
    (fun y hs₁ G₁ c₁ =>
      MvInv M S ℓ u v φ wt e W L n ιv ιg ιf ιe σ B Fo₀ T₀ val₀ Lo₀ c Wd y hs₁ G₁ c₁ ∧
        VBnd (A - y.Lo) n (runOpsE n Fo₀ hs₁).1 ∧ y.Lo ≤ Lo₀)
    MvG.cnt (MvG.ext S ℓ u v) (fun _ _ _ _ h _ => ⟨h.1.lcte, h.1.wb⟩)
    (fun y hs₁ G₁ c₁ h _ ht => by
      obtain ⟨x', c', os, G', j, h', o, hI', hc', he', hj, hh, hV', hL'⟩ := mvBody_orunC hWW hWa
        hB hP hM H hU heS hrS hφ hW hwt hwL hL hLay hK hwtb hTA hHA y hs₁ G₁ c₁ h.1 h.2.1 h.2.2 ht
      exact ⟨x', c', os, G', j, h', o, ⟨hI', hV', hL'⟩, hc', hj, by unfold opCostE; omega,
        by omega⟩)
    (x := x₀) (hs := []) ⟨hI₀, hVB₀, le_rfl⟩ trivial
  simp only [List.nil_append] at hI'
  obtain ⟨hI', hVf, hLf⟩ := hI'
  have hdone : x'.done = true := by
    cases hd : x'.done
    · exfalso; apply ht'; rw [hI'.r102, hI'.r103, hd]; simp
    · rfl
  have hcnt : x'.cnt - x₀.cnt = 27 * x'.i + 1 := by
    simp [MvG.cnt, hdone, x₀]
  rw [hcnt] at hrun
  refine ⟨x'.T, x'.val, x'.d, x'.i, os, c', G', x'.Lo, hrun, hI'.T0, hI'.v0,
    ?_, hI'.Ts, by simpa using hI'.len, hI'.out, hI'.st, ?_, hI'.kmem, hI'.fr, by
      rw [hI'.r100, h100], by rw [hI'.r101, h101], by rw [hI'.q100, q100], hI'.r102, hVf, hLf⟩
  · have hC := hC₀; rw [← hI'.T0] at hC
    have hV := hV₀; rw [← hI'.T0, ← hI'.v0] at hV
    exact dataRun_of_steps hM H hU heS hrS hφ hW hwt hwL hL hC hV hI'.sel hI'.low hI'.Ts
      hI'.vals (hI'.stop hdone)
  · have h1 := hI'.lo
    have h2 := hI'.cntb
    have h3 : (x'.i : ℝ) ≤ Fintype.card V := by exact_mod_cast (by omega : x'.i ≤ Fintype.card V)
    nlinarith

end

end Klein

end PlanarFlow
