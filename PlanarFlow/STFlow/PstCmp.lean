module

public import PlanarFlow.STFlow.PstC
public import PlanarFlow.STFlow.IsoExec
public import WordRAM.Machine.KernelRfl

/-!
# The s-t flow program compares reals within a polynomial bound

* `pst_cmpOK_of`: the compare-boundedness of `r151 := n; initS; s` (the initialisation has no
  real test) from that of `s` from every initialised configuration;
* `amtSum_buildOpsL_le`, …: the total amounts of the operations of the initialisation and of the
  change to the capacities;
* `pcore_cmpOK`: **under the hypotheses of `pcore_exec`, every run of `pstProg` from `c₀`
  compares reals at distance at most `pstH n m #F #V K`** (`ModNat.CmpOK`), `K = kH0` (which
  bounds the lengths `N c + ε`, the keys, the capacities and the threshold `kTh`), with
  `pstH = 2 pstVb`, `pstVb = n · 4 (#F + #V) K + (m + 2) (2 n K + n + 4 K) + n · 8 #F K + n + K + 1`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-- The bound of the potential of the forest along the run. -/
def pstVb (n cD cF cV K : ℕ) : ℕ :=
  n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) + n * (8 * cF * K) + n + K + 1

/-- **The bound of the compared differences** of `pstProg`. -/
def pstH (n cD cF cV K : ℕ) : ℕ := 2 * pstVb n cD cF cV K

lemma pstVb_mono {n cD cF cV K K' : ℕ} (h : K ≤ K') : pstVb n cD cF cV K ≤ pstVb n cD cF cV K' := by
  unfold pstVb
  have h1 := Nat.mul_le_mul_left (n * (4 * (cF + cV))) h
  have h2 := Nat.mul_le_mul_left (2 * n) h
  have h3 := Nat.mul_le_mul_left 4 h
  have h4 := Nat.mul_le_mul_left (n * (8 * cF)) h
  have h5 : (cD + 2) * (2 * n * K + n + 4 * K) ≤ (cD + 2) * (2 * n * K' + n + 4 * K') :=
    Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

lemma pstH_mono {n cD cF cV K K' : ℕ} (h : K ≤ K') : pstH n cD cF cV K ≤ pstH n cD cF cV K' := by
  unfold pstH; have := pstVb_mono (n := n) (cD := cD) (cF := cF) (cV := cV) h; omega

/-- **The adaptive program from a given configuration** (`lctE_adaptive_exec`): `r151 := n` and
the initialisation have no real test, so `r151 := n; initS; s` is compare-bounded when `s` is
from every configuration reached by the initialisation. -/
theorem pst_cmpOK_of {P : Input} {B n H : ℕ} {s : Stmt} {c₀ : Config}
    (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hs : ∀ c, WordsBounded (B + 16 * (n + 1)) c → LCTE B n (Forest.init n) (G0 n) c →
      c.output = c₀.output → MemFrame B n (mem c₀) (mem c) →
      (∀ r, (r < 160 ∨ 200 ≤ r) → r ≠ 151 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r) →
      ModNat.CmpOK P (B + 16 * (n + 1)) H s c) :
    ModNat.CmpOK P (B + 16 * (n + 1)) H (.seq (.instr (.constN 151 n)) (.seq (initS B) s)) c₀ := by
  have e1 := Exec.constN (P := P) hc₀ 151 n (by omega)
  obtain ⟨c2, k2, e2, hk2, hS2, hpot, hmf2, hfr2⟩ := init_exec (P := P) B n e1.wb_right le_rfl
    (by simp)
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR rfl _) fun c₁ k₁ e₁' => ?_
  obtain rfl := exec_post e1 e₁'
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR (by kernel_rfl) _) fun c₂ k₂ e₂' => ?_
  obtain rfl := exec_post e2 e₂'
  exact hs _ e2.wb_right hS2.toE (by rw [hfr2.2.2]) hmf2 (fun r hr h151 => by
    rw [(hfr2.1 r hr).1, (hfr2.1 r hr).2]; simp [upd_other _ _ _ h151])

/-! ### The amounts of the operations -/

lemma amtSum_flatMap_le {α : Type*} (xs : List α) (f : α → List EOp) {K : ℤ}
    (h : ∀ x ∈ xs, amtSum (f x) ≤ K) : amtSum (xs.flatMap f) ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, amtSum_append, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    push_cast; linarith

section Generic

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y}

/-- The total amount of the operations storing a tree with values at most `K`. -/
lemma amtSum_buildOpsL_le (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℤ) (β β₂ : Y → ℤ)
    (fs ys : List Y) {K : ℤ} (hκ : ∀ d, |κ d| ≤ K) (hβ : ∀ y, |β y| ≤ K)
    (hβ₂ : ∀ y, |β₂ y| ≤ K) :
    amtSum (buildOpsL C ιf ιe κ β β₂ fs ys) ≤ 2 * (fs.length + ys.length) * K := by
  unfold buildOpsL setOps treeValsL linkOps
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map, amtSum_append, amtSum_append]
  have h1 := amtSum_flatMap_le fs (fun y => [EOp.add (ιf y) (β y), .add2 (ιf y) (β₂ y)])
    (K := 2 * K) fun y _ => by
      simp only [amtSum_cons, amtSum_nil, EOp.amt]; linarith [hβ y, hβ₂ y]
  have h2 := amtSum_flatMap_le ys (fun y => [EOp.add (ιe (C.par y)) (κ (N.rev (C.par y))),
    .add2 (ιe (C.par y)) (κ (C.par y))]) (K := 2 * K) fun y _ => by
      simp only [amtSum_cons, amtSum_nil, EOp.amt]; linarith [hκ (C.par y), hκ (N.rev (C.par y))]
  have h3 := amtSum_flatMap_le ys (fun y => [EOp.link (ιe (C.par y)) (ιf (N.face (C.par y))),
    .link (ιf y) (ιe (C.par y))]) (K := 0) fun y _ => by simp [EOp.amt]
  simp only [mul_zero] at h3
  have e : (2 : ℤ) * ((fs.length : ℤ) + ys.length) * K = fs.length * (2 * K) + ys.length * (2 * K) :=
    by ring
  push_cast; rw [e]; linarith

end Generic

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- The lengths are at most `kZ`. -/
lemma wlen_abs_le {N : ℤ} {c ε : D → ℤ} (hN : 0 ≤ N) (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d)
    (d : D) : |wlen N c ε d| ≤ kZ D F N c ε := by
  have h1 : c d ≤ ∑ d, c d := single_le_sum (fun d _ => hc d) (mem_univ d)
  have h2 : ε d ≤ ∑ d, ε d := single_le_sum (fun d _ => hε d) (mem_univ d)
  have h3 : ∑ d, ε d ≤ lexR F ε := by
    unfold lexR; have : (0 : ℤ) ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
    nlinarith
  have h4 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
  have h5 : N * c d ≤ N * ∑ d, c d := mul_le_mul_of_nonneg_left h1 hN
  have h6 : 0 ≤ N * c d := mul_nonneg hN (hc d)
  rw [abs_of_nonneg (by unfold wlen; linarith [hε d])]
  unfold wlen kZ; linarith

/-- The capacities are at most `kZ` when `N ≥ 1`. -/
lemma cap_le_kZ {N : ℤ} {c ε : D → ℤ} (hN : 1 ≤ N) (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d)
    (d : D) : |c d| ≤ kZ D F N c ε := by
  have h1 : c d ≤ ∑ d, c d := single_le_sum (fun d _ => hc d) (mem_univ d)
  have h4 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
  have h3 : 0 ≤ lexR F ε := by unfold lexR; positivity
  have hs : 0 ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
  have h5 : ∑ d, c d ≤ N * ∑ d, c d := le_mul_of_one_le_left hs hN
  rw [abs_of_nonneg (hc d)]; unfold kZ; linarith

lemma kZ_le_kH0 {N : ℤ} {c ε : D → ℤ} (h0 : 0 ≤ kZ D F N c ε) :
    kZ D F N c ε ≤ kH0 D F N c ε := by
  unfold kH0 kTh
  have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c ε := by positivity
  linarith

lemma kTh_le_kH0 {N : ℤ} {c ε : D → ℤ} (h0 : 0 ≤ kZ D F N c ε) :
    kTh D F N c ε ≤ kH0 D F N c ε := by
  unfold kH0
  have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c ε := by positivity
  linarith

/-- The total amount of the change to the capacities. -/
lemma amtSum_cv_le (ts : List F) (T : DTree M)
    (ιF : F → ℕ) (ιG : D → ℕ) (cap w : D → ℤ) {K : ℤ} (hcap : ∀ d, |cap d| ≤ K)
    (hw : ∀ d, |w d| ≤ K) :
    amtSum (ts.flatMap fun y => pointOps ιF ιG (toDD T) y (cap (T.par y) - w (T.par y))
      (cap (M.rev (T.par y)) - w (M.rev (T.par y)))) ≤ ts.length * (8 * K) := by
  refine amtSum_flatMap_le ts _ fun y _ => ?_
  have a1 := abs_sub (cap (T.par y)) (w (T.par y))
  have a2 := abs_sub (cap (M.rev (T.par y))) (w (M.rev (T.par y)))
  simp only [pointOps, amtSum_cons, amtSum_nil, EOp.amt, abs_neg]
  linarith [hcap (T.par y), hw (T.par y), hcap (M.rev (T.par y)), hw (M.rev (T.par y))]

variable {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {B : ℕ}

/-- **The run of `pstProg` of `pcore_exec` compares reals within `pstH`**: under the hypotheses
of `pcore_exec`, every run of `pstProg B nD n` from `c₀` compares reals at distance at most
`pstH n m #F #V kH0`. -/
theorem pcore_cmpOK (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t)
    {d₀ d₁ : D} (hd₀ : M.tail d₀ = t) (hd₁ : M.tail d₁ = s) (hPO : PertOK M c ε s t d₀)
    {T₀ : DTree M}
    (hroot : T₀.root = M.face d₀)
    (hI₀ : LInv c ε s t ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩)
    {N : ℤ} (hN : 2 * lexR F ε < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = s)
    {rs : D → ℝ} {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N c ε d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N c ε d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = c d) (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = rs d)
    (hth : c₀.rmem (aTH nD) = kTh D F N c ε) (hh0 : c₀.rmem (aH0 nD) = kH0 D F N c ε) :
    ModNat.CmpOK P (B + 16 * (n + 1))
      (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V) (kH0 D F N c ε).toNat)
      (pstProg B nD n) c₀ := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  -- the constants
  have hε : ∀ d, 0 ≤ ε d := hPO.nonneg
  have hR0 : 0 ≤ lexR F ε := by
    unfold lexR; have : (0 : ℤ) ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
    positivity
  have hN1 : 1 ≤ N := by omega
  have hZ0 : 0 ≤ kZ D F N c ε := by
    have : (0 : ℤ) ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
    unfold kZ; nlinarith
  have hZH := kZ_le_kH0 hZ0
  have hTH := kTh_le_kH0 hZ0
  have hTh0 : 0 ≤ kTh D F N c ε := by unfold kTh; omega
  set Kn := (kH0 D F N c ε).toNat with hKn
  have hKe : ((Kn : ℤ)) = kH0 D F N c ε := Int.toNat_of_nonneg (by omega)
  have hKR : ((Kn : ℕ) : ℝ) = ((kH0 D F N c ε : ℤ) : ℝ) := by exact_mod_cast hKe
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (Kn : ℝ) := ⟨_, rfl⟩
  have hKw : ∀ d, |((wlen N c ε d : ℤ) : ℝ)| ≤ K := fun d => by
    rw [hKdef, hKR]; have := wlen_abs_le (F := F) (N := N) (by omega) hc hε d
    exact_mod_cast this.trans hZH
  -- the keys of the initial state
  have hμ₀ : |M.div (M.cob (T₀.psum ε)) s| ≤ lexR F ε := by
    have h0 : M.div (M.cob (T₀.psum ε)) s = 0 := M.div_cob _ s
    rw [h0, abs_zero]; exact hR0
  have hval : ∀ d, |wlen N c ε d + (toDD T₀).psum (wlen N c ε) (M.dual.tail d) -
      (toDD T₀).psum (wlen N c ε) (M.dual.head d)| ≤ (Kn : ℤ) := fun d => by
    rw [init_key N c ε T₀ d, hKe]
    exact (lkey_abs_le hM hst hI₀ hε hc hμ₀ (by omega) d).trans hZH
  have hKn0 : (0 : ℤ) ≤ Kn := Int.natCast_nonneg _
  -- the amounts
  have hAin : (n : ℝ) * (amtSum (treeOpsL (toDD T₀) ιF ιG (wlen N c ε) vs ts ++
      cotOpsL C₀ ιV ιE (fun d => wlen N c ε d + (toDD T₀).psum (wlen N c ε) (M.dual.tail d) -
        (toDD T₀).psum (wlen N c ε) (M.dual.head d)) (kH0 D F N c ε) fs cs) : ℝ) ≤
      (n : ℝ) * (4 * ((Fintype.card F : ℝ) + Fintype.card V) * K) := by
    have h1 := amtSum_buildOpsL_le (toDD T₀) ιF ιG (fun d => wlen N c ε (M.dual.rev d))
      (fun _ => 0) (fun _ => 0) vs ts (K := (Kn : ℤ))
      (fun d => by rw [← hKe] at hZH; exact (wlen_abs_le (F := F) (N := N) (by omega) hc hε _).trans hZH)
      (fun _ => by simp [hKn0]) (fun _ => by simp [hKn0])
    have h2 := amtSum_buildOpsL_le C₀ ιV ιE (fun d => wlen N c ε d +
      (toDD T₀).psum (wlen N c ε) (M.dual.tail d) - (toDD T₀).psum (wlen N c ε) (M.dual.head d))
      (fun _ => kH0 D F N c ε) (fun _ => kH0 D F N c ε) fs cs (K := (Kn : ℤ)) hval
      (fun _ => by rw [hKe, abs_of_nonneg (by omega)]) (fun _ => by rw [hKe, abs_of_nonneg (by omega)])
    have l1 := hI.oT.flen
    have l2 := hI.oT.ylen
    have l3 := hI.oC.flen
    have l4 := hI.oC.ylen
    have e : amtSum (treeOpsL (toDD T₀) ιF ιG (wlen N c ε) vs ts ++
        cotOpsL C₀ ιV ιE (fun d => wlen N c ε d + (toDD T₀).psum (wlen N c ε) (M.dual.tail d) -
          (toDD T₀).psum (wlen N c ε) (M.dual.head d)) (kH0 D F N c ε) fs cs) ≤
        4 * ((Fintype.card F : ℤ) + Fintype.card V) * Kn := by
      rw [amtSum_append]
      have h1' : amtSum (treeOpsL (toDD T₀) ιF ιG (wlen N c ε) vs ts) ≤
          2 * ((vs.length : ℤ) + ts.length) * Kn := h1
      have h2' : amtSum (cotOpsL C₀ ιV ιE (fun d => wlen N c ε d +
          (toDD T₀).psum (wlen N c ε) (M.dual.tail d) -
          (toDD T₀).psum (wlen N c ε) (M.dual.head d)) (kH0 D F N c ε) fs cs) ≤
          2 * ((fs.length : ℤ) + cs.length) * Kn := h2
      have m1 : 2 * ((vs.length : ℤ) + ts.length) * Kn ≤ 2 * ((Fintype.card F : ℤ) +
          Fintype.card F) * Kn := by
        gcongr <;> first | exact_mod_cast l1.le | exact_mod_cast l2
      have m2 : 2 * ((fs.length : ℤ) + cs.length) * Kn ≤ 2 * ((Fintype.card V : ℤ) +
          Fintype.card V) * Kn := by
        gcongr <;> first | exact_mod_cast l3.le | exact_mod_cast l4
      nlinarith
    have e' : (amtSum (treeOpsL (toDD T₀) ιF ιG (wlen N c ε) vs ts ++
        cotOpsL C₀ ιV ιE (fun d => wlen N c ε d + (toDD T₀).psum (wlen N c ε) (M.dual.tail d) -
          (toDD T₀).psum (wlen N c ε) (M.dual.head d)) (kH0 D F N c ε) fs cs) : ℝ) ≤
        4 * ((Fintype.card F : ℝ) + Fintype.card V) * K := by
      rw [hKdef]; exact_mod_cast e
    exact mul_le_mul_of_nonneg_left e' (Nat.cast_nonneg n)
  have hAcv : ∀ T : DTree M, (n : ℝ) * (amtSum (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (c (T.par y) - wlen N c ε (T.par y)) (c (M.rev (T.par y)) - wlen N c ε (M.rev (T.par y))))
        : ℝ) ≤ (n : ℝ) * (8 * (Fintype.card F : ℝ) * K) := fun T => by
    have h := amtSum_cv_le ts T ιF ιG c (wlen N c ε) (K := (Kn : ℤ))
      (fun d => by rw [hKe]; exact (cap_le_kZ (F := F) (N := N) hN1 hc hε d).trans hZH)
      (fun d => by rw [hKe]; exact (wlen_abs_le (F := F) (N := N) (by omega) hc hε d).trans hZH)
    have l2 := hI.oT.ylen
    have h' : (amtSum (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
        (c (T.par y) - wlen N c ε (T.par y)) (c (M.rev (T.par y)) - wlen N c ε (M.rev (T.par y))))
        : ℤ) ≤ 8 * (Fintype.card F : ℤ) * Kn := by
      have : (ts.length : ℤ) * (8 * Kn) ≤ (Fintype.card F : ℤ) * (8 * Kn) := by
        gcongr <;> exact_mod_cast l2
      linarith
    have h'' : (amtSum (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
        (c (T.par y) - wlen N c ε (T.par y)) (c (M.rev (T.par y)) - wlen N c ε (M.rev (T.par y))))
        : ℝ) ≤ 8 * (Fintype.card F : ℝ) * K := by rw [hKdef]; exact_mod_cast h'
    exact mul_le_mul_of_nonneg_left h'' (Nat.cast_nonneg n)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; exact Nat.cast_nonneg _
  have hZK : ((kZ D F N c ε : ℤ) : ℝ) ≤ K := by rw [hKdef, hKR]; exact_mod_cast hZH
  have hΔ : 2 * (n : ℝ) * (kZ D F N c ε : ℝ) + n + 4 * K ≤ 2 * n * K + n + 4 * K := by
    have := mul_le_mul_of_nonneg_left hZK hnR; nlinarith
  have hVb : (n : ℝ) * (4 * ((Fintype.card F : ℝ) + Fintype.card V) * K) +
      ((Fintype.card D : ℝ) + 2) * (2 * n * K + n + 4 * K) + (n : ℝ) * (8 * (Fintype.card F : ℝ) * K)
        + n ≤ (pstVb n (Fintype.card D) (Fintype.card F) (Fintype.card V) Kn : ℝ) := by
    unfold pstVb; push_cast; rw [← hKdef]; linarith
  have hTh : |((kTh D F N c ε : ℤ) : ℝ)| ≤ (pstVb n (Fintype.card D) (Fintype.card F)
      (Fintype.card V) Kn : ℝ) := by
    rw [abs_of_nonneg (by exact_mod_cast hTh0)]
    have h1 : ((kTh D F N c ε : ℤ) : ℝ) ≤ K := by rw [hKdef, hKR]; exact_mod_cast hTH
    have h2 : (Kn : ℝ) ≤ (pstVb n (Fintype.card D) (Fintype.card F) (Fintype.card V) Kn : ℝ) := by
      unfold pstVb; push_cast
      have : (0 : ℝ) ≤ (n : ℝ) * (4 * ((Fintype.card F : ℝ) + Fintype.card V) * Kn) := by
        positivity
      have : (0 : ℝ) ≤ ((Fintype.card D : ℝ) + 2) * (2 * n * Kn + n + 4 * Kn) := by positivity
      have : (0 : ℝ) ≤ (n : ℝ) * (8 * (Fintype.card F : ℝ) * Kn) := by positivity
      linarith
    linarith
  -- the run
  refine pst_cmpOK_of hc₀ fun cf hcf hS hout hmf _ => ?_
  have hm : ∀ a, a < B → cf.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
  obtain ⟨-, -, -, -, -, -, -, -, hcmp⟩ := pstS_orunC le_rfl (by omega) hB hB7 hP hM
    hc hst hd₀ hPO hd₁ hroot hI₀ hN hL hK hG hI hoff hCr (rs := rs) hcf hS
    (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
    (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
    (fun d => by rw [hm _ (by have := hσ d; unfold aCP; omega)]; exact hcp d)
    (fun d => by rw [hm _ (by have := hσ d; unfold aRS; omega)]; exact hrs d)
    (by rw [hm _ (by unfold aTH; omega)]; exact hth)
    (by rw [hm _ (by unfold aH0; omega)]; exact hh0)
    (H := pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V) Kn) hKw hΔ hAin hAcv hVb
    (by unfold pstH; push_cast; linarith) hTh (by unfold pstH pstVb; omega)
  exact hcmp

section Exists

variable {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {B : ℕ}

open Classical in
/-- **The compare-boundedness of `pstflowE_exec`**: under its hypotheses, every run of
`pstProg` from `c₀` compares reals at distance at most `pstH n m #F #V kH0` (`pcore_cmpOK`). -/
theorem pstflowE_cmpOK {E : V → D → ℤ} (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B)
    (hB7 : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty) (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    (hPO : PertOK M (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose) hY.choose)
    {st : LSt M} (hlin : linit M (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose)
      (M.face hY.choose) = some st) {d₁ : D} (hd₁ : M.tail d₁ = hX.choose)
    {N : ℤ} (hN : 2 * lexR F (E (M.tail hY.choose)) < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else hY.choose) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD st.T) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD st.T).InT (C₀.par x)) (hCr : C₀.root = hX.choose)
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N (capR M c X Y) (E (M.tail hY.choose)) d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N (capR M c X Y) (E (M.tail hY.choose)) d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = capR M c X Y d)
    (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1)
    (hth : c₀.rmem (aTH nD) = kTh D F N (capR M c X Y) (E (M.tail hY.choose)))
    (hh0 : c₀.rmem (aH0 nD) = kH0 D F N (capR M c X Y) (E (M.tail hY.choose))) :
    ModNat.CmpOK P (B + 16 * (n + 1)) (pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V)
      (kH0 D F N (capR M c X Y) (E (M.tail hY.choose))).toNat) (pstProg B nD n) c₀ := by
  have hst : hX.choose ≠ M.tail hY.choose := fun h =>
    disjoint_left.1 hXY hX.choose_spec (h ▸ hY.choose_spec)
  obtain ⟨hroot, hIst⟩ := linit_inv _ _ hlin
  have hst₀ := linit_eq hlin
  have hI₀ : LInv (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose)
      ⟨M.cob (st.T.psum (capR M c X Y)), M.cob (st.T.psum (E (M.tail hY.choose))), st.T⟩ := by
    rw [← hst₀]; exact hIst
  exact pcore_cmpOK hWa hB hB7 hP hM
    (capR_nonneg hc X Y) hst rfl hd₁ hPO
    hroot hI₀ hN hL hK hG hI hoff hCr hc₀ hwt hph hcp hrs
    hth hh0

open Classical in
/-- **`pstflowE_exec_exists` with bounded comparisons**: the starting configuration also has
its real registers `0`, and every run of `pstProg` from it compares reals at distance at most
`pstH n m #F #V kH0` (`pstflowE_cmpOK`). -/
theorem pstflowE_exec_exists_cmp {E : V → D → ℤ} (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    (hE : ∀ (s t : V) (d₀ : D), s ≠ t → M.tail d₀ = t → PertOK M (capR M c X Y) (E t) s t d₀) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      7 * Fintype.card D + 3 ≤ B ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflowE M E c X Y d) ∧
      c'.output = c₀.output ∧
      (∀ a, ∃ z : ℤ, c₀.rmem a = z ∧
        |z| ≤ kH0 D F (2 * lexR F (E (M.tail hY.choose)) + 1) (capR M c X Y)
          (E (M.tail hY.choose))) ∧ (∀ r, c₀.rreg r = 0) ∧
      ModNat.CmpOK P (B + 16 * (n + 1)) (pstH n (Fintype.card D) (Fintype.card F)
        (Fintype.card V) (kH0 D F (2 * lexR F (E (M.tail hY.choose)) + 1) (capR M c X Y)
          (E (M.tail hY.choose))).toNat) (pstProg B (Fintype.card D) n) c₀ := by
  have : Nonempty D := ⟨hY.choose⟩
  set s := hX.choose with hs
  set d₀ := hY.choose with hd₀
  set t := M.tail d₀ with ht
  have hst : s ≠ t := fun h => disjoint_left.1 hXY hX.choose_spec (by
    have := hY.choose_spec; rw [← hd₀, ← ht, ← h, hs] at this; exact this)
  set c' := capR M c X Y with hc'
  set ε := E t with hε
  have hPO : PertOK M c' ε s t d₀ := hE s t d₀ hst rfl
  obtain ⟨st, hlin, -, -, -, -⟩ := linit_spec hM (capR_nonneg (M := M) hc X Y)
    hPO.nonneg s t (M.face d₀)
  obtain ⟨d₁, hd₁⟩ := exists_dart_tail hM hst.symm
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := exists_layout M.dual
  obtain ⟨C, hCr, hoff⟩ := exists_cotree (M := M.dual) hM.dual (toDD st.T) s
  have hOT := orders_exist (toDD st.T)
  have hOC := orders_exist C
  set vs := (univ : Finset F).toList
  set ts := depthOrder (toDD st.T)
  set fs := (univ : Finset V).toList
  set cs := depthOrder C
  set nD := Fintype.card D with hnD
  set n := 2 * (Fintype.card F + Fintype.card V + Fintype.card D) with hn
  set σ : D ≃ Fin nD := Fintype.equivFin D with hσdef
  set g : ℕ → D := fun i => if i = 0 then d₁ else d₀ with hg
  set P := kInput M.dual ∅ 0 σ ιv ιg ιf ιe n 2 g (toDD st.T) C vs ts fs cs with hP
  set B := P.data.sum + 9 * nD + 7 * n + 6 + n + 2 * nD + 7 * nD + 3 with hB
  set N : ℤ := 2 * lexR F ε + 1 with hN
  set rs : D → ℝ := fun d => if Inside M X Y d then 0 else 1 with hrs
  set c₀ : Config := { initConfig with
    rmem := (pReal σ (wlen N c' ε) c' rs (kTh D F N c' ε) (kH0 D F N c' ε)) } with hc₀
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hvl := hOT.flen
  have htl := hOT.ylen
  have hfl := hOC.flen
  have hcl := hOC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hv
  have hVn : 2 * Fintype.card V ≤ n := hL.hf
  have hD1 : 1 ≤ nD := Fintype.card_pos_iff.2 ⟨d₀⟩
  have hK : KInput M.dual ∅ 0 σ ιv ιg ιf ιe P := ⟨kInput_rv, kInput_nf, kInput_ne, kInput_ng,
    kInput_nt, kInput_nh, kInput_is, fun d _ => kInput_ln d, kInput_ed hL.dual⟩
  have hG : KBnd 2 g σ n P := fun i hi => kInput_gb hi
  have hI : KInit M.dual σ ιv ιf n 2 (toDD st.T) C vs ts fs cs P := by
    refine ⟨hOT, hOC, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_,
      ?_⟩
    · rw [kInput_iv (by omega)]; simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIT nD n 2 = iIV nD n 2 + 1 * n by unfold iIT; ring, kInput_it (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIF nD n 2 = iIV nD n 2 + 2 * n by unfold iIF; ring, kInput_if (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIC nD n 2 = iIV nD n 2 + 3 * n by unfold iIC; ring, kInput_ic (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 0) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 1) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 2) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 3) (by norm_num)
  have hPb : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1) := fun i => by
    have h1 := layList_le (kRegs M.dual ∅ 0 σ ιv ιg ιf ιe n 2 g (toDD st.T) C vs ts fs cs) i
    rw [← kInput_data, ← hP] at h1
    omega
  have hσs : ∀ d (a : ℕ) (h : a < nD), (σ d : ℕ) = a → σ.symm ⟨a, h⟩ = d := fun d a h e => by
    rw [Equiv.symm_apply_eq]; exact Fin.ext e.symm
  have hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N c' ε d := fun d => by
    show pReal σ _ _ _ _ _ (aWT + σ d) = _
    simp only [pReal, aWT, zero_add, hσ d, ↓reduceDIte]
    rw [hσs d _ (hσ d) rfl]
  have hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N c' ε d := fun d => by
    show pReal σ _ _ _ _ _ (aPH nD + σ d) = _
    have h1 : ¬ nD + (σ d : ℕ) < nD := by omega
    have h2 : nD + (σ d : ℕ) - nD < nD := by have := hσ d; omega
    simp only [pReal, aPH, h1, h2, ↓reduceDIte]
    rw [hσs d _ h2 (by omega)]
  have hcp : ∀ d, c₀.rmem (aCP nD + σ d) = c' d := fun d => by
    show pReal σ _ _ _ _ _ (aCP nD + σ d) = _
    have := hσ d
    have h1 : ¬ 3 * nD + 3 + (σ d : ℕ) < nD := by omega
    have h2 : ¬ 3 * nD + 3 + (σ d : ℕ) - nD < nD := by omega
    have h3 : 3 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 1 := by omega
    have h4 : 3 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 2 := by omega
    have h5 : 3 * nD + 3 ≤ 3 * nD + 3 + (σ d : ℕ) ∧ 3 * nD + 3 + (σ d : ℕ) - (3 * nD + 3) < nD :=
      ⟨by omega, by omega⟩
    simp only [pReal, aCP, h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte, and_self]
    rw [hσs d _ h5.2 (by omega)]
  have hrs' : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1 := fun d => by
    show pReal σ _ _ _ _ _ (aRS nD + σ d) = _
    have := hσ d
    have h1 : ¬ 4 * nD + 3 + (σ d : ℕ) < nD := by omega
    have h2 : ¬ 4 * nD + 3 + (σ d : ℕ) - nD < nD := by omega
    have h3 : 4 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 1 := by omega
    have h4 : 4 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 2 := by omega
    have h5 : ¬ (3 * nD + 3 ≤ 4 * nD + 3 + (σ d : ℕ) ∧
        4 * nD + 3 + (σ d : ℕ) - (3 * nD + 3) < nD) := by omega
    have h6 : 4 * nD + 3 ≤ 4 * nD + 3 + (σ d : ℕ) ∧ 4 * nD + 3 + (σ d : ℕ) - (4 * nD + 3) < nD :=
      ⟨by omega, by omega⟩
    simp only [pReal, aRS, h1, h2, h3, h4, h5, h6, ↓reduceDIte, ↓reduceIte, and_self]
    rw [hσs d _ h6.2 (by omega)]
  have hth : c₀.rmem (aTH nD) = kTh D F N c' ε := by
    show pReal σ _ _ _ _ _ (aTH nD) = _
    have h1 : ¬ 3 * nD + 1 < nD := by omega
    have h2 : ¬ 3 * nD + 1 - nD < nD := by omega
    simp [pReal, aTH, h1, h2]
  have hh0 : c₀.rmem (aH0 nD) = kH0 D F N c' ε := by
    show pReal σ _ _ _ _ _ (aH0 nD) = _
    have h1 : ¬ 3 * nD + 2 < nD := by omega
    have h2 : ¬ 3 * nD + 2 - nD < nD := by omega
    simp [pReal, aH0, h1, h2]
  have hlr : 0 ≤ lexR F ε := by
    unfold lexR
    have : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
    positivity
  obtain ⟨c'', steps, e, hsteps, hOUT, hout⟩ := pstflowE_exec (E := E) (by omega) (by omega)
    (by omega) hPb hM hc hX hY hXY hPO hlin hd₁ (N := N)
    (by show 2 * lexR F ε < N; rw [hN]; omega) hL hK hG hI hoff hCr
    (c₀ := c₀) (wordsBounded_initConfig _ : WordsBounded (B + 16 * (n + 1)) c₀) hwt hph hcp hrs'
    hth hh0
  have hcmp := pstflowE_cmpOK (E := E) (by omega) (by omega)
    (by omega) hPb hM hc hX hY hXY hPO hlin hd₁ (N := N)
    (by show 2 * lexR F ε < N; rw [hN]; omega) hL hK hG hI hoff hCr
    (c₀ := c₀) (wordsBounded_initConfig _ : WordsBounded (B + 16 * (n + 1)) c₀) hwt hph hcp hrs'
    hth hh0
  refine ⟨n, B, P, c₀, c'', steps, rfl, by rw [hB, hnD]; omega, e, hsteps.trans ?_, hOUT, hout,
    fun a => ?_, fun r => rfl, hcmp⟩
  · have := (pst_steps_le_m hM (by omega)).1
    rw [hn, show Fintype.card F + Fintype.card V + Fintype.card D =
      Fintype.card V + Fintype.card F + Fintype.card D by ring]
    exact this
  · -- the real memory: integers of absolute value at most `kH0`
    have hc0 : ∀ d, 0 ≤ c' d := capR_nonneg hc X Y
    have hS : 0 ≤ ∑ d, c' d := sum_nonneg fun d _ => hc0 d
    have hE0 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
    have hεle : ∀ d, ε d ≤ lexR F ε := fun d => by
      have h1 : ε d ≤ ∑ d, ε d := single_le_sum (fun d _ => hPO.nonneg d) (mem_univ d)
      unfold lexR; nlinarith
    have hcle : ∀ d, c' d ≤ ∑ d, c' d := fun d => single_le_sum (fun d _ => hc0 d) (mem_univ d)
    have hZ : 0 ≤ kZ D F N c' ε := by unfold kZ; positivity
    have hTh : kTh D F N c' ε ≤ kH0 D F N c' ε := by
      unfold kH0; have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c' ε := by positivity
      linarith
    have hNpos : 1 ≤ N := by rw [hN]; omega
    have hw : ∀ d, |wlen N c' ε d| ≤ kH0 D F N c' ε := fun d => by
      have h1 := hεle d
      have h2 : N * c' d ≤ N * ∑ d, c' d := mul_le_mul_of_nonneg_left (hcle d) (by omega)
      have h3 : 0 ≤ N * c' d := mul_nonneg (by omega) (hc0 d)
      rw [abs_le]; unfold wlen
      constructor
      · have := hPO.nonneg d; unfold kH0 kTh at *; linarith
      · unfold kH0 kTh kZ at *; linarith
    have hcap : ∀ d, |c' d| ≤ kH0 D F N c' ε := fun d => by
      rw [abs_of_nonneg (hc0 d)]
      have h2 : ∑ d, c' d ≤ N * ∑ d, c' d := le_mul_of_one_le_left hS hNpos
      unfold kH0 kTh kZ at *
      have := hcle d
      linarith
    obtain ⟨z, hz, hzle⟩ := pReal_int σ (wlen N c' ε) c' rs (fun d => by
        simp only [hrs]; split_ifs <;> simp) (kTh D F N c' ε) (kH0 D F N c' ε)
      (kH0 D F N c' ε) hw hcap (by rw [abs_of_nonneg (by unfold kTh; omega)]; exact hTh)
      (by rw [abs_of_nonneg (by linarith [hTh, show 0 ≤ kTh D F N c' ε by unfold kTh; omega])])
      (by linarith [hTh, show 1 ≤ kTh D F N c' ε by unfold kTh; omega]) a
    exact ⟨z, hz, hzle⟩

open Classical in
/-- **`pstflowW_exec_exists` with bounded comparisons**: for every plane map with transitive
rotations and faces, nonnegative capacities, `X` nonempty, a dart whose tail is in `Y`, `X`, `Y`
disjoint, there are an input, a word bound and a starting configuration (real memory: integers of
absolute value at most `isoW_bound`; real registers `0`) from which `pstProg` runs within
`504 000 000 · m lg m` steps and ends with `OUT[d] = pstflowW M c X Y d`, **every run of
`pstProg` from it comparing reals at distance at most
`pstH n m #F #V isoW_bound`** (`ModNat.CmpOK`). -/
theorem pstflowW_exec_exists_cmp (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      7 * Fintype.card D + 3 ≤ B ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflowW M c X Y d) ∧
      c'.output = c₀.output ∧
      (∀ a, ∃ z : ℤ, c₀.rmem a = z ∧ |z| ≤ isoW_bound D V F (capR M c X Y)) ∧
      (∀ r, c₀.rreg r = 0) ∧
      ModNat.CmpOK P (B + 16 * (n + 1)) (pstH n (Fintype.card D) (Fintype.card F)
        (Fintype.card V) (isoW_bound D V F (capR M c X Y)).toNat)
        (pstProg B (Fintype.card D) n) c₀ := by
  have : Nonempty D := ⟨hY.choose⟩
  simp only [pstflowW_eq_E]
  obtain ⟨n, B, P, c₀, c', steps, h1, hB7, h2, h3, h4, h5, h6, h7, h8⟩ :=
    pstflowE_exec_exists_cmp hM hc hX hY hXY fun s t d₀ hst hd₀ =>
      pertOK_iso hM hrot hface (capR_nonneg hc X Y) hst hd₀
  have hK := kH0_iso_le hM (M.tail hY.choose) (capR_nonneg (M := M) hc X Y)
  refine ⟨n, B, P, c₀, c', steps, h1, hB7, h2, h3, h4, h5, fun a => ?_, h7,
    ModNat.CmpOK.mono h8 (pstH_mono (Int.toNat_le_toNat hK))⟩
  obtain ⟨z, hz, hzle⟩ := h6 a
  exact ⟨z, hz, hzle.trans hK⟩

end Exists

end STFlow

end PlanarFlow
