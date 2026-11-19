module

public import PlanarFlow.NegSSSP.KNatFace

/-!
# The word bound of the explicit encoding of a one-face instance

`Klein.kval_kInputT` meets `Klein.KVal` with the word bound `Klein.kB`, which contains the sum
`P.data.sum` of all the input words (quadratic in the size of the map, and more: it contains the
lengths). Here a sharper bound, and a lower bound showing what can and cannot be had:

* `Klein.kInputT_le`: **every word of `kInputT` is at most `#D + n + lenMax ℓ`** (`lenMax ℓ` the
  largest length word `(ℓ d).toNat`): the darts' numbers are `< #D`, the nodes `< n`, the
  offsets of the out-lists `≤ #D`, the lengths of the orders `≤ n`, the flags and reach bits
  `≤ 1`, the lengths `≤ lenMax ℓ`.
* `Klein.kBL`, `Klein.kval_kInputT'`: **`KVal` with the word bound
  `kBL = 9 #D + 7 n + k + 4 + 2 t + aOUT #D + k t + n + 2 #D + lenMax ℓ`**, linear in the size of
  the map plus the largest length.
* `Klein.kval_len_le`: **the lengths are input words**: under `KVal` with the word bound `B`,
  every length `(ℓ d).toNat` of a dart of the piece is at most `B + 16 (n + 1)`
  (`KInput.ln` and the bound of the words). So no encoding meeting `KVal` has a word bound below
  the largest length of the piece.
* `NegSSSP.fencNat_exists'`: `FEncNat` met by the explicit words with
  `Bw = kBL … (lenMax (srcIso …))`.
* `NegSSSP.fencNat_isoN2_le`: **for the isolating lengths the work space is at least cubic**:
  under `FEncNat fd ℓ n Bw σ w Pk`, `isoN2 #V' #D' #F' = (#V' #D' + 1)(2 #F' #V' + 1) ≤
  Bw + 16 (n + 1)` (`V'`, `D'`, `F'` those of the map with the sources copied): the length of
  the dart `down` of the first root is at least `isoN2`. Since the natural node
  (`node_exec_natN`) charges `17 (Bw + 16 (n + 1))` steps per part (`partNCost`), **its cost is
  not `O(m lg m)` for any encoding meeting `FEncNat`**: the word bound and the size of Klein's
  work space are the same parameter `Bw` in `KVal`, and the lengths are input words.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Bounds of lists of regions -/

lemma lay_le_of {b : ℕ} : ∀ (rs : List (ℕ × (ℕ → ℕ))), (∀ r ∈ rs, ∀ i, r.2 i ≤ b) →
    ∀ a, lay rs a ≤ b
  | [], _, _ => by simp [lay]
  | r :: rs, h, a => by
    simp only [lay]
    split_ifs
    · exact h r (by simp) a
    · exact lay_le_of rs (fun r' hr' => h r' (by simp [hr'])) _

lemma layList_le_of {b : ℕ} {rs : List (ℕ × (ℕ → ℕ))} (h : ∀ r ∈ rs, ∀ i, r.2 i ≤ b) (a : ℕ) :
    (layList rs).getD a 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : (layList rs)[a]? with _ | x
  · simp
  · have hm := List.mem_of_getElem? hx
    unfold layList at hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hm
    exact lay_le_of rs h _

lemma getD_le_of {b : ℕ} {l : List ℕ} (h : ∀ x ∈ l, x ≤ b) (j : ℕ) : l.getD j 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : l[j]? with _ | x
  · simp
  · exact h x (List.mem_of_getElem? hx)

lemma dReg_le {nD b : ℕ} (σ : D ≃ Fin nD) {f : D → ℕ} (h : ∀ d, f d ≤ b) (j : ℕ) :
    (dReg σ f).2 j ≤ b := by
  unfold dReg
  dsimp only
  split_ifs
  · exact h _
  · exact Nat.zero_le _

lemma outB_add_le (M : CombMap D V F) (S : Finset D) (x : V) :
    outB M S x + (outL M S x).length ≤ S.card := by
  have hsplit := allOut_split M S x
  have := congrArg List.length hsplit
  rw [allOut_length] at this
  simp only [List.length_append] at this
  unfold outB; omega

/-! ### The words of the explicit encoding -/

/-- **The largest length word.** -/
def lenMax (ℓ : D → ℤ) : ℕ := (univ : Finset D).sup fun d => (ℓ d).toNat

lemma le_lenMax (ℓ : D → ℤ) (d : D) : (ℓ d).toNat ≤ lenMax ℓ :=
  Finset.le_sup (f := fun d => (ℓ d).toNat) (mem_univ d)

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **Every word of the explicit encoding is at most `#D + n + lenMax ℓ`.** -/
theorem kInputT_le {n : ℕ} (σ : D ≃ Fin (Fintype.card D))
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    {T : DTree M.dual} {C : DTree M} {vs ts : List V} {fs cs : List F}
    (hOT : Orders T vs ts) (hOC : Orders C fs cs) (t : ℕ) (X : ℕ → V) (a : ℕ) :
    (kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X).data.getD a 0 ≤
      Fintype.card D + n + lenMax ℓ := by
  classical
  set b := Fintype.card D + n + lenMax ℓ with hb
  have hσ : ∀ d : D, (σ d : ℕ) ≤ b := fun d => by have := (σ d).2; omega
  have hv : ∀ x, ιv x ≤ b := fun x => by have := hL.prim.f_lt x; omega
  have hg : ∀ d, ιg d ≤ b := fun d => by have := hL.prim.e_lt d; omega
  have hf : ∀ y, ιf y ≤ b := fun y => by have := hL.dual.f_lt y; omega
  have he : ∀ d, ιe d ≤ b := fun d => by have := hL.dual.e_lt d; omega
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  have hVn := hL.hv
  have hFn := hL.hf
  have hvl := hOT.flen
  have htl := hOT.ylen
  have hfl := hOC.flen
  have hcl := hOC.ylen
  show (layList _).getD a 0 ≤ b
  refine layList_le_of (fun r hr i => ?_) a
  simp only [kRegs, kRegsX, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dReg_le σ (fun d => hσ _) i
  · exact dReg_le σ (fun d => hf _) i
  · exact dReg_le σ he i
  · exact dReg_le σ hg i
  · exact dReg_le σ (fun d => hv _) i
  · exact dReg_le σ (fun d => hv _) i
  · exact dReg_le σ (fun d => by
      have : 1 ≤ Fintype.card D := Fintype.card_pos_iff.2 ⟨d⟩
      split_ifs <;> omega) i
  · exact dReg_le σ (fun d => le_lenMax ℓ d |>.trans (by omega)) i
  · dsimp only; split_ifs
    · exact hσ _
    · exact Nat.zero_le _
  · exact hσ _
  · dsimp only; split_ifs with h
    · have := outB_add_le M S (Classical.choose h); omega
    · exact Nat.zero_le _
  · dsimp only; split_ifs with h
    · have := outB_add_le M S (Classical.choose h); omega
    · exact Nat.zero_le _
  · exact getD_le_of (fun x hx => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx; exact hσ d) i
  · exact getD_le_of (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hv y) i
  · exact getD_le_of (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hσ _) i
  · exact getD_le_of (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hf y) i
  · exact getD_le_of (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact hσ _) i
  · exact getD_le_of (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega) i
  · exact hv _
  · have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨X i⟩
    dsimp only; split_ifs <;> omega

/-- **The linear word bound**: `kB` without the sum of the words, plus the largest length. -/
def kBL (nD n k t L : ℕ) : ℕ :=
  9 * nD + 7 * n + k + 4 + 2 * t + aOUT nD + k * t + n + 2 * nD + L

/-- **The explicit words meet `KVal` with the linear word bound `kBL`** (`kval_kInputT` with
`kBL … (lenMax ℓ)` in place of `kB`). -/
theorem kval_kInputT' (H : Hyp M k g S ℓ) {t : ℕ} {X : ℕ → V}
    (hX : ∀ i < t, ¬ IsRoot M k g (X i)) {n : ℕ} (σ : D ≃ Fin (Fintype.card D))
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    {T : DTree M.dual} {C : DTree M} {vs ts : List V} {fs cs : List F}
    (hOT : Orders T vs ts) (hOC : Orders C fs cs) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k))
      (tpar (pieceGraph M S ℓ) (tripSrc M k g 0))) :
    KVal M k g S ℓ σ n (kBL (Fintype.card D) n k t (lenMax ℓ)) t X
      (kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X) := by
  obtain ⟨ιv', ιg', ιf', ιe', T', C', vs', ts', fs', cs', -, -, -, -, -, hL', hK, hG, hO, hXT, hI,
    hoff', hCr', hT'⟩ := kval_kInputT H hX σ hL hOT hOC hoff hCr hT
  refine ⟨ιv', ιg', ιf', ιe', T', C', vs', ts', fs', cs', ?_, ?_, ?_, ?_, fun i => ?_, hL', hK, hG,
    hO, hXT, hI, hoff', hCr', hT'⟩
  · unfold kBL; omega
  · unfold kBL; omega
  · unfold kBL; omega
  · unfold kBL aRB; omega
  · have := kInputT_le (S := S) (ℓ := ℓ) (k := k) (g := g) σ hL hOT hOC t X i
    unfold kBL; omega

/-- **The lengths of the piece are input words**: under `KVal` with the word bound `B`, every
length `(ℓ d).toNat`, `d ∈ S`, is at most `B + 16 (n + 1)`. -/
theorem kval_len_le {σ : D ≃ Fin (Fintype.card D)} {n B t : ℕ} {X : ℕ → V} {P : Input}
    (hv : KVal M k g S ℓ σ n B t X P) {d : D} (hd : d ∈ S) : (ℓ d).toNat ≤ B + 16 * (n + 1) := by
  obtain ⟨ιv, ιg, ιf, ιe, T, C, vs, ts, fs, cs, -, -, -, -, hP, hL, hK, hrest⟩ := hv
  rw [← hK.ln d hd]
  exact hP _

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **`FEncNat` met by the explicit words with the linear word bound**: `fencNat_exists` with
`Bw = kBL #D' n k k (lenMax (srcIso …))`, `n = 2 (#V' + #F' + #D')` (the map with the sources
copied). -/
theorem fencNat_exists' {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) :
    ∃ (w : Klein.SrcD fd.DQ fd.k → ℤ) (Pk : Input),
      FEncNat fd ℓ (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) +
          Fintype.card (Klein.SrcF fd.FQ fd.k) + Fintype.card (Klein.SrcD fd.DQ fd.k)))
        (Klein.kBL (Fintype.card (Klein.SrcD fd.DQ fd.k))
          (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
            Fintype.card (Klein.SrcD fd.DQ fd.k))) fd.k fd.k
          (Klein.lenMax (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
            (faceLen fd.P' fd.e ℓ) w σ))) σ w Pk := by
  classical
  have hnnQ : ∀ y ∈ fd.P'.image fd.e, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y _ =>
    faceLen_nonneg _ _ _ y
  obtain ⟨w, hw, hwB⟩ := MSSP.exists_isoW (Klein.srcMap_isPlane fd.inst.cycle fd.inst.plane)
    ((Klein.srcMap fd.inst.cycle).face (Klein.srcG fd.inst.cycle 0))
  obtain ⟨H, -⟩ := Klein.srcIso_hyp fd.inst.cycle fd.inst.plane fd.inst.rot hnnQ hw hwB σ
  have hR := Klein.srcMap_sameReach fd.inst.cycle (S := fd.P'.image fd.e)
    (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
  have hX : ∀ i < fd.k, ¬ MSSP.IsRoot (Klein.srcMap fd.inst.cycle) fd.k
      (Klein.srcG fd.inst.cycle) (.inl (fd.Q.tail (fd.g i))) := by
    rintro i - ⟨j, hj, hji⟩
    rw [Klein.srcTail_srcG fd.inst.cycle hj] at hji
    cases hji
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := Klein.exists_layout (Klein.srcMap fd.inst.cycle)
  obtain ⟨T, C, vs, ts, fs, cs, hOT, hOC, hoff, hCr, hT⟩ := Klein.klein_init_exists H hR
  exact ⟨w, _, rfl, hw, hwB, Klein.kval_kInputT' H hX σ hL hOT hOC hoff hCr hT⟩

/-- **The work space of an encoding meeting `FEncNat` is at least cubic in the size**: the
isolating length of the dart `down` of the first root is at least
`isoN2 #V' #D' #F' = (#V' #D' + 1) (2 #F' #V' + 1)`, and it is an input word. -/
theorem fencNat_isoN2_le {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    {n Bw : ℕ} {σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))}
    {w : Klein.SrcD fd.DQ fd.k → ℤ} {Pk : Input} (hv : FEncNat fd ℓ n Bw σ w Pk) :
    MSSP.isoN2 (Fintype.card (Klein.SrcV fd.VQ fd.k)) (Fintype.card (Klein.SrcD fd.DQ fd.k))
      (Fintype.card (Klein.SrcF fd.FQ fd.k)) ≤ Bw + 16 * (n + 1) := by
  obtain ⟨-, -, hwB, hv'⟩ := hv
  have hk := fd.inst.cycle.two_le
  set d₀ : Klein.SrcD fd.DQ fd.k := .inr (⟨0, by omega⟩, .down) with hd₀
  have hmem : d₀ ∈ Klein.srcPiece fd.k (fd.P'.image fd.e) := by
    rw [Klein.mem_srcPiece]; rfl
  have h := Klein.kval_len_le hv' hmem
  have hw := hwB d₀
  rw [abs_le] at hw
  have e : Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)
      w σ d₀ = (MSSP.isoN2 (Fintype.card (Klein.SrcV fd.VQ fd.k))
        (Fintype.card (Klein.SrcD fd.DQ fd.k)) (Fintype.card (Klein.SrcF fd.FQ fd.k)) : ℤ) +
      MSSP.isoN3 (Fintype.card (Klein.SrcV fd.VQ fd.k)) (Fintype.card (Klein.SrcD fd.DQ fd.k)) *
        (w d₀ + Fintype.card (Klein.SrcF fd.FQ fd.k)) + (σ d₀ : ℕ) := by
    simp only [Klein.srcIso, MSSP.isoLen, hd₀, Klein.srcLen, mul_zero, zero_add]
  rw [e] at h
  have h3 : (0 : ℤ) ≤ MSSP.isoN3 (Fintype.card (Klein.SrcV fd.VQ fd.k))
      (Fintype.card (Klein.SrcD fd.DQ fd.k)) * (w d₀ + Fintype.card (Klein.SrcF fd.FQ fd.k)) :=
    mul_nonneg (by positivity) (by omega)
  omega

end NegSSSP

end PlanarFlow
