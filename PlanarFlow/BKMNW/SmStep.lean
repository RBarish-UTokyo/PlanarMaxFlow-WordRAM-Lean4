module

public import PlanarFlow.BKMNW.SmFin
public import PlanarFlow.BKMNW.MfFrameSem

/-!
# One step of `smD` on the machine: the meaning

From the per-dart arrays of a piece `P` (an enumeration `f` of `[0, n)` onto a superset of `P`:
`PF[i] ≠ 0 ↔ f i ∈ P`, `RV`, `TH = hlab Hs ∘ tail`, `KR = lrk S T (hunion Hs) ∘ tail`,
`VT = ν ∘ tail` with `ν` injective; the choices `pk X` = the dart of `X` of least index), the
program `smStep` (`SmFin.lean`) computes one step of `smD`:

* the arithmetic in bits: `smEq_bf`, `smSg_bf`, `smAnd_bf`, `sub_bf`, `one_sub_bf`, …;
* `SmArr` (the arrays), the bits of the scan (`smPv_eq` … `smBv_eq`), the counts, the first
  indices (`fstT_pk`);
* the bits of the output scan for a split `s` (`SmSplit`): `smLPw_eq`, `smPDw_eq`, `smCVw_eq`,
  `smB2w_eq`, `smX2w_eq`, `smY2w_eq`, `smJ2w_eq`, the hole flags `smHM_eq`;
* **`smStep_smD`**: the node bit is `ntag (smD M pk S T P Hs)`, and at a node `.node l r π` the
  memory holds `bf (f i ∈ l.piece)`, `bf (f i ∈ π.path.darts)`, `bf (tail (f i) ∈ π.path.mverts)`,
  `bf (¬ Disjoint Hs[j] π.path.mverts)`, `ntag l`, `ntag r` — the outputs `SepPSpec` asks at a
  call of the small decomposition — within `252 n + 19 #Hs + 78` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset Function WordRAM WordRAM.Machine MfDrv

/-! ### The arithmetic in bits -/

lemma smEq_bf (x y : ℕ) : smEq x y = bf (x = y) := by
  unfold smEq bf; split_ifs <;> omega

lemma smSg_bf (x : ℕ) : smSg x = bf (x ≠ 0) := by
  unfold smSg bf; split_ifs <;> omega

lemma smAnd_bf (p q : Prop) [Decidable p] [Decidable q] :
    smAnd (bf p) (bf q) = bf (p ∧ q) := by
  unfold smAnd bf; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma sub_bf (p q : Prop) [Decidable p] [Decidable q] : bf p - bf q = bf (p ∧ ¬ q) := by
  unfold bf; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma one_sub_bf (p : Prop) [Decidable p] : 1 - bf p = bf (¬ p) := by
  unfold bf; by_cases hp : p <;> simp [hp]

lemma bf_add_ne_zero (p q : Prop) [Decidable p] [Decidable q] :
    (bf p + bf q ≠ 0) ↔ (p ∨ q) := by
  unfold bf; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma bf_ne_zero (p : Prop) [Decidable p] : (bf p ≠ 0) ↔ p := by
  unfold bf; by_cases hp : p <;> simp [hp]

lemma bf_eq_one (p : Prop) [Decidable p] : bf p = 1 ↔ p := by
  unfold bf; by_cases hp : p <;> simp [hp]

lemma bf_le_one (p : Prop) [Decidable p] : bf p ≤ 1 := by
  unfold bf; split_ifs <;> omega

lemma smHst_bf (k : ℕ) : smHst k = bf (k = 0 ∨ k = 2) := by
  unfold smHst smEq bf; split_ifs with h <;> omega

lemma lrk_sub_two {V : Type*} [DecidableEq V] [Fintype V] (S T A : Finset V) (v : V) :
    lrk S T A v - 2 = bf (lrk S T A v = 3) := by
  have := lrk_le S T A v
  unfold bf; split_ifs <;> omega

lemma smBf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : bf p = bf q := by
  unfold bf; by_cases hp : p
  · rw [iteT hp, iteT (h.1 hp)]
  · rw [iteF hp, iteF (fun hq => hp (h.2 hq))]

lemma sum_bf_ne_zero (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ j ∈ range n, bf (Q j) ≠ 0) ↔ ∃ j < n, Q j := by
  rw [Ne, sum_eq_zero_iff]
  push Not
  simp only [mem_range, bf_ne_zero]

lemma smNode_bf (cP cI : ℕ) (x y b : Prop) [Decidable x] [Decidable y] [Decidable b] :
    smNode cP cI (bf x) (bf y) (bf b) = bf ((2 < cP ∧ b) ∧ (x ∨ ¬ y ∨ cI ≠ 0)) := by
  unfold smNode smAnd smSg bf
  by_cases hx : x <;> by_cases hy : y <;> by_cases hb : b <;> simp only [hx, hy, hb] <;>
    split_ifs <;> simp_all <;> omega

lemma bf_of_le_one {g : ℕ} (hg : g ≤ 1) : g = bf (g = 1) := by
  unfold bf; split_ifs <;> omega

lemma ntag_eq_bf {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (τ : ADec M) : ntag τ = bf (ntag τ = 1) := by
  cases τ <;> simp [ntag, bf]

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The arrays of a piece -/

variable (M) in
/-- **The per-dart arrays of a piece** `P` with the holes `Hs`, by an enumeration `f` of `[0, n)`
onto a superset of `P`. -/
structure SmArr (m : ℕ → ℕ) (n PFb RVb THb KRb VTb : ℕ) (f : ℕ → D) (P : Finset D)
    (Hs : List (Finset V)) (S T : Finset V) (ν : V → ℕ) : Prop where
  inj : ∀ i < n, ∀ j < n, f i = f j → i = j
  surj : ∀ d ∈ P, ∃ i < n, f i = d
  pf : ∀ i < n, (m (PFb + i) ≠ 0 ↔ f i ∈ P)
  rv : ∀ i < n, m (RVb + i) < n ∧ f (m (RVb + i)) = M.rev (f i)
  th : ∀ i < n, m (THb + i) = hlab Hs (M.tail (f i))
  kr : ∀ i < n, m (KRb + i) = lrk S T (hunion Hs) (M.tail (f i))
  vt : ∀ i < n, m (VTb + i) = ν (M.tail (f i))
  νinj : Injective ν
  pw : Hs.Pairwise Disjoint

section Arr

variable {m : ℕ → ℕ} {n PFb RVb THb KRb VTb : ℕ} {f : ℕ → D} {P : Finset D}
  {Hs : List (Finset V)} {S T : Finset V} {ν : V → ℕ}

lemma SmArr.thr (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    m (THb + m (RVb + i)) = hlab Hs (M.head (f i)) := by
  rw [h.th _ (h.rv i hi).1, (h.rv i hi).2, CombMap.tail_rev]

lemma SmArr.krr (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    m (KRb + m (RVb + i)) = lrk S T (hunion Hs) (M.head (f i)) := by
  rw [h.kr _ (h.rv i hi).1, (h.rv i hi).2, CombMap.tail_rev]

lemma SmArr.vtr (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    m (VTb + m (RVb + i)) = ν (M.head (f i)) := by
  rw [h.vt _ (h.rv i hi).1, (h.rv i hi).2, CombMap.tail_rev]

lemma hlab_ne_zero_iff {v : V} : hlab Hs v ≠ 0 ↔ v ∈ hunion Hs := by
  rw [← hlab_pos_iff]; omega

lemma SmArr.inner_iff (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) (d : D) :
    Inner M Hs d ↔ hlab Hs (M.tail d) ≠ 0 ∧ hlab Hs (M.tail d) = hlab Hs (M.head d) := by
  rw [inner_iff_hlab h.pw]; omega

/-- **The bits of the scan.** -/
lemma SmArr.pv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smPv m PFb i = bf (f i ∈ P) := by
  simp only [smPv, smSg_bf]; exact smBf_congr (h.pf i hi)

lemma SmArr.iv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smIv m PFb RVb THb i = bf (f i ∈ P ∧ hlab Hs (M.tail (f i)) ≠ 0 ∧
      hlab Hs (M.tail (f i)) = hlab Hs (M.head (f i))) := by
  simp only [smIv, smInn, smSg_bf, smEq_bf, smAnd_bf, bf_ne_zero, h.pf i hi, h.th i hi,
    h.thr hi]

lemma SmArr.xv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smXv m PFb RVb THb KRb i = bf (f i ∈ smX M S T P Hs) := by
  simp only [smXv, smSg_bf, smAnd_bf, bf_ne_zero, h.pf i hi, h.kr i hi, h.thr hi, lrk_sub_two,
    lrk_eq_three_iff, hlab_ne_zero_iff]
  refine smBf_congr ⟨fun ⟨⟨hp, hv⟩, ha⟩ => mem_filter.2 ⟨mem_pdarts.2 ⟨hp, fun hI => ?_⟩, hv, ha⟩,
    fun hx => ?_⟩
  · obtain ⟨H, hH, ht, -⟩ := hI
    exact hv (mem_union_right _ (mem_hunion.2 ⟨H, hH, ht⟩))
  · obtain ⟨h1, hv, ha⟩ := mem_filter.1 hx
    exact ⟨⟨(mem_pdarts.1 h1).1, hv⟩, ha⟩

lemma SmArr.yv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smYv m PFb THb i = bf (f i ∈ smY M P Hs) := by
  simp only [smYv, smSg_bf, smAnd_bf, bf_ne_zero, h.pf i hi, h.th i hi, hlab_ne_zero_iff]
  exact smBf_congr (by simp [smY])

lemma SmArr.bv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smBv m PFb KRb i = bf (f i ∈ smB M S T P Hs) := by
  simp only [smBv, smSg_bf, smAnd_bf, bf_ne_zero, h.pf i hi, h.kr i hi, lrk_sub_two,
    lrk_eq_three_iff]
  refine smBf_congr ⟨fun ⟨hp, hv⟩ => mem_filter.2 ⟨mem_pdarts.2 ⟨hp, fun hI => ?_⟩, hv⟩,
    fun hx => ?_⟩
  · obtain ⟨H, hH, ht, -⟩ := hI
    exact hv (mem_union_right _ (mem_hunion.2 ⟨H, hH, ht⟩))
  · obtain ⟨h1, hv⟩ := mem_filter.1 hx
    exact ⟨(mem_pdarts.1 h1).1, hv⟩

/-- **Counting by the enumeration.** -/
lemma SmArr.sum_card (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {X : Finset D}
    (hX : X ⊆ P) : ∑ j ∈ range n, bf (f j ∈ X) = X.card := by
  rw [← card_filter_e (e := f) (n := n) (N := X) h.inj fun d hd => by
    obtain ⟨i, hi, e⟩ := h.surj d (hX hd); exact ⟨i, hi, e⟩, card_filter]
  rfl

lemma SmArr.exists_iff (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {X : Finset D}
    (hX : X ⊆ P) : (∃ j < n, f j ∈ X) ↔ X.Nonempty :=
  ⟨fun ⟨j, _, hj⟩ => ⟨_, hj⟩, fun ⟨d, hd⟩ => by
    obtain ⟨i, hi, rfl⟩ := h.surj d (hX hd); exact ⟨i, hi, hd⟩⟩

/-- **The first index with a bit set is the choice `pk`.** -/
lemma SmArr.fst (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {pk : Finset D → D}
    (hpk : ∀ X ⊆ P, ∀ i < n, f i ∈ X → (∀ j < i, f j ∉ X) → pk X = f i) {X : Finset D}
    (hX : X ⊆ P) {Q : ℕ → ℕ} (hQ : ∀ j < n, Q j = bf (f j ∈ X)) {g a : ℕ} (hF : FstT Q n g a) :
    g = bf X.Nonempty ∧ (g = 1 → a < n ∧ pk X = f a) := by
  obtain ⟨h1, h2, h3⟩ := hF
  have e : g = 1 ↔ X.Nonempty := by
    rw [h2, ← h.exists_iff hX]
    exact ⟨fun ⟨j, hj, e⟩ => ⟨j, hj, by rw [hQ j hj, bf_eq_one] at e; exact e⟩,
      fun ⟨j, hj, e⟩ => ⟨j, hj, by rw [hQ j hj, bf_eq_one]; exact e⟩⟩
  refine ⟨by rw [bf_of_le_one h1]; exact smBf_congr e, fun hg => ?_⟩
  obtain ⟨ha, hqa, hmin⟩ := h3 hg
  refine ⟨ha, hpk X hX a ha (by rw [hQ a ha, bf_eq_one] at hqa; exact hqa) fun j hj hjX => ?_⟩
  exact hmin j hj (by rw [hQ j (by omega), bf_eq_one]; exact hjX)

lemma pdarts_card_lt_iff {P : Finset D} {Hs : List (Finset V)} :
    (pdarts M P Hs).card < P.card ↔ ∃ d ∈ P, Inner M Hs d := by
  constructor
  · intro hlt
    by_contra hno
    push Not at hno
    have : pdarts M P Hs = P :=
      Finset.Subset.antisymm (pdarts_subset _ _) fun d hd => mem_pdarts.2 ⟨hd, hno d hd⟩
    rw [this] at hlt; omega
  · rintro ⟨d, hd, hI⟩
    exact card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨pdarts_subset _ _, fun e => by
      have := e ▸ hd; exact (mem_pdarts.1 this).2 hI⟩)

/-- **The node bit of the scan is the tag of `smD`.** -/
theorem SmArr.node (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {pk : Finset D → D}
    (hpk : ∀ X ⊆ P, ∀ i < n, f i ∈ X → (∀ j < i, f j ∉ X) → pk X = f i)
    (hpk0 : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d)
    {cA : Config} (hA : SmAOut m PFb RVb THb KRb VTb n cA) :
    smNode (cA.nreg 5315) (cA.nreg 5316) (cA.nreg 5317) (cA.nreg 5323) (cA.nreg 5327) =
      ntag (smD M pk S T P Hs) := by
  have hP : cA.nreg 5315 = P.card := by
    rw [hA.cp, ← h.sum_card subset_rfl]
    exact sum_congr rfl fun j hj => h.pv (mem_range.1 hj)
  have hI : cA.nreg 5316 ≠ 0 ↔ (pdarts M P Hs).card < P.card := by
    rw [hA.ci, sum_congr rfl fun j hj => h.iv (mem_range.1 hj), sum_bf_ne_zero,
      pdarts_card_lt_iff]
    constructor
    · rintro ⟨j, hj, hjP, hI⟩; exact ⟨_, hjP, (h.inner_iff _).2 hI⟩
    · rintro ⟨d, hd, hI⟩
      obtain ⟨j, hj, rfl⟩ := h.surj d hd
      exact ⟨j, hj, hd, (h.inner_iff _).1 hI⟩
  have gX := (h.fst hpk smX_sub (fun j hj => h.xv hj) hA.fx).1
  have gY := (h.fst hpk smY_sub (fun j hj => h.yv hj) hA.fy).1
  have gB := (h.fst hpk smB_sub (fun j hj => h.bv hj) hA.fb).1
  rw [gX, gY, gB, smNode_bf, ntag_eq_bf, hP]
  refine smBf_congr ?_
  rw [smD_ntag hpk0 hloop, ← hI]

end Arr

/-! ### The bits of the output scan -/

/-- The vertices of the path: `{tail x, head x}` if `U`, else `{tail x}`. -/
def smPC (M : CombMap D V F) (x : D) (U : Bool) : Finset V :=
  if U = true then {M.tail x, M.head x} else {M.tail x}

/-- The left piece: the piece map if `Lm`, else the piece without `x`, `rev x`. -/
noncomputable def smPL (M : CombMap D V F) (P : Finset D) (Hs : List (Finset V)) (x : D) (Lm : Bool) :
    Finset D :=
  if Lm = true then pdarts M P Hs else P \ {x, M.rev x}

variable (M) in
/-- **The words of a split** `s`: the dart `x` (index `a`), its reverse (index `a'`, needed when
`U` or not `Lm`), the bits `U`, `Lm`, the vertex numbers and the hole labels of its ends. -/
structure SmSplit (n : ℕ) (f : ℕ → D) (Hs : List (Finset V)) (ν : V → ℕ) (s : SmSV) (x : D)
    (U Lm : Bool) : Prop where
  a : s.a < n ∧ f s.a = x
  a' : (U = true ∨ Lm = false) → s.a' < n ∧ f s.a' = M.rev x
  up : s.up = bf (U = true)
  lpm : s.lpm = bf (Lm = true)
  v1 : s.v1 = ν (M.tail x)
  v2 : U = true → s.v2 = ν (M.head x)
  t1 : s.t1 = hlab Hs (M.tail x)
  t2 : U = true → s.t2 = hlab Hs (M.head x)

section Split

variable {m : ℕ → ℕ} {n PFb RVb THb KRb VTb : ℕ} {f : ℕ → D} {P : Finset D}
  {Hs : List (Finset V)} {S T : Finset V} {ν : V → ℕ} {s : SmSV} {x : D} {U Lm : Bool}

/-- A vertex in a hole met by the path. -/
def SmHM (Hs : List (Finset V)) (C : Finset V) (v : V) : Prop := ∃ H ∈ Hs, v ∈ H ∧ ¬ Disjoint H C

lemma SmSplit.hm_iff (hs : SmSplit M n f Hs ν s x U Lm) (hd : Hs.Pairwise Disjoint) (v : V) :
    (v ∈ hunion Hs ∧ (hlab Hs v = hlab Hs (M.tail x) ∨ (U = true ∧ hlab Hs v = hlab Hs (M.head x))))
      ↔ SmHM Hs (smPC M x U) v := by
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨hlt, hm⟩ := hlab_mem (hlab_pos_iff.2 hv)
    refine ⟨_, sm_getD_mem hlt, hm, fun hdis => ?_⟩
    rcases he with he | ⟨hU, he⟩
    · have hx : M.tail x ∈ Hs.getD (hlab Hs v - 1) ∅ :=
        (hlab_eq_succ_iff hd hlt).1 (by have := hlab_pos_iff.2 hv; omega)
      exact disjoint_left.1 hdis hx (by unfold smPC; split_ifs <;> simp)
    · have hx : M.head x ∈ Hs.getD (hlab Hs v - 1) ∅ :=
        (hlab_eq_succ_iff hd hlt).1 (by have := hlab_pos_iff.2 hv; omega)
      exact disjoint_left.1 hdis hx (by unfold smPC; simp [hU])
  · rintro ⟨H, hH, hv, hHC⟩
    obtain ⟨w, hwH, hwC⟩ := not_disjoint_iff.1 hHC
    refine ⟨mem_hunion.2 ⟨H, hH, hv⟩, ?_⟩
    have e := hlab_congr (sm_mem_iff_of_pw hd hH hv hwH)
    unfold smPC at hwC
    split_ifs at hwC with hU
    · rcases mem_insert.1 hwC with rfl | hw
      · exact Or.inl e
      · rw [mem_singleton] at hw; subst hw; exact Or.inr ⟨hU, e⟩
    · rw [mem_singleton] at hwC; subst hwC; exact Or.inl e

lemma SmSplit.mem_C (hs : SmSplit M n f Hs ν s x U Lm) (v : V) :
    (v = M.tail x ∨ (U = true ∧ v = M.head x)) ↔ v ∈ smPC M x U := by
  unfold smPC; cases U <;> simp

lemma SmArr.inner_iff' (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) (d : D) :
    (M.tail d ∈ hunion Hs ∧ hlab Hs (M.tail d) = hlab Hs (M.head d)) ↔ Inner M Hs d := by
  rw [h.inner_iff, hlab_ne_zero_iff]

/-- **The bit `LP`**: a dart of the left piece. -/
lemma SmArr.lp (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smLPw (smW m PFb RVb THb KRb VTb i) s i = bf (f i ∈ smPL M P Hs x Lm) := by
  simp only [smLPw, smW, smEaa, smInn, smSg_bf, smEq_bf, smAnd_bf, sub_bf, one_sub_bf,
    bf_add_ne_zero, bf_ne_zero, h.pf i hi, h.th i hi, h.thr hi, hs.lpm, hlab_ne_zero_iff,
    h.inner_iff']
  refine smBf_congr ?_
  unfold smPL
  cases Lm
  · obtain ⟨ha, hfa⟩ := hs.a
    obtain ⟨ha', hfa'⟩ := hs.a' (Or.inr rfl)
    have e1 : i = s.a ↔ f i = x := ⟨fun e => e ▸ hfa, fun e => h.inj _ hi _ ha (e.trans hfa.symm)⟩
    have e2 : i = s.a' ↔ f i = M.rev x :=
      ⟨fun e => e ▸ hfa', fun e => h.inj _ hi _ ha' (e.trans hfa'.symm)⟩
    simp only [e1, e2, Bool.false_eq_true, false_and, not_false_eq_true, and_true, true_and,
      ↓reduceIte, mem_sdiff, mem_insert, mem_singleton]
  · simp only [↓reduceIte, mem_pdarts, ← h.inner_iff', not_true_eq_false, false_and,
      not_false_eq_true, and_true, true_and]

/-- **The bit `PD`**: a dart of the path. -/
lemma SmArr.pd (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smPDw s i = bf (f i ∈ (if U = true then ({x, M.rev x} : Finset D) else ∅)) := by
  simp only [smPDw, smEaa, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero]
  refine smBf_congr ?_
  cases U
  · simp
  · obtain ⟨ha, hfa⟩ := hs.a
    obtain ⟨ha', hfa'⟩ := hs.a' (Or.inl rfl)
    have e1 : i = s.a ↔ f i = x := ⟨fun e => e ▸ hfa, fun e => h.inj _ hi _ ha (e.trans hfa.symm)⟩
    have e2 : i = s.a' ↔ f i = M.rev x :=
      ⟨fun e => e ▸ hfa', fun e => h.inj _ hi _ ha' (e.trans hfa'.symm)⟩
    simp [e1, e2]

/-- **The bit `CV`**: the tail on the path (and the head, `smCHw`). -/
lemma SmArr.cv (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smCVw (smW m PFb RVb THb KRb VTb i) s = bf (M.tail (f i) ∈ smPC M x U) := by
  simp only [smCVw, smCVf, smW, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero,
    h.vt i hi, hs.v1]
  refine smBf_congr ?_
  rw [← hs.mem_C]
  cases U
  · simp [h.νinj.eq_iff]
  · simp [h.νinj.eq_iff, hs.v2 rfl]

lemma SmArr.ch (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smCHw (smW m PFb RVb THb KRb VTb i) s = bf (M.head (f i) ∈ smPC M x U) := by
  simp only [smCHw, smCVf, smW, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero,
    h.vtr hi, hs.v1]
  refine smBf_congr ?_
  rw [← hs.mem_C]
  cases U
  · simp [h.νinj.eq_iff]
  · simp [h.νinj.eq_iff, hs.v2 rfl]

/-- **The hole flags**: the hole `j` meets the path. -/
lemma SmSplit.hmf (hs : SmSplit M n f Hs ν s x U Lm) (hd : Hs.Pairwise Disjoint) {j : ℕ}
    (hj : j < Hs.length) :
    smCVf (j + 1) s.t1 s.t2 s.up = bf (¬ Disjoint (Hs.getD j ∅) (smPC M x U)) := by
  simp only [smCVf, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero, hs.t1]
  refine smBf_congr ?_
  rw [not_disjoint_iff]
  constructor
  · rintro (e | ⟨hU, e⟩)
    · exact ⟨_, (hlab_eq_succ_iff hd hj).1 e.symm, by unfold smPC; split_ifs <;> simp⟩
    · rw [hs.t2 hU] at e
      exact ⟨_, (hlab_eq_succ_iff hd hj).1 e.symm, by unfold smPC; simp [hU]⟩
  · rintro ⟨v, hv, hvC⟩
    have e := (hlab_eq_succ_iff hd hj).2 hv
    unfold smPC at hvC
    split_ifs at hvC with hU
    · rcases mem_insert.1 hvC with rfl | hw
      · exact Or.inl e.symm
      · rw [mem_singleton] at hw; subst hw; exact Or.inr ⟨hU, by rw [hs.t2 hU]; exact e.symm⟩
    · rw [mem_singleton] at hvC; subst hvC; exact Or.inl e.symm

instance smInnerDec (Hs : List (Finset V)) : DecidablePred (Inner M Hs) := fun d => by
  unfold Inner; infer_instance

instance smHMDec (Hs : List (Finset V)) (C : Finset V) : DecidablePred (SmHM Hs C) := fun v => by
  unfold SmHM; infer_instance

/-- **Inside a hole of the children**, from the holes met by the path. -/
lemma inner_childHoles_iff {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V}
    (d : D) : Inner M (childHoles Hs C) d ↔
      ((M.tail d ∈ C ∨ SmHM Hs C (M.tail d)) ∧ (M.head d ∈ C ∨ SmHM Hs C (M.head d))) ∨
        (Inner M Hs d ∧ ¬ SmHM Hs C (M.tail d)) := by
  have hN : ∀ v, v ∈ newHole Hs C ↔ v ∈ C ∨ SmHM Hs C v := fun v => by
    rw [mem_newHole]; unfold SmHM
    exact or_congr_right ⟨fun ⟨H, hH, h1, h2⟩ => ⟨H, hH, h2, h1⟩,
      fun ⟨H, hH, h1, h2⟩ => ⟨H, hH, h2, h1⟩⟩
  constructor
  · rintro ⟨H, hH, ht, hh⟩
    simp only [childHoles, List.mem_append, List.mem_filter, decide_eq_true_eq,
      List.mem_singleton] at hH
    rcases hH with ⟨hH, hHC⟩ | rfl
    · refine Or.inr ⟨⟨H, hH, ht, hh⟩, fun ⟨H', hH', ht', hH'C⟩ => hH'C ?_⟩
      by_cases e : H' = H
      · rw [e]; exact hHC
      · exact absurd ht (disjoint_left.1 (disjoint_of_pairwise hd hH' hH e) ht')
    · exact Or.inl ⟨(hN _).1 ht, (hN _).1 hh⟩
  · rintro (⟨ht, hh⟩ | ⟨⟨H, hH, ht, hh⟩, hno⟩)
    · exact ⟨newHole Hs C, by simp [childHoles], (hN _).2 ht, (hN _).2 hh⟩
    · refine ⟨H, ?_, ht, hh⟩
      simp only [childHoles, List.mem_append, List.mem_filter, decide_eq_true_eq]
      exact Or.inl ⟨hH, by_contra fun hHC => hno ⟨H, hH, ht, hHC⟩⟩

lemma SmArr.inn (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smInn (smW m PFb RVb THb KRb VTb i).t (smW m PFb RVb THb KRb VTb i).h =
      bf (Inner M Hs (f i)) := by
  simp only [smW, smInn, smSg_bf, smEq_bf, smAnd_bf, h.th i hi, h.thr hi, hlab_ne_zero_iff,
    h.inner_iff']

lemma SmArr.tz (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smSg (smW m PFb RVb THb KRb VTb i).t = bf (M.tail (f i) ∈ hunion Hs) := by
  simp only [smW, smSg_bf, h.th i hi, hlab_ne_zero_iff]

lemma SmArr.hz (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    smSg (smW m PFb RVb THb KRb VTb i).h = bf (M.head (f i) ∈ hunion Hs) := by
  simp only [smW, smSg_bf, h.thr hi, hlab_ne_zero_iff]

lemma SmArr.bad (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν) {i : ℕ} (hi : i < n) :
    (smW m PFb RVb THb KRb VTb i).kr - 2 = bf (M.tail (f i) ∉ S ∪ T ∪ hunion Hs) := by
  simp only [smW, h.kr i hi, lrk_sub_two]
  exact smBf_congr lrk_eq_three_iff

lemma SmArr.ht (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smHTw (smW m PFb RVb THb KRb VTb i) s = bf (SmHM Hs (smPC M x U) (M.tail (f i))) := by
  simp only [smHTw, smHMf, smW, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero,
    h.th i hi, hs.t1, hlab_ne_zero_iff]
  refine smBf_congr ?_
  rw [← hs.hm_iff h.pw]
  cases U
  · simp
  · simp [hs.t2 rfl]

lemma SmArr.hh (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smHHw (smW m PFb RVb THb KRb VTb i) s = bf (SmHM Hs (smPC M x U) (M.head (f i))) := by
  simp only [smHHw, smHMf, smW, smSg_bf, smEq_bf, smAnd_bf, bf_add_ne_zero, hs.up, bf_ne_zero,
    h.thr hi, hs.t1, hlab_ne_zero_iff]
  refine smBf_congr ?_
  rw [← hs.hm_iff h.pw]
  cases U
  · simp
  · simp [hs.t2 rfl]

/-- **Inside a hole of the children.** -/
lemma SmArr.i2 (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smI2w (smW m PFb RVb THb KRb VTb i) s =
      bf (Inner M (childHoles Hs (smPC M x U)) (f i)) := by
  simp only [smI2w, h.cv hs hi, h.ch hs hi, h.ht hs hi, h.hh hs hi, h.inn hi, smSg_bf, smAnd_bf,
    bf_add_ne_zero, one_sub_bf, bf_ne_zero]
  exact smBf_congr (inner_childHoles_iff h.pw _).symm

variable (M) in
/-- The holes of the children of the split. -/
abbrev smHs (Hs : List (Finset V)) (x : D) (U : Bool) : List (Finset V) :=
  childHoles Hs (smPC M x U)

lemma SmArr.b2 (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smB2w (smW m PFb RVb THb KRb VTb i) s i =
      bf (f i ∈ smB M S T (smPL M P Hs x Lm) (smHs M Hs x U)) := by
  simp only [smB2w, h.lp hs hi, h.i2 hs hi, h.cv hs hi, h.bad hi, smAnd_bf, one_sub_bf]
  refine smBf_congr ?_
  simp only [smB, smHs, mem_filter, mem_pdarts, hunion_childHoles, mem_union]
  tauto

lemma SmArr.x2 (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smX2w (smW m PFb RVb THb KRb VTb i) s i =
      bf (f i ∈ smX M S T (smPL M P Hs x Lm) (smHs M Hs x U)) := by
  simp only [smX2w, smB2w, h.lp hs hi, h.i2 hs hi, h.cv hs hi, h.ch hs hi, h.bad hi, h.hz hi,
    smAnd_bf, one_sub_bf, smSg_bf, bf_add_ne_zero]
  refine smBf_congr ?_
  simp only [smX, smHs, mem_filter, mem_pdarts, hunion_childHoles, mem_union]
  tauto

lemma SmArr.y2 (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smY2w (smW m PFb RVb THb KRb VTb i) s i = bf (f i ∈ smY M (smPL M P Hs x Lm) (smHs M Hs x U)) := by
  simp only [smY2w, h.lp hs hi, h.cv hs hi, h.tz hi, smAnd_bf, smSg_bf, bf_add_ne_zero]
  refine smBf_congr ?_
  simp only [smY, smHs, mem_filter, hunion_childHoles, mem_union]

lemma SmArr.j2 (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {i : ℕ} (hi : i < n) :
    smJ2w (smW m PFb RVb THb KRb VTb i) s i =
      bf (f i ∈ smPL M P Hs x Lm ∧ Inner M (smHs M Hs x U) (f i)) := by
  simp only [smJ2w, h.lp hs hi, h.i2 hs hi, smAnd_bf]

lemma smPL_sub {P : Finset D} {Hs : List (Finset V)} {x : D} {Lm : Bool} :
    smPL M P Hs x Lm ⊆ P := by
  unfold smPL; split_ifs
  · exact pdarts_subset _ _
  · exact sdiff_subset

lemma smPL_rc {P : Finset D} (hP : RevClosed M P) {Hs : List (Finset V)} {x : D} {Lm : Bool} :
    RevClosed M (smPL M P Hs x Lm) := by
  unfold smPL; split_ifs
  · exact revClosed_pdarts' hP _
  · exact revClosed_sdiff_pair hP _

/-- **The tag of the left child**, from the five sums of the output scan. -/
theorem SmArr.child_tag (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) {pk : Finset D → D}
    (hpk0 : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d) :
    smNode (∑ j ∈ range n, smLPw (smW m PFb RVb THb KRb VTb j) s j)
        (∑ j ∈ range n, smJ2w (smW m PFb RVb THb KRb VTb j) s j)
        (smSg (∑ j ∈ range n, smX2w (smW m PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smY2w (smW m PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smB2w (smW m PFb RVb THb KRb VTb j) s j)) =
      ntag (smD M pk S T (smPL M P Hs x Lm) (smHs M Hs x U)) := by
  set L := smPL M P Hs x Lm with hL
  set Hs' := smHs M Hs x U with hHs'
  have hLP : L ⊆ P := smPL_sub
  have e1 : ∑ j ∈ range n, smLPw (smW m PFb RVb THb KRb VTb j) s j = L.card := by
    rw [← h.sum_card hLP]; exact sum_congr rfl fun j hj => h.lp hs (mem_range.1 hj)
  have sg : ∀ (X : Finset D), X ⊆ P → ∀ (g : ℕ → ℕ), (∀ j < n, g j = bf (f j ∈ X)) →
      smSg (∑ j ∈ range n, g j) = bf X.Nonempty := fun X hX g hg => by
    have e : ∑ j ∈ range n, g j = ∑ j ∈ range n, bf (f j ∈ X) :=
      sum_congr rfl fun j hj => hg j (mem_range.1 hj)
    rw [e, smSg_bf]
    exact smBf_congr ((sum_bf_ne_zero _ _).trans (h.exists_iff hX))
  have eX := sg _ (smX_sub.trans hLP) _ fun j hj => h.x2 hs hj
  have eY := sg _ (smY_sub.trans hLP) _ fun j hj => h.y2 hs hj
  have eB := sg _ (smB_sub.trans hLP) _ fun j hj => h.b2 hs hj
  have eJ : (∑ j ∈ range n, smJ2w (smW m PFb RVb THb KRb VTb j) s j ≠ 0) ↔
      (pdarts M L Hs').card < L.card := by
    rw [sum_congr rfl fun j hj => h.j2 hs (mem_range.1 hj), sum_bf_ne_zero, pdarts_card_lt_iff]
    constructor
    · rintro ⟨j, hj, hjL, hI⟩; exact ⟨_, hjL, hI⟩
    · rintro ⟨d, hd, hI⟩
      obtain ⟨j, hj, rfl⟩ := h.surj d (hLP hd)
      exact ⟨j, hj, hd, hI⟩
  rw [e1, eX, eY, eB, smNode_bf, ntag_eq_bf]
  refine smBf_congr ?_
  rw [smD_ntag hpk0 hloop, ← eJ]

/-- **The outputs at a node** of the shape `SmForm`, from the memory facts of `smStep_exec`. -/
theorem SmArr.out (h : SmArr M m n PFb RVb THb KRb VTb f P Hs S T ν)
    (hs : SmSplit M n f Hs ν s x U Lm) (hP : RevClosed M P) {pk : Finset D → D}
    (hpk0 : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d)
    (hF : SmForm M pk S T P Hs x U Lm) {mem : ℕ → ℕ} {Ob : ℕ}
    (hLP : ∀ j < n, mem (Ob + j) = smLPw (smW m PFb RVb THb KRb VTb j) s j)
    (hPD : ∀ j < n, mem (Ob + n + j) = smPDw s j)
    (hCV : ∀ j < n, mem (Ob + 2 * n + j) = smCVw (smW m PFb RVb THb KRb VTb j) s)
    (hHM : ∀ j < Hs.length, mem (Ob + 3 * n + j) = smCVf (j + 1) s.t1 s.t2 s.up)
    (hT : mem (Ob + 3 * n + Hs.length) = smNode
        (∑ j ∈ range n, smLPw (smW m PFb RVb THb KRb VTb j) s j)
        (∑ j ∈ range n, smJ2w (smW m PFb RVb THb KRb VTb j) s j)
        (smSg (∑ j ∈ range n, smX2w (smW m PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smY2w (smW m PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smB2w (smW m PFb RVb THb KRb VTb j) s j)))
    (hT1 : mem (Ob + 3 * n + Hs.length + 1) = 0) :
    ∀ l r π, smD M pk S T P Hs = .node l r π →
      (∀ i < n, mem (Ob + i) = bf (f i ∈ l.piece)) ∧
      (∀ i < n, mem (Ob + n + i) = bf (f i ∈ π.path.darts.toFinset)) ∧
      (∀ i < n, mem (Ob + 2 * n + i) = bf (M.tail (f i) ∈ π.path.mverts)) ∧
      (∀ j < Hs.length, mem (Ob + 3 * n + j) = bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
      mem (Ob + 3 * n + Hs.length) = ntag l ∧ mem (Ob + 3 * n + Hs.length + 1) = ntag r := by
  intro l r π he
  obtain ⟨R, π', hD, hd, hm⟩ := hF
  rw [hD] at he
  injection he with hl hr hπ
  subst hl hr hπ
  have hm' : π'.path.mverts = smPC M x U := hm
  have hpc : (smD M pk S T (smPL M P Hs x Lm) (smHs M Hs x U)).piece = smPL M P Hs x Lm :=
    smD_piece hpk0 _ _ _ rfl (smPL_rc hP)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [hLP i hi, h.lp hs hi]
    exact smBf_congr (by rw [show (smD M pk S T (if Lm = true then pdarts M P Hs else
      P \ {x, M.rev x}) (childHoles Hs (if U = true then {M.tail x, M.head x}
        else {M.tail x}))).piece = smPL M P Hs x Lm from hpc])
  · rw [hPD i hi, h.pd hs hi, hd]
  · rw [hCV i hi, h.cv hs hi, hm']
  · rw [hHM j hj, hs.hmf h.pw hj, hm']
  · rw [hT, h.child_tag hs hpk0 hloop]; rfl
  · rw [hT1]; rfl

lemma hlab_eq_zero_of {Hs : List (Finset V)} {v : V} (h : v ∉ hunion Hs) : hlab Hs v = 0 := by
  unfold hlab; rw [iteF h]

end Split

/-- **`smStep` has natural instructions only** (no real register or memory, no input, no
randomness), checked by the kernel. -/
lemma smStep_nat : mbNatS smStep = true := by decide +kernel

/-- **The choice by a global enumeration is the choice by the local order**: if the local
enumeration `f` of `[0, n)` is the global enumeration `e` (injective on `[0, N)`) at increasing
global indices `g`, then the first dart of `X` (`X` enumerated by `f`) by `e` (`firstE`, the
choice `pick` of `pcChoiceE`) is the dart of `X` of least local index. -/
lemma firstE_local {e : ℕ → D} {N n : ℕ} {f : ℕ → D} {g : ℕ → ℕ} (d₀ : D)
    (hg : ∀ i < n, g i < N ∧ f i = e (g i)) (hmono : ∀ i j, i < j → j < n → g i < g j)
    (heinj : ∀ a < N, ∀ b < N, e a = e b → a = b) {X : Finset D}
    (hX : ∀ d ∈ X, ∃ i < n, f i = d) {i : ℕ} (hi : i < n) (hfi : f i ∈ X)
    (hmin : ∀ j < i, f j ∉ X) : firstE e N X d₀ = f i := by
  have hf : (List.range N).find? (fun k => decide (e k ∈ X)) = some (g i) := by
    rw [List.find?_range_eq_some]
    refine ⟨by rw [← (hg i hi).2]; simpa using hfi, List.mem_range.2 (hg i hi).1,
      fun k hk => ?_⟩
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro hkX
    obtain ⟨j, hj, hfj⟩ := hX _ hkX
    have hkj : k = g j := heinj _ (by have := (hg i hi).1; omega) _ (hg j hj).1
      (by rw [← (hg j hj).2, hfj])
    have hji : j < i := by
      by_contra hc
      rcases Nat.lt_or_ge i j with h | h
      · have := hmono i j h hj; omega
      · have : j = i := by omega
        subst this; omega
    exact hmin j hji (by rw [hfj]; exact hkX)
  unfold firstE findE
  rw [hf]
  exact (hg i hi).2.symm

section Main

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 1600000 in
/-- **One step of `smD` on the machine.** From the per-dart arrays of a rev-closed piece `P`
(`SmArr`), with the choices `pk X` = the dart of `X` of least index, on a loopless map: within
`252 n + 19 #Hs + 78` steps, `r5360 = ntag (smD M pk S T P Hs)`, and at a node
`smD M pk S T P Hs = .node l r π` the memory from `Ob` holds the outputs `SepPSpec` asks for:
`bf (f i ∈ l.piece)`, `bf (f i ∈ π.path.darts)`, `bf (tail (f i) ∈ π.path.mverts)` (`i < n`),
`bf (¬ Disjoint Hs[j] π.path.mverts)` (`j < #Hs`), `ntag l`, `ntag r`; memory outside
`[Ob, Ob + 3 n + #Hs + 2)`, registers outside `5308 … 5440`, reals and output kept. -/
theorem smStep_smD (c : Config) (hc : WordsBounded W c) {n PFb RVb THb KRb VTb Ob : ℕ}
    {f : ℕ → D} {P : Finset D} {Hs : List (Finset V)} {S T : Finset V} {ν : V → ℕ}
    (h : SmArr M c.nmem n PFb RVb THb KRb VTb f P Hs S T ν) (hP : RevClosed M P)
    {pk : Finset D → D} (hpk : ∀ X ⊆ P, ∀ i < n, f i ∈ X → (∀ j < i, f j ∉ X) → pk X = f i)
    (hpk0 : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d)
    (r0 : c.nreg 5300 = n) (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb)
    (r3 : c.nreg 5303 = THb) (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb)
    (r6 : c.nreg 5306 = Ob) (r7 : c.nreg 5307 = Hs.length) (hW : 3 ≤ W)
    (w1 : PFb + n ≤ Ob) (w2 : RVb + n ≤ Ob) (w3 : THb + n ≤ Ob) (w4 : KRb + n ≤ Ob)
    (w5 : VTb + n ≤ Ob) (w6 : Ob + 3 * n + Hs.length + 2 ≤ W) (w7 : n + 1 ≤ W) :
    ∃ c' t, Exec I W smStep c c' t ∧ t ≤ 252 * n + 19 * Hs.length + 78 ∧
      c'.nreg 5360 = ntag (smD M pk S T P Hs) ∧
      (∀ l r π, smD M pk S T P Hs = .node l r π →
        (∀ i < n, c'.nmem (Ob + i) = bf (f i ∈ l.piece)) ∧
        (∀ i < n, c'.nmem (Ob + n + i) = bf (f i ∈ π.path.darts.toFinset)) ∧
        (∀ i < n, c'.nmem (Ob + 2 * n + i) = bf (M.tail (f i) ∈ π.path.mverts)) ∧
        (∀ j < Hs.length, c'.nmem (Ob + 3 * n + j) =
          bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
        c'.nmem (Ob + 3 * n + Hs.length) = ntag l ∧
        c'.nmem (Ob + 3 * n + Hs.length + 1) = ntag r) ∧
      (∀ a, (a < Ob ∨ Ob + 3 * n + Hs.length + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5308 ∨ 5440 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, s, ⟨cA, hA, hnd, hup, hlpm, hX, hY, hB⟩, hLP, hPD, hCV, hHM, hT, hT1,
      hmem, hreg, hrr, hrm, ho⟩ :=
    smStep_exec (P := I) c hc r0 r1 r2 r3 r4 r5 r6 r7 hW w1 w2 w3 w4 w5 w6 w7
      (fun i hi => (h.rv i hi).1)
  have hnode : c'.nreg 5360 = ntag (smD M pk S T P Hs) := hnd.trans (h.node hpk hpk0 hloop hA)
  refine ⟨c', t, e, ht, hnode, ?_, hmem, hreg, hrr, hrm, ho⟩
  intro l r π hD
  have h1 : ntag (smD M pk S T P Hs) = 1 := by rw [hD]; rfl
  have hnd0 : c'.nreg 5360 ≠ 0 := by rw [hnode, h1]; omega
  obtain ⟨⟨hcard, hBne⟩, hcase⟩ := (smD_ntag hpk0 hloop P Hs).1 h1
  obtain ⟨fX, fY, fB⟩ := smD_form (S := S) (T := T) hpk0 hloop hcard hBne
  have gX := h.fst hpk smX_sub (fun j hj => h.xv hj) hA.fx
  have gY := h.fst hpk smY_sub (fun j hj => h.yv hj) hA.fy
  have gB := h.fst hpk smB_sub (fun j hj => h.bv hj) hA.fb
  by_cases hXn : (smX M S T P Hs).Nonempty
  · have g1 : cA.nreg 5317 = 1 := by rw [gX.1]; exact (bf_eq_one _).2 hXn
    obtain ⟨ha, hpkx⟩ := gX.2 g1
    have hs_eq := hX hnd0 g1
    obtain ⟨v19, v20, v21, v22⟩ := hA.vx g1
    have hxX := hpk0 _ hXn
    have htl : M.tail (pk (smX M S T P Hs)) ∉ hunion Hs := fun hm =>
      (mem_filter.1 hxX).2.1 (mem_union_right _ hm)
    have hsp : SmSplit M n f Hs ν s (pk (smX M S T P Hs)) true false :=
      { a := ⟨by rw [hs_eq]; exact ha, by rw [hs_eq]; exact hpkx.symm⟩
        a' := fun _ => ⟨by rw [hs_eq, v19]; exact (h.rv _ ha).1,
          by rw [hs_eq]; simp only; rw [v19, (h.rv _ ha).2, hpkx]⟩
        up := by rw [hs_eq]; rfl
        lpm := by rw [hs_eq]; rfl
        v1 := by rw [hs_eq]; simp only; rw [v20, h.vt _ ha, hpkx]
        v2 := fun _ => by rw [hs_eq]; simp only; rw [v21, h.vtr ha, hpkx]
        t1 := by rw [hs_eq, hlab_eq_zero_of htl]
        t2 := fun _ => by rw [hs_eq]; simp only; rw [v22, h.thr ha, hpkx] }
    exact h.out hsp hP hpk0 hloop (fX hXn) hLP hPD hCV hHM hT hT1 l r π hD
  have g0 : cA.nreg 5317 = 0 := by rw [gX.1]; unfold bf; rw [iteF hXn]
  by_cases hYn : (smY M P Hs).Nonempty
  · have g2 : cA.nreg 5323 = 1 := by rw [gY.1]; exact (bf_eq_one _).2 hYn
    obtain ⟨ha, hpky⟩ := gY.2 g2
    have hs_eq := hY hnd0 g0 g2
    obtain ⟨v25, v26⟩ := hA.vy g2
    have hlt : (pdarts M P Hs).card < P.card := by
      rcases hcase with hc' | hc' | hc'
      · exact absurd hc' hXn
      · exact absurd hYn hc'
      · exact hc'
    have hsp : SmSplit M n f Hs ν s (pk (smY M P Hs)) false true :=
      { a := ⟨by rw [hs_eq]; exact ha, by rw [hs_eq]; exact hpky.symm⟩
        a' := fun hh => by simp at hh
        up := by rw [hs_eq]; rfl
        lpm := by rw [hs_eq]; rfl
        v1 := by rw [hs_eq]; simp only; rw [v25, h.vt _ ha, hpky]
        v2 := fun hh => by simp at hh
        t1 := by rw [hs_eq]; simp only; rw [v26, h.th _ ha, hpky]
        t2 := fun hh => by simp at hh }
    exact h.out hsp hP hpk0 hloop (fY hXn hYn hlt) hLP hPD hCV hHM hT hT1 l r π hD
  have g2 : cA.nreg 5323 = 0 := by rw [gY.1]; unfold bf; rw [iteF hYn]
  have g3 : cA.nreg 5327 = 1 := by rw [gB.1]; exact (bf_eq_one _).2 hBne
  obtain ⟨ha, hpkb⟩ := gB.2 g3
  have hs_eq := hB hnd0 g0 g2
  obtain ⟨v29, v30, v31, v32, v33⟩ := hA.vb g3
  have hxB := hpk0 _ hBne
  have hxP : pk (smB M S T P Hs) ∈ P := smB_sub hxB
  have htl : M.tail (pk (smB M S T P Hs)) ∉ hunion Hs := fun hm =>
    (mem_filter.1 hxB).2 (mem_union_right _ hm)
  have hhd : M.head (pk (smB M S T P Hs)) ∉ hunion Hs := fun hm =>
    hYn ⟨_, mem_filter.2 ⟨hP _ hxP, by rw [CombMap.tail_rev]; exact hm⟩⟩
  have hsp : SmSplit M n f Hs ν s (pk (smB M S T P Hs))
      (decide (M.head (pk (smB M S T P Hs)) ∉ S ∪ T)) false :=
    { a := ⟨by rw [hs_eq]; exact ha, by rw [hs_eq]; exact hpkb.symm⟩
      a' := fun _ => ⟨by rw [hs_eq, v29]; exact (h.rv _ ha).1,
        by rw [hs_eq]; simp only; rw [v29, (h.rv _ ha).2, hpkb]⟩
      up := by
        rw [hs_eq]; simp only
        rw [v32, h.krr ha, ← hpkb, smHst_bf, one_sub_bf]
        exact smBf_congr (by rw [lrk_st_iff hhd]; simp)
      lpm := by rw [hs_eq]; rfl
      v1 := by rw [hs_eq]; simp only; rw [v30, h.vt _ ha, hpkb]
      v2 := fun _ => by rw [hs_eq]; simp only; rw [v31, h.vtr ha, hpkb]
      t1 := by rw [hs_eq, hlab_eq_zero_of htl]
      t2 := fun _ => by rw [hs_eq]; simp only; rw [v33, h.thr ha, hpkb] }
  exact h.out hsp hP hpk0 hloop (fB hXn hYn) hLP hPD hCV hHM hT hT1 l r π hD

set_option maxHeartbeats 1600000 in
/-- **`smStep_smD` for the choices of the headline decomposition** (`pc.pick` of
`pcChoiceE M Q e N d₀`, as in `maxflow_plane_cost_decM`): the local enumeration `f` is the global
enumeration `e` (onto `D`, injective on `[0, N)`) at increasing global indices `g`. -/
theorem smStep_smD_pc (c : Config) (hc : WordsBounded W c) {n PFb RVb THb KRb VTb Ob : ℕ}
    {f : ℕ → D} {P : Finset D} {Hs : List (Finset V)} {S T Q : Finset V} {ν : V → ℕ}
    (h : SmArr M c.nmem n PFb RVb THb KRb VTb f P Hs S T ν) (hP : RevClosed M P)
    {e : ℕ → D} {N : ℕ} {g : ℕ → ℕ} (d₀ : D) (hsurj : ∀ d, ∃ k < N, e k = d)
    (heinj : ∀ a < N, ∀ b < N, e a = e b → a = b) (hg : ∀ i < n, g i < N ∧ f i = e (g i))
    (hmono : ∀ i j, i < j → j < n → g i < g j) (hloop : ∀ d, M.head d ≠ M.tail d)
    (r0 : c.nreg 5300 = n) (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb)
    (r3 : c.nreg 5303 = THb) (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb)
    (r6 : c.nreg 5306 = Ob) (r7 : c.nreg 5307 = Hs.length) (hW : 3 ≤ W)
    (w1 : PFb + n ≤ Ob) (w2 : RVb + n ≤ Ob) (w3 : THb + n ≤ Ob) (w4 : KRb + n ≤ Ob)
    (w5 : VTb + n ≤ Ob) (w6 : Ob + 3 * n + Hs.length + 2 ≤ W) (w7 : n + 1 ≤ W) :
    ∃ c' t, Exec I W smStep c c' t ∧ t ≤ 252 * n + 19 * Hs.length + 78 ∧
      c'.nreg 5360 = ntag (smD M (pcChoiceE M Q e N d₀).pick S T P Hs) ∧
      (∀ l r π, smD M (pcChoiceE M Q e N d₀).pick S T P Hs = .node l r π →
        (∀ i < n, c'.nmem (Ob + i) = bf (f i ∈ l.piece)) ∧
        (∀ i < n, c'.nmem (Ob + n + i) = bf (f i ∈ π.path.darts.toFinset)) ∧
        (∀ i < n, c'.nmem (Ob + 2 * n + i) = bf (M.tail (f i) ∈ π.path.mverts)) ∧
        (∀ j < Hs.length, c'.nmem (Ob + 3 * n + j) =
          bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts)) ∧
        c'.nmem (Ob + 3 * n + Hs.length) = ntag l ∧
        c'.nmem (Ob + 3 * n + Hs.length + 1) = ntag r) ∧
      (∀ a, (a < Ob ∨ Ob + 3 * n + Hs.length + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5308 ∨ 5440 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  refine smStep_smD c hc h hP (fun X hX i hi hfi hmin => ?_) (fun X ⟨d, hd⟩ => ?_) hloop
    r0 r1 r2 r3 r4 r5 r6 r7 hW w1 w2 w3 w4 w5 w6 w7
  · exact firstE_local d₀ hg hmono heinj (fun d hd => h.surj d (hX hd)) hi hfi hmin
  · obtain ⟨k, hk, rfl⟩ := hsurj d
    exact firstE_mem d₀ hk hd

end Main

end BKMNW

end PlanarFlow
