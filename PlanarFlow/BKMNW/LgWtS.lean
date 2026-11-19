module

public import PlanarFlow.BKMNW.LgKey
public import PlanarFlow.BKMNW.LgWt
public import PlanarFlow.BKMNW.FirstProg
public import PlanarFlow.BKMNW.ExistOracle

/-!
# The large-piece separator, stage 4 (pure part): the weights from the record's arrays

The weights of the certificate of a large piece are
`EX[j] = pcExf K (e' j) + lmoved (pcExf K) pcLs (e' j)` on the enumeration `e'` of the piece map
of the core `B` (`lmoved_pcLs`: `2` per attached pair `{y, rev y}`, at the anchor `ancD (rep E)`).
The anchors need the **classes of the anchor vertices** `avQ y` of the attached darts, which are
pendant darts (ends in `Q`, where the rotation of the piece map is the identity) or darts inside a
touched hole: the hole label, or else the vertex itself. A vertex is identified from the record by
its number `ν` (array `VP`); to give it a compact key we require the record's enumeration (in
increasing `gid`) to list the darts **sorted by the numbers of their tails** (`WtIn.sorted`; it
follows from the input convention `TailSorted gid ν`: `gid a < gid b → ν (tail a) ≤ ν (tail b)`,
i.e. the darts are given in adjacency-list order). Then the darts with one tail are consecutive,
and the first index of the run (`vkF`) is a compact vertex key.

* `vkF` (first index of the run of equal values), `vkF_le`, `vkF_val`, `vkF_step`, `vkF_min`,
  **`vkF_eq_iff`** (on a sorted array: equal keys ↔ equal values);
* `ckv` (class key: the hole label, or `kk + 1 + vkF`), **`ckv_iff`** (equal keys ↔ `HRel`);
* `WtIn` (the arrays of the record and of the core's enumeration), `ckA`, `akI`, `akA`, `tbA`
  (the table of first core indices of a key, `fiF`), `selP` (the representative of an attached
  pair), `avA` (`1 +` its anchor's core index);
* `findE`/`firstE` across enumerations: `firstE_tb`, `pcExf_loc`, `rep_loc`, **`ancD_loc`**;
* `mem_pcNf_idx`, `pcNfB_rev`, **`attached_anchor`** (every attached dart has an anchor);
* **`card_pcEs_anc`** (the pairs anchored at a dart ↔ their representatives' indices),
  **`saF_avA`**, and **`wt_closed`**:
  `fiO K fl TH j + saF avA 2 n (j + 1) = pcExf K (e' j) + lmoved (pcExf K) pcLs (e' j)` for the
  choices `pcChoiceE M Q eG N d₀` of the global enumeration `eG` (`gid (eG i) = i`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Relation CombMap Orbit

attribute [-instance] PlanarFlow.BKMNW.smInnerDec

/-! ### The first index of a run of equal values -/

/-- The first index of the run of equal values containing `i` (`vp` read from `0`). -/
def vkF (vp : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if vp (i + 1) = vp i then vkF vp i else i + 1

lemma vkF_le (vp : ℕ → ℕ) (i : ℕ) : vkF vp i ≤ i := by
  induction i with
  | zero => simp [vkF]
  | succ i ih => simp only [vkF]; split_ifs <;> omega

lemma vkF_val (vp : ℕ → ℕ) (i : ℕ) : vp (vkF vp i) = vp i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [vkF]
    split_ifs with h
    · rw [ih, h]
    · rfl

lemma vkF_step (vp : ℕ → ℕ) (i : ℕ) :
    vkF vp i = if vp i = vp (i - 1) then vkF vp (i - 1) else i := by
  cases i with
  | zero => simp [vkF]
  | succ i => simp [vkF]

lemma vkF_min {vp : ℕ → ℕ} {n : ℕ} (hmono : ∀ i j, i < j → j < n → vp i ≤ vp j) :
    ∀ i < n, ∀ i' < vkF vp i, vp i' < vp i := by
  intro i
  induction i with
  | zero => intro _ i' h; simp [vkF] at h
  | succ i ih =>
    intro hi i' hi'
    simp only [vkF] at hi'
    split_ifs at hi' with h
    · rw [h]; exact ih (by omega) i' hi'
    · have h1 : vp i ≤ vp (i + 1) := hmono i (i + 1) (by omega) hi
      have h2 : vp i < vp (i + 1) := lt_of_le_of_ne h1 (Ne.symm h)
      rcases Nat.lt_or_ge i' i with h3 | h3
      · exact lt_of_le_of_lt (hmono i' i h3 (by omega)) h2
      · have : i' = i := by omega
        subst this; exact h2

/-- **On a sorted array, equal run keys are equal values.** -/
lemma vkF_eq_iff {vp : ℕ → ℕ} {n : ℕ} (hmono : ∀ i j, i < j → j < n → vp i ≤ vp j) {i j : ℕ}
    (hi : i < n) (hj : j < n) : vkF vp i = vkF vp j ↔ vp i = vp j := by
  constructor
  · intro h
    have a := vkF_val vp i
    have b := vkF_val vp j
    rw [h] at a
    rw [← a, b]
  · intro h
    have a1 := vkF_min hmono i hi
    have a2 := vkF_min hmono j hj
    have v1 := vkF_val vp i
    have v2 := vkF_val vp j
    rcases lt_trichotomy (vkF vp i) (vkF vp j) with h3 | h3 | h3
    · have := a2 _ h3; rw [v1, h] at this; omega
    · exact h3
    · have := a1 _ h3; rw [v2, ← h] at this; omega

/-! ### Class keys -/

/-- **The class key of a vertex**: its hole label `h` if positive, else `kk + 1 + vk` (`vk` a key
of the vertex itself). -/
def ckv (kk h vk : ℕ) : ℕ := if 0 < h then h else kk + 1 + vk

lemma ckv_pos (kk h vk : ℕ) : 0 < ckv kk h vk := by unfold ckv; split_ifs <;> omega

lemma ckv_lt {kk h vk n : ℕ} (hh : h ≤ kk) (hv : vk < n) : ckv kk h vk < kk + 1 + n := by
  unfold ckv; split_ifs <;> omega

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Equal class keys are related vertices** (pairwise disjoint holes; `va`, `vb` keys of the
vertices themselves). -/
lemma ckv_iff {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {ν : V → ℕ} (hν : Injective ν)
    {a b : V} {va vb : ℕ} (hva : va = vb ↔ ν a = ν b) :
    ckv Hs.length (hlab Hs a) va = ckv Hs.length (hlab Hs b) vb ↔ HRel Hs a b := by
  have la := hlab_le Hs a
  have lb := hlab_le Hs b
  unfold ckv
  by_cases ha : 0 < hlab Hs a <;> by_cases hb : 0 < hlab Hs b
  · rw [iteT ha, iteT hb]
    constructor
    · intro h
      obtain ⟨hlt, hma⟩ := hlab_mem ha
      obtain ⟨-, hmb⟩ := hlab_mem hb
      rw [h] at hma
      exact Or.inr ⟨_, sm_getD_mem (by omega), hma, hmb⟩
    · rintro (h | ⟨H, hH, h1, h2⟩)
      · rw [h]
      · obtain ⟨-, e⟩ := hlab_unique hd hH h1
        obtain ⟨hlt, -⟩ := hlab_mem ha
        have := (hlab_eq_succ_iff hd hlt (v := b)).2 (by rw [e]; exact h2)
        omega
  · rw [iteT ha, iteF hb]
    refine ⟨fun h => by omega, fun h => ?_⟩
    rcases h with h | ⟨H, hH, h1, h2⟩
    · subst h; exact absurd ha hb
    · exact absurd (hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, h2⟩)) hb
  · rw [iteF ha, iteT hb]
    refine ⟨fun h => by omega, fun h => ?_⟩
    rcases h with h | ⟨H, hH, h1, h2⟩
    · subst h; exact absurd hb ha
    · exact absurd (hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, h1⟩)) ha
  · rw [iteF ha, iteF hb]
    constructor
    · intro h
      exact Or.inl (hν (hva.1 (by omega)))
    · rintro (h | ⟨H, hH, h1, h2⟩)
      · subst h; have := hva.2 rfl; omega
      · exact absurd (hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, h1⟩)) ha

/-! ### The arrays -/

variable (M) in
/-- **The input of the weights scan**: the record's enumeration `g` of the piece `P` (`n` darts,
increasing in `gid`; reverse indices `rp`, hole labels `hp` and vertex numbers `vp` of the tails,
the latter sorted), and the enumeration `e'` of the piece map of the core (`n'` darts, increasing
in `gid`, `e' j = g (ix j)`). -/
structure WtIn (gid : D → ℕ) (ν : V → ℕ) (Q : Finset V) (P : Finset D) (Hs : List (Finset V))
    (n : ℕ) (g : ℕ → D) (rp hp vp : ℕ → ℕ) (n' : ℕ) (e' : ℕ → D) (ix : ℕ → ℕ) : Prop where
  g_mem : ∀ i < n, g i ∈ P
  g_surj : ∀ y ∈ P, ∃ i < n, g i = y
  g_mono : ∀ i j, i < j → j < n → gid (g i) < gid (g j)
  rpOk : ∀ i < n, rp i < n ∧ g (rp i) = M.rev (g i)
  hpOk : ∀ i < n, hp i = hlab Hs (M.tail (g i))
  vpOk : ∀ i < n, vp i = ν (M.tail (g i))
  sorted : ∀ i j, i < j → j < n → vp i ≤ vp j
  e_mem : ∀ j < n', e' j ∈ pdarts M (core M Q P) Hs
  e_surj : ∀ y ∈ pdarts M (core M Q P) Hs, ∃ j < n', e' j = y
  e_mono : ∀ i j, i < j → j < n' → gid (e' i) < gid (e' j)
  ixOk : ∀ j < n', ix j < n ∧ g (ix j) = e' j

/-- The class key of the tail of the dart of index `i`. -/
def ckA (kk : ℕ) (hp vp : ℕ → ℕ) (i : ℕ) : ℕ := ckv kk (hp i) (vkF vp i)

/-- The index of a dart whose tail is the anchor vertex of the dart of index `i` (its reverse if
its tail is pendant, i.e. of odd number). -/
def akI (rp vp : ℕ → ℕ) (i : ℕ) : ℕ := if vp i % 2 = 1 then rp i else i

/-- The class key of the anchor vertex of the dart of index `i`. -/
def akA (kk : ℕ) (rp hp vp : ℕ → ℕ) (i : ℕ) : ℕ := ckA kk hp vp (akI rp vp i)

/-- The table of the first core index (`+ 1`) of every key. -/
def tbA (kk : ℕ) (hp vp ix fl : ℕ → ℕ) (n' k : ℕ) : ℕ :=
  fiF fl (fun j => ckA kk hp vp (ix j)) n' k

/-- **The representative of an attached pair**: off the core (`cf = 0`), in `pcNf` (not inside a
hole untouched by the core), of smaller index than its reverse. -/
def selP (kk : ℕ) (rp hp vp ix fl cf : ℕ → ℕ) (n' i : ℕ) : Prop :=
  cf i = 0 ∧ ¬ (0 < hp i ∧ hp i = hp (rp i) ∧ tbA kk hp vp ix fl n' (ckA kk hp vp i) = 0) ∧
    i < rp i

instance (kk : ℕ) (rp hp vp ix fl cf : ℕ → ℕ) (n' i : ℕ) :
    Decidable (selP kk rp hp vp ix fl cf n' i) := by unfold selP; infer_instance

/-- **The anchor of a representative**: `1 +` the core index of its anchor, `0` off the
representatives. -/
def avA (kk : ℕ) (rp hp vp ix fl cf : ℕ → ℕ) (n' i : ℕ) : ℕ :=
  if selP kk rp hp vp ix fl cf n' i then tbA kk hp vp ix fl n' (akA kk rp hp vp i) else 0

section Sem

variable {gid : D → ℕ} {ν : V → ℕ} {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
  {n : ℕ} {g : ℕ → D} {rp hp vp : ℕ → ℕ} {n' : ℕ} {e' : ℕ → D} {ix : ℕ → ℕ}

lemma WtIn.g_inj (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {i j : ℕ} (hi : i < n)
    (hj : j < n) (h : g i = g j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · have := hW.g_mono i j h' hj; rw [h] at this; omega
  · exact h'
  · have := hW.g_mono j i h' hi; rw [h] at this; omega

lemma WtIn.e_inj (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {i j : ℕ} (hi : i < n')
    (hj : j < n') (h : e' i = e' j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · have := hW.e_mono i j h' hj; rw [h] at this; omega
  · exact h'
  · have := hW.e_mono j i h' hi; rw [h] at this; omega

lemma WtIn.rp_rp (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {i : ℕ} (hi : i < n) :
    rp (rp i) = i := by
  obtain ⟨h1, h2⟩ := hW.rpOk i hi
  obtain ⟨h3, h4⟩ := hW.rpOk _ h1
  exact hW.g_inj h3 hi (by rw [h4, h2, M.rev_rev])

lemma WtIn.rp_ne (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {i : ℕ} (hi : i < n) :
    rp i ≠ i := by
  intro h
  have := (hW.rpOk i hi).2
  rw [h] at this
  exact M.rev_ne (g i) this.symm

/-- **The class keys of the tails** of two darts of the record are equal iff the tails are
related by the holes. -/
lemma WtIn.ck_iff (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) (hd : Hs.Pairwise Disjoint)
    (hν : Injective ν) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ckA Hs.length hp vp i = ckA Hs.length hp vp j ↔ HRel Hs (M.tail (g i)) (M.tail (g j)) := by
  unfold ckA
  rw [hW.hpOk i hi, hW.hpOk j hj]
  refine ckv_iff hd hν ?_
  rw [vkF_eq_iff hW.sorted hi hj, hW.vpOk i hi, hW.vpOk j hj]

lemma WtIn.akI_lt (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {i : ℕ} (hi : i < n) :
    akI rp vp i < n := by
  unfold akI; split_ifs
  · exact (hW.rpOk i hi).1
  · exact hi

/-- The dart of index `akI i` has the anchor vertex of `g i` as tail (`QPar`). -/
lemma WtIn.tail_akI (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) (hQ : QPar Q ν) {i : ℕ}
    (hi : i < n) : M.tail (g (akI rp vp i)) = avQ M Q (g i) := by
  unfold akI avQ
  have hq : M.tail (g i) ∈ Q ↔ vp i % 2 = 1 := by rw [hW.vpOk i hi]; exact hQ _
  by_cases h : vp i % 2 = 1
  · rw [iteT h, iteT (hq.2 h), (hW.rpOk i hi).2, CombMap.tail_rev]
  · rw [iteF h, iteF (fun h' => h (hq.1 h'))]

/-! ### First darts across enumerations -/

/-- **The first dart of a set of the piece map of the core**, by the global enumeration, read off
the table of first core indices. -/
lemma firstE_tb (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {eG : ℕ → D} {N : ℕ}
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) {X : Finset D}
    (hXB : X ⊆ pdarts M (core M Q P) Hs) {fl kt : ℕ → ℕ} {k : ℕ} (hk : k ≠ 0)
    (hXk : ∀ j < n', (e' j ∈ X ↔ fl j ≠ 0 ∧ kt j = k)) (d₀ : D) :
    firstE eG N X d₀ = if fiF fl kt n' k = 0 then d₀ else e' (fiF fl kt n' k - 1) := by
  unfold firstE
  rw [findE_gidLoc he hesurj hW.e_mono (fun d hd => hW.e_surj d (hXB hd)), findE_fiF hk hXk]
  split_ifs <;> rfl

/-- **`pcExf` of the global choices is that of the core's enumeration.** -/
lemma pcExf_loc (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {eG : ℕ → D} {N : ℕ}
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) (d₀ : D) (K : ℕ) (d : D) :
    pcExf M (pcChoiceE M Q eG N d₀) Q P Hs K d = pcExf M (pcChoiceE M Q e' n' d₀) Q P Hs K d := by
  have h : ∀ H, (pcChoiceE M Q eG N d₀).anch P Hs H = (pcChoiceE M Q e' n' d₀).anch P Hs H :=
    fun H => firstE_gidLoc d₀ he hesurj hW.e_mono fun d hd => hW.e_surj d (mem_filter.1 hd).1
  unfold pcExf
  simp only [h]

/-- **The representative of a pair** is its dart of smaller index. -/
lemma rep_loc (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) {eG : ℕ → D} {N : ℕ}
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) (d₀ : D) {i : ℕ}
    (hi : i < n) (hlt : i < rp i) :
    (pcChoiceE M Q eG N d₀).rep {g i, M.rev (g i)} = g i := by
  show firstE eG N {g i, M.rev (g i)} d₀ = g i
  have hemono : ∀ a b, a < b → b < N → gid (eG a) < gid (eG b) := fun a b h hb => by
    rw [he a (by omega), he b hb]; exact h
  obtain ⟨hr, hgr⟩ := hW.rpOk i hi
  unfold firstE
  rw [findE_eq_min hemono (fun d _ => hesurj d) (d := g i) (by simp) ?_]
  · rfl
  · intro d' hd'
    simp only [mem_insert, mem_singleton] at hd'
    rcases hd' with rfl | rfl
    · exact le_rfl
    · rw [← hgr]; exact (hW.g_mono i (rp i) hlt hr).le

/-- The table of first core indices: a key `k` of an index of the core. -/
lemma WtIn.mem_key (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) (hd : Hs.Pairwise Disjoint)
    (hν : Injective ν) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n') :
    HRel Hs (M.tail (e' j)) (M.tail (g i)) ↔ ckA Hs.length hp vp (ix j) = ckA Hs.length hp vp i := by
  obtain ⟨h1, h2⟩ := hW.ixOk j hj
  rw [hW.ck_iff hd hν h1 hi, h2]

/-- **The anchor of a dart of the record**, read off the table. -/
lemma ancD_loc (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) (hd : Hs.Pairwise Disjoint)
    (hν : Injective ν) (hQ : QPar Q ν) {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i)
    (hesurj : ∀ d, ∃ i < N, eG i = d) (d₀ : D) {fl : ℕ → ℕ} (hfl : ∀ j < n', fl j ≠ 0) {i : ℕ}
    (hi : i < n) :
    (pcChoiceE M Q eG N d₀).ancD P Hs (g i) =
      if tbA Hs.length hp vp ix fl n' (akA Hs.length rp hp vp i) = 0 then d₀
      else e' (tbA Hs.length hp vp ix fl n' (akA Hs.length rp hp vp i) - 1) := by
  classical
  show firstE eG N _ d₀ = _
  refine firstE_tb hW he hesurj (fun d hd => (mem_filter.1 hd).1) (ckv_pos _ _ _).ne'
    (fun j hj => ?_) d₀
  rw [mem_filter]
  have ha := hW.akI_lt hi
  rw [← hW.tail_akI hQ hi, hW.mem_key hd hν ha hj]
  exact ⟨fun h => ⟨hfl j hj, h.2⟩, fun h => ⟨hW.e_mem j hj, h.2⟩⟩

/-! ### The attached darts -/

/-- **A dart of the record in `pcNf`**, from its labels and the table. -/
lemma mem_pcNf_idx (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix) (hd : Hs.Pairwise Disjoint)
    (hν : Injective ν) {fl : ℕ → ℕ} (hfl : ∀ j < n', fl j ≠ 0) {i : ℕ} (hi : i < n) :
    g i ∈ pcNf M Q P Hs ↔
      ¬ (0 < hp i ∧ hp i = hp (rp i) ∧ tbA Hs.length hp vp ix fl n' (ckA Hs.length hp vp i) = 0) := by
  classical
  have hinner : Inner M Hs (g i) ↔ 0 < hp i ∧ hp i = hp (rp i) := by
    rw [inner_iff_hlab hd, hW.hpOk i hi, hW.hpOk _ (hW.rpOk i hi).1, (hW.rpOk i hi).2, CombMap.tail_rev]
  have htb : (∀ b ∈ pdarts M (core M Q P) Hs, ¬ HRel Hs (M.tail b) (M.tail (g i))) ↔
      tbA Hs.length hp vp ix fl n' (ckA Hs.length hp vp i) = 0 := by
    unfold tbA
    rw [fiF_zero_iff]
    constructor
    · intro h
      refine Or.inr fun j hj hh => h _ (hW.e_mem j hj) ((hW.mem_key hd hν hi hj).2 hh.2)
    · rintro (h | h) b hb hr
      · exact absurd h (ckv_pos _ _ _).ne'
      · obtain ⟨j, hj, rfl⟩ := hW.e_surj b hb
        exact h j hj ⟨hfl j hj, (hW.mem_key hd hν hi hj).1 hr⟩
  unfold pcNf
  rw [mem_sdiff, mem_filter]
  simp only [hW.g_mem i hi, true_and, hinner, htb]
  tauto

/-- **The attached darts are closed under reversal.** -/
lemma pcNfB_rev {S T Q : Finset V} {P : Finset D} {Hs : List (Finset V)} (hP : PcOK M S T P Hs)
    {d : D} (hdm : d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs) :
    M.rev d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs := by
  classical
  have hd := hP.disj
  obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hdm
  obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
  refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hP.rev _ hdP, fun h => hdD ?_⟩, fun h => hdB ?_⟩
  · obtain ⟨-, h1, h2⟩ := mem_filter.1 h
    have hdi : Inner M Hs d := inner_rev.1 h1
    refine mem_filter.2 ⟨hdP, hdi, fun b hb hr => h2 b hb ?_⟩
    obtain ⟨H, hH, ht, hh⟩ := hdi
    rw [CombMap.tail_rev]
    exact hRel_trans' hd hr (Or.inr ⟨H, hH, ht, hh⟩)
  · have := stable_pdarts (revClosed_core hP.rev) Hs _ h
    rw [revPerm_apply, M.rev_rev] at this; exact this

/-- **Every attached dart has an anchor** in the piece map of the core (the argument of
`pcert_of_core'`). -/
lemma attached_anchor {S T Q : Finset V} (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q →
    M.tail d' = q → d = d') (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) (hHQ : Disjoint (hunion Hs) Q) {b₀ : D}
    (hb₀ : b₀ ∈ pdarts M (core M Q P) Hs) {d : D}
    (hdm : d ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs) :
    ∃ b ∈ pdarts M (core M Q P) Hs, HRel Hs (M.tail b) (avQ M Q d) := by
  classical
  set B₀ := pdarts M (core M Q P) Hs
  have hanc : ∀ d ∈ pcNf M Q P Hs \ B₀, M.tail d ∉ Q → ∃ b ∈ B₀, HRel Hs (M.tail b) (M.tail d) := by
    intro d hd htQ
    obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hd
    obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
    by_cases hhQ : M.head d ∈ Q
    · exact exists_core_anchor hQdeg hP hHQ hb₀ hdP hhQ htQ
    · have hinner : Inner M Hs d := by
        by_contra h
        exact hdB (mem_pdarts.2 ⟨mem_core.2 ⟨hdP, htQ, hhQ⟩, h⟩)
      by_contra hno
      push Not at hno
      exact hdD (mem_filter.2 ⟨hdP, hinner, hno⟩)
  by_cases htQ : M.tail d ∈ Q
  · have := hanc _ (pcNfB_rev hP hdm) (by rw [CombMap.tail_rev]; exact fun h => hQ5 d ⟨htQ, h⟩)
    simpa [avQ, htQ] using this
  · simpa [avQ, htQ] using hanc d hdm htQ

/-! ### The counts -/

/-- **The pairs anchored at a dart are counted by their representatives' indices.** -/
theorem card_pcEs_anc {S T : Finset V} (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix)
    (hP : PcOK M S T P Hs) {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i)
    (hesurj : ∀ d, ∃ i < N, eG i = d) (d₀ : D) (d : D) :
    ((pcEs M Q P Hs).filter fun E =>
        d = (pcChoiceE M Q eG N d₀).ancD P Hs ((pcChoiceE M Q eG N d₀).rep E)).card =
      ((range n).filter fun i => (g i ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs ∧ i < rp i) ∧
        d = (pcChoiceE M Q eG N d₀).ancD P Hs (g i)).card := by
  classical
  symm
  refine card_bij (fun i _ => ({g i, M.rev (g i)} : Finset D)) (fun i hi => ?_)
    (fun i hi i' hi' h => ?_) (fun E hE => ?_)
  · obtain ⟨hi1, ⟨hA, hlt⟩, hdd⟩ := mem_filter.1 hi
    have hin := mem_range.1 hi1
    refine mem_filter.2 ⟨mem_image.2 ⟨g i, hA, rfl⟩, ?_⟩
    rw [rep_loc hW he hesurj d₀ hin hlt]; exact hdd
  · obtain ⟨hi1, ⟨-, hlt⟩, -⟩ := mem_filter.1 hi
    obtain ⟨hi1', ⟨-, hlt'⟩, -⟩ := mem_filter.1 hi'
    have h1 := rep_loc (Q := Q) hW he hesurj d₀ (mem_range.1 hi1) hlt
    have h2 := rep_loc (Q := Q) hW he hesurj d₀ (mem_range.1 hi1') hlt'
    rw [h, h2] at h1
    exact hW.g_inj (mem_range.1 hi1) (mem_range.1 hi1') h1.symm
  · obtain ⟨hE1, hE2⟩ := mem_filter.1 hE
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hE1
    obtain ⟨i0, hi0, rfl⟩ := hW.g_surj y (mem_sdiff.1 (mem_sdiff.1 hy).1).1
    obtain ⟨hr0, hgr0⟩ := hW.rpOk i0 hi0
    have hne := hW.rp_ne hi0
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · -- the representative is the reverse
      have hrr := hW.rp_rp hi0
      have hlt' : rp i0 < rp (rp i0) := by rw [hrr]; exact hlt
      have hA : g (rp i0) ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs := by
        rw [hgr0]; exact pcNfB_rev hP hy
      have hEq : ({g (rp i0), M.rev (g (rp i0))} : Finset D) = {g i0, M.rev (g i0)} := by
        rw [hgr0, M.rev_rev, pair_comm]
      refine ⟨rp i0, mem_filter.2 ⟨mem_range.2 hr0, ⟨hA, hlt'⟩, ?_⟩, hEq⟩
      rw [← rep_loc (Q := Q) hW he hesurj d₀ hr0 hlt', hEq]; exact hE2
    · refine ⟨i0, mem_filter.2 ⟨mem_range.2 hi0, ⟨hy, hlt⟩, ?_⟩, rfl⟩
      rw [← rep_loc (Q := Q) hW he hesurj d₀ hi0 hlt]; exact hE2

/-- **The scatter-add of the anchors** counts the pairs anchored at `e' j`. -/
theorem saF_avA {S T : Finset V} (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix)
    (hP : PcOK M S T P Hs) (hHQ : Disjoint (hunion Hs) Q) (hν : Injective ν) (hQ : QPar Q ν)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (hne : 0 < n')
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {fl cf : ℕ → ℕ} (hfl : ∀ j < n', fl j ≠ 0)
    (hcf : ∀ i < n, cf i = bf (g i ∈ pdarts M (core M Q P) Hs)) {j : ℕ} (hj : j < n') :
    saF (avA Hs.length rp hp vp ix fl cf n') (fun _ => 2) n (j + 1) =
      2 * ((range n).filter fun i => (g i ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs ∧ i < rp i) ∧
        e' j = (pcChoiceE M Q eG N d₀).ancD P Hs (g i)).card := by
  classical
  have hd := hP.disj
  unfold saF
  rw [sum_const, smul_eq_mul, mul_comm]
  congr 2
  refine filter_congr fun i hi => ?_
  have hin := mem_range.1 hi
  have hsel : selP Hs.length rp hp vp ix fl cf n' i ↔
      g i ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs ∧ i < rp i := by
    unfold selP
    rw [hcf i hin, mem_sdiff, mem_pcNf_idx hW hd hν hfl hin]
    unfold bf
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, fun h => by rw [iteT h] at h1; omega⟩, h3⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩
      exact ⟨by rw [iteF h1], h2, h3⟩
  unfold avA
  by_cases hs : selP Hs.length rp hp vp ix fl cf n' i
  · rw [iteT hs]
    have hA := (hsel.1 hs).1
    -- the anchor exists
    obtain ⟨b, hb, hbr⟩ := attached_anchor hQdeg hQ5 hP hHQ (hW.e_mem 0 hne) hA
    obtain ⟨j0, hj0, rfl⟩ := hW.e_surj b hb
    have hkey : ckA Hs.length hp vp (ix j0) = akA Hs.length rp hp vp i := by
      unfold akA
      rw [← hW.mem_key hd hν (hW.akI_lt hin) hj0, hW.tail_akI hQ hin]; exact hbr
    have hpos : tbA Hs.length hp vp ix fl n' (akA Hs.length rp hp vp i) ≠ 0 := by
      unfold tbA
      rw [Ne, fiF_zero_iff]
      push Not
      exact ⟨(ckv_pos _ _ _).ne', j0, hj0, hfl j0 hj0, hkey⟩
    obtain ⟨k, hk⟩ : ∃ k, tbA Hs.length hp vp ix fl n' (akA Hs.length rp hp vp i) = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_ne_zero hpos).symm⟩
    have hkn : k < n' := (fiF_pos hk).1
    rw [ancD_loc hW hd hν hQ he hesurj d₀ hfl hin, iteF hpos, hk, Nat.add_sub_cancel]
    constructor
    · intro h
      refine ⟨hsel.1 hs, ?_⟩
      have : k = j := by omega
      rw [this]
    · rintro ⟨-, h⟩
      have := hW.e_inj hj hkn h
      omega
  · rw [iteF hs]
    constructor
    · intro h; omega
    · rintro ⟨h, -⟩; exact absurd (hsel.2 h) hs

/-- **The weights in closed form**: the marks `fiO K` of the first core index of every hole plus
the scatter-add of `2` at the anchors of the representatives are the weights `pcExf + lmoved` of
the certificate of the piece, for the choices of the global enumeration. -/
theorem wt_closed {S T : Finset V} (hW : WtIn M gid ν Q P Hs n g rp hp vp n' e' ix)
    (hP : PcOK M S T P Hs) (hHQ : Disjoint (hunion Hs) Q) (hν : Injective ν) (hQ : QPar Q ν)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (hne : 0 < n')
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) (K : ℕ) {fl cf : ℕ → ℕ} (hfl : ∀ j < n', fl j ≠ 0)
    (hcf : ∀ i < n, cf i = bf (g i ∈ pdarts M (core M Q P) Hs)) {j : ℕ} (hj : j < n') :
    fiO K fl (fun j => hlab Hs (M.tail (e' j))) j +
        saF (avA Hs.length rp hp vp ix fl cf n') (fun _ => 2) n (j + 1) =
      pcExf M (pcChoiceE M Q eG N d₀) Q P Hs K (e' j) +
        lmoved (pcExf M (pcChoiceE M Q eG N d₀) Q P Hs K) (pcLs M (pcChoiceE M Q eG N d₀) Q P Hs)
          (e' j) := by
  have hd := hP.disj
  have hB : ∀ x ∈ pdarts M (core M Q P) Hs, M.rev x ∈ pdarts M (core M Q P) Hs := fun x hx => by
    have := stable_pdarts (revClosed_core hP.rev) Hs x hx
    rwa [revPerm_apply] at this
  have hx : pcExf M (pcChoiceE M Q e' n' d₀) Q P Hs K (e' j) =
      fiO K fl (fun j => hlab Hs (M.tail (e' j))) j := by
    refine pcExf_fiF (fl := fl) (key := fun j => hlab Hs (M.tail (e' j))) d₀ K
      (fun a ha b hb h => hW.e_inj ha hb h)
      (fun i hi => ⟨fun _ => hW.e_mem i hi, fun _ => hfl i hi⟩)
      (fun i hi => ?_) (fun i hi H hH ht j hj => ?_) hj
    · show hlab Hs (M.tail (e' i)) ≠ 0 ↔ _
      rw [← mem_hunion, ← hlab_pos_iff]; omega
    · show _ ↔ hlab Hs (M.tail (e' j)) = hlab Hs (M.tail (e' i))
      obtain ⟨hp0, e⟩ := hlab_unique hd hH ht
      obtain ⟨hlt, -⟩ := hlab_mem hp0
      have := hlab_eq_succ_iff hd hlt (v := M.tail (e' j))
      rw [e, Nat.sub_add_cancel hp0] at this
      exact this.symm
  rw [lmoved_pcLs _ K (ordE_ok hesurj _) hB, card_pcEs_anc hW hP he hesurj d₀,
    ← saF_avA hW hP hHQ hν hQ hQdeg hQ5 hne he hesurj d₀ hfl hcf hj, pcExf_loc hW he hesurj d₀ K,
    hx]

end Sem

end MfDrv

end BKMNW

end PlanarFlow
