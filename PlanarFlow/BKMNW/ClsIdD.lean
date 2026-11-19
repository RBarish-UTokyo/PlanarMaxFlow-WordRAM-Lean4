module

public import PlanarFlow.BKMNW.ExistGroupD
public import PlanarFlow.BKMNW.CompGraph

/-!
# The classes of a split as numbers

The class function `clsF M P Nf Hs K ρ` of a split (`PlanarFlow/BKMNW/ExistGroupD.lean`) read
through an enumeration `e` of the darts of `P` by the indices `< n`: a number `clsIdF … i` per
index with `clsIdF i = clsIdF j ↔ e j ∈ clsF … (e i)`. The components off the new hole `Y`
(of the darts of `Nf` not inside `Y`) are those of the graph `cgAdj` on all the indices of `P`
with the darts outside `Nf \ J` isolated (`mem_comp_iff_cgAdj_sub`).

* `CgEnumSub` (an enumeration of a superset `B` of `N`), `CgEnumSub.rvOK`,
  **`mem_comp_iff_cgAdj_sub`**;
* `ClsEnum` (an enumeration of `P` with the index of the reverse dart `rv`, the class numbers of
  the tails `key`, the flags `yt`/`yh` of the ends in `Y`, `nf` of `Nf`); `clsJ`, `clsN`,
  `clsRv`, `clsYf` (the input of the graph of the components), **`ClsEnum.sub`**;
* `clsIdF` (`3 min(i, rv i)` on pairs, `3 lab i + 1` on the components, `3 key i + 2` on the darts
  at a hole); **`clsIdF_iff`**: with labels of the components and `IsCls P (clsF …)` (the first
  conclusion of `exists_cls'`), `clsIdF i = clsIdF j ↔ e j ∈ clsF M P Nf Hs K ρ (e i)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Components of a subset -/

variable (M) in
/-- An enumeration `e` of a superset `B` of the darts `N`; the reverse slot `rv` is the index of
the reverse dart when both are in `N` (the index itself otherwise), `yf` flags the darts with the
tail in `Y` or outside `N`. -/
structure CgEnumSub (B N : Finset D) (Hs : List (Finset V)) (Y : Finset V) (n : ℕ) (e : ℕ → D)
    (rv key : ℕ → ℕ) (yf : ℕ → Bool) : Prop where
  mem : ∀ i < n, e i ∈ B
  surj : ∀ d ∈ B, ∃ i < n, e i = d
  inj : ∀ i < n, ∀ j < n, e i = e j → i = j
  sub : N ⊆ B
  rvlt : ∀ i < n, rv i < n
  rvin : ∀ i < n, e i ∈ N → M.rev (e i) ∈ N → e (rv i) = M.rev (e i)
  rvout : ∀ i < n, ¬ (e i ∈ N ∧ M.rev (e i) ∈ N) → rv i = i
  key : ∀ i < n, ∀ j < n, (key i = key j ↔ HRel Hs (M.tail (e i)) (M.tail (e j)))
  yf : ∀ i < n, (yf i = true ↔ (M.tail (e i) ∈ Y ∨ e i ∉ N))

lemma CgEnumSub.rvOK {B N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {n : ℕ}
    {e : ℕ → D} {rv key : ℕ → ℕ} {yf : ℕ → Bool} (hE : CgEnumSub M B N Hs Y n e rv key yf) :
    RvOK n rv := by
  intro i hi
  refine ⟨hE.rvlt i hi, ?_⟩
  by_cases hr : e i ∈ N ∧ M.rev (e i) ∈ N
  · have h1 := hE.rvin i hi hr.1 hr.2
    have h2 : e (rv i) ∈ N ∧ M.rev (e (rv i)) ∈ N := by
      rw [h1, M.rev_rev]; exact ⟨hr.2, hr.1⟩
    have h3 := hE.rvin _ (hE.rvlt i hi) h2.1 h2.2
    rw [h1, M.rev_rev] at h3
    exact hE.inj _ (hE.rvlt _ (hE.rvlt i hi)) _ hi h3
  · rw [hE.rvout i hi hr, hE.rvout i hi hr]

/-- **The components off `Y` of a subset `N`, through an enumeration of a superset.** -/
theorem mem_comp_iff_cgAdj_sub {B N : Finset D} {Hs : List (Finset V)} {Y : Finset V} {n : ℕ}
    {e : ℕ → D} {rv key : ℕ → ℕ} {yf : ℕ → Bool} (hY : HClosed Hs Y)
    (hE : CgEnumSub M B N Hs Y n e rv key yf) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hiN : e i ∈ N) :
    e j ∈ comp M N Hs Y (e i) ↔ ReflTransGen (cgAdj key yf n rv) i j := by
  have hrv := hE.rvOK
  constructor
  · intro h
    have key' : ∀ b, ReflTransGen (AStep M N Hs Y) (e i) b →
        ∃ jb < n, e jb = b ∧ b ∈ N ∧ ReflTransGen (cgAdj key yf n rv) i jb := by
      intro b hb
      induction hb with
      | refl => exact ⟨i, hi, rfl, hiN, .refl⟩
      | @tail b c _ hst ih =>
        obtain ⟨jb, hjb, rfl, hbN, hr⟩ := ih
        obtain ⟨jc, hjc, rfl⟩ := hE.surj c (hE.sub hst.1)
        refine ⟨jc, hjc, rfl, hst.1, hr.trans ?_⟩
        rcases hst.2 with h1 | ⟨h1, h2⟩
        · have hin : M.rev (e jb) ∈ N := h1 ▸ hst.1
          have := hE.rvin jb hjb hbN hin
          rw [← h1] at this
          have hj' := hE.inj _ (hE.rvlt jb hjb) _ hjc this
          exact .single ⟨hjb, Or.inl hj'.symm⟩
        · have hyb : yf jb = false := by
            by_contra hc
            rcases (hE.yf jb hjb).1 (by simpa using hc) with h | h
            · exact h2 h
            · exact h hbN
          have hyc : yf jc = false := by
            by_contra hc
            rcases (hE.yf jc hjc).1 (by simpa using hc) with h | h
            · exact h2 (hY _ h _ (hRel_symm h1))
            · exact h hst.1
          exact cgAdj_conn' hrv hjb hjc hyb hyc ((hE.key jb hjb jc hjc).2 h1)
    obtain ⟨jb, hjb, he, _, hr⟩ := key' _ (mem_comp.1 h).2
    rwa [hE.inj _ hjb _ hj he] at hr
  · intro h
    have key' : ∀ b, ReflTransGen (cgAdj key yf n rv) i b →
        b < n ∧ e b ∈ N ∧ ReflTransGen (AStep M N Hs Y) (e i) (e b) := by
      intro b hb
      induction hb with
      | refl => exact ⟨hi, hiN, .refl⟩
      | @tail b c _ hst ih =>
        obtain ⟨hb, hbN, hr⟩ := ih
        have hc := cgAdj_lt hrv hst
        rcases cgAdj_cases hst with h1 | h1 | ⟨h1, h2, h3⟩
        · by_cases hin : e b ∈ N ∧ M.rev (e b) ∈ N
          · have he := hE.rvin b hb hin.1 hin.2
            rw [← h1] at he
            exact ⟨hc, by rw [he]; exact hin.2, hr.tail ⟨by rw [he]; exact hin.2, Or.inl he⟩⟩
          · rw [h1, hE.rvout b hb hin]; exact ⟨hb, hbN, hr⟩
        · rw [h1]; exact ⟨hb, hbN, hr⟩
        · have hcN : e c ∈ N := by
            by_contra hc'
            have := (hE.yf c hc).2 (Or.inr hc')
            rw [h2] at this; exact Bool.false_ne_true this
          refine ⟨hc, hcN, hr.tail ⟨hcN, Or.inr ⟨(hE.key b hb c hc).1 h3.symm, fun hY' => ?_⟩⟩⟩
          have := (hE.yf b hb).2 (Or.inl hY')
          rw [h1] at this; exact Bool.false_ne_true this
    exact mem_comp.2 ⟨(key' j h).2.1, (key' j h).2.2⟩

/-! ### The classes as numbers -/

variable (M) in
/-- An enumeration `e` of the darts of `P`, the index `rv i` of the reverse dart, the class numbers
`key` of the tails, the flags `yt`, `yh` (tail, head in `Y`) and `nf` (in `Nf`). -/
structure ClsEnum (P Nf : Finset D) (Hs : List (Finset V)) (Y : Finset V) (n : ℕ) (e : ℕ → D)
    (rv key yt yh nf : ℕ → ℕ) : Prop where
  mem : ∀ i < n, e i ∈ P
  surj : ∀ d ∈ P, ∃ i < n, e i = d
  inj : ∀ i < n, ∀ j < n, e i = e j → i = j
  rvlt : ∀ i < n, rv i < n
  rvin : ∀ i < n, e (rv i) = M.rev (e i)
  key : ∀ i < n, ∀ j < n, (key i = key j ↔ HRel Hs (M.tail (e i)) (M.tail (e j)))
  yt : ∀ i < n, (0 < yt i ↔ M.tail (e i) ∈ Y)
  yh : ∀ i < n, (0 < yh i ↔ M.head (e i) ∈ Y)
  nf : ∀ i < n, (0 < nf i ↔ e i ∈ Nf)

/-- Both ends in `Y`. -/
def clsJ (yt yh : ℕ → ℕ) (i : ℕ) : Prop := 0 < yt i ∧ 0 < yh i

/-- In `Nf`, not both ends in `Y`. -/
def clsN (yt yh nf : ℕ → ℕ) (i : ℕ) : Prop := 0 < nf i ∧ ¬ clsJ yt yh i

instance (yt yh : ℕ → ℕ) (i : ℕ) : Decidable (clsJ yt yh i) := by unfold clsJ; infer_instance

instance (yt yh nf : ℕ → ℕ) (i : ℕ) : Decidable (clsN yt yh nf i) := by
  unfold clsN; infer_instance

/-- The reverse slot of the graph of the components. -/
def clsRv (rv yt yh nf : ℕ → ℕ) (i : ℕ) : ℕ :=
  if clsN yt yh nf i ∧ clsN yt yh nf (rv i) then rv i else i

/-- The flags of the graph of the components: tail in `Y`, or not in `Nf \ J`. -/
def clsYf (yt yh nf : ℕ → ℕ) (i : ℕ) : Bool := decide (0 < yt i ∨ ¬ clsN yt yh nf i)

/-- The darts of `P` with both ends in `Y`. -/
def clsJs (P : Finset D) (Y : Finset V) : Finset D :=
  P.filter fun d => M.tail d ∈ Y ∧ M.head d ∈ Y

section ClsEnum

variable {P Nf : Finset D} {Hs : List (Finset V)} {Y : Finset V} {n : ℕ} {e : ℕ → D}
  {rv key yt yh nf : ℕ → ℕ}

lemma ClsEnum.rv_rv (hE : ClsEnum M P Nf Hs Y n e rv key yt yh nf) {i : ℕ} (hi : i < n) :
    rv (rv i) = i := by
  have h := hE.rvin _ (hE.rvlt i hi)
  rw [hE.rvin i hi, M.rev_rev] at h
  exact hE.inj _ (hE.rvlt _ (hE.rvlt i hi)) _ hi h

lemma ClsEnum.memJ (hE : ClsEnum M P Nf Hs Y n e rv key yt yh nf) {i : ℕ} (hi : i < n) :
    e i ∈ clsJs (M := M) P Y ↔ clsJ yt yh i := by
  unfold clsJs clsJ
  rw [mem_filter, hE.yt i hi, hE.yh i hi]
  exact ⟨fun h => h.2, fun h => ⟨hE.mem i hi, h⟩⟩

lemma ClsEnum.memN (hE : ClsEnum M P Nf Hs Y n e rv key yt yh nf) {i : ℕ} (hi : i < n) :
    e i ∈ Nf \ clsJs (M := M) P Y ↔ clsN yt yh nf i := by
  unfold clsN
  rw [mem_sdiff, hE.memJ hi, hE.nf i hi]

lemma ClsEnum.clsJ_rv (hE : ClsEnum M P Nf Hs Y n e rv key yt yh nf) {i : ℕ} (hi : i < n) :
    clsJ yt yh (rv i) ↔ clsJ yt yh i := by
  unfold clsJ
  rw [hE.yt _ (hE.rvlt i hi), hE.yh _ (hE.rvlt i hi), hE.rvin i hi, M.tail_rev, M.head_rev,
    hE.yt i hi, hE.yh i hi]
  exact and_comm

/-- **The input of the graph of the components** (`N = Nf \ J` inside the enumeration of `P`). -/
lemma ClsEnum.sub (hE : ClsEnum M P Nf Hs Y n e rv key yt yh nf) (hNf : Nf ⊆ P) :
    CgEnumSub M P (Nf \ clsJs (M := M) P Y) Hs Y n e (clsRv rv yt yh nf) key
      (clsYf yt yh nf) := by
  refine ⟨hE.mem, hE.surj, hE.inj, fun d hd => hNf (mem_sdiff.1 hd).1, fun i hi => ?_,
    fun i hi h1 h2 => ?_, fun i hi h => ?_, hE.key, fun i hi => ?_⟩
  · unfold clsRv; split_ifs
    · exact hE.rvlt i hi
    · exact hi
  · have h2' : e (rv i) ∈ Nf \ clsJs (M := M) P Y := by rw [hE.rvin i hi]; exact h2
    unfold clsRv
    rw [cgIteT ⟨(hE.memN hi).1 h1, (hE.memN (hE.rvlt i hi)).1 h2'⟩, hE.rvin i hi]
  · unfold clsRv
    rw [cgIteF (fun h' => h ⟨(hE.memN hi).2 h'.1, by
      rw [← hE.rvin i hi]; exact (hE.memN (hE.rvlt i hi)).2 h'.2⟩)]
  · unfold clsYf
    rw [decide_eq_true_iff, hE.yt i hi, ← hE.memN hi]

end ClsEnum

/-- **The number of the class of the index `i`**: `3 min(i, rv i)` on the pairs (inside `Y`, or
off `Nf` when `K = 0`), `3 lab i + 1` on the darts of `Nf` (label of the component), `3 key i + 2`
on the other darts (the class number of the tail). -/
def clsIdF (K : ℕ) (rv key yt yh nf lab : ℕ → ℕ) (i : ℕ) : ℕ :=
  if clsJ yt yh i then 3 * min i (rv i) else if 0 < nf i then 3 * lab i + 1 else
    if K = 0 then 3 * min i (rv i) else 3 * key i + 2

lemma cls_min_eq {rv : ℕ → ℕ} {i j : ℕ} (hi : rv (rv i) = i) (hj : rv (rv j) = j)
    (h : min i (rv i) = min j (rv j)) : j = i ∨ j = rv i := by
  rcases min_choice i (rv i) with h1 | h1 <;> rcases min_choice j (rv j) with h2 | h2 <;>
    rw [h1, h2] at h
  · exact Or.inl h.symm
  · right; rw [h, hj]
  · exact Or.inr h.symm
  · left; rw [← hi, h, hj]

section ClsF

variable {P Nf : Finset D} {Hs : List (Finset V)} {K : ℕ} {ρ : HPath M} {d : D}

lemma clsF_of_J (h : d ∈ clsJs (M := M) P (newHole Hs ρ.mverts)) :
    clsF M P Nf Hs K ρ d = {d, M.rev d} := by
  unfold clsF; unfold clsJs at h; rw [cgIteT h]

lemma clsF_of_N (h : d ∉ clsJs (M := M) P (newHole Hs ρ.mverts)) (hd : d ∈ Nf) :
    clsF M P Nf Hs K ρ d = comp M (Nf \ clsJs (M := M) P (newHole Hs ρ.mverts)) Hs
      (newHole Hs ρ.mverts) d := by
  unfold clsF; unfold clsJs at h ⊢; rw [cgIteF h, cgIteT hd]

lemma clsF_of_K0 (h : d ∉ clsJs (M := M) P (newHole Hs ρ.mverts)) (hd : d ∉ Nf) (hK : K = 0) :
    clsF M P Nf Hs K ρ d = {d, M.rev d} := by
  unfold clsF; unfold clsJs at h; rw [cgIteF h, cgIteF hd, cgIteT hK]

open Classical in
lemma clsF_of_K (h : d ∉ clsJs (M := M) P (newHole Hs ρ.mverts)) (hd : d ∉ Nf) (hK : K ≠ 0) :
    clsF M P Nf Hs K ρ d = ((P \ Nf) \ clsJs (M := M) P (newHole Hs ρ.mverts)).filter
      fun e => HRel Hs (M.tail d) (M.tail e) := by
  unfold clsF; unfold clsJs at h ⊢; rw [cgIteF h, cgIteF hd, cgIteF hK]

open Classical in
/-- **The numbers of the classes**: with labels `lab` of the components off `Y` of `Nf \ J`
(equal exactly on a component) and the classes forming a partition of `P` (`IsCls`, the first
conclusion of `exists_cls'`), `clsIdF i = clsIdF j ↔ e j ∈ clsF M P Nf Hs K ρ (e i)`. -/
theorem clsIdF_iff {n : ℕ} {e : ℕ → D} {rv key yt yh nf lab : ℕ → ℕ}
    (hE : ClsEnum M P Nf Hs (newHole Hs ρ.mverts) n e rv key yt yh nf)
    (hlab : ∀ i < n, ∀ j < n, clsN yt yh nf i → clsN yt yh nf j →
      (lab i = lab j ↔ e j ∈ comp M (Nf \ clsJs (M := M) P (newHole Hs ρ.mverts)) Hs
        (newHole Hs ρ.mverts) (e i)))
    (hC : IsCls P (clsF M P Nf Hs K ρ)) {i j : ℕ} (hi : i < n) (hj : j < n) :
    clsIdF K rv key yt yh nf lab i = clsIdF K rv key yt yh nf lab j ↔
      e j ∈ clsF M P Nf Hs K ρ (e i) := by
  set Y := newHole Hs ρ.mverts with hY
  have rri := hE.rv_rv hi
  have rrj := hE.rv_rv hj
  have hJi := hE.memJ hi
  have hJj := hE.memJ hj
  have hNi := hE.nf i hi
  have hNj := hE.nf j hj
  -- the pair `{e i, rev (e i)}`
  have hpair : e j ∈ ({e i, M.rev (e i)} : Finset D) ↔ j = i ∨ j = rv i := by
    rw [mem_insert, mem_singleton, ← hE.rvin i hi]
    exact ⟨fun h => h.imp (hE.inj _ hj _ hi) (hE.inj _ hj _ (hE.rvlt i hi)),
      fun h => h.imp (fun h => by rw [h]) (fun h => by rw [h])⟩
  have hmin : ∀ j', j' = i ∨ j' = rv i → min j' (rv j') = min i (rv i) := by
    rintro j' (rfl | rfl)
    · rfl
    · rw [rri, min_comm]
  unfold clsIdF
  by_cases cJi : clsJ yt yh i
  · rw [clsF_of_J (hJi.2 cJi), hpair, cgIteT cJi]
    constructor
    · intro h
      by_cases cJj : clsJ yt yh j
      · rw [cgIteT cJj] at h; exact cls_min_eq rri rrj (by omega)
      · rw [cgIteF cJj] at h
        split_ifs at h with h1 h2
        · omega
        · exact cls_min_eq rri rrj (by omega)
        · omega
    · intro h
      have cJj : clsJ yt yh j := by
        rcases h with rfl | rfl
        · exact cJi
        · exact (hE.clsJ_rv hi).2 cJi
      rw [cgIteT cJj, hmin j h]
  · rw [cgIteF cJi]
    by_cases cNi : 0 < nf i
    · have hiN : e i ∈ Nf := hNi.1 cNi
      have hiJ : e i ∉ clsJs (M := M) P Y := fun h => cJi (hJi.1 h)
      rw [clsF_of_N hiJ hiN, cgIteT cNi]
      constructor
      · intro h
        by_cases cJj : clsJ yt yh j
        · rw [cgIteT cJj] at h; omega
        · rw [cgIteF cJj] at h
          by_cases cNj : 0 < nf j
          · rw [cgIteT cNj] at h
            exact (hlab i hi j hj ⟨cNi, cJi⟩ ⟨cNj, cJj⟩).1 (by omega)
          · rw [cgIteF cNj] at h; split_ifs at h <;> omega
      · intro h
        have hjN := (mem_comp.1 h).1
        have cNj : clsN yt yh nf j := (hE.memN hj).1 hjN
        rw [cgIteF cNj.2, cgIteT cNj.1, (hlab i hi j hj ⟨cNi, cJi⟩ cNj).2 h]
    · rw [cgIteF cNi]
      have hiJ : e i ∉ clsJs (M := M) P Y := fun h => cJi (hJi.1 h)
      have hiN : e i ∉ Nf := fun h => cNi (hNi.2 h)
      by_cases hK : K = 0
      · rw [clsF_of_K0 hiJ hiN hK, hpair, cgIteT hK]
        constructor
        · intro h
          by_cases cJj : clsJ yt yh j
          · rw [cgIteT cJj] at h; exact cls_min_eq rri rrj (by omega)
          · rw [cgIteF cJj] at h
            by_cases cNj : 0 < nf j
            · rw [cgIteT cNj] at h; omega
            · rw [cgIteF cNj, cgIteT hK] at h; exact cls_min_eq rri rrj (by omega)
        · intro h
          have cJj : ¬ clsJ yt yh j := by
            rcases h with rfl | rfl
            · exact cJi
            · exact fun h' => cJi ((hE.clsJ_rv hi).1 h')
          have cNj : ¬ 0 < nf j := by
            intro hn
            -- the class of `e j` is a component inside `Nf`, it contains `e i ∉ Nf`
            have hjN : e j ∈ Nf := hNj.1 hn
            have hjJ : e j ∉ clsJs (M := M) P Y := fun h' => cJj (hJj.1 h')
            have hmem : e j ∈ clsF M P Nf Hs K ρ (e i) := by
              rw [clsF_of_K0 hiJ hiN hK, hpair]; exact h
            have heq := hC.eq _ (hE.mem i hi) _ hmem
            have hself := hC.self _ (hE.mem i hi)
            rw [← heq, clsF_of_N hjJ hjN] at hself
            exact hiN (mem_sdiff.1 (mem_comp.1 hself).1).1
          rw [cgIteF cJj, cgIteF cNj, cgIteT hK, hmin j h]
      · rw [clsF_of_K hiJ hiN hK, cgIteF hK]
        constructor
        · intro h
          by_cases cJj : clsJ yt yh j
          · rw [cgIteT cJj] at h; omega
          · rw [cgIteF cJj] at h
            by_cases cNj : 0 < nf j
            · rw [cgIteT cNj] at h; omega
            · rw [cgIteF cNj, cgIteF hK] at h
              refine mem_filter.2 ⟨mem_sdiff.2 ⟨mem_sdiff.2 ⟨hE.mem j hj,
                fun h' => cNj (hNj.2 h')⟩, fun h' => cJj (hJj.1 h')⟩, ?_⟩
              exact (hE.key i hi j hj).1 (by omega)
        · intro h
          obtain ⟨h1, h2⟩ := mem_filter.1 h
          obtain ⟨h3, h4⟩ := mem_sdiff.1 h1
          obtain ⟨_, h6⟩ := mem_sdiff.1 h3
          have cJj : ¬ clsJ yt yh j := fun h' => h4 (hJj.2 h')
          have cNj : ¬ 0 < nf j := fun h' => h6 (hNj.1 h')
          rw [cgIteF cJj, cgIteF cNj, cgIteF hK, (hE.key i hi j hj).2 h2]

end ClsF

end BKMNW

end PlanarFlow
