module

public import PlanarFlow.BKMNW.SplitRotHead
public import Mathlib.Combinatorics.Colex

/-!
# The choices of the split chain made by an enumeration of the darts

The split functions `spSR`/`spHR` take choice functions `pc : PcChoice` and
`sc : … → ScChoice` meeting local specifications. A program makes these choices by the
positions of the darts in memory: "the first dart (by position) with the property". This file
defines such choices from an enumeration `e : ℕ → D` of the darts (`e` bijective from `[0, n)`)
and proves they meet the specifications, so only Miller's separator is left as a parameter.

* `firstE e n X d₀` (the first `e i ∈ X`, `i < n`, or `d₀`), `firstE_mem`; `findE`
  (`Option` version), `findE_some`, `findE_none`;
* `idxE`, `codeE` (`E ↦ Σ_{i<n, e i ∈ E} 2^i`), `decodeE`, `decodeE_codeE`, **`ordE e n X`**
  (the sets of `X` sorted by their codes), `ordE_ok`;
* **`pcChoiceE M Q e n d₀`**, **`pcChoiceE_ok`**: meets `PcChoice.OK M Q P Hs` for all `P`, `Hs`;
* **`scChoiceE M sepF e n Hs A W`** (the first hole of the list that is a cut vertex, the first
  dart with a heavy component, the first dart leaving the hole), **`scChoiceE_ok`**: meets
  `ScChoice.OK Hs A W` when `sepF` meets the separator specification;
* **`maxflow_plane_cost_decE`**: the headline bound of `maxflow_plane_cost_decDD'` with these
  choices: the decomposition is a function of the map, an enumeration of the darts, a dart and a
  separator function `sepF` (meeting its specification) only.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Relation

variable {D : Type*} [DecidableEq D]

/-! ### The first dart with a property -/

/-- The first index `i < n` with `e i ∈ X`, as a dart. -/
def findE (e : ℕ → D) (n : ℕ) (X : Finset D) : Option D :=
  ((List.range n).find? fun i => decide (e i ∈ X)).map e

/-- The first dart of `X` by its index, or `d₀`. -/
def firstE (e : ℕ → D) (n : ℕ) (X : Finset D) (d₀ : D) : D := (findE e n X).getD d₀

lemma findE_some {e : ℕ → D} {n : ℕ} {X : Finset D} {d : D} (h : findE e n X = some d) :
    d ∈ X := by
  unfold findE at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
  simpa using List.find?_some hi

lemma findE_none {e : ℕ → D} {n : ℕ} {X : Finset D} (h : findE e n X = none) :
    ∀ i < n, e i ∉ X := by
  unfold findE at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro i hi hX
  exact absurd (by simpa using hX) (h i (List.mem_range.2 hi))

lemma findE_isSome {e : ℕ → D} {n : ℕ} {X : Finset D} {i : ℕ} (hi : i < n) (hX : e i ∈ X) :
    ∃ d, findE e n X = some d := by
  cases h : findE e n X with
  | none => exact absurd hX (findE_none h i hi)
  | some d => exact ⟨d, rfl⟩

lemma firstE_mem {e : ℕ → D} {n : ℕ} {X : Finset D} (d₀ : D) {i : ℕ} (hi : i < n)
    (hX : e i ∈ X) : firstE e n X d₀ ∈ X := by
  obtain ⟨d, hd⟩ := findE_isSome hi hX
  unfold firstE; rw [hd]; exact findE_some hd

/-! ### Listing a set of sets -/

/-- The indices of the darts of `E`. -/
def idxE (e : ℕ → D) (n : ℕ) (E : Finset D) : Finset ℕ := (range n).filter fun i => e i ∈ E

/-- The code of a set of darts: `Σ_{i<n, e i ∈ E} 2^i`. -/
def codeE (e : ℕ → D) (n : ℕ) (E : Finset D) : ℕ := ∑ i ∈ idxE e n E, 2 ^ i

/-- The set of darts of a code. -/
def decodeE (e : ℕ → D) (n : ℕ) (k : ℕ) : Finset D :=
  ((k.bitIndices.toFinset).filter (· < n)).image e

lemma decodeE_codeE {e : ℕ → D} {n : ℕ} (hsurj : ∀ d, ∃ i < n, e i = d) (E : Finset D) :
    decodeE e n (codeE e n E) = E := by
  unfold decodeE codeE
  rw [Finset.toFinset_bitIndices_sum_two_pow]
  ext d
  simp only [idxE, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨⟨_, h⟩, _⟩, rfl⟩; exact h
  · intro hd
    obtain ⟨i, hi, rfl⟩ := hsurj d
    exact ⟨i, ⟨⟨hi, hd⟩, hi⟩, rfl⟩

/-- **A listing of a set of sets of darts**: sorted by the codes. -/
def ordE (e : ℕ → D) (n : ℕ) (X : Finset (Finset D)) : List (Finset D) :=
  ((X.image (codeE e n)).sort (· ≤ ·)).map (decodeE e n)

lemma ordE_ok {e : ℕ → D} {n : ℕ} (hsurj : ∀ d, ∃ i < n, e i = d) (X : Finset (Finset D)) :
    (ordE e n X).Nodup ∧ (ordE e n X).toFinset = X := by
  unfold ordE
  refine ⟨?_, ?_⟩
  · refine List.Nodup.map_on (fun a ha b hb hab => ?_) (sort_nodup _ _)
    rw [mem_sort] at ha hb
    obtain ⟨E, _, rfl⟩ := mem_image.1 ha
    obtain ⟨E', _, rfl⟩ := mem_image.1 hb
    rw [decodeE_codeE hsurj, decodeE_codeE hsurj] at hab
    rw [hab]
  · ext E
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [mem_sort] at hk
      obtain ⟨E', hE', rfl⟩ := mem_image.1 hk
      rw [decodeE_codeE hsurj]; exact hE'
    · intro hE
      exact ⟨codeE e n E, (mem_sort _).2 (mem_image_of_mem _ hE), decodeE_codeE hsurj E⟩

/-! ### The choices of the certificate of a whole piece -/

section Pc

variable {V F : Type*} [Fintype D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (M : CombMap D V F)

open Classical in
/-- **The choices of `pcertD` by the enumeration `e`**: every choice is the first dart (by
index) with the required property. -/
noncomputable def pcChoiceE (Q : Finset V) (e : ℕ → D) (n : ℕ) (d₀ : D) : PcChoice D V where
  rep X := firstE e n X d₀
  ancD P Hs d := firstE e n ((pdarts M (core M Q P) Hs).filter
    fun b => HRel Hs (M.tail b) (avQ M Q d)) d₀
  anch P Hs H := firstE e n ((pdarts M (core M Q P) Hs).filter fun b => M.tail b ∈ H) d₀
  ord := ordE e n
  pick X := firstE e n X d₀

variable {M}

open Classical in
/-- **The choices by the enumeration meet the specification.** -/
theorem pcChoiceE_ok {e : ℕ → D} {n : ℕ} (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : D)
    (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) :
    (pcChoiceE M Q e n d₀).OK M Q P Hs := by
  refine ⟨fun d => ?_, fun d ⟨b, hb, hr⟩ => ?_, fun H ⟨b, hb, hr⟩ => ?_, ordE_ok hsurj,
    fun X ⟨d, hd⟩ => ?_⟩
  · obtain ⟨i, hi, he⟩ := hsurj d
    have := firstE_mem (e := e) d₀ hi (X := {d, M.rev d}) (by rw [he]; simp)
    simp only [mem_insert, mem_singleton] at this
    exact this
  · obtain ⟨i, hi, rfl⟩ := hsurj b
    have := firstE_mem (e := e) d₀ hi (X := (pdarts M (core M Q P) Hs).filter
      fun b => HRel Hs (M.tail b) (avQ M Q d)) (mem_filter.2 ⟨hb, hr⟩)
    exact mem_filter.1 this
  · obtain ⟨i, hi, rfl⟩ := hsurj b
    have := firstE_mem (e := e) d₀ hi (X := (pdarts M (core M Q P) Hs).filter fun b => M.tail b ∈ H)
      (mem_filter.2 ⟨hb, hr⟩)
    exact mem_filter.1 this
  · obtain ⟨i, hi, rfl⟩ := hsurj d
    exact firstE_mem d₀ hi hd

end Pc

/-! ### The choices of the certificate of a piece map -/

section Sc

open Function Equiv Orbit CombMap PlanarSeparator

variable {V F : Type*} [Fintype D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (M : CombMap D V F)

/-- The type of a separator function (the `sep` field of `ScChoice`). -/
abbrev SepFn := ∀ (N : Finset D) (τ : Perm D) (hσ : Stable τ N) (hB : Stable (revPerm M) N)
    (_ex : D → ℕ), Option ((psep M hσ hB).stellar.SCycle × Finset (psep M hσ hB).stellar.Face)

open Classical PlanarSeparator.Map in
/-- **The specification of a separator function** (the `sep` field of `ScChoice.OK`). -/
def SepFnOK (sepF : SepFn M) (Hs : List (Finset V)) : Prop :=
  ∀ (N : Finset D) (τ : Perm D) (hN : PMap M N Hs τ) (ex : D → ℕ), N.Nonempty →
    NoCut M N Hs → ∃ C Z, sepF N τ hN.stable hN.rev ex = some (C, Z) ∧
      C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert τ N) +
        Fintype.card (psep M hN.stable hN.rev).Face) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      3 * ∑ y ∈ sideIn C Z, coreWt hN.stable hN.rev (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2 ∧
      3 * ∑ y ∈ sideOut C Z, coreWt hN.stable hN.rev (fun _ => 1) (coreExW τ N ex) y ≤
        2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2

open Classical in
/-- **The choices of `scertD` by the enumeration `e`**: the separator `sepF`, the first hole of
the list that is a cut vertex, the first dart (by index) with a heavy component, the first dart
(by index) leaving the hole. -/
noncomputable def scChoiceE (sepF : SepFn M) (e : ℕ → D) (n : ℕ) (Hs : List (Finset V))
    (A W : ℕ) : ScChoice M where
  sep := sepF
  hole N := Hs.find? fun g => decide (∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧
    ¬ ReflTransGen (AStep M N Hs g) x y)
  heavy N g ex := findE e n (N.filter fun z => W < A + ∑ d ∈ comp M N Hs g z, (1 + ex d))
  anchor S g := findE e n (S.filter fun a => M.tail a ∈ g)

variable {M}

open Classical in
/-- **The choices by the enumeration meet the specification** (given the separator's). -/
theorem scChoiceE_ok {sepF : SepFn M} {e : ℕ → D} {n : ℕ} (hsurj : ∀ d, ∃ i < n, e i = d)
    {Hs : List (Finset V)} (hsep : SepFnOK M sepF Hs) (A W : ℕ) :
    (scChoiceE M sepF e n Hs A W).OK Hs A W := by
  refine ⟨hsep, fun N hN => ?_, fun N g ex z h => ?_, fun N g ex h z hz => ?_,
    fun S g ⟨a, ha, hg⟩ => ?_⟩
  · unfold NoCut at hN
    push Not at hN
    obtain ⟨g, hg, x, hx, y, hy, h1, h2, h3⟩ := hN
    have hs : (Hs.find? fun g => decide (∃ x ∈ N, ∃ y ∈ N, M.tail x ∉ g ∧ M.tail y ∉ g ∧
        ¬ ReflTransGen (AStep M N Hs g) x y)).isSome := by
      rw [List.find?_isSome]
      exact ⟨g, hg, by simpa using ⟨x, hx, y, hy, h1, h2, h3⟩⟩
    obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨g', hg', List.mem_of_find?_eq_some hg', ?_⟩
    simpa using List.find?_some hg'
  · exact mem_filter.1 (findE_some h)
  · obtain ⟨i, hi, rfl⟩ := hsurj z
    have := findE_none h i hi
    rw [mem_filter] at this
    push Not at this
    exact this hz
  · obtain ⟨i, hi, rfl⟩ := hsurj a
    obtain ⟨d, hd⟩ := findE_isSome (X := S.filter fun a => M.tail a ∈ g) hi (mem_filter.2 ⟨ha, hg⟩)
    exact ⟨d, hd, (mem_filter.1 (findE_some hd)).1, (mem_filter.1 (findE_some hd)).2⟩

end Sc

/-! ### The headline bound with these choices -/

section Head

open Function Equiv Orbit CombMap

universe w

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Maximum flow in plane graphs in `O(n log³ n)` with the choices made by an enumeration of
the darts**: `maxflow_plane_cost_decDD'` for `pc = pcChoiceE …` and `sc Hs A W = scChoiceE … sepF
e n Hs A W`: every choice of the decomposition is "the first dart (by index) with the property"
for an enumeration `e` of the darts of `lpreMap M` (bijective on `[0, n)`), except Miller's
separator `sepF`, which is any function meeting its specification `SepFnOK` (as the machine's
separator does by `coreSep_of_sepOK`). Constants as in `maxflow_plane_cost`. -/
theorem maxflow_plane_cost_decE (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    (sepF : SepFn (lpreMap M)) (hsep : ∀ Hs, SepFnOK (lpreMap M) sepF Hs)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) sepF e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  intro pc sc τ
  exact maxflow_plane_cost_decDD' hM hrot hface hu hST pc (fun P Hs => pcChoiceE_ok hsurj d₀ _ P Hs)
    sc (fun Hs A W => scChoiceE_ok hsurj (hsep Hs) A W) hc

end Head

end BKMNW

end PlanarFlow
