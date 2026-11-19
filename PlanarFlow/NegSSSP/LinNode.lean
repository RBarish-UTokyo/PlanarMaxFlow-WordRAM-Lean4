module

public import PlanarFlow.NegSSSP.LinGlue2
public import PlanarFlow.NegSSSP.BFExec

/-!
# The plain encoding of a node, and the glue programs on it

A node of the recursion for negative lengths is a piece `P₀ ∪ P₁` of a map `N` split into two
disjoint parts. Its **plain encoding** (`NodeEnc`): the darts of `P₀ ∪ P₁` enumerated as
`e 0, …, e (m - 1)`, the vertices of the piece numbered by `ν` below `w ≤ 2m` (with inverse `ι`
on the vertices of the piece); the arrays of tails `ν (tail (e d))`, heads `ν (head (e d))`,
sides (`0` for `P₀`, `1` for `P₁`), lengths `ℓ (e d)` and potentials `δᵢ (ι v)`.

* `inSide_enc`: the marks of `bdryProg` are the vertices of the parts.
* `bdry_enum`: the list of `bdryProg`, read through `ι`, enumerates `bdry N P₀ P₁` (`IsEnum`).
* `bdryProg_node`, `redProg_node`: the runs on the encoding of a node compute the boundary with
  an enumeration, and the reduced lengths `redLen N ℓ δᵢ` of the darts.
* `permProg_node`: from the numbers of two enumerations `β₀`, `β₁` of the boundary, the order
  `permOf b β₀ β₁` of `bfStartP`.
* `minProg_node`: from the outcomes of the two runs of Dijkstra at the vertex numbers, the values
  `(omin …).getD 0` of `NegSSSP.step`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine

attribute [local instance] Classical.propDecidable

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The plain encoding of a node**: an enumeration `e` of the darts, a numbering `ν` of the
vertices below `w` with inverse `ι`. -/
structure NodeEnc (N : CombMap D V F) (P₀ P₁ : Finset D) (m w : ℕ) (e : ℕ → D) (ν : V → ℕ)
    (ι : ℕ → V) : Prop where
  enum : IsEnum m e (P₀ ∪ P₁)
  disj : Disjoint P₀ P₁
  lt : ∀ x ∈ verts N (P₀ ∪ P₁), ν x < w
  inv : ∀ x ∈ verts N (P₀ ∪ P₁), ι (ν x) = x
  w2 : w ≤ 2 * m

/-- The arrays of the encoding: tails, heads, sides. -/
def encT (N : CombMap D V F) (e : ℕ → D) (ν : V → ℕ) (d : ℕ) : ℕ := ν (N.tail (e d))
/-- The heads. -/
def encH (N : CombMap D V F) (e : ℕ → D) (ν : V → ℕ) (d : ℕ) : ℕ := ν (N.head (e d))
/-- The sides. -/
noncomputable def encS (P₀ : Finset D) (e : ℕ → D) (d : ℕ) : ℕ := if e d ∈ P₀ then 0 else 1

/-- The part of side `s`. -/
def partOf (P₀ P₁ : Finset D) (s : ℕ) : Finset D := if s = 0 then P₀ else P₁

lemma mem_verts {P : Finset D} {x : V} : x ∈ verts N P ↔ ∃ d ∈ P, N.tail d = x ∨ N.head d = x := by
  unfold verts
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨d, hd, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨d, hd, Or.inl h⟩
    · exact ⟨d, hd, Or.inr h⟩
  · rintro ⟨d, hd, h | h⟩
    · exact Or.inl ⟨d, hd, h⟩
    · exact Or.inr ⟨d, hd, h⟩

variable {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}

/-- **The marks are the vertices of the parts.** -/
theorem inSide_enc (h : NodeEnc N P₀ P₁ m w e ν ι) {s : ℕ} (hs : s ≤ 1) {x : V}
    (hx : x ∈ verts N (P₀ ∪ P₁)) :
    InSide (encT N e ν) (encH N e ν) (encS P₀ e) m s (ν x) ↔ x ∈ verts N (partOf P₀ P₁ s) := by
  have hT : ∀ d < m, N.tail (e d) ∈ verts N (P₀ ∪ P₁) := fun d hd =>
    mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inl rfl⟩
  have hH : ∀ d < m, N.head (e d) ∈ verts N (P₀ ∪ P₁) := fun d hd =>
    mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inr rfl⟩
  have hinj : ∀ y ∈ verts N (P₀ ∪ P₁), ν y = ν x → y = x := fun y hy hyx => by
    rw [← h.inv y hy, ← h.inv x hx, hyx]
  have hside : ∀ d < m, (encS P₀ e d = s ↔ e d ∈ partOf P₀ P₁ s) := fun d hd => by
    have hm := h.enum.mem d hd
    unfold encS partOf
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · by_cases h0 : e d ∈ P₀ <;> simp [h0]
    · by_cases h0 : e d ∈ P₀
      · simp only [h0, ↓reduceIte, one_ne_zero]
        exact ⟨fun h' => absurd h' (by omega),
          fun h1 => absurd h1 (Finset.disjoint_left.1 h.disj h0)⟩
      · simp only [h0, ↓reduceIte, one_ne_zero, true_iff]
        rcases mem_union.1 hm with h' | h'
        · exact absurd h' h0
        · exact h'
  constructor
  · rintro ⟨d, hd, hS, hTH⟩
    refine mem_verts.2 ⟨e d, (hside d hd).1 hS, ?_⟩
    rcases hTH with h1 | h1
    · exact Or.inl (hinj _ (hT d hd) h1)
    · exact Or.inr (hinj _ (hH d hd) h1)
  · intro hxs
    obtain ⟨y, hy, hyx⟩ := mem_verts.1 hxs
    have hyP : y ∈ P₀ ∪ P₁ := by
      unfold partOf at hy; split_ifs at hy
      · exact mem_union_left _ hy
      · exact mem_union_right _ hy
    obtain ⟨d, hd, rfl⟩ := h.enum.surj y hyP
    refine ⟨d, hd, (hside d hd).2 hy, ?_⟩
    rcases hyx with h1 | h1
    · exact Or.inl (by unfold encT; rw [h1])
    · exact Or.inr (by unfold encH; rw [h1])

/-- An end of an encoded dart is the number of a vertex of the piece. -/
lemma inSide_num (h : NodeEnc N P₀ P₁ m w e ν ι) {s v : ℕ}
    (hv : InSide (encT N e ν) (encH N e ν) (encS P₀ e) m s v) :
    ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v := by
  obtain ⟨d, hd, -, h1 | h1⟩ := hv
  · exact ⟨_, mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inl rfl⟩, h1⟩
  · exact ⟨_, mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inr rfl⟩, h1⟩

lemma bdry_sub_verts {x : V} (hx : x ∈ bdry N P₀ P₁) : x ∈ verts N (P₀ ∪ P₁) := by
  obtain ⟨d, hd, h⟩ := mem_verts.1 (mem_inter.1 hx).1
  exact mem_verts.2 ⟨d, mem_union_left _ hd, h⟩

/-- `ν x` is a boundary vertex of the encoding exactly when `x ∈ bdry N P₀ P₁`. -/
lemma isBd_enc (h : NodeEnc N P₀ P₁ m w e ν ι) {x : V} (hx : x ∈ verts N (P₀ ∪ P₁)) :
    IsBd (encT N e ν) (encH N e ν) (encS P₀ e) m (ν x) ↔ x ∈ bdry N P₀ P₁ := by
  unfold IsBd bdry
  rw [inSide_enc h (by omega) hx, inSide_enc h le_rfl hx, mem_inter]
  simp [partOf]

/-- **The list of `bdryProg`, read through `ι`, enumerates the boundary.** -/
theorem bdry_enum (h : NodeEnc N P₀ P₁ m w e ν ι) :
    IsEnum (bList (encT N e ν) (encH N e ν) (encS P₀ e) m w).length
      (fun j => ι ((bList (encT N e ν) (encH N e ν) (encS P₀ e) m w).getD j 0))
      (bdry N P₀ P₁) := by
  set L := bList (encT N e ν) (encH N e ν) (encS P₀ e) m w
  have hmem : ∀ v, v ∈ L ↔ v < w ∧ IsBd (encT N e ν) (encH N e ν) (encS P₀ e) m v := by
    intro v; simp [L, bList, IsBd]
  have hnd : L.Nodup := (List.nodup_range).filter _
  have hget : ∀ j < L.length, L.getD j 0 ∈ L := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hnum : ∀ j < L.length, ∃ x ∈ bdry N P₀ P₁, ν x = L.getD j 0 := fun j hj => by
    obtain ⟨-, hb⟩ := (hmem _).1 (hget j hj)
    obtain ⟨x, hx, hxv⟩ := inSide_num h hb.1
    exact ⟨x, (isBd_enc h hx).1 (hxv ▸ hb), hxv⟩
  refine ⟨fun j hj => ?_, fun x hx => ?_, fun j hj j' hj' hjj => ?_⟩
  · obtain ⟨x, hx, hxv⟩ := hnum j hj
    rw [← hxv, h.inv x (bdry_sub_verts hx)]; exact hx
  · have hxv := bdry_sub_verts hx
    have hL : ν x ∈ L := (hmem _).2 ⟨h.lt x hxv, (isBd_enc h hxv).2 hx⟩
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hL
    refine ⟨j, hj, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
      hjx, h.inv x hxv]
  · obtain ⟨x, hx, hxv⟩ := hnum j hj
    obtain ⟨x', hx', hxv'⟩ := hnum j' hj'

    rw [← hxv, ← hxv', h.inv x (bdry_sub_verts hx), h.inv x' (bdry_sub_verts hx')] at hjj
    subst hjj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hxv
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] at hxv'
    exact (hnd.getElem_inj_iff).1 (hxv.symm.trans hxv')

/-- The ends and sides of the encoded darts are in range. -/
lemma enc_ends (h : NodeEnc N P₀ P₁ m w e ν ι) :
    ∀ d < m, encT N e ν d < w ∧ encH N e ν d < w ∧ encS P₀ e d ≤ 1 := fun d hd =>
  ⟨h.lt _ (mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inl rfl⟩),
    h.lt _ (mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inr rfl⟩), by unfold encS; split_ifs <;> omega⟩

variable {W : ℕ} {I : Input}

/-- **The boundary of a node on the machine.** On the plain encoding of a node, `bdryProg`
leaves `b = |bdry N P₀ P₁|` in `r217` and at `Bb + j` (`j < b`) the numbers of an enumeration
`β` of `bdry N P₀ P₁` (`β j = ι (nmem (Bb + j))`), within `61 m + 12` steps. -/
theorem bdryProg_node (h : NodeEnc N P₀ P₁ m w e ν ι) {Tb Hb Sb Mb Bb : ℕ}
    (hL : BdLay m w Tb Hb Sb Mb Bb W (encT N e ν) (encH N e ν) (encS P₀ e)) (c : Config)
    (hc : WordsBounded W c) (hI : BdIn m w Tb Hb Sb Mb Bb (encT N e ν) (encH N e ν) (encS P₀ e) c) :
    ∃ c' k b, ∃ β : ℕ → V, Exec I W bdryProg c c' k ∧ k ≤ 61 * m + 12 ∧ c'.nreg 217 = b ∧
      IsEnum b β (bdry N P₀ P₁) ∧ (∀ j < b, ι (c'.nmem (Bb + j)) = β j) ∧
      (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → (a < Bb ∨ Bb + w ≤ a) → c'.nmem a = c.nmem a) ∧
      BFr c c' := by
  obtain ⟨c', k, hex, hk, h217, hl, hm, hf⟩ := bdryProg_exec (P := I) hL c hc hI
  have := h.w2
  exact ⟨c', k, _, _, hex, by omega, h217, bdry_enum h, fun j hj => by rw [hl j hj], hm, hf⟩

/-- **The reduced lengths of a part on the machine.** On the plain encoding of a node with the
lengths `ℓ (e d)` at `Lb + d` and the potentials `δ (ι v)` at `δb + v` (real memory), `redProg`
writes `redLen N ℓ δ (e d)` at `Rb + d` for every `d < m`, within `17 m + 3` steps. -/
theorem redProg_node (h : NodeEnc N P₀ P₁ m w e ν ι) {ℓ : D → ℤ} {δ : V → ℤ}
    {Tb Hb Lb δb Rb : ℕ} (hL : RedLay m w Tb Hb Lb δb Rb W (encT N e ν) (encH N e ν))
    (c : Config) (hc : WordsBounded W c)
    (hI : RedIn m w Tb Hb Lb δb Rb (encT N e ν) (encH N e ν) (fun d => (ℓ (e d) : ℝ))
      (fun v => (δ (ι v) : ℝ)) c) :
    ∃ c' k, Exec I W redProg c c' k ∧ k ≤ 17 * m + 3 ∧
      (∀ d < m, c'.rmem (Rb + d) = (redLen N ℓ δ (e d) : ℝ)) ∧
      (∀ a, (a < Rb ∨ Rb + m ≤ a) → c'.rmem a = c.rmem a) ∧ c'.nmem = c.nmem ∧
      (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, hex, hk, hR, hrm, hnm, hn, -, -⟩ := redProg_exec (P := I) hL c hc hI
  refine ⟨c', k, hex, hk, fun d hd => ?_, hrm, hnm, hn⟩
  rw [hR d hd]
  have hm := h.enum.mem d hd
  unfold encT encH redLen
  rw [h.inv _ (mem_verts.2 ⟨e d, hm, Or.inl rfl⟩), h.inv _ (mem_verts.2 ⟨e d, hm, Or.inr rfl⟩)]
  push_cast; ring

/-- The boundary has at most `w` vertices. -/
lemma card_bdry_le (h : NodeEnc N P₀ P₁ m w e ν ι) : (bdry N P₀ P₁).card ≤ w := by
  have := card_le_card_of_injOn ν (t := range w) (fun x hx => by
      simp only [coe_range, Set.mem_Iio]; exact h.lt x (bdry_sub_verts hx))
    (fun x hx y hy hxy => by
      rw [← h.inv x (bdry_sub_verts hx), ← h.inv y (bdry_sub_verts hy)]; exact congrArg ι hxy)
  simpa using this

/-- **The order `π` of a node on the machine.** For two enumerations `β₀`, `β₁` of the boundary
(their vertex numbers `ν (βᵢ i)` at `B0`, `B1`), `permProg` writes `permOf b β₀ β₁ i` at
`πb + i` for every `i < b`, within `16 b + 6 ≤ 32 m + 6` steps. -/
theorem permProg_node (h : NodeEnc N P₀ P₁ m w e ν ι) {b : ℕ} {β₀ β₁ : ℕ → V}
    (e₀ : IsEnum b β₀ (bdry N P₀ P₁)) (e₁ : IsEnum b β₁ (bdry N P₀ P₁)) {B0 B1 Ib πb : ℕ}
    (hL : PermLay b w B0 B1 Ib πb W (fun i => ν (β₀ i)) (fun i => ν (β₁ i))) (c : Config)
    (hc : WordsBounded W c) (hI : PermIn b B0 B1 Ib πb (fun i => ν (β₀ i)) (fun i => ν (β₁ i)) c) :
    ∃ c' k, Exec I W permProg c c' k ∧ k ≤ 32 * m + 6 ∧
      (∀ i < b, c'.nmem (πb + i) = permOf b β₀ β₁ i) ∧
      (∀ a, (a < Ib ∨ Ib + w ≤ a) → (a < πb ∨ πb + b ≤ a) → c'.nmem a = c.nmem a) ∧
      PFr c c' := by
  obtain ⟨c', k, hex, hk, hπ, hm, hf⟩ := permProg_exec (P := I) hL c hc hI
  have hb : b ≤ w := e₀.card ▸ card_bdry_le h
  have := h.w2
  refine ⟨c', k, hex, by omega, fun i hi => ?_, hm, hf⟩
  obtain ⟨h1, h2⟩ := hπ i hi
  obtain ⟨p1, p2⟩ := permOf_spec e₀ e₁ hi
  have hv : β₀ (c'.nmem (πb + i)) = β₁ i := by
    have a := bdry_sub_verts (e₀.mem _ h1)
    have b' := bdry_sub_verts (e₁.mem _ hi)
    rw [← h.inv _ a, ← h.inv _ b']; exact congrArg ι h2
  exact e₀.inj _ h1 _ p1 (hv.trans p2.symm)

/-- **The minima of a node on the machine.** With the outcomes `D₀ (some (ι v))`,
`D₁ (some (ι v))` of the two runs of Dijkstra at the vertex numbers `v < w` (flags and values),
`minProg` writes the value of `NegSSSP.step` at `x`, `(omin (D₀ (some x)) (D₁ (some x))).getD 0`,
at `Ob + ν x` for every vertex `x` of the piece, within `21 w + 3 ≤ 42 m + 3` steps. -/
theorem minProg_node (h : NodeEnc N P₀ P₁ m w e ν ι) {D₀ D₁ : Option V → Option ℤ}
    {F0 V0 F1 V1 Ob : ℕ} (hL : MinLay w F0 V0 F1 V1 Ob W) (c : Config) (hc : WordsBounded W c)
    (hI : MinIn w F0 V0 F1 V1 Ob (fun v => D₀ (some (ι v))) (fun v => D₁ (some (ι v))) c) :
    ∃ c' k, Exec I W minProg c c' k ∧ k ≤ 42 * m + 3 ∧
      (∀ x ∈ verts N (P₀ ∪ P₁),
        c'.rmem (Ob + ν x) = ((omin (D₀ (some x)) (D₁ (some x))).getD 0 : ℤ)) ∧
      (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.rmem a = c.rmem a) ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, hex, hk, hv, hm, hn, -, -⟩ := minProg_exec (P := I) hL c hc hI
  have := h.w2
  refine ⟨c', k, hex, by omega, fun x hx => ?_, hm, hn⟩
  rw [hv _ (h.lt x hx), h.inv x hx]

end NegSSSP

end PlanarFlow
