module

public import PlanarFlow.NegSSSP.DriverRun
public import PlanarFlow.NegSSSP.CompProg
public import PlanarFlow.NegSSSP.SplitRunA

/-!
# The frame format of the recursion for negative lengths

The frames of the driver (`Driver.lean`, `DriverRun.lean`) hold the pieces of the recursion. This
file fixes their format, **canonically**: the content of the input part of a frame is a function
of the piece `P` and the rounds `n` alone (`InP.content`), so that a program reading only the
frame (and a canonically initialized work area) computes a function of `P` (`exec_agree`).

**Global identifiers** (`GIds`): a list `uL` of all darts without repetition (the global dart
identifier `gd d` is the index of `d` in `uL`), an injective vertex identifier `gv` below `G`, a
default dart.

**The canonical numbering of a piece** `P`: `cL P` the darts of `P` in the order of `uL`,
`rL P` the reverses not in `P` of the darts of `P`, in the order of these darts; `fL P = cL P ++
rL P` lists `rcl N P` (`mem_fL`) without repetition. `cδ P h` is its `h`-th dart, `cα P h` the
index of the reverse, `cσ P h` the index of the first return of the rotation to `rcl N P`;
**`penc_canon`**: `PEnc N P #P #(rcl N P) cδ cα cσ`. The numbering of a sub-piece is the filter
of the numbering of the piece (`cL_sub`).

**The frame** of a piece `P` (`m = #P`, `k = #(rcl N P)`), data `[d, e)` with
`e = d + fsz m k = d + 6 + 5 k + 5 m` (`InP`):
* `d`: the rounds `n`; `d + 1`: `m`; `d + 2`: `k`; `d + 3`: the offset `L`;
* `d + 4 + j k + h`, `h < k`: `gd (cδ h)` (`j = 0`), `cα h` (`j = 1`), `cσ h` (`j = 2`),
  `gv (tail (cδ h))` (`j = 3`), `gv (head (cδ h))` (`j = 4`);
* `d + 4 + 5 k + h`, `h < m`: the length `ℓ (cδ h) + L` (offset encoding);
* the outcome region from `d + fin m k = d + 4 + 5 k + m` (`Res`): a flag (`0`: a potential,
  otherwise none), the number `w ≤ 2 m` of listed vertices, for `v < w` the identifier
  `gv (ι v)` at `d + fin + 2 + v` and `f (ι v) + L` at `d + fin + 2 + 2 m + v`; every vertex of
  the piece is listed, `|f| ≤ L` on the listed vertices.

`InP` and `Res` depend only on the memory of the frame (`inP_stab`, `res_stab`: the fields
`in_stab`, `res_stab` of `NSpec`).

**The node's dart numbering is the piece numbering.** The node of `P = P₀ ∪ P₁` enumerates its
darts by `e` (`NodeEnc`); taking `e = cδ P` (`nodeEnc_enum`) the node's numbering is the split's
`δ` (the assumption of `sdArr_exec`): both read the same frame.

**Determinism** (`exec_agree`): two runs of a program naming registers in `U`, without input or
randomness, from configurations agreeing on `U` and on the memory up to the word bound `W` of the
first, end agreeing there, in the same number of steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine Orbit CombMap BKMNW

/-- **Global identifiers**: all darts listed once by `uL` (the dart identifier is the index), an
injective vertex identifier below `G`, a default dart. -/
structure GIds (D V : Type*) where
  uL : List D
  nodup : uL.Nodup
  comp : ∀ d, d ∈ uL
  gv : V → ℕ
  gv_inj : Function.Injective gv
  G : ℕ
  gv_lt : ∀ v, gv v < G
  d₀ : D

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

namespace GIds

variable (g : GIds D V)

/-- The global identifier of a dart: its index in `uL`. -/
def gd (d : D) : ℕ := g.uL.idxOf d

theorem gd_lt (d : D) : g.gd d < g.uL.length := List.idxOf_lt_length_iff.2 (g.comp d)

theorem gd_inj : Function.Injective g.gd := fun a b h => by
  have ha := List.getElem_idxOf (List.idxOf_lt_length_iff.2 (g.comp a))
  have hb := List.getElem_idxOf (List.idxOf_lt_length_iff.2 (g.comp b))
  unfold gd at h
  simp only [h] at ha
  rw [← ha, hb]

end GIds

variable (g : GIds D V) {N : CombMap D V F}

/-! ### The canonical numbering of a piece -/

/-- The darts of `P` in the global order. -/
def cL (P : Finset D) : List D := g.uL.filter (· ∈ P)

variable (N) in
/-- The reverses not in `P` of the darts of `P`, in the order of these darts. -/
def rL (P : Finset D) : List D := ((cL g P).filter (fun d => N.rev d ∉ P)).map N.rev

variable (N) in
/-- The canonical list of `rcl N P`. -/
def fL (P : Finset D) : List D := cL g P ++ rL g N P

variable (N) in
/-- **The canonical numbering of the darts of `rcl N P`**, those of `P` first. -/
def cδ (P : Finset D) (h : ℕ) : D := (fL g N P).getD h g.d₀

variable (N) in
/-- The index of the reverse. -/
def cα (P : Finset D) (h : ℕ) : ℕ := (fL g N P).idxOf (N.rev (cδ g N P h))

variable (N) in
/-- The index of the first return of the rotation to `rcl N P`. -/
noncomputable def cσ (P : Finset D) (h : ℕ) : ℕ :=
  (fL g N P).idxOf (ret (rotPerm N) (rcl N P) (cδ g N P h))

variable {g}

theorem mem_cL {P : Finset D} {d : D} : d ∈ cL g P ↔ d ∈ P := by
  simp [cL, g.comp d]

theorem cL_nodup (P : Finset D) : (cL g P).Nodup := g.nodup.filter _

theorem length_cL (P : Finset D) : (cL g P).length = P.card := by
  rw [← List.toFinset_card_of_nodup (cL_nodup P)]
  congr 1
  ext d; rw [List.mem_toFinset, mem_cL]

theorem mem_rL {P : Finset D} {x : D} : x ∈ rL g N P ↔ x ∉ P ∧ N.rev x ∈ P := by
  unfold rL
  rw [List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [List.mem_filter, mem_cL] at hd
    refine ⟨by simpa using hd.2, by rw [N.rev_rev]; exact hd.1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨N.rev x, ?_, N.rev_rev x⟩
    rw [List.mem_filter, mem_cL]
    exact ⟨h2, by simpa [N.rev_rev] using h1⟩

theorem rL_nodup (P : Finset D) : (rL g N P).Nodup :=
  ((cL_nodup P).filter _).map (fun a b h => by rw [← N.rev_rev a, h, N.rev_rev])

theorem fL_nodup (P : Finset D) : (fL g N P).Nodup := by
  unfold fL
  rw [List.nodup_append]
  refine ⟨cL_nodup P, rL_nodup P, fun a ha b hb hab => ?_⟩
  rw [mem_cL] at ha
  rw [mem_rL] at hb
  exact hb.1 (hab ▸ ha)

theorem mem_fL {P : Finset D} {x : D} : x ∈ fL g N P ↔ x ∈ rcl N P := by
  unfold fL
  rw [List.mem_append, mem_cL, mem_rL, mem_rcl]
  by_cases h : x ∈ P <;> simp [h]

theorem length_fL (P : Finset D) : (fL g N P).length = (rcl N P).card := by
  rw [← List.toFinset_card_of_nodup (fL_nodup P)]
  congr 1
  ext d; rw [List.mem_toFinset, mem_fL]

theorem cδ_eq {P : Finset D} {h : ℕ} (hh : h < (fL g N P).length) :
    cδ g N P h = (fL g N P)[h] := List.getD_eq_getElem _ _ hh

theorem cδ_mem {P : Finset D} {h : ℕ} (hh : h < (rcl N P).card) : cδ g N P h ∈ rcl N P := by
  rw [← length_fL (g := g)] at hh
  rw [cδ_eq hh, ← mem_fL (g := g)]; exact List.getElem_mem hh

theorem cδ_idx {P : Finset D} {x : D} (hx : x ∈ rcl N P) :
    (fL g N P).idxOf x < (rcl N P).card ∧ cδ g N P ((fL g N P).idxOf x) = x := by
  have hl : (fL g N P).idxOf x < (fL g N P).length :=
    List.idxOf_lt_length_iff.2 (mem_fL.2 hx)
  refine ⟨by rw [← length_fL (g := g)]; exact hl, ?_⟩
  rw [cδ_eq hl]; exact List.getElem_idxOf hl

theorem cδ_inj {P : Finset D} {h h' : ℕ} (hh : h < (rcl N P).card)
    (hh' : h' < (rcl N P).card) (e : cδ g N P h = cδ g N P h') : h = h' := by
  rw [← length_fL (g := g)] at hh hh'
  rw [cδ_eq hh, cδ_eq hh'] at e
  exact ((fL_nodup P).getElem_inj_iff).1 e

theorem cδ_lt {P : Finset D} {h : ℕ} (hh : h < P.card) :
    cδ g N P h = (cL g P).getD h g.d₀ := by
  unfold cδ fL
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, length_cL]; omega),
    List.getD_eq_getElem _ _ (by rw [length_cL]; exact hh)]
  exact List.getElem_append_left _

theorem cδ_memP {P : Finset D} {h : ℕ} (hh : h < P.card) : cδ g N P h ∈ P := by
  rw [cδ_lt hh, List.getD_eq_getElem _ _ (by rw [length_cL]; exact hh), ← mem_cL (g := g)]
  exact List.getElem_mem _

theorem rev_mem_rcl' {P : Finset D} {x : D} (hx : x ∈ rcl N P) : N.rev x ∈ rcl N P := by
  rw [mem_rcl] at hx ⊢
  rw [N.rev_rev]; exact hx.symm

/-- **The canonical numbering is a plain encoding of the piece** (`PEnc`). -/
theorem penc_canon (P : Finset D) :
    PEnc N P P.card (rcl N P).card (cδ g N P) (cα g N P) (cσ g N P) where
  enum := ⟨fun h hh => cδ_mem hh, fun x hx => ⟨_, (cδ_idx hx).1, (cδ_idx hx).2⟩,
    fun h hh h' hh' e => cδ_inj hh hh' e⟩
  enumP := ⟨fun h hh => cδ_memP hh, fun x hx => by
      have hl : (cL g P).idxOf x < (cL g P).length := List.idxOf_lt_length_iff.2 (mem_cL.2 hx)
      refine ⟨(cL g P).idxOf x, by rw [← length_cL (g := g)]; exact hl, ?_⟩
      rw [cδ_lt (by rw [← length_cL (g := g)]; exact hl), List.getD_eq_getElem _ _ hl]
      exact List.getElem_idxOf hl,
    fun h hh h' hh' e => cδ_inj (lt_of_lt_of_le hh (card_le_card (subset_rcl P)))
      (lt_of_lt_of_le hh' (card_le_card (subset_rcl P))) e⟩
  mle := card_le_card (subset_rcl P)
  α_lt h hh := (cδ_idx (rev_mem_rcl' (cδ_mem hh))).1
  α_eq h hh := (cδ_idx (rev_mem_rcl' (cδ_mem hh))).2
  σ_lt h hh := (cδ_idx (ret_mem (cδ_mem hh))).1
  σ_eq h hh := (cδ_idx (ret_mem (cδ_mem hh))).2

/-- **The numbering of a sub-piece is the filter of the numbering of the piece.** -/
theorem cL_sub {P Q : Finset D} (hQ : Q ⊆ P) : cL g Q = (cL g P).filter (· ∈ Q) := by
  unfold cL
  rw [List.filter_filter]
  congr 1
  funext d
  by_cases h : d ∈ Q
  · simp [h, hQ h]
  · simp [h]

/-- **The node's dart numbering is the piece numbering** (`NodeEnc.enum` with `e = cδ P`). -/
theorem nodeEnc_enum {P P₀ P₁ : Finset D} (hu : P₀ ∪ P₁ = P) :
    IsEnum P.card (cδ g N P) (P₀ ∪ P₁) := hu ▸ (penc_canon (g := g) (N := N) P).enumP

/-! ### The frame -/

/-- The number of darts of the closure. -/
def ck (N : CombMap D V F) (P : Finset D) : ℕ := (rcl N P).card

/-- The start of the outcome region (relative to the data). -/
def fin (m k : ℕ) : ℕ := 4 + 5 * k + m

/-- The size of the data of a frame. -/
def fsz (m k : ℕ) : ℕ := 6 + 5 * k + 5 * m

variable (g N) in
/-- **The input of a frame**: the piece `P` with `n` rounds left, lengths `ℓ` in the offset
encoding with offset `L` (see the module docstring). -/
structure InP (ℓ : D → ℤ) (L n : ℕ) (P : Finset D) (d e : ℕ) (c : Config) : Prop where
  en : e = d + fsz P.card (ck N P)
  rn : c.nmem d = n
  rm : c.nmem (d + 1) = P.card
  rk : c.nmem (d + 2) = ck N P
  rL : c.nmem (d + 3) = L
  gd : ∀ h < ck N P, c.nmem (d + 4 + h) = g.gd (cδ g N P h)
  α : ∀ h < ck N P, c.nmem (d + 4 + ck N P + h) = cα g N P h
  σ : ∀ h < ck N P, c.nmem (d + 4 + 2 * ck N P + h) = cσ g N P h
  gt : ∀ h < ck N P, c.nmem (d + 4 + 3 * ck N P + h) = g.gv (N.tail (cδ g N P h))
  gh : ∀ h < ck N P, c.nmem (d + 4 + 4 * ck N P + h) = g.gv (N.head (cδ g N P h))
  ln : ∀ h < P.card, c.nmem (d + 4 + 5 * ck N P + h) = (ℓ (cδ g N P h) + L).toNat

variable (g N) in
/-- **The outcome of a frame**: `o` in the outcome region (see the module docstring). -/
def Res (L : ℕ) (P : Finset D) (o : Option (V → ℤ)) (d e : ℕ) (c : Config) : Prop :=
  e = d + fsz P.card (ck N P) ∧
  match o with
  | none => c.nmem (d + fin P.card (ck N P)) ≠ 0
  | some f => c.nmem (d + fin P.card (ck N P)) = 0 ∧
      ∃ (w : ℕ) (ι : ℕ → V), w ≤ 2 * P.card ∧ c.nmem (d + fin P.card (ck N P) + 1) = w ∧
        (∀ v < w, ι v ∈ verts N P ∧
          c.nmem (d + fin P.card (ck N P) + 2 + v) = g.gv (ι v) ∧
          c.nmem (d + fin P.card (ck N P) + 2 + 2 * P.card + v) = (f (ι v) + L).toNat ∧
          |f (ι v)| ≤ L) ∧
        ∀ x ∈ verts N P, ∃ v < w, ι v = x

theorem ck_ge (P : Finset D) : P.card ≤ ck N P := card_le_card (subset_rcl P)

open Driver in
/-- **`InP` depends only on the memory of the frame.** -/
theorem inP_stab {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e : ℕ} {c c' : Config}
    (h : InP g N ℓ L n P d e c) (hm : MemEq c c' d e) : InP g N ℓ L n P d e c' := by
  have he := h.en
  unfold fsz at he
  have hk := ck_ge (N := N) P
  have M : ∀ a, d ≤ a → a < e → c'.nmem a = c.nmem a := fun a h1 h2 => (hm a h1 h2).1
  exact ⟨h.en, by rw [M _ le_rfl (by omega)]; exact h.rn,
    by rw [M _ (by omega) (by omega)]; exact h.rm, by rw [M _ (by omega) (by omega)]; exact h.rk,
    by rw [M _ (by omega) (by omega)]; exact h.rL,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.gd i hi,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.α i hi,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.σ i hi,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.gt i hi,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.gh i hi,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact h.ln i hi⟩

open Driver in
/-- **`Res` depends only on the memory of the frame.** -/
theorem res_stab {L : ℕ} {P : Finset D} {o : Option (V → ℤ)} {d e : ℕ} {c c' : Config}
    (h : Res g N L P o d e c) (hm : MemEq c c' d e) : Res g N L P o d e c' := by
  obtain ⟨he, h⟩ := h
  refine ⟨he, ?_⟩
  unfold fsz at he
  have M : ∀ a, d ≤ a → a < e → c'.nmem a = c.nmem a := fun a h1 h2 => (hm a h1 h2).1
  unfold fin at *
  rcases o with _ | f
  · rw [M _ (by omega) (by omega)]; exact h
  · obtain ⟨h0, w, ι, hw, h1, h2, h3⟩ := h
    refine ⟨by rw [M _ (by omega) (by omega)]; exact h0, w, ι, hw,
      by rw [M _ (by omega) (by omega)]; exact h1, fun v hv => ?_, h3⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 v hv
    exact ⟨a1, by rw [M _ (by omega) (by omega)]; exact a2,
      by rw [M _ (by omega) (by omega)]; exact a3, a4⟩

/-- **The content of the input part of a frame is a function of the piece and the rounds.** -/
theorem InP.content {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e d' e' : ℕ} {c c' : Config}
    (h : InP g N ℓ L n P d e c) (h' : InP g N ℓ L n P d' e' c') :
    ∀ i < fin P.card (ck N P), c.nmem (d + i) = c'.nmem (d' + i) := by
  intro i hi
  unfold fin at hi
  set k := ck N P
  set m := P.card
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · interval_cases i
    · rw [add_zero, add_zero, h.rn, h'.rn]
    · rw [h.rm, h'.rm]
    · rw [h.rk, h'.rk]
    · rw [h.rL, h'.rL]
  obtain ⟨j, rfl⟩ : ∃ j, i = 4 + j := ⟨i - 4, by omega⟩
  have e1 : ∀ x, x + (4 + j) = x + 4 + j := fun x => by omega
  rw [e1, e1]
  rcases Nat.lt_or_ge j k with j1 | j1
  · rw [h.gd j j1, h'.gd j j1]
  obtain ⟨j, rfl⟩ : ∃ j', j = k + j' := ⟨j - k, by omega⟩
  have e2 : ∀ x, x + 4 + (k + j) = x + 4 + k + j := fun x => by omega
  rw [e2, e2]
  rcases Nat.lt_or_ge j k with j2 | j2
  · rw [h.α j j2, h'.α j j2]
  obtain ⟨j, rfl⟩ : ∃ j', j = k + j' := ⟨j - k, by omega⟩
  have e3 : ∀ x, x + 4 + k + (k + j) = x + 4 + 2 * k + j := fun x => by omega
  rw [e3, e3]
  rcases Nat.lt_or_ge j k with j3 | j3
  · rw [h.σ j j3, h'.σ j j3]
  obtain ⟨j, rfl⟩ : ∃ j', j = k + j' := ⟨j - k, by omega⟩
  have e4 : ∀ x, x + 4 + 2 * k + (k + j) = x + 4 + 3 * k + j := fun x => by omega
  rw [e4, e4]
  rcases Nat.lt_or_ge j k with j4 | j4
  · rw [h.gt j j4, h'.gt j j4]
  obtain ⟨j, rfl⟩ : ∃ j', j = k + j' := ⟨j - k, by omega⟩
  have e5 : ∀ x, x + 4 + 3 * k + (k + j) = x + 4 + 4 * k + j := fun x => by omega
  rw [e5, e5]
  rcases Nat.lt_or_ge j k with j5 | j5
  · rw [h.gh j j5, h'.gh j j5]
  obtain ⟨j, rfl⟩ : ∃ j', j = k + j' := ⟨j - k, by omega⟩
  have e6 : ∀ x, x + 4 + 4 * k + (k + j) = x + 4 + 5 * k + j := fun x => by omega
  rw [e6, e6, h.ln j (by omega), h'.ln j (by omega)]

/-! ### Determinism -/

/-- **Runs from agreeing configurations end agreeing.** -/
theorem exec_agree {P P' : Input} {W W' : ℕ} {s : Stmt} {U : ℕ → Bool} {c c' d d' : Config}
    {k k' : ℕ} (h : Exec P W s c c' k) (h' : Exec P' W' s d d' k')
    (hs : s.regsOK U = true) (hn : s.noInp = true) (hr : s.noRand = true) (hW : W ≤ W')
    (hA : Agree U W c d) : Agree U W c' d' ∧ k = k' ∧ Keep U W d d' := by
  obtain ⟨d'', e, hA', hK, -⟩ := Exec.lift (P' := P') h hs hn hr hW hA h'.wb_left
  obtain ⟨rfl, rfl⟩ := stmt_exec_det e h'
  exact ⟨hA', rfl, hK⟩

end Frame

end NegSSSP

end PlanarFlow
