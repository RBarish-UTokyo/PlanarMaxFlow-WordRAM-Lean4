module

public import PlanarFlow.BKMNW.MfSplitSpec
public import PlanarFlow.BKMNW.SmStep
public import PlanarFlow.BKMNW.DecS
public import PlanarFlow.BKMNW.SplitRot

/-!
# The extended frame: the frame of a call with its decomposition record

The frame `Lay` of a call (`MfFrame.lean`) holds only the darts of the **piece map**
`pdarts M x.1.piece x.2.1`; the split of the decomposition `decS … (smD …) …` at a call depends
on more: the darts of the piece inside the holes, the
vertex identities, the flag `b` and the state of `decS`. The **extended frame** adds, after the
frame (`d + fsz m`), a pointer to a **decomposition record** at `R` (inside `[d, e)`):

* header: `R ↦ n` (the darts of the piece), `R + 1 ↦ ph` (the phase: `0` a call `decS … P Hs st b`
  of the decomposition, `1` a call `smD … P Hs` of the small decomposition, `2` a leaf),
  `R + 2 ↦ b` (the flag of `decS`, `0`/`1`);
* for `ph < 2`, seven arrays over an enumeration `g` of the **whole piece** `P = x.1.piece` in the
  increasing order of the global numbering `gid`: `GP` (`gid`), `RP` (the index of the reverse),
  `HP` (the hole label of the tail), `KP` (the rank of the tail), `VP` (the vertex number `ν` of
  the tail: a global vertex numbering, the same for every call), `SP` (the state `st` of `decS`,
  the rotation of the piece map of the core, as indices, on the darts of that piece map), all of
  length `n` from `R + 3`, and `FX` (length `m`, from `R + 3 + 6 n`): the index in `g` of the
  frame's darts, increasing in `gid` (so `g ∘ FX` is the frame's enumeration, `fx_en`).

Definitions: `DSys` (the functions of the decomposition), `DSys.dec`, `rszC` (the size of a
record, `3 + 6 #P + #pdarts`), `PhOk` (the meaning of the phase), `RArr`, **`LayR`**, **`FInLX`**
(`FInL` with the record), **`FOutLX`** (`= FOutL`: the output of a call is its flow in the
frame). Lemmas: `RArr.card`, `LayR.congr`, `FInLX.finL` (**`FInLX → FInL`**), `FInLX.stab`,
`enum_unique` (two increasing enumerations of a set agree), `RArr.fx_en`, and the children's
records: `smD_children` (at a node of `smD` the left child is `smD` of its piece with the
child's holes, the right child a leaf), `decS_children` (at a node of `decS` of a large piece
the children are `decS` calls with the states `chS` and the flag `!holeStep`; of a small piece,
`smD`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The functions of the decomposition** `decS spS spH (smD pk S T) chS s`, with the set `Q`
whose core carries the state. -/
structure DSys where
  spS : Finset D → List (Finset V) → Perm D → SplitAns M
  spH : Finset D → List (Finset V) → Perm D → SplitAns M
  chS : Finset D → List (Finset V) → Perm D → HSep M → Finset D → Perm D
  s : ℕ
  Q : Finset V
  pk : Finset D → D

/-- The decomposition of a piece with its state and flag. -/
noncomputable def DSys.dec (ds : DSys M) (S T : Finset V) (P : Finset D) (Hs : List (Finset V))
    (st : Perm D) (b : Bool) : ADec M :=
  decS M ds.spS ds.spH (smD M ds.pk S T) ds.chS ds.s P Hs st b

variable (M) in
/-- **The size of the record of a call**: `3 + 6 #P + #pdarts`. -/
noncomputable def rszC (x : MCall M) : ℕ :=
  3 + 6 * x.1.piece.card + (pdarts M x.1.piece x.2.1).card

variable (M) in
/-- **The meaning of the phase** `ph` and the flag `b` of a record (state array `SP` at `SPb`,
the enumeration `g` of the piece, `n` darts). -/
def PhOk (ds : DSys M) (S T : Finset V) (x : MCall M) (ph b n SPb : ℕ) (g : ℕ → D)
    (mem : ℕ → ℕ) : Prop :=
  (ph = 0 ∧ ∃ st : Perm D, x.1 = ds.dec S T x.1.piece x.2.1 st (decide (b = 1)) ∧
      ∀ i < n, g i ∈ pdarts M (core M ds.Q x.1.piece) x.2.1 →
        mem (SPb + i) < n ∧ g (mem (SPb + i)) = st (g i)) ∨
    (ph = 1 ∧ x.1 = smD M ds.pk S T x.1.piece x.2.1) ∨
    (ph = 2 ∧ ∃ Q, x.1 = .leaf Q)

variable (M) in
/-- **The arrays of a record** at `R` (`n` darts of the piece enumerated by `g`, `m` darts of the
piece map; see the module docstring). -/
structure RArr (gid : D → ℕ) (ν : V → ℕ) (S T : Finset V) (x : MCall M) (m n R : ℕ)
    (g : ℕ → D) (mem : ℕ → ℕ) : Prop where
  g_mem : ∀ i < n, g i ∈ x.1.piece
  g_surj : ∀ y ∈ x.1.piece, ∃ i < n, g i = y
  g_mono : ∀ i j, i < j → j < n → gid (g i) < gid (g j)
  gp : ∀ i < n, mem (R + 3 + i) = gid (g i)
  rp : ∀ i < n, mem (R + 3 + n + i) < n ∧ g (mem (R + 3 + n + i)) = M.rev (g i)
  hp : ∀ i < n, mem (R + 3 + 2 * n + i) = hlab x.2.1 (M.tail (g i))
  kp : ∀ i < n, mem (R + 3 + 3 * n + i) = lrk S T (hunion x.2.1) (M.tail (g i))
  vp : ∀ i < n, mem (R + 3 + 4 * n + i) = ν (M.tail (g i))
  fx : ∀ i < m, mem (R + 3 + 6 * n + i) < n
  fx_mem : ∀ i < m, g (mem (R + 3 + 6 * n + i)) ∈ pdarts M x.1.piece x.2.1
  fx_surj : ∀ y ∈ pdarts M x.1.piece x.2.1, ∃ i < m, g (mem (R + 3 + 6 * n + i)) = y
  fx_mono : ∀ i j, i < j → j < m →
    gid (g (mem (R + 3 + 6 * n + i))) < gid (g (mem (R + 3 + 6 * n + j)))

variable (M) in
/-- **The decomposition record of a call** at `R` (see the module docstring). -/
structure LayR (ds : DSys M) (gid : D → ℕ) (ν : V → ℕ) (S T : Finset V) (x : MCall M)
    (m n R : ℕ) (g : ℕ → D) (mem : ℕ → ℕ) : Prop where
  hn : mem R = n
  hph : mem (R + 1) ≤ 2
  hb : mem (R + 2) ≤ 1
  ph : PhOk M ds S T x (mem (R + 1)) (mem (R + 2)) n (R + 3 + 5 * n) g mem
  arr : mem (R + 1) < 2 → RArr M gid ν S T x m n R g mem

/-- **The size of a record** of phase `ph` (`n` darts of the piece, `m` of the piece map): the
header alone for a leaf (`ph = 2`). -/
def rszL (ph n m : ℕ) : ℕ := if ph < 2 then 3 + 6 * n + m else 3

lemma three_le_rszL (ph n m : ℕ) : 3 ≤ rszL ph n m := by unfold rszL; split_ifs <;> omega

variable (M) in
/-- **The input of a call in the extended frame `[d, e)`**: `FInL` with the pointer
`mem (d + fsz m) = R` to a record `LayR` inside the frame. -/
def FInLX (ds : DSys M) (Reach : MCall M → Prop) (gid : D → ℕ) (ν : V → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (x : MCall M) (d e : ℕ) (c : Config) : Prop :=
  Reach x ∧ CallOk M S T x ∧ ∃ m en n g, Lay M gid u S T Z x m en d c.nmem ∧
    d + fsz m < c.nmem (d + fsz m) ∧
    c.nmem (d + fsz m) + rszL (c.nmem (c.nmem (d + fsz m) + 1)) n m ≤ e ∧
    LayR M ds gid ν S T x m n (c.nmem (d + fsz m)) g c.nmem

variable (M) in
/-- **A record of the call `x` at `R`, of size `z`** (at most `rszC M x`), as a property of the
memory on `[R, R + z)` only: what the separator program writes for each child. -/
def RecAt (ds : DSys M) (gid : D → ℕ) (ν : V → ℕ) (S T : Finset V) (x : MCall M) (R z : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  z ≤ rszC M x ∧ ∃ n g, z = rszL (mem (R + 1)) n (pdarts M x.1.piece x.2.1).card ∧
    LayR M ds gid ν S T x (pdarts M x.1.piece x.2.1).card n R g mem

variable (M) in
/-- **The output of a call in the extended frame**: the flow in the frame (`FOutL`); the record
is not needed after the split. -/
def FOutLX (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) : FOutT M := FOutL M gid u S T Z

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

lemma fOutLX_iff {x : MCall M} {f : SDart (pdarts M x.1.piece x.2.1) → ℤ} {d e : ℕ}
    {c : Config} : FOutLX M gid u S T Z x f d e c ↔ FOutL M gid u S T Z x f d e c := Iff.rfl

/-- The enumeration of a record is injective. -/
lemma RArr.g_inj {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem) {i j : ℕ} (hi : i < n) (hj : j < n) (e : g i = g j) :
    i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := h.g_mono i j hij hj; rw [e] at this; omega
  · rfl
  · have := h.g_mono j i hij hi; rw [e] at this; omega

/-- **The record enumerates the piece**: `n = #P`. -/
lemma RArr.card {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem) : n = x.1.piece.card := by
  have e : x.1.piece = (range n).image g := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · intro hy; obtain ⟨i, hi, rfl⟩ := h.g_surj y hy; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact h.g_mem i hi
  rw [e, card_image_of_injOn (fun i hi j hj e => h.g_inj (mem_range.1 hi) (mem_range.1 hj) e),
    card_range]

/-- The frame part of a record enumerates the piece map: `m = #pdarts`. -/
lemma RArr.card_m {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem) : m = (pdarts M x.1.piece x.2.1).card := by
  have inj : ∀ i < m, ∀ j < m, g (mem (R + 3 + 6 * n + i)) = g (mem (R + 3 + 6 * n + j)) →
      i = j := fun i hi j hj e => by
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := h.fx_mono i j hij hj; rw [e] at this; omega
    · rfl
    · have := h.fx_mono j i hij hi; rw [e] at this; omega
  have e : pdarts M x.1.piece x.2.1 = (range m).image fun i => g (mem (R + 3 + 6 * n + i)) := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · intro hy; obtain ⟨i, hi, hh⟩ := h.fx_surj y hy; exact ⟨i, hi, hh⟩
    · rintro ⟨i, hi, rfl⟩; exact h.fx_mem i hi
  rw [e, card_image_of_injOn (fun i hi j hj e => inj i (mem_range.1 hi) j (mem_range.1 hj) e),
    card_range]

/-- **Two enumerations of a set, increasing in `gid`, agree.** -/
lemma enum_unique {B : Finset D} {m : ℕ} {f₁ f₂ : ℕ → D}
    (h1m : ∀ i < m, f₁ i ∈ B) (h1s : ∀ y ∈ B, ∃ i < m, f₁ i = y)
    (h1o : ∀ i j, i < j → j < m → gid (f₁ i) < gid (f₁ j))
    (h2m : ∀ i < m, f₂ i ∈ B) (h2s : ∀ y ∈ B, ∃ i < m, f₂ i = y)
    (h2o : ∀ i j, i < j → j < m → gid (f₂ i) < gid (f₂ j)) : ∀ i < m, f₁ i = f₂ i := by
  -- the rank of `f₁ i` among the darts of `B` is `i`
  have rk : ∀ (f : ℕ → D), (∀ i < m, f i ∈ B) → (∀ y ∈ B, ∃ i < m, f i = y) →
      (∀ i j, i < j → j < m → gid (f i) < gid (f j)) →
      ∀ i < m, (B.filter fun y => gid y < gid (f i)).card = i := by
    intro f hm hs ho i hi
    have e : B.filter (fun y => gid y < gid (f i)) = (range i).image f := by
      ext y
      simp only [mem_filter, mem_image, mem_range]
      constructor
      · rintro ⟨hy, hlt⟩
        obtain ⟨j, hj, rfl⟩ := hs y hy
        refine ⟨j, ?_, rfl⟩
        by_contra hc
        rcases Nat.lt_or_ge i j with h | h
        · have := ho i j h hj; omega
        · have : j = i := by omega
          subst this; omega
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hm j (by omega), ho j i hj hi⟩
    rw [e, card_image_of_injOn, card_range]
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := ho a b h (by omega); rw [hab] at this; omega
    · exact h
    · have := ho b a h (by omega); rw [hab] at this; omega
  intro i hi
  obtain ⟨j, hj, hji⟩ := h2s _ (h1m i hi)
  have r1 := rk f₁ h1m h1s h1o i hi
  have r2 := rk f₂ h2m h2s h2o j hj
  rw [hji] at r2
  have : i = j := by omega
  subst this
  exact hji.symm

/-- **The frame darts in the record**: `g (FX[i]) = en i`. -/
lemma RArr.fx_en {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ} {en : ℕ → D} {d : ℕ}
    (h : RArr M gid ν S T x m n R g mem) (hL : Lay M gid u S T Z x m en d mem') :
    ∀ i < m, g (mem (R + 3 + 6 * n + i)) = en i :=
  enum_unique h.fx_mem h.fx_surj h.fx_mono hL.en_mem hL.en_surj hL.en_mono

/-- The arrays of a record depend only on `[R, R + 3 + 6 n + m)`. -/
lemma RArr.congr {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem)
    (he : ∀ a, R ≤ a → a < R + 3 + 6 * n + m → mem' a = mem a) :
    RArr M gid ν S T x m n R g mem' where
  g_mem := h.g_mem
  g_surj := h.g_surj
  g_mono := h.g_mono
  gp i hi := by rw [he _ (by omega) (by omega)]; exact h.gp i hi
  rp i hi := by rw [he _ (by omega) (by omega)]; exact h.rp i hi
  hp i hi := by rw [he _ (by omega) (by omega)]; exact h.hp i hi
  kp i hi := by rw [he _ (by omega) (by omega)]; exact h.kp i hi
  vp i hi := by rw [he _ (by omega) (by omega)]; exact h.vp i hi
  fx i hi := by rw [he _ (by omega) (by omega)]; exact h.fx i hi
  fx_mem i hi := by rw [he _ (by omega) (by omega)]; exact h.fx_mem i hi
  fx_surj y hy := by
    obtain ⟨i, hi, e⟩ := h.fx_surj y hy
    exact ⟨i, hi, by rw [he _ (by omega) (by omega)]; exact e⟩
  fx_mono i j hij hj := by
    rw [he _ (by omega) (by omega), he (R + 3 + 6 * n + j) (by omega) (by omega)]
    exact h.fx_mono i j hij hj

/-- **The record depends only on `[R, R + rszC x)`.** -/
lemma LayR.congr {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ}
    (h : LayR M ds gid ν S T x m n R g mem)
    (he : ∀ a, R ≤ a → a < R + rszC M x → mem' a = mem a) :
    LayR M ds gid ν S T x m n R g mem' := by
  have e1 : mem' (R + 1) = mem (R + 1) := he _ (by omega) (by unfold rszC; omega)
  have e2 : mem' (R + 2) = mem (R + 2) := he _ (by omega) (by unfold rszC; omega)
  -- the size of the arrays, when there are arrays
  have hsz : mem (R + 1) < 2 → R + 3 + 6 * n + m ≤ R + rszC M x := fun hp => by
    have a := h.arr hp
    rw [a.card, a.card_m]; unfold rszC; omega
  refine ⟨by rw [he _ le_rfl (by unfold rszC; omega)]; exact h.hn, by rw [e1]; exact h.hph,
    by rw [e2]; exact h.hb, ?_, fun hp => ?_⟩
  · have hph := h.ph
    rw [e1, e2]
    rcases hph with ⟨h0, st, hx, hs⟩ | h1 | h2
    · refine Or.inl ⟨h0, st, hx, fun i hi hg => ?_⟩
      have hsz' := hsz (by omega)
      rw [he _ (by omega) (by omega)]
      exact hs i hi hg
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  · rw [e1] at hp
    exact (h.arr hp).congr fun a h1 h2 => he a h1 (by have := hsz hp; omega)

/-- **The record depends only on `[R, R + rszL ph n m)`** (`ph` its phase). -/
lemma LayR.congrL {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ}
    (h : LayR M ds gid ν S T x m n R g mem)
    (he : ∀ a, R ≤ a → a < R + rszL (mem (R + 1)) n m → mem' a = mem a) :
    LayR M ds gid ν S T x m n R g mem' := by
  have h3 := three_le_rszL (mem (R + 1)) n m
  have e1 : mem' (R + 1) = mem (R + 1) := he _ (by omega) (by omega)
  have e2 : mem' (R + 2) = mem (R + 2) := he _ (by omega) (by omega)
  have hsz : mem (R + 1) < 2 → rszL (mem (R + 1)) n m = 3 + 6 * n + m := fun hp => by
    unfold rszL; rw [iteT hp]
  refine ⟨by rw [he _ le_rfl (by omega)]; exact h.hn, by rw [e1]; exact h.hph,
    by rw [e2]; exact h.hb, ?_, fun hp => ?_⟩
  · have hph := h.ph
    rw [e1, e2]
    rcases hph with ⟨h0, st, hx, hs⟩ | h1 | h2
    · refine Or.inl ⟨h0, st, hx, fun i hi hg => ?_⟩
      have hsz' := hsz (by omega)
      rw [he _ (by omega) (by omega)]
      exact hs i hi hg
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  · rw [e1] at hp
    exact (h.arr hp).congr fun a h1 h2 => he a h1 (by have := hsz hp; omega)

/-- `RecAt` depends only on `[R, R + z)`. -/
lemma RecAt.congr {x : MCall M} {R z : ℕ} {mem mem' : ℕ → ℕ}
    (h : RecAt M ds gid ν S T x R z mem)
    (he : ∀ a, R ≤ a → a < R + z → mem' a = mem a) : RecAt M ds gid ν S T x R z mem' := by
  obtain ⟨hz, n, g, hzn, hR⟩ := h
  have h3 := three_le_rszL (mem (R + 1)) n (pdarts M x.1.piece x.2.1).card
  have e1 : mem' (R + 1) = mem (R + 1) := he _ (by omega) (by omega)
  exact ⟨hz, n, g, by rw [e1]; exact hzn, hR.congrL fun a a1 a2 => he a a1 (by omega)⟩

/-- **The extended frame gives the frame**: `FInLX → FInL`. -/
lemma FInLX.finL {Reach : MCall M → Prop} {x : MCall M} {d e : ℕ} {c : Config}
    (h : FInLX M ds Reach gid ν u S T Z x d e c) : FInL M Reach gid u S T Z x d e c := by
  obtain ⟨hr, ho, m, en, n, g, hL, h1, h2, -⟩ := h
  exact ⟨hr, ho, m, en, hL, by omega⟩

/-- **The extended frame depends only on the memory in `[d, e)`.** -/
lemma FInLX.stab {Reach : MCall M → Prop} {x : MCall M} {d e : ℕ} {c c' : Config}
    (h : FInLX M ds Reach gid ν u S T Z x d e c) (hm : MemEq c c' d e) :
    FInLX M ds Reach gid ν u S T Z x d e c' := by
  obtain ⟨hr, ho, m, en, n, g, hL, h1, h2, hR⟩ := h
  have hf : fsz m = 4 + 7 * m := rfl
  set R := c.nmem (d + fsz m) with hRdef
  have h3 := three_le_rszL (c.nmem (R + 1)) n m
  have hp : c'.nmem (d + fsz m) = R := (hm _ (by omega) (by omega)).1
  have hp1 : c'.nmem (R + 1) = c.nmem (R + 1) := (hm _ (by omega) (by omega)).1
  refine ⟨hr, ho, m, en, n, g, hL.congr fun a a1 a2 => (hm a a1 (by omega)).1,
    by rw [hp]; exact h1, by rw [hp, hp1]; exact h2, ?_⟩
  rw [hp]
  exact hR.congrL fun a a1 a2 => (hm a (by omega) (by omega)).1

lemma FOutLX.stab {x : MCall M} {f : SDart (pdarts M x.1.piece x.2.1) → ℤ} {d e : ℕ}
    {c c' : Config} (h : FOutLX M gid u S T Z x f d e c) (hm : MemEq c c' d e) :
    FOutLX M gid u S T Z x f d e c' := FOutL.stab h hm

/-! ### The records of the children -/

/-- **The children at a node of `smD`**: the left child is `smD` of its own piece with the
child's holes, the right child a leaf. -/
theorem smD_children {pk : Finset D → D} (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X)
    (hloop : ∀ d, M.head d ≠ M.tail d) {P : Finset D} {Hs : List (Finset V)}
    (hP : RevClosed M P) {l r : ADec M} {π : HSep M} (h : smD M pk S T P Hs = .node l r π) :
    l = smD M pk S T l.piece (childHoles Hs π.path.mverts) ∧ ∃ Q, r = .leaf Q := by
  have h1 : ntag (smD M pk S T P Hs) = 1 := by rw [h]; rfl
  obtain ⟨⟨hcard, hBne⟩, -⟩ := (smD_ntag hpk hloop P Hs).1 h1
  -- in each case of `SmForm`
  have key : ∀ x up lpm, SmForm M pk S T P Hs x up lpm → RevClosed M
      (if lpm then pdarts M P Hs else P \ {x, M.rev x}) →
      l = smD M pk S T l.piece (childHoles Hs π.path.mverts) ∧ ∃ Q, r = .leaf Q := by
    rintro x up lpm ⟨R, π', hD, -, hmv⟩ hrc
    rw [h] at hD
    injection hD with el er eπ
    subst el er eπ
    refine ⟨?_, R, rfl⟩
    rw [smD_piece hpk _ _ _ rfl hrc, hmv]
  obtain ⟨fX, fY, fB⟩ := smD_form (S := S) (T := T) hpk hloop hcard hBne
  have hrc2 : ∀ y ∈ P, RevClosed M (P \ {y, M.rev y}) := fun y hy z hz => by
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hz ⊢
    refine ⟨hP z hz.1, fun e => hz.2.2 ?_, fun e => hz.2.1 ?_⟩
    · rw [← e, M.rev_rev]
    · rw [← M.rev_rev z, e, M.rev_rev]
  have hrcp : RevClosed M (pdarts M P Hs) := stable_pdarts hP Hs
  by_cases hX : (smX M S T P Hs).Nonempty
  · have hr : RevClosed M (if false = true then pdarts M P Hs else
        P \ {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}) := by
      simp only [Bool.false_eq_true, ↓reduceIte]; exact hrc2 _ (smX_sub (hpk _ hX))
    exact key _ _ _ (fX hX) hr
  by_cases hY : (smY M P Hs).Nonempty
  · have hlt : (pdarts M P Hs).card < P.card := by
      rcases (smD_ntag hpk hloop P Hs).1 h1 |>.2 with hc | hc | hc
      · exact absurd hc hX
      · exact absurd hY hc
      · exact hc
    have hr : RevClosed M (if true = true then pdarts M P Hs else
        P \ {pk (smY M P Hs), M.rev (pk (smY M P Hs))}) := by
      simp only [↓reduceIte]; exact hrcp
    exact key _ _ _ (fY hX hY hlt) hr
  · have hr : RevClosed M (if false = true then pdarts M P Hs else
        P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}) := by
      simp only [Bool.false_eq_true, ↓reduceIte]; exact hrc2 _ (smB_sub (hpk _ hBne))
    exact key _ _ _ (fB hX hY) hr

/-- **The children at a node of `decS`**: of a small piece, `smD` (`decS_small`); of a large
piece, the children are `decS` of the pieces of the split with the child's holes, the states
`chS` and the flag `!holeStep`. -/
theorem decS_children {P : Finset D} {Hs : List (Finset V)} {st : Perm D} {b : Bool}
    {l r : ADec M} {π : HSep M} (h : ds.dec S T P Hs st b = .node l r π) :
    (P.card ≤ ds.s ∧ smD M ds.pk S T P Hs = .node l r π) ∨
    (ds.s < P.card ∧ ∃ l' r' : Finset D,
      (if holeStep M P Hs b then ds.spH P Hs st else ds.spS P Hs st) = some (l', r', π) ∧
      l = ds.dec S T l' (childHoles Hs π.path.mverts) (ds.chS P Hs st π l')
        (!holeStep M P Hs b) ∧
      r = ds.dec S T r' (childHoles Hs π.path.mverts) (ds.chS P Hs st π r')
        (!holeStep M P Hs b)) := by
  by_cases hs : P.card ≤ ds.s
  · left
    refine ⟨hs, ?_⟩
    rw [← h]; unfold DSys.dec; rw [decS_small hs]
  right
  refine ⟨by omega, ?_⟩
  unfold DSys.dec at h
  rw [decS] at h
  simp only [hs, ↓reduceIte] at h
  split at h
  · cases h
  · rename_i l' r' π' he
    split at h
    · rename_i hlt
      injection h with el er eπ
      subst eπ
      exact ⟨l', r', he, el.symm, er.symm⟩
    · cases h

end MfDrv

end BKMNW

end PlanarFlow
