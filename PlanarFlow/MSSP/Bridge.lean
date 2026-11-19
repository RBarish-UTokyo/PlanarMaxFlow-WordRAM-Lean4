module

public import PlanarFlow.MSSP.Query

/-!
# Multiple-source shortest paths meet the specification

The specification `PlanarFlow.MSSP.MSSPSpec` of the planar subroutine asks, for a piece `P` with
nonnegative lengths and vertices `B` on one face, for the distances from every vertex of `B`.

* `msspDist`: the distances themselves (`none` for an empty piece, which has no walks in the
  indexed form of the specification); `msspDist_spec`: they meet `MSSPSpec` for every map.
* `dkpw`: the answer of the data structure of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen
  (SOSA 2022), a query on the whole interval of roots; `dkpw_eq`: in the setting of the article
  (`PlanarFlow.MSSP.Hyp`), it equals `msspDist` for every root, hence (`dkpw_msspOut`) it is a
  correct output of multiple-source shortest paths from the roots of the face.
* `ddgOf`, `isDDGOf_of_msspOut`: the dense distance graph on boundary vertices `bd` is read off
  any correct output from `bd`; `msspOut_union`: outputs for the boundary vertices of several
  faces combine.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap

/-! ### Dense distance graphs from multiple-source shortest paths -/

section DDG

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]

/-- The dense distance graph on `bd` with the lengths of an output of multiple-source shortest
paths. -/
def ddgOf (bd : Finset X) (δ : X → X → Option ℤ) : DDG X := ⟨bd, δ⟩

/-- **A correct output of multiple-source shortest paths from the boundary vertices gives the
dense distance graph.** -/
theorem isDDGOf_of_msspOut {G : Digraph X A} {bd : Finset X} {δ : X → X → Option ℤ}
    (h : MSSPOut G bd δ) : IsDDGOf G (ddgOf bd δ) :=
  fun b hb => ⟨δ b, h b hb, fun _ _ => rfl⟩

open Classical in
/-- Outputs for two sets of sources combine. -/
theorem msspOut_union {G : Digraph X A} {B₁ B₂ : Finset X} {δ₁ δ₂ : X → X → Option ℤ}
    (h₁ : MSSPOut G B₁ δ₁) (h₂ : MSSPOut G B₂ δ₂) :
    MSSPOut G (B₁ ∪ B₂) (fun b => if b ∈ B₁ then δ₁ b else δ₂ b) := by
  intro b hb
  show IsDist G b (if b ∈ B₁ then δ₁ b else δ₂ b)
  split_ifs with h
  · exact h₁ b h
  · exact h₂ b ((mem_union.1 hb).resolve_left h)

end DDG

/-! ### The specification is met -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

open Classical in
/-- The distances in a piece (`none` everywhere for an empty piece). -/
noncomputable def msspDist (M : CombMap D V F) (P : Finset D) (ℓ : D → ℤ) (_φ : F)
    (_B : Finset V) (b v : V) : Option ℤ :=
  if P.Nonempty then odist (pieceGraph M P ℓ) b v else none

/-- **The distances meet the specification of multiple-source shortest paths.** -/
theorem msspDist_spec (M : CombMap D V F) : MSSPSpec M (msspDist M) := by
  intro P ℓ φ B hnn _ b _
  by_cases hP : P.Nonempty
  · have : Nonempty {d // d ∈ P} := ⟨⟨hP.choose, hP.choose_spec⟩⟩
    have h := isDist (G := pieceGraph M P ℓ) (fun a => hnn a.1 a.2) b
    have e : msspDist M P ℓ φ B b = odist (pieceGraph M P ℓ) b :=
      funext fun v => by simp [msspDist, hP]
    rwa [e]
  · have : IsEmpty {d // d ∈ P} := ⟨fun a => hP ⟨a.1, a.2⟩⟩
    have h := isDist_of_isEmpty (G := pieceGraph M P ℓ) b
    have e : msspDist M P ℓ φ B b = fun _ => none :=
      funext fun v => by simp [msspDist, hP]
    rwa [e]

/-! ### The data structure of the article -/

open Classical in
/-- The index of a root (`0` for other vertices). -/
noncomputable def rootIdx (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (b : V) : ℕ :=
  if h : ∃ i, i < k ∧ M.tail (g i) = b then Nat.find h else 0

open Classical in
/-- **The answer of the data structure of the article**: a query on the whole interval of roots
`[0, k - 1]` (`none` for an empty piece). -/
noncomputable def dkpw (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (P : Finset D) (ℓ : D → ℤ)
    (b v : V) : Option ℤ :=
  if P.Nonempty then query M g P ℓ (rootIdx M k g b) 0 (k - 1) v else none

/-- The roots of the face. -/
def roots (M : CombMap D V F) (k : ℕ) (g : ℕ → D) : Finset V :=
  (range k).image fun i => M.tail (g i)

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {P : Finset D} {ℓ : D → ℤ}

lemma rootIdx_eq (hf : FaceCycle M k g) {j : ℕ} (hj : j < k) : rootIdx M k g (M.tail (g j)) = j := by
  classical
  have h : ∃ i, i < k ∧ M.tail (g i) = M.tail (g j) := ⟨j, hj, rfl⟩
  simp only [rootIdx, h, ↓reduceDIte]
  have hs := Nat.find_spec h
  exact hf.inj _ hs.1 _ hj hs.2

/-- **The data structure answers with the distances**, from every root of the face. -/
theorem dkpw_eq (H : Hyp M k g P ℓ) {j : ℕ} (hj : j < k) (φ : F) (B : Finset V) (v : V) :
    dkpw M k g P ℓ (M.tail (g j)) v = msspDist M P ℓ φ B (M.tail (g j)) v := by
  unfold dkpw msspDist
  split_ifs with hP
  · rw [rootIdx_eq H.face hj, query_eq H (Nat.zero_le j) (by omega) (by omega)]
  · rfl

/-- **The data structure of the article is a correct multiple-source shortest path output** for
the roots of the face, in the setting of the article. -/
theorem dkpw_msspOut (H : Hyp M k g P ℓ) :
    MSSPOut (pieceGraph M P ℓ) (roots M k g) (dkpw M k g P ℓ) := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
  rw [mem_range] at hj
  have h := msspDist_spec M P ℓ (M.face (g j)) {M.tail (g j)} (fun d hd => (H.pos d hd).le)
    (fun b hb => ⟨g j, rfl, by rw [mem_singleton.1 hb]⟩) _ (mem_singleton_self _)
  have e : dkpw M k g P ℓ (M.tail (g j)) = msspDist M P ℓ (M.face (g j)) {M.tail (g j)} (M.tail (g j)) :=
    funext fun v => dkpw_eq H hj _ _ v
  rw [e]; exact h

/-- **The dense distance graph on the roots of the face, from the data structure.** -/
theorem dkpw_isDDGOf (H : Hyp M k g P ℓ) :
    IsDDGOf (pieceGraph M P ℓ) (ddgOf (roots M k g) (dkpw M k g P ℓ)) :=
  isDDGOf_of_msspOut (dkpw_msspOut H)

end MSSP

end PlanarFlow
