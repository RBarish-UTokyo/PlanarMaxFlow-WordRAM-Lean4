module

public import PlanarFlow.BKMNW.MfNode
public import PlanarFlow.BKMNW.MachCost

/-!
# The per-call costs and the room of the fixed max-flow program, with explicit constants

`mfDriveFrame_decM2` (`PlanarFlow/BKMNW/MfNode.lean`) leaves the per-call cost hypotheses `hl`,
`hn` (against the charges of `arunLCost`, for **every** call) and a room bound `R` (for every
call). Only the calls of the decomposition matter, and on them the invariants `CallOk` hold:

* `mcost_le_on`, `roomC_le_on`: `mcost_le`, `roomC_le` with the hypotheses only on the calls of
  `Calls τ Hs σ`;
* `callOk_calls` (the invariants pass to every call), **`callOk_cond`** (at a node call with
  `CallOk`, the condition `PieceInv ∧ SegIn` of `arunL` and `nodeCharge` holds), `runsCharge`
  (the charge of the subroutine runs of a node call, the part of `nodeCharge` besides the
  separator and the bookkeeping), `nodeCharge_eq`;
* **`calls_size`** (with `Core`: along the calls, `#Hs + #piece` does not grow), so at every call
  of the root decomposition `#pdarts ≤ N` and `#Hs ≤ N` (`N = #τ.piece`, the darts).

**`mfDriveFrame_cMach`**: the fixed program `driver mtProg mlProg (splitS sepP) (nodeSF stepP)`
with the machine subroutine costs `cMach C C₀` (`68 ≤ C`, `20 ≤ C₀`), **`A = 1`, `B = 1000`**, and
the room `R = 39 N + 20 + RS + RT`: the hypotheses left are the specifications `SepPSpec sepP`,
`StepPSpec stepP`, the separator program's cost `sT m ≤ C m lg m` (the field `sep` of `cMach`),
the step's cost `stT x ≤ runsCharge x` at the calls of the decomposition (the charges of the
subroutine runs of the article), the rooms `sR m k ≤ RS` (`m, k ≤ N`), `rT x ≤ RT`, the word bound
`h + (2 N + 1) R ≤ W`, and the root frame.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### Costs and rooms on the calls of a decomposition -/

/-- **`mcost_le` on the calls**: the per-call cost hypotheses only on the calls satisfying `P`,
which contains the calls from `(τ, Hs, σ)`. -/
theorem mcost_le_on {tc lc sc nc : MCall M → ℕ} (c : SubCosts) {A B : ℕ} (P : MCall M → Prop)
    (hl : ∀ Q Hs σ, P (.leaf Q, Hs, σ) → tc ((.leaf Q, Hs, σ) : MCall M) + lc (.leaf Q, Hs, σ) +
      20 ≤ A * (c.leaf (pdarts M Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B)
    (hn : ∀ l r π Hs σ, P (.node l r π, Hs, σ) → tc ((.node l r π, Hs, σ) : MCall M) +
      sc (.node l r π, Hs, σ) + nc (.node l r π, Hs, σ) + 80 ≤
        A * nodeCharge M c l r π Hs σ + B) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), (∀ x, Calls M τ Hs σ x → P x) →
      mcost M tc lc sc nc τ Hs σ ≤ A * arunLCost M c τ Hs σ + B * asize τ
  | .leaf Q, Hs, σ, hP => by
    simp only [mcost, arunLCost, asize, mul_one]
    exact hl Q Hs σ (hP _ rfl)
  | .node l r π, Hs, σ, hP => by
    have il := mcost_le_on c P hl hn l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2
      (fun x hx => hP x (Or.inr (Or.inl hx)))
    have ir := mcost_le_on c P hl hn r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2
      (fun x hx => hP x (Or.inr (Or.inr hx)))
    have h0 := hn l r π Hs σ (hP _ (Or.inl rfl))
    rw [arunLCost_node]
    simp only [mcost, asize]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega

/-- **`roomC_le` on the calls.** -/
theorem roomC_le_on {rL rS rN : MCall M → ℕ} {R : ℕ} (P : MCall M → Prop)
    (hL : ∀ x, P x → rL x ≤ R) (hSN : ∀ x, P x → rS x + rN x ≤ R) :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), (∀ x, Calls M τ Hs σ x → P x) →
      roomC M rL rS rN τ Hs σ ≤ asize τ * R
  | .leaf Q, Hs, σ, hP => by simp only [roomC, asize, one_mul]; exact hL _ (hP _ rfl)
  | .node l r π, Hs, σ, hP => by
    have il := roomC_le_on P hL hSN l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2
      (fun x hx => hP x (Or.inr (Or.inl hx)))
    have ir := roomC_le_on P hL hSN r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2
      (fun x hx => hP x (Or.inr (Or.inr hx)))
    have h0 := hSN (.node l r π, Hs, σ) (hP _ (Or.inl rfl))
    simp only [roomC, asize]
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have : max (roomC M rL rS rN l (chL M l r π Hs σ).2.1 (chL M l r π Hs σ).2.2)
        (roomC M rL rS rN r (chR M l r π Hs σ).2.1 (chR M l r π Hs σ).2.2) ≤
        asize l * R + asize r * R := max_le (by omega) (by omega)
    omega

/-- The calls from a call are calls of any decomposition containing it. -/
lemma calls_trans : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) (y x : MCall M),
    Calls M τ Hs σ y → Calls M y.1 y.2.1 y.2.2 x → Calls M τ Hs σ x
  | .leaf Q, Hs, σ, y, x, hy, hx => by subst hy; exact hx
  | .node l r π, Hs, σ, y, x, hy, hx => by
    rcases hy with hy | hy | hy
    · subst hy; exact hx
    · exact Or.inr (Or.inl (calls_trans l _ _ y x hy hx))
    · exact Or.inr (Or.inr (calls_trans r _ _ y x hy hx))

/-! ### The invariants and the sizes along the calls -/

variable {S T : Finset V}

/-- **The invariants pass to every call.** -/
lemma callOk_calls : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) (x : MCall M),
    CallOk M S T (τ, Hs, σ) → Calls M τ Hs σ x → CallOk M S T x
  | .leaf Q, Hs, σ, x, h, hx => by subst hx; exact h
  | .node l r π, Hs, σ, x, h, hx => by
    rcases hx with hx | hx | hx
    · subst hx; exact h
    · exact callOk_calls l _ _ x h.chL hx
    · exact callOk_calls r _ _ x h.chR hx

/-- **The condition of `arunL` at a node call with the invariants.** -/
lemma callOk_cond {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : CallOk M S T (.node l r π, Hs, σ)) :
    PieceInv M (l.piece ∪ r.piece) Hs σ ∧ ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s := by
  obtain ⟨⟨hpi, -, -⟩, ⟨-, -, -, -, -, hseg⟩, ⟨-, -, -, -, -, hsegP⟩, -⟩ := h
  refine ⟨hpi, fun s hs => ?_⟩
  obtain ⟨hsd, x, hx, ex⟩ := hsegP s hs
  have hav := hseg.1 s hs
  refine ⟨⟨⟨x, mem_pdarts.2 ⟨hx, fun ⟨H, hH, ht, _⟩ => ?_⟩⟩, ex⟩,
    fun e he => mem_pdarts.2 ⟨hsd e he, fun ⟨H, hH, ht, _⟩ => ?_⟩, hav⟩
  · exact disjoint_left.1 hav (by rw [ex]; exact s.p_mem_init le_rfl) (subset_hunion hH ht)
  · obtain ⟨i, hi, hti⟩ := SPath.tail_mem_darts s he
    exact disjoint_left.1 hav (by rw [hti]; exact s.p_mem_init hi) (subset_hunion hH ht)

variable (M) in
open Classical in
/-- **The charge of the subroutine runs of a node call** (the part of `nodeCharge` besides the
separator and the bookkeeping): FixConservationOnPath, the hole loop and the push-backs on each
part of the separator. -/
noncomputable def runsCharge (c : SubCosts) (l r : ADec M) (π : HSep M) (Hs : List (Finset V))
    (σ : Perm D) : ℕ :=
  if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
    c.nodeRuns (pdarts M (l.piece ∪ r.piece) Hs).card
      (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
      (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
      ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k))
  else 0

/-- Under the condition, `nodeCharge = sep + runsCharge + 8 lin`. -/
lemma nodeCharge_eq (c : SubCosts) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D}
    (h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧ ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s) :
    nodeCharge M c l r π Hs σ = c.sep (l.piece ∪ r.piece).card + runsCharge M c l r π Hs σ +
      8 * c.lin ((l.piece ∪ r.piece).card + Hs.length) := by
  unfold nodeCharge runsCharge
  rw [dite_of_pos h, dite_of_pos h]

variable {κ η : ℕ}

/-- **Along the calls, `#Hs + #piece` does not grow** (with `Core`: siblings disjoint and
nonempty, one new hole per level). -/
lemma calls_size : ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) (x : MCall M),
    τ.Core M κ η Hs → Calls M τ Hs σ x →
      x.2.1.length + x.1.piece.card ≤ Hs.length + τ.piece.card
  | .leaf Q, Hs, σ, x, _, hx => by subst hx; exact le_rfl
  | .node l r π, Hs, σ, x, ⟨hl, hr, hlr, hl0, hr0, _⟩, hx => by
    have hc := length_childHoles Hs π.path.mverts
    have hu : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card := card_union_of_disjoint hlr
    rcases hx with hx | hx | hx
    · subst hx; exact le_rfl
    · have := calls_size l _ _ x hl hx
      simp only [ADec.piece] at this ⊢
      omega
    · have := calls_size r _ _ x hr hx
      simp only [ADec.piece] at this ⊢
      omega

end Gen

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The fixed program with the machine subroutine costs and explicit constants** (see the
module docstring): `A = 1`, `B = 1000`, `R = 39 N + 20 + RS + RT` (`N = #τ.piece`, the darts of
the preprocessed map). -/
theorem mfDriveFrame_cMach (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {C C₀ : ℕ} (hC : 68 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP stepP : Stmt} {sT : ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    (∀ m, sT m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    0 < Hb → ∀ {eF h : ℕ} (c₀ : Config), WordsBounded W c₀ → c₀.nreg 3000 = 0 →
    c₀.nreg 3001 = 1 → c₀.nreg 3002 = Hb → c₀.nreg 3003 = h → c₀.nmem Hb = 0 →
    c₀.nmem (Hb + 1) = 0 → c₀.nmem (Hb + 2) = eF → Hb + 5 ≤ eF → eF ≤ h →
    h + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    FInL (lpreMap M) Reach gid u' S' T' Z (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver mtProg mlProg (splitS sepP) (nodeSF stepP)) c₀ c' t ∧
      t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach N hsep hstep hsT hstT hsR hrT hHb eF h c₀ hc₀ r0 r1 r2 r3 m0 m1
    m2 he hh hroom hin
  obtain ⟨hbal, hmax, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hcore := ADec.BalA.core hbal.2.2.2.2
  have hsz := asize_le hcore
  have hok0 := hin.2.1
  -- the sizes at the calls of the decomposition
  have hsize : ∀ x, Reach x → (pdarts (lpreMap M) x.1.piece x.2.1).card ≤ N ∧
      x.2.1.length ≤ N ∧ x.1.piece.card ≤ N := fun x hx => by
    have h1 := calls_size τ [] _ x hcore hx
    have h2 := card_le_card (pdarts_subset (M := lpreMap M) x.1.piece x.2.1)
    simp only [List.length_nil, zero_add] at h1
    exact ⟨by omega, by omega, by omega⟩
  -- the room
  have hR : ∀ x, Reach x → rSp (lpreMap M) sR x + rT x ≤ 39 * N + 20 + RS + RT := fun x hx => by
    obtain ⟨a1, a2, -⟩ := hsize x hx
    have := hsR _ _ a1 a2
    have := hrT x hx
    unfold rSp; omega
  have hrm := roomC_le_on (M := lpreMap M) (rL := fun _ => 0) (rS := rSp (lpreMap M) sR)
    (rN := rT) Reach (fun _ _ => Nat.zero_le _) hR τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have hsz' := Nat.mul_le_mul_right (39 * N + 20 + RS + RT) hsz
  obtain ⟨c', t, ex, ht, hout, -, -⟩ := mfDriveFrame hsep
    (fun l r π Hs σ hx => calls_child τ [] _ l r π Hs σ hx) hZ (nodeSF_spec (Hb := Hb) hstep)
    hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ r0 r1 r2 r3 m0 m1 m2 he hh
    ((Nat.add_le_add_left (hrm.trans hsz') h).trans hroom) hin
  -- the per-call costs
  have hm := mcost_le_on (M := lpreMap M) (tc := fun _ => 3)
    (lc := fun x => 20 * (pdarts (lpreMap M) x.1.piece x.2.1).card + 17)
    (sc := scp (lpreMap M) sT) (nc := ncF (lpreMap M) stT) (cMach C C₀) (A := 1) (B := 1000)
    Reach (fun Q Hs σ _ => by
      have := Nat.mul_le_mul_right (pdarts (lpreMap M) Q Hs).card hC₀
      simp only [cMach, ADec.piece]; omega)
    (fun l r π Hs σ hx => by
      have hok := callOk_calls τ [] _ _ hok0 hx
      have hcond := callOk_cond hok
      rw [nodeCharge_eq _ hcond]
      obtain ⟨a1, a2, a3⟩ := hsize _ hx
      have hs := hstT l r π Hs σ hx
      simp only [ADec.piece] at a1 a3
      set P := (l.piece ∪ r.piece).card with hP
      set m := (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card with hmdef
      have hmP : m ≤ P := card_le_card (pdarts_subset _ _)
      have e1 : sT m ≤ C * P * lg P := (hsT m).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ hmP) (lg_mono hmP))
      have e2 : 544 * m + 21 * Hs.length ≤ 8 * (C * (P + Hs.length)) := by
        have h1 : 68 * P ≤ C * P := Nat.mul_le_mul_right P hC
        have h2 : 68 * Hs.length ≤ C * Hs.length := Nat.mul_le_mul_right _ hC
        rw [Nat.mul_add C P Hs.length]
        omega
      have es : (cMach C C₀).sep P = C * P * lg P := rfl
      have el : (cMach C C₀).lin (P + Hs.length) = C * (P + Hs.length) := rfl
      rw [es, el]
      simp only [scp, ncF, ADec.piece]
      rw [← hmdef]
      omega)
    τ [] (rotPerm (lpreMap M)) (fun x hx => hx)
  have ha : arunLCost (lpreMap M) (cMach C C₀) τ [] (rotPerm (lpreMap M)) ≤
      runLCost (lpreMap M) (cMach C C₀) τ := by
    unfold runLCost; omega
  have hB : 1000 * asize τ ≤ 1000 * (2 * N + 1) := Nat.mul_le_mul_left 1000 hsz
  refine ⟨hbal.1, c', t, ex, ?_, hout, hmax⟩
  have := ha.trans hcost
  omega

end Head

end MfDrv

end BKMNW

end PlanarFlow
