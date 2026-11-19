module

public import PlanarFlow.BKMNW.NpMach

/-!
# Canonical explicit choices of the push-back

The push-back of explicit choices `pushFwdL M fr r ord outs` (`NpPushL.lean`) meets `PushSpec` for
any root `r`, any topological order `ord` (`TopoOK`) and any dart lists `outs` (`OutsOK`). Here
the choices are fixed from **a list `L` of all the darts** (for a piece map: the frame order):

* `outsL L v` (the darts of `L` with tail `v`, in the order of `L`), `outsL_ok`;
* `vertsL L` (the tails of `L`, duplicates removed), `ordRk L g` (`vertsL L` stably sorted by the
  height `rk M g` of the cancelled flow), `idxOf_lt_of_sorted`, **`ordRk_topo`** (`TopoOK`);
* **`pchL M L`** (`pushFwdL M (frRef _) (face L₀) (ordRk L) (outsL L)`, or the identity when `L`
  is empty), **`pushSpec_pchL`** (`PushSpec` on a plane map, `L` listing every dart once);
* **`pchCall gid`** (at every call: `pchL` of the darts of the piece map sorted by `gid`) and
  **`pushSpec_pchCall`**: the hypothesis `PushSpec (pmap h) (pch x h)` of `mfMain_cMachXGEF` holds
  for `pch = pchCall gid`, unconditionally.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

section Gen

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The darts of `L` leaving `v`, in the order of `L`. -/
def outsL (L : List D) (v : V) : List D := L.filter fun d => M.tail d = v

lemma outsL_ok {L : List D} (hnd : L.Nodup) (hall : ∀ d, d ∈ L) : OutsOK M (outsL M L) :=
  fun v => ⟨hnd.filter _, fun d => by simp [outsL, hall d]⟩

variable (M) in
/-- The tails of the darts of `L`, each once. -/
def vertsL (L : List D) : List V := (L.map M.tail).dedup

variable (M) in
/-- **The order of the visits**: the vertices by increasing height of the flow (stable). -/
noncomputable def ordRk (L : List D) (g : D → ℤ) : List V :=
  (vertsL M L).mergeSort fun a b => decide (rk M g a ≤ rk M g b)

/-- In a list without duplicates sorted by a key, a smaller key comes first. -/
lemma idxOf_lt_of_sorted {α : Type*} [DecidableEq α] (key : α → ℕ) :
    ∀ {L : List α}, L.Nodup → L.Pairwise (fun a b => key a ≤ key b) → ∀ {a b : α}, a ∈ L →
      b ∈ L → key a < key b → L.idxOf a < L.idxOf b
  | [], _, _, a, b, ha, _, _ => absurd ha List.not_mem_nil
  | x :: L, hnd, hpw, a, b, ha, hb, hab => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hpx, hpw'⟩ := List.pairwise_cons.1 hpw
    have hbx : x ≠ b := by
      rintro rfl
      rcases List.mem_cons.1 ha with rfl | ha'
      · omega
      · have := hpx a ha'; omega
    rw [List.idxOf_cons, List.idxOf_cons]
    simp only [beq_iff_eq, hbx, ↓reduceIte]
    by_cases hax : x = a
    · simp [hax]
    · simp only [hax, ↓reduceIte]
      have ha' : a ∈ L := (List.mem_cons.1 ha).resolve_left (Ne.symm hax)
      have hb' : b ∈ L := (List.mem_cons.1 hb).resolve_left (Ne.symm hbx)
      have := idxOf_lt_of_sorted key hnd' hpw' ha' hb' hab
      omega

/-- **The order of the visits is topological** (every vertex is the tail of a dart of `L`). -/
lemma ordRk_topo {L : List D} (hall : ∀ d, d ∈ L) (hV : ∀ v : V, ∃ d, M.tail d = v) :
    TopoOK M (ordRk M L) := by
  intro g hg hac
  have hperm := List.mergeSort_perm (vertsL M L) fun a b => decide (rk M g a ≤ rk M g b)
  have hnd : (vertsL M L).Nodup := List.nodup_dedup _
  have hmem : ∀ v, v ∈ vertsL M L := fun v => by
    obtain ⟨d, rfl⟩ := hV v
    simp only [vertsL, List.mem_dedup, List.mem_map]
    exact ⟨d, hall d, rfl⟩
  have hsort := List.pairwise_mergeSort (le := fun a b => decide (rk M g a ≤ rk M g b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (vertsL M L)
  refine ⟨hperm.nodup_iff.2 hnd, fun v => hperm.mem_iff.2 (hmem v), fun d hd => ?_⟩
  exact idxOf_lt_of_sorted (rk M g) (hperm.nodup_iff.2 hnd)
    (hsort.imp fun h => by simpa using h) (hperm.mem_iff.2 (hmem _)) (hperm.mem_iff.2 (hmem _))
    (rk_lt hac hd)

variable (M) in
/-- **The machine's push-back from a list of the darts**: the cancellation from the face of the
first dart, the visits by height, the darts in the order of the list (the identity when there is
no dart). -/
noncomputable def pchL (L : List D) : PushFn D V :=
  match L with
  | [] => fun _ _ g => g
  | d :: L' => pushFwdL M (frRef _) (M.face d) (ordRk M (d :: L')) (outsL M (d :: L'))

/-- On a map without darts the identity meets `PushSpec`. -/
lemma pushSpec_id_of_isEmpty (hD : IsEmpty D) : PushSpec M (fun _ _ g => g) := by
  intro c g hc hg β Fr W hW hout hin
  have hdiv : ∀ (h : D → ℤ) v, M.div h v = 0 := fun h v => by
    simp [CombMap.div, Finset.univ_eq_empty]
  refine ⟨hg, Conf.refl g, fun v hv => ?_, fun v hv => ?_, fun v _ => le_rfl⟩
  · rw [hdiv]
    by_cases hvW : v ∈ W
    · exact hin v hvW hv
    · have := hout v hvW hv; rw [hdiv] at this; exact this
  · rw [hdiv]; exact min_le_left _ _

/-- **The machine's push-back meets `PushSpec`** on a plane map, for a list of all the darts
without duplicates. -/
theorem pushSpec_pchL (hM : M.IsPlane) {L : List D} (hnd : L.Nodup) (hall : ∀ d, d ∈ L) :
    PushSpec M (pchL M L) := by
  cases L with
  | nil =>
    show PushSpec M (fun _ _ g => g)
    exact pushSpec_id_of_isEmpty (M := M) ⟨fun d => absurd (hall d) List.not_mem_nil⟩
  | cons d L' =>
    have hV : ∀ v : V, ∃ d, M.tail d = v := fun v => by
      rcases Relation.ReflTransGen.cases_head (hM.conn v (M.tail d)) with h | ⟨w, ⟨d'', h1, -⟩, -⟩
      · exact ⟨d, h.symm⟩
      · exact ⟨d'', h1⟩
    show PushSpec M (pushFwdL M (frRef _) (M.face d) (ordRk M (d :: L')) (outsL M (d :: L')))
    exact pushSpec_pushFwdL hM (frRef_spec _) _ (ordRk_topo hall hV) (outsL_ok hnd hall)

end Gen

namespace NsStep

open MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The machine's push-back at every call**: `pchL` of the darts of the piece map sorted by
`gid` (stable sort of `univ.toList`; for `gid` injective on the piece, this is the frame order). -/
noncomputable def pchCall (gid : D → ℕ) (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2) :
    PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1)) :=
  pchL (pmap h) ((Finset.univ : Finset (Orbit.SDart (pdarts M x.1.piece x.2.1))).toList.mergeSort
    fun a b => decide (gid a.1 ≤ gid b.1))

/-- **`pchCall` meets `PushSpec`** on every plane piece map (the hypothesis of
`mfMain_cMachXGEF` on the push-back). -/
theorem pushSpec_pchCall (gid : D → ℕ) (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap h).IsPlane) : PushSpec (pmap h) (pchCall gid x h) := by
  have hperm := List.mergeSort_perm
    ((Finset.univ : Finset (Orbit.SDart (pdarts M x.1.piece x.2.1))).toList)
    fun a b => decide (gid a.1 ≤ gid b.1)
  intro c g hc hg β Fr W hW hout hin
  exact pushSpec_pchL (M := pmap h) hpl (hperm.nodup_iff.2 (Finset.nodup_toList _))
    (fun d => hperm.mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ d))) hc hg hW hout hin

end NsStep

end BKMNW

end PlanarFlow
