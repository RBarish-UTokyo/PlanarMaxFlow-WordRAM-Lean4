module

public import PlanarFlow.BKMNW.NrComm
public import PlanarFlow.NegSSSP.Enc.DkRun

/-!
# One pass of the cancellation from Dijkstra's distances in memory (math)

The cancellation `cancelR M fr r g` is two passes `cpass M fr r`, each adding the coboundary of
the dual distances `dualDijkstra M fr (canLen g) r` (FR-Dijkstra with no dense distance graph).
A machine runs `NegSSSP.dkProg` on the dual graph with the faces numbered by keys `key i < n` of
the darts `ed i` (`i < m`), the out-list of a key listing the darts of that face, the head of the
arc `i` the key of its reverse dart, its length `canLen g`:

* `nr_walk_nodup` (a walk contains a walk without repeated arcs), `nr_wlen_le_sum`;
* `nr_dk_reach_walk`, `nr_walk_dk_reach` (`DkReach` ↔ walks of the dual graph);
* **`nr_dk_isDist`**: the distances of `dkProg` (as `Option ℤ`, `Inf` = unreached) meet
  `IsDist (M.dualGraph ℓ) (face (ed 0))`, when `Σ ℓ < Inf`;
* **`nr_dk_dual`**: on a plane map, `(dualDijkstra M fr ℓ r y).getD 0 = D[fk y]` for every face,
  **`nr_dk_cpass`**: `cpass M fr r g e = g e + D[fk (face (rev e))] - D[fk (face e)]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap NegSSSP

/-! ### Walks without repeated arcs -/

section Walk

variable {X A : Type*} {G : Digraph X A}

/-- **A walk contains a walk without repeated arcs** between the same ends. -/
lemma nr_walk_nodup [DecidableEq A] : ∀ (l : List A) {x y : X}, IsWalk G x l y →
    ∃ l', l'.Nodup ∧ (∀ a ∈ l', a ∈ l) ∧ IsWalk G x l' y
  | [], x, y, h => ⟨[], List.nodup_nil, fun _ h => h, h⟩
  | a :: l, x, y, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨l', hnd, hsub, hw⟩ := nr_walk_nodup l h2
    by_cases ha : a ∈ l'
    · obtain ⟨p, q, rfl⟩ := List.append_of_mem ha
      obtain ⟨z, -, hz⟩ := isWalk_append_iff.1 hw
      obtain ⟨hz1, hz2⟩ := hz
      refine ⟨a :: q, ?_, fun b hb => ?_, ⟨h1, hz2⟩⟩
      · have := List.nodup_append.1 hnd
        exact this.2.1
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub b (List.mem_append_right _ (List.mem_cons_of_mem _ hb)))
    · exact ⟨a :: l', List.nodup_cons.2 ⟨ha, hnd⟩, fun b hb => by
        rcases List.mem_cons.1 hb with rfl | hb
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub b hb), ⟨h1, hw⟩⟩

/-- The length of a walk without repeated arcs and nonnegative lengths is at most the sum of all
the lengths. -/
lemma nr_wlen_le_sum [Fintype A] [DecidableEq A] (hG : ∀ a, 0 ≤ G.len a) {l : List A}
    (hl : l.Nodup) : wlen G l ≤ ∑ a, G.len a := by
  unfold wlen
  rw [← List.sum_toFinset _ hl]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hG a

end Walk

/-! ### Dijkstra's walks and the walks of the dual graph -/

section Dual

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The numbering of the faces of a map by keys of darts** (`i < m` the darts `ed i`):
every dart and every face numbered, two darts on the same face iff same key, `fk` the key of a
face, `rv` the index of the reverse dart. -/
structure FKey (M : CombMap D V F) (m n : ℕ) (ed : ℕ → D) (rv key : ℕ → ℕ) (fk : F → ℕ) :
    Prop where
  surj : ∀ x, ∃ i < m, ed i = x
  rv : ∀ i < m, rv i < m ∧ ed (rv i) = M.rev (ed i)
  fkey : ∀ i < m, fk (M.face (ed i)) = key i
  key_lt : ∀ i < m, key i < n
  fk_inj : ∀ x y, fk x = fk y → x = y
  face_surj : ∀ y : F, ∃ i < m, M.face (ed i) = y

/-- **The arcs of Dijkstra** in the dual graph: the out-list of the key `y` the darts of that face
(every dart in the out-list of its key), the head of the arc `j` the key of its reverse dart, the
length `ℓ`. -/
structure DkDual (p : DkP) (m : ℕ) (ed : ℕ → D) (rv key : ℕ → ℕ) (ℓ : D → ℤ) : Prop where
  arc : ∀ y < p.n, ∀ i, p.ob y ≤ i → i < p.oe y → p.ol i < m ∧ key (p.ol i) = y
  all : ∀ j < m, ∃ i, p.ob (key j) ≤ i ∧ i < p.oe (key j) ∧ p.ol i = j
  nh : ∀ j < m, p.nh j = key (rv j)
  ln : ∀ j < m, (p.ln j : ℤ) = ℓ (ed j)

variable {m n : ℕ} {ed : ℕ → D} {rv key : ℕ → ℕ} {fk : F → ℕ} {ℓ : D → ℤ} {p : DkP}

lemma nr_dk_reach_walk (hK : FKey M m n ed rv key fk) (hA : DkDual p m ed rv key ℓ)
    (hs : p.s = key 0) (h0 : 0 < m) {y L : ℕ} (hr : DkReach p y L) :
    ∃ x, fk x = y ∧ ∃ l, IsWalk (M.dualGraph ℓ) (M.face (ed 0)) l x ∧
      wlen (M.dualGraph ℓ) l = L := by
  induction hr with
  | src => exact ⟨M.face (ed 0), by rw [hK.fkey 0 h0, hs], [], rfl, by simp⟩
  | @step u L i _ hu h1 h2 ih =>
    obtain ⟨x, hx, l, hl, hw⟩ := ih
    obtain ⟨hj, hkj⟩ := hA.arc u hu i h1 h2
    set j := p.ol i
    have hxj : x = M.face (ed j) := hK.fk_inj _ _ (by rw [hx, hK.fkey j hj, hkj])
    obtain ⟨hrv, hed⟩ := hK.rv j hj
    refine ⟨M.face (M.rev (ed j)), ?_, l ++ [ed j], hl.append ⟨hxj.symm, rfl⟩, ?_⟩
    · rw [← hed, hK.fkey _ hrv, hA.nh j hj]
    · rw [wlen_append, hw]
      simp only [wlen_cons, wlen_nil, add_zero, Nat.cast_add]
      rw [hA.ln j hj]; rfl

lemma nr_walk_dk_reach (hK : FKey M m n ed rv key fk) (hA : DkDual p m ed rv key ℓ)
    (hn : p.n = n) (hℓ : ∀ d, 0 ≤ ℓ d) :
    ∀ (l : List D) (x z : F), IsWalk (M.dualGraph ℓ) x l z → ∀ L, DkReach p (fk x) L →
      DkReach p (fk z) (L + (wlen (M.dualGraph ℓ) l).toNat)
  | [], x, z, h, L, hr => by rw [← h]; simpa using hr
  | a :: l, x, z, h, L, hr => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨j, hj, rfl⟩ := hK.surj a
    obtain ⟨i, i1, i2, i3⟩ := hA.all j hj
    have hkx : fk x = key j := by rw [← h1]; exact hK.fkey j hj
    have hlt : key j < p.n := by rw [hn]; exact hK.key_lt j hj
    have hs := DkReach.step (p := p) (by rw [hkx] at hr; exact hr) hlt i1 i2
    rw [i3, hA.nh j hj] at hs
    obtain ⟨hrv, hed⟩ := hK.rv j hj
    have hk2 : key (rv j) = fk ((M.dualGraph ℓ).dst (ed j)) := by
      show _ = fk (M.face (M.rev (ed j))); rw [← hed, hK.fkey _ hrv]
    rw [hk2] at hs
    have := nr_walk_dk_reach hK hA hn hℓ l _ z h2 _ hs
    have hw : 0 ≤ wlen (M.dualGraph ℓ) l := List.sum_nonneg (by simp; exact fun a _ => hℓ a)
    have hln : (p.ln j : ℤ) = ℓ (ed j) := hA.ln j hj
    have hlj := hℓ (ed j)
    rw [wlen_cons]
    have e : (L + p.ln j + (wlen (M.dualGraph ℓ) l).toNat) =
        L + ((M.dualGraph ℓ).len (ed j) + wlen (M.dualGraph ℓ) l).toNat := by
      show _ = L + (ℓ (ed j) + wlen (M.dualGraph ℓ) l).toNat
      omega
    rw [← e]; exact this

/-- **Dijkstra's distances in the dual graph** (see the module docstring). -/
theorem nr_dk_isDist (hK : FKey M m n ed rv key fk) (hA : DkDual p m ed rv key ℓ)
    (hn : p.n = n) (hs : p.s = key 0) (h0 : 0 < m) (hℓ : ∀ d, 0 ≤ ℓ d)
    {Dv : ℕ → ℕ} (hD : ∀ y < n, Dv y ≤ p.Inf ∧ (Dv y < p.Inf → DkReach p y (Dv y)) ∧
      ∀ L, DkReach p y L → Dv y ≤ L)
    (hInf : ∑ d, ℓ d < p.Inf) :
    IsDist (M.dualGraph ℓ) (M.face (ed 0))
      (fun y => if Dv (fk y) < p.Inf then some (Dv (fk y) : ℤ) else none) := by
  have hsrc : DkReach p (fk (M.face (ed 0))) 0 := by rw [hK.fkey 0 h0, ← hs]; exact DkReach.src
  have hfk : ∀ y : F, fk y < n := fun y => by
    obtain ⟨i, hi, rfl⟩ := hK.face_surj y
    rw [hK.fkey i hi]; exact hK.key_lt i hi
  have hw0 : ∀ l : List D, 0 ≤ wlen (M.dualGraph ℓ) l :=
    fun l => List.sum_nonneg (by simp; exact fun a _ => hℓ a)
  refine ⟨fun y L hy => ?_, fun y L hy l hl => ?_, fun y hy l hl => ?_⟩
  · split_ifs at hy with hlt
    cases hy
    obtain ⟨x, hx, l, hl, hw⟩ := nr_dk_reach_walk hK hA hs h0 ((hD _ (hfk y)).2.1 hlt)
    rw [hK.fk_inj _ _ hx] at hl
    exact ⟨l, hl, hw⟩
  · split_ifs at hy with hlt
    cases hy
    have := (hD _ (hfk y)).2.2 _ (nr_walk_dk_reach hK hA hn hℓ l _ y hl 0 hsrc)
    have := hw0 l
    omega
  · split_ifs at hy with hlt
    obtain ⟨l', hnd, -, hl'⟩ := nr_walk_nodup l hl
    have h1 := (hD _ (hfk y)).2.2 _ (nr_walk_dk_reach hK hA hn hℓ l' _ y hl' 0 hsrc)
    have h2 := nr_wlen_le_sum (G := M.dualGraph ℓ) hℓ hnd
    have h3 := hw0 l'
    have h4 : ∑ a, (M.dualGraph ℓ).len a = ∑ d, ℓ d := rfl
    omega

/-- **FR-Dijkstra's distances are Dijkstra's** on a plane map: every face reached (`< Inf`). -/
theorem nr_dk_dual (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr)
    (hK : FKey M m n ed rv key fk) (hA : DkDual p m ed rv key ℓ)
    (hn : p.n = n) (hs : p.s = key 0) (h0 : 0 < m) (hℓ : ∀ d, 0 ≤ ℓ d)
    {Dv : ℕ → ℕ} (hD : ∀ y < n, Dv y ≤ p.Inf ∧ (Dv y < p.Inf → DkReach p y (Dv y)) ∧
      ∀ L, DkReach p y L → Dv y ≤ L)
    (hInf : ∑ d, ℓ d < p.Inf) (y : F) :
    Dv (fk y) < p.Inf ∧ (dualDijkstra M fr ℓ (M.face (ed 0)) y).getD 0 = Dv (fk y) := by
  have h1 := nr_dk_isDist hK hA hn hs h0 hℓ hD hInf
  have h2 := isDist_dualDijkstra (M := M) hfr hℓ (M.face (ed 0))
  have e := h2.unique h1
  have hne := dist_ne_none hM h1 y
  have hlt : Dv (fk y) < p.Inf := by
    by_contra h; exact hne (by simp only [h, ite_false])
  refine ⟨hlt, ?_⟩
  rw [e]; simp [hlt]

/-- **One pass of the cancellation from Dijkstra's distances**. -/
theorem nr_dk_cpass (hM : M.IsPlane) {fr : FRFun F} (hfr : FRSpec fr) {g : D → ℤ}
    (hK : FKey M m n ed rv key fk) (hA : DkDual p m ed rv key (canLen g))
    (hn : p.n = n) (hs : p.s = key 0) (h0 : 0 < m)
    {Dv : ℕ → ℕ} (hD : ∀ y < n, Dv y ≤ p.Inf ∧ (Dv y < p.Inf → DkReach p y (Dv y)) ∧
      ∀ L, DkReach p y L → Dv y ≤ L)
    (hInf : ∑ d, canLen g d < p.Inf) (e : D) :
    cpass M fr (M.face (ed 0)) g e =
      g e + Dv (fk (M.face (M.rev e))) - Dv (fk (M.face e)) := by
  unfold cpass
  simp only [Pi.add_apply, cob]
  rw [(nr_dk_dual hM hfr hK hA hn hs h0 (canLen_nonneg g) hD hInf _).2,
    (nr_dk_dual hM hfr hK hA hn hs h0 (canLen_nonneg g) hD hInf _).2]
  ring

end Dual

end BKMNW

end PlanarFlow
