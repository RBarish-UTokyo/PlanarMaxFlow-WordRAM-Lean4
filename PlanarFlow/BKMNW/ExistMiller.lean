module

public import PlanarFlow.BKMNW.ExistJordan
public import PlanarFlow.BKMNW.Triangulate

/-!
# Miller's theorem on a piece map with small faces

* `PlanarFlow.BKMNW.psep`: the piece map of a set `B` of darts with a rotation `σ`, as a map of
  `PlanarSeparator` (vertices the orbits of `σ`); it is plane when `B` is connected with zero Euler
  gap (`PlanarFlow.BKMNW.psep_isPlane`).
* `PlanarSeparator.Map.stellar_cycle_path`: **a cycle of the stellar subdivision of a map with
  small faces is a sequence of distinct vertices of the map joined by darts**: a passage
  `a → centre → b` through the centre of a face of at most three darts is replaced by the dart of
  the face between `a` and `b`.
* `PlanarFlow.BKMNW.exists_core_cycle`: **Miller's theorem on a piece map with small faces**: a
  simple path through the holes of at most `6 √(2 m) + 4` vertices (`m` darts) and two sides with
  no dart between them, each weighing at most `(2 W + 2) / 3 + 3 (6 √(2 m) + 4)` for weights at most
  one on the darts and any weights on the vertices of the piece map.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Map

open Finset StDart

variable {X Q : Type*} [Fintype X] [DecidableEq X] {N : Map X Q}

/-- The dart of the map under a dart of the stellar subdivision. -/
def stU : StDart X → X
  | old e => e
  | up e => e
  | down e => e

/-- The darts of the stellar subdivision leaving a centre. -/
def IsDn : StDart X → Prop
  | down _ => True
  | _ => False

/-- The spokes leaving a vertex of the map. -/
def IsUp : StDart X → Prop
  | up _ => True
  | _ => False

instance (δ : StDart X) : Decidable (IsUp δ) := by cases δ <;> simp [IsUp] <;> infer_instance

lemma stellar_vert_of_not_dn {δ : StDart X} (h : ¬ IsDn δ) :
    N.stellar.vert δ = .inl (N.vert (stU δ)) := by
  cases δ <;> simp_all [stU, IsDn]

/-- **A cycle of the stellar subdivision of a map with small faces, as a sequence of distinct
vertices of the map joined by darts**: the vertices of the map on the cycle, in order, are the
tails of darts `e 0, …, e (n - 1)`, the head of `e j` being the tail of `e (j + 1)`. A passage
`a → centre → b` of the cycle through the centre of a face is replaced by the dart of the face
between `a` and `b`. -/
theorem stellar_cycle_path (hl : ∀ d, N.vert (N.α d) ≠ N.vert d)
    (hsm : ∀ x y, N.face x = N.face y → y = x ∨ y = N.φ x ∨ y = N.φ.symm x)
    (C : N.stellar.SCycle) :
    ∃ (n : ℕ) (e : ℕ → X), 0 < n ∧ n ≤ C.k ∧
      (∀ j, j + 1 < n → N.vert (N.α (e j)) = N.vert (e (j + 1))) ∧
      (∀ i < n, ∀ j < n, N.vert (e i) = N.vert (e j) → i = j) ∧
      (∀ q : Q, (∃ i < C.k, N.stellar.vert (C.d i) = .inl q) ↔ ∃ j < n, N.vert (e j) = q) := by
  classical
  set K := C.k with hKdef
  have hK1 : 0 < K := C.pos
  have hK2 : 2 ≤ K := by
    by_contra h
    have hK : K = 1 := by omega
    have := C.vert_α 0 hK1
    rw [← hKdef, hK, Nat.mod_self] at this
    exact stellar_loopless hl (C.d 0) this
  -- the cycle starting at a vertex of the map
  have hchain0 : ∀ i, N.stellar.vert (N.stellar.α (C.d (i % K))) =
      N.stellar.vert (C.d ((i + 1) % K)) := by
    intro i
    rw [C.vert_α _ (Nat.mod_lt _ hK1), Nat.add_mod (i % K), Nat.mod_mod, ← Nat.add_mod]
  have hnext_dn : ∀ i, IsDn (C.d (i % K)) → ¬ IsDn (C.d ((i + 1) % K)) := by
    intro i h h'
    have := hchain0 i
    revert this h h'
    generalize C.d (i % K) = a
    generalize C.d ((i + 1) % K) = b
    cases a <;> cases b <;> simp [IsDn]
  obtain ⟨s, hsK, hs⟩ : ∃ s < K, ¬ IsDn (C.d s) := by
    by_cases h : IsDn (C.d 0)
    · refine ⟨1, by omega, ?_⟩
      have := hnext_dn 0 (by rwa [Nat.zero_mod])
      rwa [zero_add, Nat.mod_eq_of_lt (by omega)] at this
    · exact ⟨0, hK1, h⟩
  set δ : ℕ → StDart X := fun i => C.d ((s + i) % K) with hδ
  have hchain : ∀ i, N.stellar.vert (N.stellar.α (δ i)) = N.stellar.vert (δ (i + 1)) := by
    intro i
    simp only [hδ]
    rw [show s + (i + 1) = s + i + 1 by ring]
    exact hchain0 (s + i)
  have hδ0 : ¬ IsDn (δ 0) := by simpa [hδ, Nat.mod_eq_of_lt hsK] using hs
  have fa : ∀ i e, δ i = up e → ∃ e', δ (i + 1) = down e' ∧ N.face e' = N.face e := by
    intro i e h
    have := hchain i
    rw [h] at this
    revert this
    generalize δ (i + 1) = b
    cases b <;> simp
    intro h'; exact h'.symm
  have fb : ∀ i e', δ i = down e' → ¬ IsDn (δ (i + 1)) ∧ N.vert (stU (δ (i + 1))) = N.vert e' := by
    intro i e' h
    have := hchain i
    rw [h] at this
    revert this
    generalize δ (i + 1) = b
    cases b <;> simp [IsDn, stU]
    · intro h'; exact h'.symm
    · intro h'; exact h'.symm
  have fc : ∀ i e, δ i = old e → ¬ IsDn (δ (i + 1)) ∧
      N.vert (stU (δ (i + 1))) = N.vert (N.α e) := by
    intro i e h
    have := hchain i
    rw [h] at this
    revert this
    generalize δ (i + 1) = b
    cases b <;> simp [IsDn, stU]
    · intro h'; exact h'.symm
    · intro h'; exact h'.symm
  have hinj : ∀ i < K, ∀ j < K, N.stellar.vert (δ i) = N.stellar.vert (δ j) → i = j := by
    intro i hi j hj h
    have := C.inj _ (Nat.mod_lt _ hK1) _ (Nat.mod_lt _ hK1) h
    have h2 : (s + i) ≡ (s + j) [MOD K] := this
    have h3 := Nat.ModEq.add_left_cancel' s h2
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h3
  have hup_of : ∀ t, IsDn (δ (t + 1)) → IsUp (δ t) := by
    intro t h
    generalize hd : δ t = d0
    cases d0 with
    | old e0 => exact absurd h (fc t e0 hd).1
    | up e0 => trivial
    | down e0 => exact absurd h (fb t e0 hd).1
  -- the positions of the vertices of the map on the cycle
  set stp : StDart X → ℕ := fun δ' => if IsUp δ' then 2 else 1 with hstp
  set g : ℕ → ℕ := fun j => Nat.rec 0 (fun _ gj => gj + stp (δ gj)) j with hg
  have g0 : g 0 = 0 := rfl
  have gs : ∀ j, g (j + 1) = g j + stp (δ (g j)) := fun j => rfl
  have stp_pos : ∀ δ', 1 ≤ stp δ' := fun δ' => by simp only [hstp]; split_ifs <;> omega
  have g_ge : ∀ j, j ≤ g j := by
    intro j
    induction j with
    | zero => simp [g0]
    | succ j ih => rw [gs]; have := stp_pos (δ (g j)); omega
  have g_lt : ∀ i j, i < j → g i < g j := by
    intro i j hij
    induction j with
    | zero => omega
    | succ j ih =>
      rw [gs]
      have := stp_pos (δ (g j))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · have := ih h; omega
      · subst h; omega
  have hex : ∃ j, K ≤ g j := ⟨K, g_ge K⟩
  set n := Nat.find hex with hn
  have hgn : ∀ j < n, g j < K := fun j hj => by have := Nat.find_min hex hj; omega
  have hn0 : 0 < n := by
    rw [hn, Nat.pos_iff_ne_zero, Ne, Nat.find_eq_zero]; simp only [g0]; omega
  have hnK : n ≤ K := Nat.find_le (g_ge K)
  have hgs_up : ∀ j e0, δ (g j) = up e0 → g (j + 1) = g j + 1 + 1 := by
    intro j e0 h; rw [gs, h]; simp [hstp, IsUp]
  have hgs_old : ∀ j e0, δ (g j) = old e0 → g (j + 1) = g j + 1 := by
    intro j e0 h; rw [gs, h]; simp [hstp, IsUp]
  have hnd : ∀ j, g j < K → ¬ IsDn (δ (g j)) := by
    intro j
    induction j with
    | zero => intro _; simpa [g0] using hδ0
    | succ j ih =>
      intro hj
      have hdj := ih (lt_trans (g_lt j (j + 1) (Nat.lt_succ_self j)) hj)
      generalize hd : δ (g j) = d0 at hdj
      cases d0 with
      | old e0 => rw [hgs_old j e0 hd]; exact (fc (g j) e0 hd).1
      | up e0 =>
        obtain ⟨e', h1, -⟩ := fa (g j) e0 hd
        rw [hgs_up j e0 hd]; exact (fb (g j + 1) e' h1).1
      | down e0 => exact absurd trivial hdj
  set e : ℕ → X := fun j =>
    if j + 1 < n ∧ IsUp (δ (g j)) then
      (if N.vert (N.φ (stU (δ (g j)))) = N.vert (stU (δ (g j + 1))) then stU (δ (g j))
        else N.α (stU (δ (g j + 1))))
    else stU (δ (g j)) with he
  have hsv : ∀ j, g j < K → N.stellar.vert (δ (g j)) = .inl (N.vert (stU (δ (g j)))) :=
    fun j hj => stellar_vert_of_not_dn (hnd j hj)
  have hev : ∀ j < n, N.vert (e j) = N.vert (stU (δ (g j))) := by
    intro j hj
    simp only [he]
    split_ifs with h1 h2
    · rfl
    · obtain ⟨hj1, hup⟩ := h1
      obtain ⟨e0, he0⟩ : ∃ e0, δ (g j) = up e0 := by
        revert hup; generalize δ (g j) = d0; cases d0 <;> simp [IsUp]
      obtain ⟨e', h1', hf'⟩ := fa (g j) e0 he0
      rw [he0, h1'] at h2 ⊢
      simp only [stU] at h2 ⊢
      rcases hsm e0 e' hf'.symm with rfl | rfl | rfl
      · exfalso
        have hlt : g j + 1 + 1 < K := hgs_up j _ he0 ▸ hgn (j + 1) hj1
        have h3 := fb (g j + 1) _ h1'
        have := hinj (g j) (by omega) (g j + 1 + 1) hlt (by
          rw [he0, stellar_vert_of_not_dn h3.1, h3.2]; rfl)
        omega
      · exact absurd rfl h2
      · rw [← N.vert_φ, Equiv.apply_symm_apply]
    · rfl
  have hch : ∀ j, j + 1 < n → N.vert (N.α (e j)) = N.vert (e (j + 1)) := by
    intro j hj
    rw [hev (j + 1) hj]
    have hgj : g j < K := hgn j (by omega)
    have hd := hnd j hgj
    generalize hd0 : δ (g j) = d0 at hd
    cases d0 with
    | old e0 =>
      have : e j = e0 := by simp [he, hd0, IsUp, stU]
      rw [this, hgs_old j e0 hd0, (fc (g j) e0 hd0).2]
    | up e0 =>
      obtain ⟨e', h1, -⟩ := fa (g j) e0 hd0
      rw [hgs_up j e0 hd0, (fb (g j + 1) e' h1).2]
      simp only [he, hd0, h1, stU, IsUp, hj, and_self, ite_true]
      split_ifs with h2
      · rw [← N.vert_φ]; exact h2
      · rw [N.α_α]
    | down e0 => exact absurd trivial hd
  have hdis : ∀ i < n, ∀ j < n, N.vert (e i) = N.vert (e j) → i = j := by
    intro i hi j hj h
    rw [hev i hi, hev j hj] at h
    have := hinj (g i) (hgn i hi) (g j) (hgn j hj) (by
      rw [hsv i (hgn i hi), hsv j (hgn j hj), h])
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd this (g_lt _ _ h').ne
    · exact absurd this (g_lt _ _ h').ne'
  have hcov : ∀ t < K, ¬ IsDn (δ t) → ∃ j, g j = t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro ht hnt
    rcases t with _ | t
    · exact ⟨0, g0⟩
    · by_cases hp : IsDn (δ t)
      · rcases t with _ | t
        · exact absurd hp hδ0
        · have hup : IsUp (δ t) := hup_of t hp
          have hnd' : ¬ IsDn (δ t) := by
            revert hup; generalize δ t = d0; cases d0 <;> simp [IsUp, IsDn]
          obtain ⟨j, hj⟩ := ih t (by omega) (by omega) hnd'
          exact ⟨j + 1, by rw [gs, hj]; simp [hstp, hup]⟩
      · obtain ⟨j, hj⟩ := ih t (by omega) (by omega) hp
        have hnu : ¬ IsUp (δ t) := fun hu => by
          obtain ⟨e0, he0⟩ : ∃ e0, δ t = up e0 := by
            revert hu; generalize δ t = d0; cases d0 <;> simp [IsUp]
          obtain ⟨e', h1, -⟩ := fa t e0 he0
          exact hnt (by rw [h1]; trivial)
        exact ⟨j + 1, by rw [gs, hj]; simp [hstp, hnu]⟩
  refine ⟨n, e, hn0, hnK, hch, hdis, fun q => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi, hq⟩
    set t := (i + (K - s)) % K with ht
    have hst : (s + t) % K = i := by
      rw [ht, Nat.add_mod_mod, show s + (i + (K - s)) = i + K by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    have hδt : δ t = C.d i := by simp only [hδ, hst]
    have hnt : ¬ IsDn (δ t) := by
      rw [hδt]; intro h
      revert hq h; generalize C.d i = d0; cases d0 <;> simp [IsDn]
    obtain ⟨j, hj⟩ := hcov t (Nat.mod_lt _ hK1) hnt
    have hjn : j < n := by
      by_contra h'
      push Not at h'
      have h1 : K ≤ g n := by rw [hn]; exact Nat.find_spec hex
      have h2 : g n ≤ g j := by
        rcases Nat.eq_or_lt_of_le h' with h'' | h''
        · rw [h'']
        · exact (g_lt _ _ h'').le
      have : t < K := Nat.mod_lt _ hK1
      omega
    refine ⟨j, hjn, ?_⟩
    rw [hev j hjn, hj]
    have := stellar_vert_of_not_dn (N := N) hnt
    rw [hδt, hq] at this
    rw [hδt]
    exact (Sum.inl.inj this).symm
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(s + g j) % K, Nat.mod_lt _ hK1, ?_⟩
    have := hsv j (hgn j hj)
    rw [hev j hj]
    exact this

end Map

end PlanarSeparator

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.StDart

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

section PSep

variable {σ : Perm D} {B : Finset D} (hσ : Stable σ B) (hB : Stable (revPerm M) B)

variable (M) in
/-- **The piece map of the darts `B` with rotation `σ`**, as a map of `PlanarSeparator`: darts the
darts of `B`, vertices the orbits of `σ`. -/
noncomputable def psep : PlanarSeparator.Map (SDart B) (SVert σ B) :=
  (subMap B (revPerm_isInv M) hσ hB).toSep (subMap_rotTrans (revPerm_isInv M) hσ hB)

@[simp] lemma psep_α (x : SDart B) : ((psep M hσ hB).α x).1 = M.rev x.1 := rfl

@[simp] lemma psep_σ (x : SDart B) : ((psep M hσ hB).σ x).1 = σ x.1 := by
  simp [psep]

lemma psep_vert (x : SDart B) : (psep M hσ hB).vert x = Quotient.mk _ x := rfl

lemma psep_vert_eq {x y : SDart B} :
    (psep M hσ hB).vert x = (psep M hσ hB).vert y ↔ σ.SameCycle x.1 y.1 := sVert_eq_iff

@[simp] lemma psep_φ (x : SDart B) : ((psep M hσ hB).φ x).1 = σ (M.rev x.1) := by
  simp [psep, PlanarSeparator.Map.φ_apply]

lemma psep_φ_pow (n : ℕ) (x : SDart B) :
    (((psep M hσ hB).φ ^ n) x).1 = ((σ * revPerm M)^[n]) x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Perm.mul_apply, ih, psep_φ, iterate_succ_apply]
    rfl

lemma psep_φ_symm (x : SDart B) : ((psep M hσ hB).φ.symm x).1 = (σ * revPerm M).symm x.1 := by
  have h := psep_φ hσ hB ((psep M hσ hB).φ.symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [Equiv.eq_symm_apply, Perm.mul_apply]; exact h.symm

lemma psep_face_eq {x y : SDart B} :
    (psep M hσ hB).face x = (psep M hσ hB).face y ↔ (σ * revPerm M).SameCycle x.1 y.1 := by
  rw [PlanarSeparator.Map.face_eq_face_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact sameCycle_iff.2 ⟨n, by rw [← psep_φ_pow hσ hB, hn]⟩
  · intro h
    obtain ⟨n, hn⟩ := sameCycle_iff.1 h
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext (by rw [psep_φ_pow hσ hB, hn])

/-- **The piece map is plane** when the darts are connected and the Euler gap vanishes. -/
theorem psep_isPlane {x₀ : D} (hx₀ : x₀ ∈ B)
    (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn (revPerm M) σ x y) (h0 : gap (revPerm M) σ B = 0) :
    (psep M hσ hB).IsPlane := by
  have : Nonempty (SDart B) := ⟨⟨x₀, hx₀⟩⟩
  exact toSep_isPlane (subMap_isPlane (revPerm_isInv M) hσ hB hx₀ hconn h0)
    (subMap_rotTrans (revPerm_isInv M) hσ hB) (subMap_faceTrans (revPerm_isInv M) hσ hB)

end PSep

/-- The number of vertices and of faces of the piece map are at most its number of darts. -/
lemma card_psep_le {σ : Perm D} {B : Finset D} (hσ : Stable σ B) (hB : Stable (revPerm M) B) :
    Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face ≤ 2 * B.card := by
  have h1 : Fintype.card (SVert σ B) ≤ Fintype.card (SDart B) :=
    Fintype.card_le_of_surjective _ Quotient.mk_surjective
  have h2 : Fintype.card (psep M hσ hB).Face ≤ Fintype.card (SDart B) :=
    Fintype.card_le_of_surjective _ (psep M hσ hB).face_surjective
  have h3 : Fintype.card (SDart B) = B.card := Fintype.card_coe B
  omega

open Classical PlanarSeparator.Map in
/-- **Miller's theorem on a piece map with small faces.** Let `B` be the darts of a plane piece map
(rotation `σ`, orbits the vertices of `M` with the holes `Hs` contracted, no loop) all of whose
faces are small, with weights `wd ≤ 1` on the darts and `wq` on the vertices of the piece map, of
total `W`. Then there is a simple path `ρ` through the holes, along darts of `B`, through at most
`6 √(2 #B) + 4` vertices, and two disjoint sets `I`, `O` of vertices of the piece map, the vertices
off the path, with no dart between them, such that the darts with an end in `I` with the vertices
of `I` weigh at most `(2 W + 2) / 3 + 3 (6 √(2 #B) + 4)`, and the same for `O`. The path is the
cycle of Miller's theorem on the stellar subdivision of the piece map
(`PlanarSeparator.Map.exists_short_cycle_separator_stellar`, the weight of every dart on its face)
with its passages through the centres of faces replaced by edges
(`PlanarSeparator.Map.stellar_cycle_path`); a dart with an end in `I` has its face in `I` or on the
cycle, and a face on the cycle has at most three darts. -/
theorem exists_core_cycle {σ : Perm D} {B : Finset D} (hσ : Stable σ B)
    (hB : Stable (revPerm M) B) {Hs : List (Finset V)}
    (hvert : ∀ x ∈ B, ∀ y ∈ B, σ.SameCycle x y ↔ HRel Hs (M.tail x) (M.tail y))
    {x₀ : D} (hx₀ : x₀ ∈ B) (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn (revPerm M) σ x y)
    (h0 : gap (revPerm M) σ B = 0) (hloop : ∀ x ∈ B, ¬ HRel Hs (M.head x) (M.tail x))
    (hsmall : ∀ x ∈ B, ∀ z ∈ pface M σ B x,
      z = x ∨ z = (σ * revPerm M) x ∨ z = (σ * revPerm M).symm x)
    (wd : D → ℕ) (hwd : ∀ d, wd d ≤ 1) (wq : SVert σ B → ℕ) :
    ∃ (ρ : HPath M) (I O : Finset (SVert σ B)),
      ρ.Simple Hs ∧ (∀ e ∈ ρ.darts, e ∈ B) ∧ ρ.k + 1 ≤ 6 * Nat.sqrt (2 * B.card) + 4 ∧
      (∀ j ≤ ρ.k, ∃ x ∈ B, M.tail x = ρ.p j) ∧ Disjoint I O ∧
      (∀ x : SDart B, Quotient.mk _ x ∉ I → Quotient.mk _ x ∉ O →
        ∃ j ≤ ρ.k, HRel Hs (M.tail x.1) (ρ.p j)) ∧
      (∀ x : SDart B, (Quotient.mk _ x ∈ I ∨ Quotient.mk _ x ∈ O) →
        ∀ j ≤ ρ.k, ¬ HRel Hs (M.tail x.1) (ρ.p j)) ∧
      (∀ x : SDart B, Quotient.mk _ x ∈ I → Quotient.mk _ ((psep M hσ hB).α x) ∉ O) ∧
      (∀ x : SDart B, Quotient.mk _ x ∈ O → Quotient.mk _ ((psep M hσ hB).α x) ∉ I) ∧
      3 * (∑ x : SDart B with (Quotient.mk _ x ∈ I ∨ Quotient.mk _ ((psep M hσ hB).α x) ∈ I),
          wd x.1 + ∑ q ∈ I, wq q) ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 + 9 * (6 * Nat.sqrt (2 * B.card) + 4) ∧
      3 * (∑ x : SDart B with (Quotient.mk _ x ∈ O ∨ Quotient.mk _ ((psep M hσ hB).α x) ∈ O),
          wd x.1 + ∑ q ∈ O, wq q) ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 + 9 * (6 * Nat.sqrt (2 * B.card) + 4) := by
  set N := psep M hσ hB with hNdef
  have hN : N.IsPlane := psep_isPlane hσ hB hx₀ hconn h0
  have hsc : ∀ x y : SDart B, N.vert x = N.vert y ↔ HRel Hs (M.tail x.1) (M.tail y.1) :=
    fun x y => (psep_vert_eq hσ hB).trans (hvert _ x.2 _ y.2)
  have hl : ∀ d, N.vert (N.α d) ≠ N.vert d := by
    intro d h
    rw [hsc, psep_α, CombMap.tail_rev] at h
    exact hloop d.1 d.2 h
  have hsm : ∀ x y, N.face x = N.face y → y = x ∨ y = N.φ x ∨ y = N.φ.symm x := by
    intro x y h
    have hy : y.1 ∈ pface M σ B x.1 := mem_pface.2 ⟨y.2, (psep_face_eq hσ hB).1 h⟩
    rcases hsmall x.1 x.2 y.1 hy with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext (by rw [e, psep_φ]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [e, psep_φ_symm])))
  -- the weights
  set W := ∑ x : SDart B, wd x.1 + ∑ q, wq q with hW
  set fw : N.Face → ℕ := fun f => ∑ x : SDart B with N.face x = f, wd x.1 with hfw
  set w : SVert σ B ⊕ N.Face → ℝ :=
    Sum.elim (fun q => (wq q : ℝ) / (W + 1)) (fun f => (fw f : ℝ) / (W + 1)) with hwdef
  have hWp : (0 : ℝ) < W + 1 := by positivity
  have hw0 : ∀ y, 0 ≤ w y := by intro y; cases y <;> simp only [w, Sum.elim_inl,
    Sum.elim_inr] <;> positivity
  have hfwsum : ∑ f, fw f = ∑ x : SDart B, wd x.1 := Finset.sum_fiberwise _ _ _
  have h1 : ∑ y, w y ≤ 1 := by
    rw [Fintype.sum_sum_type]
    simp only [w, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, div_le_one hWp]
    have : (∑ q, (wq q : ℝ)) + ∑ f, (fw f : ℝ) = W := by
      rw [hW]; push_cast [← hfwsum]; ring
    linarith
  obtain ⟨C, Z, hk, hsep, hin, hout⟩ := N.exists_short_cycle_separator_stellar hN hl hw0 h1
  obtain ⟨n, e, hn0, hnk, hch, hdis, hcov⟩ := Map.stellar_cycle_path hl hsm C
  have hcB : Fintype.card (SVert σ B) + Fintype.card N.Face ≤ 2 * B.card := card_psep_le hσ hB
  have hkB : C.k ≤ 6 * Nat.sqrt (2 * B.card) + 4 :=
    hk.trans (by have := Nat.sqrt_le_sqrt hcB; omega)
  set ρ : HPath M := ⟨n - 1, fun j => (e j).1, fun j => M.tail (e j).1, fun _ _ => rfl⟩ with hρ
  have hcyc : ∀ y : SVert σ B ⊕ N.Face, y ∈ C.verts ∨ y ∈ Map.sideIn C Z ∨ y ∈ Map.sideOut C Z := by
    intro y
    have := hsep.cover
    have hy : y ∈ C.verts ∪ Map.sideIn C Z ∪ Map.sideOut C Z := by rw [this]; exact mem_univ _
    simp only [mem_union] at hy; tauto
  have hvC : ∀ q : SVert σ B, (Sum.inl q : SVert σ B ⊕ N.Face) ∈ C.verts ↔
      ∃ j < n, N.vert (e j) = q := fun q => by rw [SCycle.mem_verts]; exact hcov q
  set I := univ.filter fun q : SVert σ B => (Sum.inl q : SVert σ B ⊕ N.Face) ∈ Map.sideIn C Z
    with hI
  set O := univ.filter fun q : SVert σ B => (Sum.inl q : SVert σ B ⊕ N.Face) ∈ Map.sideOut C Z
    with hO
  have hIl : I = (Map.sideIn C Z).toLeft := by ext q; simp [hI]
  have hOl : O = (Map.sideOut C Z).toLeft := by ext q; simp [hO]
  -- the faces of a side
  have hcard3 : ∀ f : N.Face, (univ.filter fun x : SDart B => N.face x = f).card ≤ 3 := by
    intro f
    by_cases hne : ∃ x₁ : SDart B, N.face x₁ = f
    · obtain ⟨x₁, hx₁⟩ := hne
      refine (card_le_card (t := {x₁, N.φ x₁, N.φ.symm x₁}) fun x hx => ?_).trans
        card_le_three
      have := hsm x₁ x (by rw [hx₁]; exact (mem_filter.1 hx).2.symm)
      simp only [mem_insert, mem_singleton]; exact this
    · push Not at hne
      rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ => hne x)]; omega
  have wbound : ∀ (S S' : Finset (SVert σ B ⊕ N.Face)), ∑ y ∈ S, w y ≤ 2 / 3 →
      (∀ y, y ∈ C.verts ∨ y ∈ S ∨ y ∈ S') → ∀ T : Finset (SDart B),
      (∀ x ∈ T, (Sum.inr (N.face x) : SVert σ B ⊕ N.Face) ∉ S') →
      3 * (∑ x ∈ T, wd x.1 + ∑ q ∈ S.toLeft, wq q) ≤ 2 * W + 2 + 9 * C.k := by
    intro S S' hS hcv T hT
    -- the darts of `T` have their face on `S` or on the cycle
    have hsplit : ∑ x ∈ T, wd x.1 ≤ ∑ x : SDart B with (Sum.inr (N.face x) ∈ S), wd x.1 +
        ∑ x : SDart B with (Sum.inr (N.face x) ∈ C.verts), wd x.1 := by
      rw [← sum_union_inter (f := fun x : SDart B => wd x.1)]
      refine le_trans (sum_le_sum_of_subset fun x hx => ?_) (Nat.le_add_right _ _)
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hcv (Sum.inr (N.face x)) with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd h (hT x hx)
    have hC3 : ∑ x : SDart B with (Sum.inr (N.face x) ∈ C.verts), wd x.1 ≤ 3 * C.k := by
      calc ∑ x : SDart B with (Sum.inr (N.face x) ∈ C.verts), wd x.1
          ≤ ∑ x : SDart B with (Sum.inr (N.face x) ∈ C.verts), 1 :=
            sum_le_sum fun x _ => hwd x.1
        _ = ∑ f ∈ C.verts.toRight, (univ.filter fun x : SDart B => N.face x = f).card := by
            simp only [card_eq_sum_ones]
            rw [sum_fiberwise_eq_sum_filter univ C.verts.toRight N.face (fun _ => 1)]
            simp only [mem_toRight]
        _ ≤ ∑ f ∈ C.verts.toRight, 3 := sum_le_sum fun f _ => hcard3 f
        _ = 3 * C.verts.toRight.card := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ 3 * C.k := by
            have := card_toRight_le (u := C.verts); rw [C.card_verts] at this; omega
    have hSsum : ∑ x : SDart B with (Sum.inr (N.face x) ∈ S), wd x.1 =
        ∑ f ∈ S.toRight, fw f := by
      simp only [fw]
      rw [sum_fiberwise_eq_sum_filter univ S.toRight N.face (fun x => wd x.1)]
      simp only [mem_toRight]
    have hreal : ((∑ q ∈ S.toLeft, wq q + ∑ f ∈ S.toRight, fw f : ℕ) : ℝ) ≤ 2 / 3 * (W + 1) := by
      rw [sum_sum_eq_sum_toLeft_add_sum_toRight] at hS
      simp only [w, Sum.elim_inl, Sum.elim_inr] at hS
      rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, div_le_iff₀ hWp] at hS
      push_cast; linarith
    have hnat : 3 * (∑ q ∈ S.toLeft, wq q + ∑ f ∈ S.toRight, fw f) ≤ 2 * W + 2 := by
      have : (3 * (∑ q ∈ S.toLeft, wq q + ∑ f ∈ S.toRight, fw f : ℕ) : ℝ) ≤ 2 * W + 2 := by
        push_cast at hreal ⊢; linarith
      exact_mod_cast this
    omega
  refine ⟨ρ, I, O, ⟨fun j hj => ?_, fun i hi j hj h => ?_⟩, fun d hd => ?_, ?_,
    fun j _ => ⟨(e j).1, (e j).2, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hch j (by simp [ρ] at hj; omega)
    rw [hsc, psep_α, CombMap.tail_rev] at this
    exact this
  · simp only [ρ] at hi hj h
    exact hdis i (by omega) j (by omega) ((hsc _ _).2 h)
  · obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 hd
    · exact (e j).2
    · exact hB _ (e j).2
  · simp only [ρ]; omega
  · rw [hIl, hOl]
    refine disjoint_left.2 fun q h1 h2 => ?_
    rw [mem_toLeft] at h1 h2
    exact disjoint_left.1 hsep.disjAB h1 h2
  · intro x hxI hxO
    have hx : (Sum.inl (Quotient.mk _ x) : SVert σ B ⊕ N.Face) ∈ C.verts := by
      rcases hcyc (Sum.inl (Quotient.mk _ x)) with h | h | h
      · exact h
      · exact absurd (show Quotient.mk _ x ∈ I from mem_filter.2 ⟨mem_univ _, h⟩) hxI
      · exact absurd (show Quotient.mk _ x ∈ O from mem_filter.2 ⟨mem_univ _, h⟩) hxO
    obtain ⟨j, hj, hej⟩ := (hvC _).1 hx
    refine ⟨j, by simp only [ρ]; omega, hRel_symm ((hsc (e j) x).1 hej)⟩
  · intro x hx j hj hr
    have hx' : (Sum.inl (Quotient.mk _ x) : SVert σ B ⊕ N.Face) ∈ C.verts :=
      (hvC _).2 ⟨j, by simp only [ρ] at hj; omega, (hsc (e j) x).2 (hRel_symm hr)⟩
    rcases hx with h | h
    · exact disjoint_left.1 hsep.disjA hx' (mem_filter.1 h).2
    · exact disjoint_left.1 hsep.disjB hx' (mem_filter.1 h).2
  · intro x hx hxO
    have := hsep.noEdge (old x)
    simp only [stellar_vert_old, stellar_α, stα_old] at this
    exact this (mem_filter.1 hx).2 (mem_filter.1 hxO).2
  · intro x hx hxI
    have := hsep.noEdge (old (N.α x))
    simp only [stellar_vert_old, stellar_α, stα_old, N.α_α] at this
    exact this (mem_filter.1 hxI).2 (mem_filter.1 hx).2
  · rw [hIl]
    refine (wbound _ _ hin (fun y => hcyc y) _ fun x hx hxo => ?_).trans (by omega)
    rcases (mem_filter.1 hx).2 with h | h
    · have := hsep.noEdge (up x)
      simp only [stellar_vert_up, stellar_α, stα_up, stellar_vert_down] at this
      exact this (mem_toLeft.1 h) hxo
    · have := hsep.noEdge (up (N.φ x))
      simp only [stellar_vert_up, stellar_α, stα_up, stellar_vert_down, vert_φ,
        face_φ] at this
      exact this (mem_toLeft.1 h) hxo
  · rw [hOl]
    refine (wbound _ _ hout (fun y => by have := hcyc y; tauto) _ fun x hx hxi => ?_).trans
      (by omega)
    rcases (mem_filter.1 hx).2 with h | h
    · have := hsep.noEdge (down x)
      simp only [stellar_vert_down, stellar_α, stα_down, stellar_vert_up] at this
      exact this hxi (mem_toLeft.1 h)
    · have := hsep.noEdge (down (N.φ x))
      simp only [stellar_vert_down, stellar_α, stα_down, stellar_vert_up, vert_φ,
        face_φ] at this
      exact this hxi (mem_toLeft.1 h)

end BKMNW

end PlanarFlow
