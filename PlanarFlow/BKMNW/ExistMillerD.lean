module

public import PlanarFlow.BKMNW.ExistMiller

/-!
# Miller's theorem on a piece map from a given separator

* `PlanarSeparator.Map.stN`, `PlanarSeparator.Map.stE`: the explicit sequence of darts of the map
  underlying a simple cycle of its stellar subdivision (passages through face centres replaced by
  face darts); `PlanarSeparator.Map.stellar_cycle_path'`.
* `PlanarFlow.BKMNW.corePath`, `coreI`, `coreO`: the simple path through the holes and the two
  sides, as functions of a separator `(C, Z)` of the stellar subdivision of the piece map;
  **`PlanarFlow.BKMNW.exists_core_cycle'`**: the conclusion of `exists_core_cycle` for these
  explicit objects, from any separator `(C, Z)` whose sides weigh (in natural numbers) at most
  `2 W + 2` thirds of the total `W` (`coreWt`).
* `PlanarFlow.BKMNW.coreSep_of_real`, `coreSep_of_wR`: the hypothesis from the real-weight form of
  Miller's theorem, and from the form `SepOK (wR wP)` proved for the machine program
  `PlanarSeparator.MillerProg.millerFull`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Map

open Finset StDart

variable {X Q : Type*} [Fintype X] [DecidableEq X] [DecidableEq Q] {N : Map X Q}

instance (δ : StDart X) : Decidable (IsDn δ) := by cases δ <;> simp [IsDn] <;> infer_instance

/-- The start of the explicit path: the first dart of the cycle not leaving a face centre. -/
def stS (C : N.stellar.SCycle) : ℕ := if IsDn (C.d 0) then 1 else 0

/-- The cycle read from `stS C`. -/
def stD (C : N.stellar.SCycle) (i : ℕ) : StDart X := C.d ((stS C + i) % C.k)

/-- The step to the next vertex of the map: two darts for a passage through a centre. -/
def stStp (δ' : StDart X) : ℕ := if IsUp δ' then 2 else 1

/-- The positions on the cycle of the vertices of the map. -/
def stG (C : N.stellar.SCycle) (j : ℕ) : ℕ := Nat.rec 0 (fun _ gj => gj + stStp (stD C gj)) j

lemma stG_ge (C : N.stellar.SCycle) (j : ℕ) : j ≤ stG C j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    show j + 1 ≤ stG C j + stStp (stD C (stG C j))
    have : 1 ≤ stStp (stD C (stG C j)) := by unfold stStp; split_ifs <;> omega
    omega

/-- The number of vertices of the map on the cycle. -/
def stN (C : N.stellar.SCycle) : ℕ := Nat.find (⟨C.k, stG_ge C C.k⟩ : ∃ j, C.k ≤ stG C j)

/-- The darts of the map along the cycle. -/
def stE (C : N.stellar.SCycle) (j : ℕ) : X :=
  if j + 1 < stN C ∧ IsUp (stD C (stG C j)) then
    (if N.vert (N.φ (stU (stD C (stG C j)))) = N.vert (stU (stD C (stG C j + 1))) then
      stU (stD C (stG C j)) else N.α (stU (stD C (stG C j + 1))))
  else stU (stD C (stG C j))

/-- **`stellar_cycle_path` with the vertices named**: the explicit sequence `stE C` of
`stN C` darts of the map (`stellar_cycle_path`, whose proof builds it). -/
theorem stellar_cycle_path' (hl : ∀ d, N.vert (N.α d) ≠ N.vert d)
    (hsm : ∀ x y, N.face x = N.face y → y = x ∨ y = N.φ x ∨ y = N.φ.symm x)
    (C : N.stellar.SCycle) :
    0 < stN C ∧ stN C ≤ C.k ∧
      (∀ j, j + 1 < stN C → N.vert (N.α (stE C j)) = N.vert (stE C (j + 1))) ∧
      (∀ i < stN C, ∀ j < stN C, N.vert (stE C i) = N.vert (stE C j) → i = j) ∧
      (∀ q : Q, (∃ i < C.k, N.stellar.vert (C.d i) = .inl q) ↔
        ∃ j < stN C, N.vert (stE C j) = q) := by
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
  obtain ⟨hsK, hs⟩ : stS C < K ∧ ¬ IsDn (C.d (stS C)) := by
    unfold stS
    by_cases h : IsDn (C.d 0)
    · simp only [h, ite_true]
      refine ⟨by omega, ?_⟩
      have := hnext_dn 0 (by rwa [Nat.zero_mod])
      rwa [zero_add, Nat.mod_eq_of_lt (by omega)] at this
    · simp only [h, ite_false]; exact ⟨hK1, not_false⟩
  set s := stS C with hsdef
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
  have hnN : stN C = n := rfl
  have heE : stE C = e := rfl
  rw [hnN, heE]
  refine ⟨hn0, hnK, hch, hdis, fun q => ⟨?_, ?_⟩⟩
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

section CoreD

variable {σ : Perm D} {B : Finset D} (hσ : Stable σ B) (hB : Stable (revPerm M) B)

open Classical in
/-- **The path through the holes from a cycle `C` of the stellar subdivision of the piece map**:
the tails of the darts `stE C j`, `j < stN C`. -/
noncomputable def corePath (C : (psep M hσ hB).stellar.SCycle) : HPath M :=
  ⟨Map.stN C - 1, fun j => (Map.stE C j).1, fun j => M.tail (Map.stE C j).1, fun _ _ => rfl⟩

open Classical in
/-- The vertices of the piece map strictly inside the separator `(C, Z)`. -/
noncomputable def coreI (C : (psep M hσ hB).stellar.SCycle)
    (Z : Finset (psep M hσ hB).stellar.Face) : Finset (SVert σ B) :=
  univ.filter fun q => (Sum.inl q : SVert σ B ⊕ (psep M hσ hB).Face) ∈ Map.sideIn C Z

open Classical in
/-- The vertices of the piece map strictly outside the separator `(C, Z)`. -/
noncomputable def coreO (C : (psep M hσ hB).stellar.SCycle)
    (Z : Finset (psep M hσ hB).stellar.Face) : Finset (SVert σ B) :=
  univ.filter fun q => (Sum.inl q : SVert σ B ⊕ (psep M hσ hB).Face) ∈ Map.sideOut C Z

open Classical in
/-- **The natural weights on the vertices of the stellar subdivision** of the piece map: `wq` on
the vertices, and on a face the weights `wd` of its darts. -/
noncomputable def coreWt (wd : D → ℕ) (wq : SVert σ B → ℕ) :
    SVert σ B ⊕ (psep M hσ hB).Face → ℕ :=
  Sum.elim wq fun f => ∑ x : SDart B with (psep M hσ hB).face x = f, wd x.1

open Classical in
lemma sum_coreWt (wd : D → ℕ) (wq : SVert σ B → ℕ) :
    ∑ y, coreWt hσ hB wd wq y = ∑ x : SDart B, wd x.1 + ∑ q, wq q := by
  rw [Fintype.sum_sum_type]
  simp only [coreWt, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_fiberwise, add_comm]

end CoreD

open Classical PlanarSeparator.Map in
/-- **Miller's theorem on a piece map with small faces, from a given separator.** The hypotheses
of `exists_core_cycle`, and a separator `(C, Z)` of the stellar subdivision of the piece map
(at most `6 √(n + F) + 4` darts, `n` vertices, `F` faces) whose two sides weigh, for the natural
weights `coreWt` (`wq` on the vertices, the darts' `wd` on the faces), at most `(2 W + 2) / 3` each
(`W` the total). Then the conclusion of `exists_core_cycle` holds for the explicit path
`corePath C` and the explicit sides `coreI C Z`, `coreO C Z`. -/
theorem exists_core_cycle' {σ : Perm D} {B : Finset D} (hσ : Stable σ B)
    (hB : Stable (revPerm M) B) {Hs : List (Finset V)}
    (hvert : ∀ x ∈ B, ∀ y ∈ B, σ.SameCycle x y ↔ HRel Hs (M.tail x) (M.tail y))
    (hloop : ∀ x ∈ B, ¬ HRel Hs (M.head x) (M.tail x))
    (hsmall : ∀ x ∈ B, ∀ z ∈ pface M σ B x,
      z = x ∨ z = (σ * revPerm M) x ∨ z = (σ * revPerm M).symm x)
    (wd : D → ℕ) (hwd : ∀ d, wd d ≤ 1) (wq : SVert σ B → ℕ)
    (C : (psep M hσ hB).stellar.SCycle) (Z : Finset (psep M hσ hB).stellar.Face)
    (hk : C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face) + 4)
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z))
    (hin : 3 * ∑ y ∈ sideIn C Z, coreWt hσ hB wd wq y ≤
      2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2)
    (hout : 3 * ∑ y ∈ sideOut C Z, coreWt hσ hB wd wq y ≤
      2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2) :
    (corePath hσ hB C).Simple Hs ∧ (∀ e ∈ (corePath hσ hB C).darts, e ∈ B) ∧
      (corePath hσ hB C).k + 1 ≤ 6 * Nat.sqrt (2 * B.card) + 4 ∧
      (∀ j ≤ (corePath hσ hB C).k, ∃ x ∈ B, M.tail x = (corePath hσ hB C).p j) ∧
      Disjoint (coreI hσ hB C Z) (coreO hσ hB C Z) ∧
      (∀ x : SDart B, Quotient.mk _ x ∉ coreI hσ hB C Z → Quotient.mk _ x ∉ coreO hσ hB C Z →
        ∃ j ≤ (corePath hσ hB C).k, HRel Hs (M.tail x.1) ((corePath hσ hB C).p j)) ∧
      (∀ x : SDart B, (Quotient.mk _ x ∈ coreI hσ hB C Z ∨ Quotient.mk _ x ∈ coreO hσ hB C Z) →
        ∀ j ≤ (corePath hσ hB C).k, ¬ HRel Hs (M.tail x.1) ((corePath hσ hB C).p j)) ∧
      (∀ x : SDart B, Quotient.mk _ x ∈ coreI hσ hB C Z →
        Quotient.mk _ ((psep M hσ hB).α x) ∉ coreO hσ hB C Z) ∧
      (∀ x : SDart B, Quotient.mk _ x ∈ coreO hσ hB C Z →
        Quotient.mk _ ((psep M hσ hB).α x) ∉ coreI hσ hB C Z) ∧
      3 * (∑ x : SDart B with (Quotient.mk _ x ∈ coreI hσ hB C Z ∨
            Quotient.mk _ ((psep M hσ hB).α x) ∈ coreI hσ hB C Z),
          wd x.1 + ∑ q ∈ coreI hσ hB C Z, wq q) ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 + 9 * (6 * Nat.sqrt (2 * B.card) + 4) ∧
      3 * (∑ x : SDart B with (Quotient.mk _ x ∈ coreO hσ hB C Z ∨
            Quotient.mk _ ((psep M hσ hB).α x) ∈ coreO hσ hB C Z),
          wd x.1 + ∑ q ∈ coreO hσ hB C Z, wq q) ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 + 9 * (6 * Nat.sqrt (2 * B.card) + 4) := by
  have hsc : ∀ x y : SDart B, (psep M hσ hB).vert x = (psep M hσ hB).vert y ↔ HRel Hs (M.tail x.1) (M.tail y.1) :=
    fun x y => (psep_vert_eq hσ hB).trans (hvert _ x.2 _ y.2)
  have hl : ∀ d, (psep M hσ hB).vert ((psep M hσ hB).α d) ≠ (psep M hσ hB).vert d := by
    intro d h
    rw [hsc, psep_α, CombMap.tail_rev] at h
    exact hloop d.1 d.2 h
  have hsm : ∀ x y, (psep M hσ hB).face x = (psep M hσ hB).face y → y = x ∨ y = (psep M hσ hB).φ x ∨ y = (psep M hσ hB).φ.symm x := by
    intro x y h
    have hy : y.1 ∈ pface M σ B x.1 := mem_pface.2 ⟨y.2, (psep_face_eq hσ hB).1 h⟩
    rcases hsmall x.1 x.2 y.1 hy with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext (by rw [e, psep_φ]; rfl)))
    · exact Or.inr (Or.inr (Subtype.ext (by rw [e, psep_φ_symm])))
  set W := ∑ x : SDart B, wd x.1 + ∑ q, wq q with hW
  set fw : (psep M hσ hB).Face → ℕ := fun f => ∑ x : SDart B with (psep M hσ hB).face x = f, wd x.1 with hfw
  obtain ⟨hn0, hnk, hch, hdis, hcov⟩ := Map.stellar_cycle_path' hl hsm C
  set n := Map.stN C with hn
  set e := Map.stE C with he
  have hcB : Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face ≤ 2 * B.card := card_psep_le hσ hB
  have hkB : C.k ≤ 6 * Nat.sqrt (2 * B.card) + 4 :=
    hk.trans (by have := Nat.sqrt_le_sqrt hcB; omega)
  set ρ : HPath M := corePath hσ hB C with hρ
  have hρk : ρ.k = n - 1 := rfl
  have hρp : ∀ j, ρ.p j = M.tail (e j).1 := fun _ => rfl
  have hρd : ∀ j, ρ.d j = (e j).1 := fun _ => rfl
  have hcyc : ∀ y : SVert σ B ⊕ (psep M hσ hB).Face, y ∈ C.verts ∨ y ∈ Map.sideIn C Z ∨ y ∈ Map.sideOut C Z := by
    intro y
    have := hsep.cover
    have hy : y ∈ C.verts ∪ Map.sideIn C Z ∪ Map.sideOut C Z := by rw [this]; exact mem_univ _
    simp only [mem_union] at hy; tauto
  have hvC : ∀ q : SVert σ B, (Sum.inl q : SVert σ B ⊕ (psep M hσ hB).Face) ∈ C.verts ↔
      ∃ j < n, (psep M hσ hB).vert (e j) = q := fun q => by rw [SCycle.mem_verts]; exact hcov q
  set I := coreI hσ hB C Z with hI
  set O := coreO hσ hB C Z with hO
  have hIl : I = (Map.sideIn C Z).toLeft := by ext q; simp [hI, coreI]
  have hOl : O = (Map.sideOut C Z).toLeft := by ext q; simp [hO, coreO]
  have hcard3 : ∀ f : (psep M hσ hB).Face, (univ.filter fun x : SDart B => (psep M hσ hB).face x = f).card ≤ 3 := by
    intro f
    by_cases hne : ∃ x₁ : SDart B, (psep M hσ hB).face x₁ = f
    · obtain ⟨x₁, hx₁⟩ := hne
      refine (card_le_card (t := {x₁, (psep M hσ hB).φ x₁, (psep M hσ hB).φ.symm x₁}) fun x hx => ?_).trans
        card_le_three
      have := hsm x₁ x (by rw [hx₁]; exact (mem_filter.1 hx).2.symm)
      simp only [mem_insert, mem_singleton]; exact this
    · push Not at hne
      rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ => hne x)]; omega
  have wbound : ∀ (S S' : Finset (SVert σ B ⊕ (psep M hσ hB).Face)),
      3 * ∑ y ∈ S, coreWt hσ hB wd wq y ≤ 2 * W + 2 →
      (∀ y, y ∈ C.verts ∨ y ∈ S ∨ y ∈ S') → ∀ T : Finset (SDart B),
      (∀ x ∈ T, (Sum.inr ((psep M hσ hB).face x) : SVert σ B ⊕ (psep M hσ hB).Face) ∉ S') →
      3 * (∑ x ∈ T, wd x.1 + ∑ q ∈ S.toLeft, wq q) ≤ 2 * W + 2 + 9 * C.k := by
    intro S S' hS hcv T hT
    have hsplit : ∑ x ∈ T, wd x.1 ≤ ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ S), wd x.1 +
        ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ C.verts), wd x.1 := by
      rw [← sum_union_inter (f := fun x : SDart B => wd x.1)]
      refine le_trans (sum_le_sum_of_subset fun x hx => ?_) (Nat.le_add_right _ _)
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hcv (Sum.inr ((psep M hσ hB).face x)) with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd h (hT x hx)
    have hC3 : ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ C.verts), wd x.1 ≤ 3 * C.k := by
      calc ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ C.verts), wd x.1
          ≤ ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ C.verts), 1 :=
            sum_le_sum fun x _ => hwd x.1
        _ = ∑ f ∈ C.verts.toRight, (univ.filter fun x : SDart B => (psep M hσ hB).face x = f).card := by
            simp only [card_eq_sum_ones]
            rw [sum_fiberwise_eq_sum_filter univ C.verts.toRight (psep M hσ hB).face (fun _ => 1)]
            simp only [mem_toRight]
        _ ≤ ∑ f ∈ C.verts.toRight, 3 := sum_le_sum fun f _ => hcard3 f
        _ = 3 * C.verts.toRight.card := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ 3 * C.k := by
            have := card_toRight_le (u := C.verts); rw [C.card_verts] at this; omega
    have hSsum : ∑ x : SDart B with (Sum.inr ((psep M hσ hB).face x) ∈ S), wd x.1 =
        ∑ f ∈ S.toRight, fw f := by
      simp only [fw]
      rw [sum_fiberwise_eq_sum_filter univ S.toRight (psep M hσ hB).face (fun x => wd x.1)]
      simp only [mem_toRight]
    have hnat : 3 * (∑ q ∈ S.toLeft, wq q + ∑ f ∈ S.toRight, fw f) ≤ 2 * W + 2 := by
      rw [sum_sum_eq_sum_toLeft_add_sum_toRight] at hS
      simpa only [coreWt, Sum.elim_inl, Sum.elim_inr] using hS
    omega
  refine ⟨⟨fun j hj => ?_, fun i hi j hj h => ?_⟩, fun d hd => ?_, ?_,
    fun j _ => ⟨(e j).1, (e j).2, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hch j (by rw [hρk] at hj; omega)
    rw [hsc, psep_α, CombMap.tail_rev] at this
    rw [hρd, hρp]
    exact this
  · rw [hρk] at hi hj
    rw [hρp, hρp] at h
    exact hdis i (by omega) j (by omega) ((hsc _ _).2 h)
  · obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 hd
    · exact (e j).2
    · exact hB _ (e j).2
  · rw [hρk]; omega
  · rw [hIl, hOl]
    refine disjoint_left.2 fun q h1 h2 => ?_
    rw [mem_toLeft] at h1 h2
    exact disjoint_left.1 hsep.disjAB h1 h2
  · intro x hxI hxO
    have hx : (Sum.inl (Quotient.mk _ x) : SVert σ B ⊕ (psep M hσ hB).Face) ∈ C.verts := by
      rcases hcyc (Sum.inl (Quotient.mk _ x)) with h | h | h
      · exact h
      · exact absurd (show Quotient.mk _ x ∈ I by rw [hIl, mem_toLeft]; exact h) hxI
      · exact absurd (show Quotient.mk _ x ∈ O by rw [hOl, mem_toLeft]; exact h) hxO
    obtain ⟨j, hj, hej⟩ := (hvC _).1 hx
    refine ⟨j, by rw [hρk]; omega, ?_⟩
    rw [hρp]
    exact hRel_symm ((hsc (e j) x).1 hej)
  · intro x hx j hj hr
    rw [hρp] at hr
    have hx' : (Sum.inl (Quotient.mk _ x) : SVert σ B ⊕ (psep M hσ hB).Face) ∈ C.verts :=
      (hvC _).2 ⟨j, by rw [hρk] at hj; omega, (hsc (e j) x).2 (hRel_symm hr)⟩
    rcases hx with h | h
    · rw [hIl, mem_toLeft] at h
      exact disjoint_left.1 hsep.disjA hx' h
    · rw [hOl, mem_toLeft] at h
      exact disjoint_left.1 hsep.disjB hx' h
  · intro x hx hxO
    rw [hIl, mem_toLeft] at hx
    rw [hOl, mem_toLeft] at hxO
    have := hsep.noEdge (old x)
    simp only [stellar_vert_old, stellar_α, stα_old] at this
    exact this hx hxO
  · intro x hx hxI
    rw [hOl, mem_toLeft] at hx
    rw [hIl, mem_toLeft] at hxI
    have := hsep.noEdge (old ((psep M hσ hB).α x))
    simp only [stellar_vert_old, stellar_α, stα_old, (psep M hσ hB).α_α] at this
    exact this hxI hx
  · rw [hIl]
    refine (wbound _ _ hin (fun y => hcyc y) _ fun x hx hxo => ?_).trans (by omega)
    rcases (mem_filter.1 hx).2 with h | h
    · rw [mem_toLeft] at h
      have := hsep.noEdge (up x)
      simp only [stellar_vert_up, stellar_α, stα_up, stellar_vert_down] at this
      exact this h hxo
    · rw [mem_toLeft] at h
      have := hsep.noEdge (up ((psep M hσ hB).φ x))
      simp only [stellar_vert_up, stellar_α, stα_up, stellar_vert_down, vert_φ,
        face_φ] at this
      exact this h hxo
  · rw [hOl]
    refine (wbound _ _ hout (fun y => by have := hcyc y; tauto) _ fun x hx hxi => ?_).trans
      (by omega)
    rcases (mem_filter.1 hx).2 with h | h
    · rw [mem_toLeft] at h
      have := hsep.noEdge (down x)
      simp only [stellar_vert_down, stellar_α, stα_down, stellar_vert_up] at this
      exact this hxi h
    · rw [mem_toLeft] at h
      have := hsep.noEdge (down ((psep M hσ hB).φ x))
      simp only [stellar_vert_down, stellar_α, stα_down, stellar_vert_up, vert_φ,
        face_φ] at this
      exact this hxi h

/-- **Normalized real weights to natural weights**: if the part `S` weighs at most `2/3` of the
total for the weights `f v / Σ f`, then `3 Σ_S f ≤ 2 Σ f + 2`. -/
lemma three_sum_le_of_norm {α : Type*} [Fintype α] (f : α → ℕ) (S : Finset α)
    (h : ∑ v ∈ S, (f v : ℝ) / ∑ u, (f u : ℝ) ≤ 2 / 3) : 3 * ∑ v ∈ S, f v ≤ 2 * ∑ v, f v + 2 := by
  have hle : ∑ v ∈ S, f v ≤ ∑ v, f v := sum_le_sum_of_subset (subset_univ _)
  rcases Nat.eq_zero_or_pos (∑ v, f v) with h0 | hpos
  · omega
  have hS : (0 : ℝ) < ∑ u, (f u : ℝ) := by exact_mod_cast hpos
  rw [← Finset.sum_div, div_le_iff₀ hS] at h
  have : (3 * ∑ v ∈ S, f v : ℕ) ≤ (2 * ∑ v, f v : ℕ) := by
    have h' : (3 * ∑ v ∈ S, (f v : ℝ)) ≤ 2 * ∑ u, (f u : ℝ) := by linarith
    exact_mod_cast h'
  omega

/-- **Real weights with a margin to natural weights**: if `S` weighs at most `2/3` for the
weights `f v / (W + 1)`, then `3 Σ_S f ≤ 2 W + 2`. -/
lemma three_sum_le_of_succ {α : Type*} (f : α → ℕ) (S : Finset α) (W : ℕ)
    (h : ∑ v ∈ S, (f v : ℝ) / (W + 1) ≤ 2 / 3) : 3 * ∑ v ∈ S, f v ≤ 2 * W + 2 := by
  have hW : (0 : ℝ) < W + 1 := by positivity
  rw [← Finset.sum_div, div_le_iff₀ hW] at h
  have h' : (3 * ∑ v ∈ S, (f v : ℝ)) ≤ 2 * W + 2 := by linarith
  exact_mod_cast h'

open Classical PlanarSeparator.Map in
/-- **The separator of Miller's theorem on the stellar subdivision** (real weights `w / (W + 1)`,
as in `exists_core_cycle`) meets the hypotheses of `exists_core_cycle'`: there is a separator
`(C, Z)` with the natural bounds. -/
theorem exists_coreSep {σ : Perm D} {B : Finset D} (hσ : Stable σ B)
    (hB : Stable (revPerm M) B) {x₀ : D} (hx₀ : x₀ ∈ B)
    (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn (revPerm M) σ x y) (h0 : gap (revPerm M) σ B = 0)
    (hl : ∀ d, (psep M hσ hB).vert ((psep M hσ hB).α d) ≠ (psep M hσ hB).vert d)
    (wd : D → ℕ) (wq : SVert σ B → ℕ) :
    ∃ (C : (psep M hσ hB).stellar.SCycle) (Z : Finset (psep M hσ hB).stellar.Face),
      C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      3 * ∑ y ∈ sideIn C Z, coreWt hσ hB wd wq y ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 ∧
      3 * ∑ y ∈ sideOut C Z, coreWt hσ hB wd wq y ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 := by
  have hN : (psep M hσ hB).IsPlane := psep_isPlane hσ hB hx₀ hconn h0
  set W := ∑ x : SDart B, wd x.1 + ∑ q, wq q with hW
  set w : SVert σ B ⊕ (psep M hσ hB).Face → ℝ :=
    fun y => (coreWt hσ hB wd wq y : ℝ) / (W + 1) with hw
  have hWp : (0 : ℝ) < W + 1 := by positivity
  have hw0 : ∀ y, 0 ≤ w y := fun y => by positivity
  have h1 : ∑ y, w y ≤ 1 := by
    simp only [w]
    rw [← Finset.sum_div, div_le_one hWp]
    have : (∑ y, (coreWt hσ hB wd wq y : ℝ)) = W := by
      rw [hW, ← sum_coreWt hσ hB wd wq]; push_cast; rfl
    linarith
  obtain ⟨C, Z, hk, hsep, hin, hout⟩ :=
    (psep M hσ hB).exists_short_cycle_separator_stellar hN hl hw0 h1
  exact ⟨C, Z, hk, hsep, three_sum_le_of_succ _ _ W hin, three_sum_le_of_succ _ _ W hout⟩

end BKMNW

end PlanarFlow
