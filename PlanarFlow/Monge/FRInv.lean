module

public import PlanarFlow.Monge.FRHeap

/-!
# FR-Dijkstra on the machine: the heap of the vertices and the ghost run

The parts of the state of a run (`PlanarFlow.Monge.FR.MSt`) that do not involve the half
blocks, in terms of the memory:

* `Hp`: the heap of the vertices (`PlanarFlow.Monge.FR.WinOK`), its present flags at most `1`,
  the settled flags at most `1`, a present vertex is not settled;
* `Gh`: the *ghost run* `(K, v, d)`: the settled vertices are `v 0, …, v (K - 1)`, their
  distances in the memory are `d i`, and the key of a present vertex is *justified* (`Just`): it
  is `d i + ℓ - p y` for an arc of length `ℓ` (`IsArc`) from a settled vertex, or the initial key
  `-p r` of the root;
* `Arcs`: every explicit arc from a settled vertex to an unsettled one is claimed (`Claim`: its
  head is present with a key at most the reduced length), except the arcs of `ex` (`arcEx`: the
  arcs of the vertex being settled not yet relaxed);
* `hbAct`, `hbe`: the active sources of a half block (the settled ones, except the pending ones,
  `pend`) and their distances;
* `MRun`: a prefix of a run of Dijkstra's algorithm with the price function
  (`PlanarFlow.Monge.DijkRun`) on the machine's vertices and arcs; `FRes`: the result of a run,
  closed under the arcs, with the settled flags and the distances in the memory.

The generic steps:

* `DecEff`, `decEff_of_dec`: the effect of a decrease of a key
  (`PlanarFlow.Monge.FR.decKey_exec`); `Hp.dec`, `Gh.dec`: it keeps the heap and the ghost run;
* `Hp.low`, `Gh.low`, `Arcs.low`: these depend only on the memory below `wb + 3 N`;
* `arc_block`: every arc of the dense distance graph lies in a half block;
* `whileLtN_ghost_pot`: a loop rule with a ghost state, keeping the final potential.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The definitions -/

/-- The settled flag of a vertex. -/
def sfV (P : Prm) (nm : ℕ → ℕ) (y : ℕ) : ℕ := nm (P.sb + y)
/-- The distance of a vertex. -/
def dV (P : Prm) (rm : ℕ → ℝ) (y : ℕ) : ℝ := rm (P.db + y)

/-- The active sources of the half block `k` of the level `2 ^ t`: the settled sources, except
the pending ones (`pA`). -/
def hbAct (P : Prm) (pA : ℕ → ℕ → Prop) (nm : ℕ → ℕ) (t k σ : ℕ) : Prop :=
  σ < hbNc P.b (2 ^ t) k ∧ sfV P nm (sib k * 2 ^ t + σ) = 1 ∧ ¬ pA t (sib k * 2 ^ t + σ)

/-- The distances of the sources of the half block `k` of the level `2 ^ t`. -/
def hbe (P : Prm) (rm : ℕ → ℝ) (t k σ : ℕ) : ℝ := dV P rm (sib k * 2 ^ t + σ)

/-- `y` is present in the heap with a key at most `val`. -/
def Claim (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) (y : ℕ) (val : ℝ) : Prop :=
  prV P nm y = 1 ∧ keyV P rm y ≤ val

/-- **The explicit arcs from the settled vertices to the unsettled ones are claimed**, except the
arcs of `ex`. -/
def Arcs (P : Prm) (ex : ℕ → ℕ → Prop) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop :=
  ∀ u < P.N, sfV P nm u = 1 → ∀ e, P.off u ≤ e → e < P.off (u + 1) → sfV P nm (P.dst e) = 0 →
    ex u e ∨ Claim P nm rm (P.dst e) (dV P rm u + P.len e - P.p (P.dst e))

/-- The heap of the vertices. -/
structure Hp (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  win : WinOK P.N (prV P nm) (keyV P rm) (wnV P nm) 0
  pr_le : ∀ y < P.N, prV P nm y ≤ 1
  sf_le : ∀ y < P.N, sfV P nm y ≤ 1
  pr_sf : ∀ y < P.N, prV P nm y = 1 → sfV P nm y = 0

/-- An arc of length `ℓ` from `u` to `y`: an arc of the dense distance graph, or an explicit
arc. -/
def IsArc (P : Prm) (u y : ℕ) (ℓ : ℤ) : Prop :=
  (u < P.b ∧ y < P.b ∧ u ≠ y ∧ ℓ = P.D u y) ∨
    (u < P.N ∧ ∃ e, P.off u ≤ e ∧ e < P.off (u + 1) ∧ y = P.dst e ∧ ℓ = P.len e)

/-- A justified key of `y`: the initial key of the root, or `d i + ℓ - p y` for an arc from a
settled vertex. -/
def Just (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (y : ℕ) (val : ℝ) : Prop :=
  (y = P.r ∧ val = ((-P.p P.r : ℤ) : ℝ)) ∨
    ∃ i < K, ∃ ℓ : ℤ, IsArc P (v i) y ℓ ∧ val = ((d i + ℓ - P.p y : ℤ) : ℝ)

/-- The ghost run. -/
structure Gh (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  vlt : ∀ i < K, v i < P.N
  sf : ∀ y < P.N, sfV P nm y = 1 ↔ ∃ i < K, v i = y
  dist : ∀ i < K, dV P rm (v i) = d i
  just : ∀ y < P.N, prV P nm y = 1 → Just P K v d y (keyV P rm y)

/-- The vertex `x` is pending at the levels from `t₀` on. -/
def pend (x t₀ t y : ℕ) : Prop := y = x ∧ t₀ ≤ t

/-- The explicit arcs of `x` from the arc `cur` on are not yet relaxed. -/
def arcEx (x cur u e : ℕ) : Prop := u = x ∧ cur ≤ e

/-- **A prefix of a run of Dijkstra's algorithm** with the price function, on the machine's
vertices and arcs. -/
structure MRun (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) : Prop where
  root : 0 < K → v 0 = P.r
  root_d : 0 < K → d 0 = 0
  inj : ∀ i j, i < K → j < K → v i = v j → i = j
  parent : ∀ k, 0 < k → k < K → ∃ i < k, ∃ ℓ, IsArc P (v i) (v k) ℓ ∧ d k = d i + ℓ
  least : ∀ k < K, ∀ i < k, ∀ y ℓ, IsArc P (v i) y ℓ → (∀ j < k, y ≠ v j) →
    d k - P.p (v k) ≤ d i + ℓ - P.p y

/-- No pending vertex, no exception. -/
def F2 (_ _ : ℕ) : Prop := False

/-- The result of the run: a run of Dijkstra's algorithm with the price function, closed under
the arcs, with the settled flags and the distances in the memory. -/
def FRes (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop :=
  MRun P K v d ∧ 0 < K ∧ (∀ i < K, v i < P.N) ∧
    (∀ i < K, ∀ y ℓ, IsArc P (v i) y ℓ → ∃ j < K, y = v j) ∧
    (∀ y < P.N, nm (P.sb + y) = 1 ↔ ∃ i < K, v i = y) ∧ (∀ i < K, rm (P.db + v i) = d i)

variable {P : Prm}

/-! ### Small facts -/

lemma sib_sib (k : ℕ) : sib (sib k) = k := by
  unfold sib; split_ifs <;> omega

lemma sib_ne (k : ℕ) : sib k ≠ k := by unfold sib; split_ifs <;> omega

lemma div_eq_of_mul {k s ρ : ℕ} (hρ : ρ < s) : (k * s + ρ) / s = k := by
  have hs : 0 < s := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hρ, Nat.zero_add]

lemma hbF_live {b : ℕ} {D : ℕ → ℕ → ℤ} {p : ℕ → ℤ} {s k ρ σ : ℕ} (h : k * s + ρ < b) :
    hbF b D p s k ρ σ = ((D (sib k * s + σ) (k * s + ρ) - p (k * s + ρ) : ℤ) : ℝ) := by
  unfold hbF cl; rw [min_eq_left (by omega)]

/-- The sources and the targets of a half block are distinct. -/
lemma src_ne_tgt {k s σ ρ : ℕ} (hσ : σ < s) (hρ : ρ < s) : sib k * s + σ ≠ k * s + ρ := by
  intro h
  have h1 := div_eq_of_mul (k := sib k) hσ
  have h2 := div_eq_of_mul (k := k) hρ
  rw [h, h2] at h1
  exact sib_ne k h1.symm

lemma hbNc_le {b s k : ℕ} : hbNc b s k ≤ s := by unfold hbNc; omega

lemma lg_le_of_le_pow {n T : ℕ} (h : n ≤ 2 ^ T) : lg n ≤ T + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lg_zero]; omega
  · rw [lg_eq_log hn]
    have := Nat.log_mono_right (b := 2) h
    rw [Nat.log_pow (by norm_num)] at this
    omega

lemma lay_w (hL : Lay P) : P.wb + 3 * P.N + 16 * P.b * P.Lv + 16 * P.b + 16 ≤ P.W ∧
    P.b ≤ P.N ∧ P.N ≤ P.wb ∧ 1 ≤ P.b :=
  ⟨hL.w, hL.bN, by have := hL.m6; omega, hL.b_pos⟩

/-! ### Decreasing a key -/

/-- The effect of a decrease of the key of `y₀` to `val` (done exactly when `D`). -/
structure DecEff (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) (nm' : ℕ → ℕ) (rm' : ℕ → ℝ) (y₀ : ℕ)
    (val : ℝ) (D : Prop) : Prop where
  pr1 : ∀ y < P.N, D → y = y₀ → prV P nm' y = 1
  pr2 : ∀ y < P.N, ¬ (D ∧ y = y₀) → prV P nm' y = prV P nm y
  key1 : ∀ y < P.N, D → y = y₀ → keyV P rm' y = val
  key2 : ∀ y < P.N, ¬ (D ∧ y = y₀) → keyV P rm' y = keyV P rm y
  dd : D → DecDo P nm rm y₀ val
  win : WinOK P.N (prV P nm') (keyV P rm') (wnV P nm') 0
  nmo : ∀ a, (a < P.wb ∨ P.wb + 2 * P.N ≤ a) → nm' a = nm a
  rmo : ∀ a, (a < P.wb ∨ P.wb + P.N ≤ a) → rm' a = rm a

variable {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {y₀ : ℕ} {val : ℝ} {D : Prop}

lemma DecEff.sf (hL : Lay P) (h : DecEff P nm rm nm' rm' y₀ val D) {y : ℕ} (hy : y < P.N) :
    sfV P nm' y = sfV P nm y := by
  have := hL.m5; have := hL.m6
  exact h.nmo _ (Or.inl (by omega))

lemma DecEff.dist (hL : Lay P) (h : DecEff P nm rm nm' rm' y₀ val D) {y : ℕ} (hy : y < P.N) :
    dV P rm' y = dV P rm y := by
  have := hL.m6
  exact h.rmo _ (Or.inl (by omega))

/-- A claim stays. -/
lemma DecEff.claim (h : DecEff P nm rm nm' rm' y₀ val D) {y : ℕ} (hy : y < P.N) {w : ℝ}
    (hc : Claim P nm rm y w) : Claim P nm' rm' y w := by
  by_cases hD : D ∧ y = y₀
  · obtain ⟨hD, rfl⟩ := hD
    refine ⟨h.pr1 y hy hD rfl, ?_⟩
    rw [h.key1 y hy hD rfl]
    rcases (h.dd hD).2 with h0 | h0
    · unfold Claim at hc; omega
    · exact h0.le.trans hc.2
  · exact ⟨by rw [h.pr2 y hy hD]; exact hc.1, by rw [h.key2 y hy hD]; exact hc.2⟩

/-- The new claim. -/
lemma DecEff.fresh (h : DecEff P nm rm nm' rm' y₀ val D) (hp : Hp P nm rm) (hy : y₀ < P.N)
    (hsf : sfV P nm y₀ = 0) (hD : DecDo P nm rm y₀ val → D) : Claim P nm' rm' y₀ val := by
  by_cases hdo : DecDo P nm rm y₀ val
  · exact ⟨h.pr1 y₀ hy (hD hdo) rfl, by rw [h.key1 y₀ hy (hD hdo) rfl]⟩
  · have hnD : ¬ (D ∧ y₀ = y₀) := fun h' => hdo (h.dd h'.1)
    rw [Claim, h.pr2 y₀ hy hnD, h.key2 y₀ hy hnD]
    unfold DecDo at hdo
    have := hp.pr_le y₀ hy
    have hs : P.sb + y₀ = P.sb + y₀ := rfl
    unfold sfV at hsf
    refine ⟨?_, ?_⟩
    · by_contra hc; exact hdo ⟨hsf, Or.inl (by omega)⟩
    · by_contra hc; exact hdo ⟨hsf, Or.inr (not_le.1 hc)⟩

lemma Hp.dec (hL : Lay P) (hp : Hp P nm rm) (h : DecEff P nm rm nm' rm' y₀ val D) :
    Hp P nm' rm' := by
  refine ⟨h.win, fun y hy => ?_, fun y hy => by rw [h.sf hL hy]; exact hp.sf_le y hy,
    fun y hy h1 => ?_⟩
  · by_cases hD : D ∧ y = y₀
    · rw [h.pr1 y hy hD.1 hD.2]
    · rw [h.pr2 y hy hD]; exact hp.pr_le y hy
  · rw [h.sf hL hy]
    by_cases hD : D ∧ y = y₀
    · obtain ⟨hD, rfl⟩ := hD; exact (h.dd hD).1
    · rw [h.pr2 y hy hD] at h1; exact hp.pr_sf y hy h1

lemma Gh.dec (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} (hg : Gh P K v d nm rm)
    (h : DecEff P nm rm nm' rm' y₀ val D) (hJ : D → Just P K v d y₀ val) :
    Gh P K v d nm' rm' := by
  refine ⟨hg.vlt, fun y hy => by rw [h.sf hL hy]; exact hg.sf y hy,
    fun i hi => by rw [h.dist hL (hg.vlt i hi)]; exact hg.dist i hi, fun y hy h1 => ?_⟩
  by_cases hD : D ∧ y = y₀
  · obtain ⟨hD, rfl⟩ := hD
    rw [h.key1 y hy hD rfl]; exact hJ hD
  · rw [h.pr2 y hy hD] at h1; rw [h.key2 y hy hD]; exact hg.just y hy h1

/-! ### The arcs -/

lemma off_mono' (hL : Lay P) : ∀ a c, a ≤ c → c ≤ P.N → P.off a ≤ P.off c := by
  intro a c hac hc
  induction c, hac using Nat.le_induction with
  | base => exact le_rfl
  | succ c _ ih => exact (ih (by omega)).trans (hL.off_mono c (by omega))

lemma dst_lt' (hL : Lay P) {u e : ℕ} (hu : u < P.N) (he : e < P.off (u + 1)) : P.dst e < P.N :=
  hL.dst_lt e (by
    have := off_mono' hL (u + 1) P.N (by omega) le_rfl; rw [hL.off_last] at this; omega)

lemma IsArc.dst_lt (hL : Lay P) {u y : ℕ} {ℓ : ℤ} (h : IsArc P u y ℓ) : y < P.N := by
  rcases h with ⟨-, hy, -⟩ | ⟨hu, e, -, he, rfl, -⟩
  · have := hL.bN; omega
  · exact dst_lt' hL hu he

/-- The half block of an arc of the dense distance graph. -/
lemma arc_block {u y : ℕ} (hu : u < P.b) (hy : y < P.b) (hne : u ≠ y) :
    ∃ t k, 2 ^ t < P.b ∧ k * 2 ^ t < P.b ∧ y - k * 2 ^ t < min (2 ^ t) (P.b - k * 2 ^ t) ∧
      k * 2 ^ t + (y - k * 2 ^ t) = y ∧ u - sib k * 2 ^ t < hbNc P.b (2 ^ t) k ∧
      sib k * 2 ^ t + (u - sib k * 2 ^ t) = u := by
  obtain ⟨t, q, hb⟩ := dyadic_cover hne
  have hs := Nat.one_le_two_pow (n := t)
  have e2 : 2 * 2 ^ t * q = 2 * (q * 2 ^ t) := by ring
  have e3 : (2 * q + 1) * 2 ^ t = 2 * (q * 2 ^ t) + 2 ^ t := by ring
  have e4 : 2 * q * 2 ^ t = 2 * (q * 2 ^ t) := by ring
  rw [e2] at hb
  rcases hb with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- `u` in the left half, `y` in the right half
    have hsib : sib (2 * q + 1) = 2 * q := by unfold sib; split_ifs <;> omega
    refine ⟨t, 2 * q + 1, ?_⟩
    unfold hbNc; rw [hsib, e3, e4]
    generalize q * 2 ^ t = Q at *
    generalize 2 ^ t = s at *
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- `y` in the left half, `u` in the right half
    have hsib : sib (2 * q) = 2 * q + 1 := by unfold sib; split_ifs <;> omega
    refine ⟨t, 2 * q, ?_⟩
    unfold hbNc; rw [hsib, e3, e4]
    generalize q * 2 ^ t = Q at *
    generalize 2 ^ t = s at *
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ### Operations above the heap -/

lemma lay_low (hL : Lay P) : P.sb + P.N ≤ P.db ∧ P.db + P.N ≤ P.wb ∧ P.b ≤ P.N :=
  ⟨hL.m5, hL.m6, hL.bN⟩

/-- The heap, the settled flags and the distances depend only on the memory below `wb + 3 N`. -/
lemma Hp.low (hL : Lay P) (h : Hp P nm rm) (hn : ∀ a < P.hb, nm' a = nm a)
    (hr : ∀ a < P.hb, rm' a = rm a) : Hp P nm' rm' := by
  have := lay_low hL; unfold Prm.hb at hn hr
  refine ⟨(h.win.congr_wn fun i h1 h2 => hn _ (by omega)).congr (fun x hx => hn _ (by omega))
    (fun x hx => hr _ (by omega)), fun y hy => ?_, fun y hy => ?_, fun y hy h1 => ?_⟩
  · unfold prV; rw [hn _ (by omega)]; exact h.pr_le y hy
  · unfold sfV; rw [hn _ (by omega)]; exact h.sf_le y hy
  · unfold prV at h1; unfold sfV; rw [hn _ (by omega)] at h1 ⊢; exact h.pr_sf y hy h1

lemma Gh.low (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} (h : Gh P K v d nm rm)
    (hn : ∀ a < P.hb, nm' a = nm a) (hr : ∀ a < P.hb, rm' a = rm a) : Gh P K v d nm' rm' := by
  have := lay_low hL; unfold Prm.hb at hn hr
  refine ⟨h.vlt, fun y hy => ?_, fun i hi => ?_, fun y hy h1 => ?_⟩
  · unfold sfV; rw [hn _ (by omega)]; exact h.sf y hy
  · have := h.vlt i hi; unfold dV; rw [hr _ (by omega)]; exact h.dist i hi
  · unfold prV at h1; unfold keyV; rw [hn _ (by omega)] at h1; rw [hr _ (by omega)]
    exact h.just y hy h1

lemma Claim.low (hL : Lay P) {y : ℕ} {w : ℝ} (h : Claim P nm rm y w) (hy : y < P.N)
    (hn : ∀ a < P.hb, nm' a = nm a) (hr : ∀ a < P.hb, rm' a = rm a) : Claim P nm' rm' y w := by
  have := lay_low hL; unfold Prm.hb at hn hr
  unfold Claim prV keyV at *; rw [hn _ (by omega), hr _ (by omega)]; exact h

lemma Arcs.low (hL : Lay P) {ex ex' : ℕ → ℕ → Prop} (h : Arcs P ex nm rm)
    (hn : ∀ a < P.hb, nm' a = nm a) (hr : ∀ a < P.hb, rm' a = rm a)
    (hex : ∀ u < P.N, ∀ e, P.off u ≤ e → e < P.off (u + 1) → ex u e → ex' u e) :
    Arcs P ex' nm' rm' := by
  have := lay_low hL
  intro u hu hsu e h1 h2 hse
  have hdst := dst_lt' hL hu h2
  have es : ∀ y < P.N, sfV P nm' y = sfV P nm y := fun y hy => by
    unfold sfV; unfold Prm.hb at hn; rw [hn _ (by omega)]
  rw [es u hu] at hsu; rw [es _ hdst] at hse
  rcases h u hu hsu e h1 h2 hse with h' | h'
  · exact Or.inl (hex u hu e h1 h2 h')
  · refine Or.inr ?_
    have : dV P rm' u = dV P rm u := by unfold dV; unfold Prm.hb at hr; rw [hr _ (by omega)]
    rw [this]; exact h'.low hL hdst hn hr

/-! ### The effects of the routines of the heap -/

open Classical in
/-- The effect of `decKey`. -/
lemma decEff_of_dec {y₀ : ℕ} {val : ℝ}
    (hp : ∀ x < P.N, prV P nm' x = if DecDo P nm rm y₀ val ∧ x = y₀ then 1 else prV P nm x)
    (hk : ∀ x < P.N, keyV P rm' x = if DecDo P nm rm y₀ val ∧ x = y₀ then val else keyV P rm x)
    (hW : WinOK P.N (prV P nm') (keyV P rm') (wnV P nm') 0)
    (hn : ∀ a, (a < P.wb ∨ P.wb + 2 * P.N ≤ a) → nm' a = nm a)
    (hr : ∀ a, (a < P.wb ∨ P.wb + P.N ≤ a) → rm' a = rm a) :
    DecEff P nm rm nm' rm' y₀ val (DecDo P nm rm y₀ val) := by
  refine ⟨fun x hx h1 h2 => ?_, fun x hx h1 => ?_, fun x hx h1 h2 => ?_, fun x hx h1 => ?_, id,
    hW, hn, hr⟩
  · rw [hp x hx]; split_ifs <;> first | rfl | (exfalso; tauto)
  · rw [hp x hx]; split_ifs; rfl
  · rw [hk x hx]; split_ifs <;> first | rfl | (exfalso; tauto)
  · rw [hk x hx]; split_ifs; rfl

/-! ### A loop rule -/

/-- **A loop with a ghost state, keeping the final potential**: the cost plus the final
potential is at most the initial potential plus `2`. -/
theorem whileLtN_ghost_pot {α : Type} {P' : Input} {W a b : ℕ} {body : Stmt} (I : α → Config → Prop)
    (Φ : α → Config → ℕ) (hI : ∀ x c, I x c → WordsBounded W c)
    (hbody : ∀ x c, I x c → c.nreg a < c.nreg b →
      ∃ x' c' k, Exec P' W body c c' k ∧ I x' c' ∧ Φ x' c' + k + 2 ≤ Φ x c)
    {x : α} {c : Config} (hc : I x c) :
    ∃ x' c' k, Exec P' W (.whileLtN a b body) c c' k ∧ I x' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ x' c' ≤ Φ x c + 2 := by
  induction hn : Φ x c using Nat.strong_induction_on generalizing x c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, k₁, hb, hI₁, hΦ⟩ := hbody x c hc ht
      obtain ⟨x', c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ x₁ c₁) (by omega) hI₁ rfl
      exact ⟨x', c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨x, c, 2, .whileLtN_false ht (hI x c hc), hc, ht, by omega⟩

end FR

end Monge

end PlanarFlow
