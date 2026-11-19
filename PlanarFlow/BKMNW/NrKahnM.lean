module

public import PlanarFlow.BKMNW.NrOs

/-!
# Kahn's algorithm on index arrays (the pure part)

Darts `j < m` with a flag `ps j ≠ 0` (positive), tail label `tl j` and head label `hd j`; the
vertices are the labels `v < m` with `vl v = v` (`KRep`). Kahn's algorithm keeps a queue
`Q[0 … t)` (popped `Q[0 … h)`) and for every vertex the number `IND` of positive darts entering
it from a vertex not yet popped (`kIn`):

* `kIn`, `kIn_pop` (popping `u`: `kIn` drops by the positive darts from `u`);
* `KSt` (the state between two pops), `KIn` (inside the visit of `Q[h]`, after `s` of its
  positive darts), `kst_start`, `kin_start`, `kin_step`, `kin_close`;
* **`kst_final`**: when the queue is exhausted and a rank increases along the positive darts,
  every vertex is in the queue, without duplicates, and the tail of every positive dart comes
  before its head.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {m : ℕ} {vl tl hd ps : ℕ → ℕ}

/-- The vertices: labels fixed by `vl`. -/
def KRep (m : ℕ) (vl : ℕ → ℕ) (v : ℕ) : Prop := v < m ∧ vl v = v

/-- The positive darts entering `w` from a vertex not in `P`. -/
def kIn (m : ℕ) (tl hd ps : ℕ → ℕ) (P : List ℕ) (w : ℕ) : ℕ :=
  ((range m).filter fun j => ps j ≠ 0 ∧ hd j = w ∧ tl j ∉ P).card

/-- The queue as a list. -/
def kQ (Q : ℕ → ℕ) (t : ℕ) : List ℕ := (List.range t).map Q

lemma kQ_succ (Q : ℕ → ℕ) (t : ℕ) : kQ Q (t + 1) = kQ Q t ++ [Q t] := by
  simp [kQ, List.range_succ]

lemma mem_kQ {Q : ℕ → ℕ} {t x : ℕ} : x ∈ kQ Q t ↔ ∃ k < t, Q k = x := by
  simp [kQ]

lemma nrF_mem {u j : ℕ} (h : j ∈ nrF tl ps m u) : j < m ∧ ps j ≠ 0 ∧ tl j = u := by
  simp only [nrF, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

lemma nrF_nodup (u : ℕ) : (nrF tl ps m u).Nodup := (List.nodup_range).filter _

/-- **Popping `u`**: the positive darts from `u` leave the count. -/
lemma kIn_pop (P : List ℕ) {u : ℕ} (hu : u ∉ P) (w : ℕ) :
    kIn m tl hd ps (P ++ [u]) w + ((nrF tl ps m u).filter fun j => hd j = w).length =
      kIn m tl hd ps P w := by
  have e : ((nrF tl ps m u).filter fun j => hd j = w).length =
      ((range m).filter fun j => ps j ≠ 0 ∧ hd j = w ∧ tl j = u).card := by
    rw [← List.toFinset_card_of_nodup ((nrF_nodup u).filter _)]
    congr 1
    ext j
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, b, c⟩ := nrF_mem h1
      exact ⟨a, b, h2, c⟩
    · rintro ⟨a, b, c, d⟩
      refine ⟨?_, c⟩
      simp only [nrF, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨a, b, d⟩
  rw [e, kIn, kIn, ← card_union_of_disjoint]
  · congr 1
    ext j
    simp only [mem_union, mem_filter, mem_range, List.mem_append, List.mem_singleton]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, h2, h3, fun h => h4 (Or.inl h)⟩
      · exact ⟨h1, h2, h3, by rw [h4]; exact hu⟩
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases e : tl j = u
      · exact Or.inr ⟨h1, h2, h3, e⟩
      · exact Or.inl ⟨h1, h2, h3, by tauto⟩
  · rw [disjoint_filter]
    intro j _ h1 h2
    exact h1.2.2 (List.mem_append_right _ (by rw [h2.2.2]; exact List.mem_singleton_self _))

variable (m vl tl hd ps) in
/-- **The state of Kahn's algorithm between two pops.** -/
structure KSt (Q IND : ℕ → ℕ) (h t : ℕ) : Prop where
  ht : h ≤ t
  nd : (kQ Q t).Nodup
  rep : ∀ k < t, KRep m vl (Q k)
  ind : ∀ w, KRep m vl w → IND w = kIn m tl hd ps (kQ Q h) w
  mem : ∀ w, KRep m vl w → (w ∈ kQ Q t ↔ IND w = 0)
  topo : ∀ k < t, ∀ j < m, ps j ≠ 0 → hd j = Q k → ∃ k' < k, Q k' = tl j

variable (m vl tl hd ps) in
/-- **The state inside the visit of `Q[h]`**, after `s` of its positive darts. -/
structure KIn (Q IND : ℕ → ℕ) (h t s : ℕ) : Prop where
  ht : h < t
  nd : (kQ Q t).Nodup
  rep : ∀ k < t, KRep m vl (Q k)
  ind : ∀ w, KRep m vl w →
    IND w + (((nrF tl ps m (Q h)).take s).filter fun j => hd j = w).length =
      kIn m tl hd ps (kQ Q h) w
  mem : ∀ w, KRep m vl w → (w ∈ kQ Q t ↔ IND w = 0)
  topo : ∀ k < t, ∀ j < m, ps j ≠ 0 → hd j = Q k → ∃ k' < k, Q k' = tl j

/-- The start of a visit. -/
lemma kin_start {Q IND : ℕ → ℕ} {h t : ℕ} (hs : KSt m vl tl hd ps Q IND h t) (hlt : h < t) :
    KIn m vl tl hd ps Q IND h t 0 :=
  ⟨hlt, hs.nd, hs.rep, fun w hw => by simp [hs.ind w hw], hs.mem,
    hs.topo⟩

/-- The start: the vertices without positive darts entering them, in the queue. -/
lemma kst_start {Q IND : ℕ → ℕ} {t : ℕ} (hnd : (kQ Q t).Nodup) (hrep : ∀ k < t, KRep m vl (Q k))
    (hind : ∀ w, KRep m vl w → IND w = kIn m tl hd ps [] w)
    (hmem : ∀ w, KRep m vl w → (w ∈ kQ Q t ↔ IND w = 0)) : KSt m vl tl hd ps Q IND 0 t := by
  refine ⟨Nat.zero_le _, hnd, hrep, fun w hw => by simpa [kQ] using hind w hw, hmem,
    fun k hk j hj hp he => ?_⟩
  have h1 := (hmem _ (hrep k hk)).1 (mem_kQ.2 ⟨k, hk, rfl⟩)
  rw [hind _ (hrep k hk), kIn, card_eq_zero, filter_eq_empty_iff] at h1
  exact absurd ⟨hp, he, List.not_mem_nil⟩ (h1 (mem_range.2 hj))

/-- The positive darts of `u` entering `w` are counted. -/
lemma kIn_ge (P : List ℕ) {u : ℕ} (hu : u ∉ P) (w s : ℕ) :
    (((nrF tl ps m u).take s).filter fun j => hd j = w).length ≤ kIn m tl hd ps P w := by
  have := kIn_pop (m := m) (tl := tl) (hd := hd) (ps := ps) P hu w
  have h2 := ((List.take_sublist s (nrF tl ps m u)).filter (fun j => decide (hd j = w))).length_le
  omega

/-- **One positive dart of the visited vertex**: `IND[w] -= 1`, push `w` when it reaches zero. -/
lemma kin_step {Q IND : ℕ → ℕ} {h t s : ℕ} (hk : KIn m vl tl hd ps Q IND h t s)
    (hs : s < (nrF tl ps m (Q h)).length)
    (hhd : ∀ j < m, KRep m vl (hd j)) {j w : ℕ} (hj : (nrF tl ps m (Q h))[s] = j)
    (hw : hd j = w) :
    (IND w - 1 = 0 → KIn m vl tl hd ps (Function.update Q t w)
      (Function.update IND w (IND w - 1)) h (t + 1) (s + 1)) ∧
    (IND w - 1 ≠ 0 → KIn m vl tl hd ps Q (Function.update IND w (IND w - 1)) h t (s + 1)) := by
  obtain ⟨L, hL⟩ : ∃ L, L = nrF tl ps m (Q h) := ⟨_, rfl⟩
  obtain ⟨IND', hI'⟩ : ∃ f, f = Function.update IND w (IND w - 1) := ⟨_, rfl⟩
  rw [← hI']
  have hs' : s < L.length := hL ▸ hs
  have hj' : L[s] = j := by subst hL; exact hj
  suffices H : (IND w - 1 = 0 → KIn m vl tl hd ps (Function.update Q t w) IND' h (t + 1) (s + 1)) ∧
      (IND w - 1 ≠ 0 → KIn m vl tl hd ps Q IND' h t (s + 1)) from H
  have hjL : j ∈ L := hj' ▸ List.getElem_mem hs'
  obtain ⟨hjm, hjp, hjt⟩ := nrF_mem (hL ▸ hjL)
  have hwr : KRep m vl w := hw ▸ hhd j hjm
  have huP : Q h ∉ kQ Q h := by
    intro hm
    have hht := hk.ht
    obtain ⟨k, hk', e⟩ := mem_kQ.1 hm
    have h1 : (kQ Q t)[k]'(by simp [kQ]; omega) = (kQ Q t)[h]'(by simp [kQ]; exact hk.ht) := by
      simp [kQ, e]
    have := List.Nodup.getElem_inj_iff hk.nd |>.1 h1
    omega
  have htake : L.take (s + 1) = L.take s ++ [j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hs', hj']; rfl
  have hge := kIn_ge (m := m) (tl := tl) (hd := hd) (ps := ps) (kQ Q h) huP w (s + 1)
  rw [← hL, htake, List.filter_append] at hge
  simp only [List.filter_cons, List.filter_nil, hw, decide_true, ite_true,
    List.length_append, List.length_cons, List.length_nil] at hge
  have hiw := hk.ind w hwr
  rw [← hL] at hiw
  have hpos : 1 ≤ IND w := by omega
  have hind' : ∀ w', KRep m vl w' →
      IND' w' + (((L.take (s + 1)).filter fun j => hd j = w')).length =
        kIn m tl hd ps (kQ Q h) w' := by
    intro w' hw'
    rw [htake, List.filter_append, hI']
    by_cases e : w' = w
    · subst e
      simp only [Function.update_self, List.filter_cons, List.filter_nil, hw, decide_true,
        ite_true, List.length_append, List.length_cons, List.length_nil]
      omega
    · have e' : ¬ (hd j = w') := fun h' => e (h'.symm.trans hw)
      simp only [Function.update_of_ne e, List.filter_cons, List.filter_nil, e',
        decide_false, Bool.false_eq_true, ite_false, List.append_nil]
      have := hk.ind w' hw'
      rw [← hL] at this; exact this
  have hwq : w ∉ kQ Q t := fun h' => by have := (hk.mem w hwr).1 h'; omega
  -- the tails of the positive darts entering `w` once `IND' w = 0`
  have htail : IND w - 1 = 0 → ∀ j' < m, ps j' ≠ 0 → hd j' = w → tl j' ∈ kQ Q (h + 1) := by
    intro h0 j' hj' hp' he'
    by_contra hn
    rw [kQ_succ, List.mem_append, not_or] at hn
    have hset : ((L.take (s + 1)).filter fun j => hd j = w).toFinset ⊆
        ((range m).filter fun j => ps j ≠ 0 ∧ hd j = w ∧ tl j ∉ kQ Q h) := by
      intro x hx
      rw [List.mem_toFinset, List.mem_filter] at hx
      obtain ⟨x1, x2, x3⟩ := nrF_mem (hL ▸ List.mem_of_mem_take hx.1)
      simp only [mem_filter, mem_range]
      exact ⟨x1, x2, by simpa using hx.2, by rw [x3]; exact huP⟩
    have hj'n : j' ∉ ((L.take (s + 1)).filter fun j => hd j = w).toFinset := by
      intro hx
      rw [List.mem_toFinset, List.mem_filter] at hx
      have := (nrF_mem (hL ▸ List.mem_of_mem_take hx.1)).2.2
      exact hn.2 (by rw [this]; simp)
    have hj'm : j' ∈ ((range m).filter fun j => ps j ≠ 0 ∧ hd j = w ∧ tl j ∉ kQ Q h) := by
      simp only [mem_filter, mem_range]; exact ⟨hj', hp', he', hn.1⟩
    have hcard := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hset, fun e => hj'n (e ▸ hj'm)⟩)
    rw [List.toFinset_card_of_nodup (((hL ▸ nrF_nodup _).sublist (List.take_sublist _ _)).filter _)]
      at hcard
    have := hind' w hwr
    simp only [hI', Function.update_self] at this
    unfold kIn at this
    omega
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hQ : ∀ k < t, Function.update Q t w k = Q k := fun k hk' =>
      Function.update_of_ne (by omega) _ _
    have hkq : kQ (Function.update Q t w) t = kQ Q t := by
      simp only [kQ]; exact List.map_congr_left fun k hk' => hQ k (List.mem_range.1 hk')
    have hkq' : kQ (Function.update Q t w) (t + 1) = kQ Q t ++ [w] := by
      rw [kQ_succ, hkq, Function.update_self]
    have hkh : kQ (Function.update Q t w) h = kQ Q h := by
      simp only [kQ]
      exact List.map_congr_left fun k hk' => hQ k (by have := List.mem_range.1 hk'; have := hk.ht; omega)
    have hQh : Function.update Q t w h = Q h := hQ h hk.ht
    refine ⟨by have := hk.ht; omega, by rw [hkq']; exact List.nodup_append.2 ⟨hk.nd, List.nodup_singleton _,
        fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun e => hwq (e ▸ ha)⟩,
      fun k hk' => ?_, fun w' hw' => ?_, fun w' hw' => ?_, fun k hk' j' hj' hp' he' => ?_⟩
    · by_cases e : k = t
      · subst e; rw [Function.update_self]; exact hwr
      · rw [hQ k (by omega)]; exact hk.rep k (by omega)
    · rw [hQh, hkh, ← hL]; exact hind' w' hw'
    · rw [hkq', List.mem_append, List.mem_singleton]
      by_cases e : w' = w
      · subst e; simp [hI', h0]
      · simp only [hI', Function.update_of_ne e, e, or_false]; exact hk.mem w' hw'
    · by_cases e : k = t
      · subst e
        rw [Function.update_self] at he'
        obtain ⟨k', hk'', e'⟩ := mem_kQ.1 (htail h0 j' hj' hp' he')
        exact ⟨k', by have := hk.ht; omega, by rw [hQ k' (by have := hk.ht; omega)]; exact e'⟩
      · rw [hQ k (by omega)] at he'
        obtain ⟨k', hk'', e'⟩ := hk.topo k (by omega) j' hj' hp' he'
        exact ⟨k', hk'', by rw [hQ k' (by omega)]; exact e'⟩
  · refine ⟨hk.ht, hk.nd, hk.rep, fun w' hw' => by rw [← hL]; exact hind' w' hw',
      fun w' hw' => ?_, hk.topo⟩
    by_cases e : w' = w
    · subst e; simp only [hI', Function.update_self]
      constructor
      · intro h'; exact absurd h' hwq
      · intro h'; exact absurd h' h0
    · simp only [hI', Function.update_of_ne e]; exact hk.mem w' hw'

/-- **The end of a visit.** -/
lemma kin_close {Q IND : ℕ → ℕ} {h t : ℕ}
    (hk : KIn m vl tl hd ps Q IND h t (nrF tl ps m (Q h)).length) :
    KSt m vl tl hd ps Q IND (h + 1) t := by
  have huP : Q h ∉ kQ Q h := by
    intro hm
    have hht := hk.ht
    obtain ⟨k, hk', e⟩ := mem_kQ.1 hm
    have h1 : (kQ Q t)[k]'(by simp [kQ]; omega) =
        (kQ Q t)[h]'(by simp [kQ]; exact hk.ht) := by simp [kQ, e]
    have := List.Nodup.getElem_inj_iff hk.nd |>.1 h1
    omega
  refine ⟨hk.ht, hk.nd, hk.rep, fun w hw => ?_, hk.mem, hk.topo⟩
  have h1 := hk.ind w hw
  rw [List.take_length] at h1
  have h2 := kIn_pop (m := m) (tl := tl) (hd := hd) (ps := ps) (kQ Q h) huP w
  rw [kQ_succ]; omega

/-- **The end of Kahn's algorithm**: with a rank increasing along the positive darts, every
vertex is in the queue. -/
lemma kst_final {Q IND : ℕ → ℕ} {t : ℕ} (hk : KSt m vl tl hd ps Q IND t t) (rk : ℕ → ℕ)
    (hrk : ∀ j < m, ps j ≠ 0 → rk (tl j) < rk (hd j)) (htl : ∀ j < m, KRep m vl (tl j)) :
    ∀ w, KRep m vl w → w ∈ kQ Q t := by
  intro w
  induction hr : rk w using Nat.strong_induction_on generalizing w with
  | _ r ih =>
    intro hw
    by_contra hn
    have h1 := hk.ind w hw
    have h2 : IND w ≠ 0 := fun h0 => hn ((hk.mem w hw).2 h0)
    rw [h1, kIn, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty] at h2
    obtain ⟨j, hj⟩ := h2
    simp only [mem_filter, mem_range] at hj
    obtain ⟨hjm, hjp, hjh, hjt⟩ := hj
    exact hjt (ih (rk (tl j)) (by rw [← hr, ← hjh]; exact hrk j hjm hjp) (tl j) rfl (htl j hjm))

end BKMNW

end PlanarFlow
