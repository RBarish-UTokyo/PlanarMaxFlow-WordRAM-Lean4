module

public import PlanarFlow.DynTree.Rotate

/-!
# Dynamic trees: pushing a reversal bit down

`flipM c` reverses the subtree of `c` lazily: it mirrors the aggregates of `c`, exchanges its two
values and its two tags, and toggles its reversal bit. `pushM x` pushes the reversal bit of `x`
to its children: if it is set, it swaps the children of `x`, flips both, and clears the bit.

Neither changes the virtual forest represented: a flipped tree is stored with the opposite
parity (`enc_flip`), and a push keeps the encoding, the values and the represented forest
(`push_okE`); afterwards the bit of `x` is clear. The splay step pushes the three nodes it
rotates, top down, so that every rotation is at nodes whose bits are clear.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- Reverse the subtree of `c` lazily. -/
def flipM (c : ℕ) (M : Mem) : Mem :=
  ⟨upd (setOwn B c (own B M c).mir M).nm (adr B c 10) (if rv B M c then 0 else 1),
    upd (upd (upd (upd (setOwn B c (own B M c).mir M).rm (adr B c 0) (vl2 B M c)) (adr B c 5)
      (vl B M c)) (adr B c 1) (tg2 B M c)) (adr B c 6) (tg B M c)⟩

/-- Push the reversal bit of `x` to its children. -/
def pushM (x : ℕ) (M : Mem) : Mem :=
  if rv B M x then
    ⟨upd (upd (upd (flipM B (rc B M x) (flipM B (lc B M x) M)).nm (adr B x 1) (rc B M x))
      (adr B x 2) (lc B M x)) (adr B x 10) 0, (flipM B (rc B M x) (flipM B (lc B M x) M)).rm⟩
  else M

section fields
variable {B n} {M : Mem}

lemma flipM_agr {c v : ℕ} (h : v ≠ c) : Agr B M (flipM B c M) v := by
  intro j hj
  have e := setOwn_agr B (M := M) (own B M c).mir h j hj
  simp only [flipM]
  refine ⟨?_, ?_⟩
  · rw [upd_adr _ _ hj (by omega)]; simp [h, e.1]
  · simp only [upd_adr _ _ hj (show (6 : ℕ) < 16 by omega), upd_adr _ _ hj (show (1 : ℕ) < 16 by omega),
      upd_adr _ _ hj (show (5 : ℕ) < 16 by omega), upd_adr _ _ hj (show (0 : ℕ) < 16 by omega)]
    simp [h, e.2]

lemma flipM_nm {c v j : ℕ} (hj : j < 16) (h : j < 3 ∨ j = 4 ∨ 11 ≤ j) :
    (flipM B c M).nm (adr B v j) = M.nm (adr B v j) := by
  simp only [flipM, upd_adr _ _ hj (show (10 : ℕ) < 16 by omega)]
  rw [setOwn_nm B _ hj (by omega)]
  split_ifs <;> first | rfl | omega

lemma flipM_rv_ne {c v : ℕ} (h : v ≠ c) : rv B (flipM B c M) v = rv B M v :=
  (flipM_agr h).rv B

lemma flipM_rv (c : ℕ) : rv B (flipM B c M) c = !rv B M c := by
  simp only [rv, rvw, flipM, upd_adr _ _ (show (10 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega)]
  simp only [and_self, ↓reduceIte]
  split_ifs with h <;> simp_all

lemma flipM_own (c : ℕ) : own B (flipM B c M) c = (own B M c).mir := by
  have h := own_setOwn B (M := M) (u := c) (own B M c).mir
  simp only [own, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm, flipM] at h ⊢
  simp only [upd_adr _ _ (show (3 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (5 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (6 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (7 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (8 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (9 : ℕ) < 16 by omega) (show (10 : ℕ) < 16 by omega),
    upd_adr _ _ (show (2 : ℕ) < 16 by omega) (show (6 : ℕ) < 16 by omega),
    upd_adr _ _ (show (3 : ℕ) < 16 by omega) (show (6 : ℕ) < 16 by omega),
    upd_adr _ _ (show (4 : ℕ) < 16 by omega) (show (6 : ℕ) < 16 by omega),
    upd_adr _ _ (show (7 : ℕ) < 16 by omega) (show (6 : ℕ) < 16 by omega),
    upd_adr _ _ (show (8 : ℕ) < 16 by omega) (show (6 : ℕ) < 16 by omega),
    upd_adr _ _ (show (2 : ℕ) < 16 by omega) (show (1 : ℕ) < 16 by omega),
    upd_adr _ _ (show (3 : ℕ) < 16 by omega) (show (1 : ℕ) < 16 by omega),
    upd_adr _ _ (show (4 : ℕ) < 16 by omega) (show (1 : ℕ) < 16 by omega),
    upd_adr _ _ (show (7 : ℕ) < 16 by omega) (show (1 : ℕ) < 16 by omega),
    upd_adr _ _ (show (8 : ℕ) < 16 by omega) (show (1 : ℕ) < 16 by omega),
    upd_adr _ _ (show (2 : ℕ) < 16 by omega) (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ (show (3 : ℕ) < 16 by omega) (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ (show (4 : ℕ) < 16 by omega) (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ (show (7 : ℕ) < 16 by omega) (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ (show (8 : ℕ) < 16 by omega) (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ (show (2 : ℕ) < 16 by omega) (show (0 : ℕ) < 16 by omega),
    upd_adr _ _ (show (3 : ℕ) < 16 by omega) (show (0 : ℕ) < 16 by omega),
    upd_adr _ _ (show (4 : ℕ) < 16 by omega) (show (0 : ℕ) < 16 by omega),
    upd_adr _ _ (show (7 : ℕ) < 16 by omega) (show (0 : ℕ) < 16 by omega),
    upd_adr _ _ (show (8 : ℕ) < 16 by omega) (show (0 : ℕ) < 16 by omega)] at h ⊢
  simpa using h

lemma flipM_vals (c : ℕ) : vl B (flipM B c M) c = vl2 B M c ∧ vl2 B (flipM B c M) c = vl B M c ∧
    tg B (flipM B c M) c = tg2 B M c ∧ tg2 B (flipM B c M) c = tg B M c := by
  simp only [vl, vl2, tg, tg2, flipM]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [upd_adr]

lemma flipM_rd (c : ℕ) : rd B (flipM B c M) c = (rd B M c).mir := by
  obtain ⟨e1, e2, e3, e4⟩ := flipM_vals (B := B) (M := M) c
  simp only [rd, flipM_own, e3, e4, Ag.mir_addTags]

lemma flipM_vlc (c : ℕ) (k : Bool) : vlc B (flipM B c M) k c = vlc B M (!k) c := by
  obtain ⟨e1, e2, -, -⟩ := flipM_vals (B := B) (M := M) c
  cases k <;> simp [vlc, e1, e2]

lemma flipM_tgc (c : ℕ) (k : Bool) : tgc B (flipM B c M) k c = tgc B M (!k) c := by
  obtain ⟨-, -, e3, e4⟩ := flipM_vals (B := B) (M := M) c
  cases k <;> simp [tgc, e3, e4]

lemma flipM_frame {c : ℕ} (hc : c ≤ n) : MemFrame B n M (flipM B c M) := by
  intro a ha
  have e := setOwn_frame B n (M := M) (own B M c).mir hc a ha
  simp only [flipM, upd_apply]
  unfold adr at *
  refine ⟨?_, ?_⟩ <;> split_ifs <;> first | omega | simp [e.1, e.2]

lemma flipM_nil (hN : NilOK B n M) {c : ℕ} : NilOK B n (flipM B c M) := by
  by_cases hc : c = n
  · subst hc
    have e := flipM_own (B := B) (M := M) c
    have hc4 := congrArg Ag.c e
    have hs1 := congrArg Ag.s1 e
    have hs2 := congrArg Ag.s2 e
    simp only [own, Ag.mir] at hc4 hs1 hs2
    exact ⟨by simp only [lc]; rw [flipM_nm (by omega) (by omega)]; exact hN.lc,
      by simp only [rc]; rw [flipM_nm (by omega) (by omega)]; exact hN.rc,
      by rw [hc4]; exact hN.cnt, by rw [hs1]; exact hN.sm2, by rw [hs2]; exact hN.sm⟩
  · have h := flipM_agr (B := B) (M := M) (Ne.symm hc)
    exact ⟨by simp only [lc]; rw [(h 1 (by omega)).1]; exact hN.lc,
      by simp only [rc]; rw [(h 2 (by omega)).1]; exact hN.rc,
      by simp only [cnt]; rw [(h 4 (by omega)).2]; exact hN.cnt,
      by simp only [sm]; rw [(h 3 (by omega)).2]; exact hN.sm,
      by simp only [sm2]; rw [(h 8 (by omega)).2]; exact hN.sm2⟩

end fields

/-- **A flipped tree is stored with the opposite parity**, and has the same values. -/
theorem enc_flip {M : Mem} (hN : NilOK B n M) {s : VT} {p : ℕ} {ρ : Bool} (h : Enc B n M s p ρ)
    (hnd : (nodes s).Nodup) (hs : s ≠ VT.leaf) :
    Enc B n (flipM B (rt n s) M) s p (!ρ) ∧
      ∀ k, rs B (flipM B (rt n s) M) s (!ρ) k = rs B M s ρ k := by
  cases h with
  | leaf => exact absurd rfl hs
  | @node l r x p ds _ h1 h2 h3 h4 h5 h6 h7 =>
    simp only [rt_node]
    simp only [nodes_node, List.nodup_append, List.nodup_cons] at hnd
    have hN' := flipM_nil (n := n) (M := M) (c := x) hN
    have nx : ∀ u ∈ nodes l ++ nodes r ++ nodesL ds, u ≠ x := by
      intro u hu e; subst e
      simp only [List.mem_append] at hu
      rcases hu with (hu | hu) | hu
      · exact hnd.1.2.2 u hu u (by simp) rfl
      · exact hnd.1.2.1.1 hu
      · exact hnd.2.2 u (by simp) u hu rfl
    have ag : ∀ u ∈ nodes l ++ nodes r ++ nodesL ds, Agr B M (flipM B x M) u :=
      fun u hu => flipM_agr (nx u hu)
    have hσ : cσ B (flipM B x M) (!ρ) x = cσ B M ρ x := by
      simp only [cσ, flipM_rv]; cases ρ <;> simp
    have elc : lc B (flipM B x M) x = lc B M x := by simp only [lc]; rw [flipM_nm (by omega) (by omega)]
    have erc : rc B (flipM B x M) x = rc B M x := by simp only [rc]; rw [flipM_nm (by omega) (by omega)]
    have hS : ∀ σ, lcS B (flipM B x M) σ x = lcS B M σ x := by intro σ; simp only [lcS, elc, erc]
    have lk : ∀ s : VT, (∀ u ∈ nodes s, u ∈ nodes l ++ nodes r ++ nodesL ds) →
        Look B n M (flipM B x M) (rt n s) (rt n s) := fun s hs =>
      look_rt B n hN hN' s (fun u hu => ag u (hs u hu))
    have hl : Look B n M (flipM B x M) (lc B M x) (lc B (flipM B x M) x) ∧
        Look B n M (flipM B x M) (rc B M x) (rc B (flipM B x M) x) := by
      rw [elc, erc]
      cases e : cσ B M ρ x <;> simp only [lcS, e, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] at h2 h3
      · rw [h2, h3]; exact ⟨lk l (by intro u hu; simp [hu]), lk r (by intro u hu; simp [hu])⟩
      · rw [h2, h3]; exact ⟨lk r (by intro u hu; simp [hu]), lk l (by intro u hu; simp [hu])⟩
    refine ⟨.node ?_ ?_ ?_ ?_ ?_ ?_ ?_, fun k => ?_⟩
    · simp only [par]; rw [flipM_nm (by omega) (by omega)]; exact h1
    · rw [hσ, hS]; exact h2
    · rw [hσ, hS]; exact h3
    · rw [aggOK_iff] at h4 ⊢
      rw [flipM_own, h4, flipM_rv]
      have c1 := hl.1.childOK B n
      have c2 := hl.2.childOK B n
      have e3 : ∀ R : Bool, comb n (lc B (flipM B x M) x) (rd B (flipM B x M) (lc B (flipM B x M) x)) x
          (vlc B (flipM B x M) R x) (vlc B (flipM B x M) (!R) x) (rc B (flipM B x M) x)
          (rd B (flipM B x M) (rc B (flipM B x M) x)) =
          comb n (lc B M x) (rd B M (lc B M x)) x (vlc B M (!R) x) (vlc B M R x) (rc B M x)
            (rd B M (rc B M x)) := by
        intro R
        rw [flipM_vlc, flipM_vlc, Bool.not_not]
        exact comb_congr n hl.1.lt.symm ⟨c1.1, fun hh => c1.2 (hl.1.lt.mpr hh)⟩ hl.2.lt.symm
          ⟨c2.1, fun hh => c2.2 (hl.2.lt.mpr hh)⟩
      cases hR : rv B M x
      · simp only [Bool.not_false, Ag.mirIf_true, Ag.mirIf_false]
        rw [e3 true]; rfl
      · simp only [Bool.not_true, Ag.mirIf_true, Ag.mirIf_false, Ag.mir_mir]
        rw [e3 false]; rfl
    · rw [hσ]; exact enc_frame_all B n hN hN' h5 hnd.1.1 (fun u hu => ag u (by simp [hu]))
    · rw [hσ]; exact enc_frame_all B n hN hN' h6 hnd.1.2.1.2 (fun u hu => ag u (by simp [hu]))
    · exact fun d hd => enc_frame_all B n hN hN' (h7 d hd) (nodup_of_mem_nodesL hnd.2.1 hd)
        (fun u hu => ag u (by simp [mem_nodesL_of hd hu]))
    · have e1 : (k ^^ !ρ) = !(k ^^ ρ) := by cases k <;> cases ρ <;> rfl
      simp only [rs_node, hσ, e1, flipM_vlc, flipM_tgc, Bool.not_not]
      rw [rs_frame B l (fun u hu => (ag u (by simp [hu])).agrV B),
        rs_frame B r (fun u hu => (ag u (by simp [hu])).agrV B)]

/-! ### The memory after a push -/

/-- `M'` holds at `c` the flipped record of `c` in `M`. -/
def FlipAt (M M' : Mem) (c : ℕ) : Prop :=
  ∀ j < 16, M'.nm (adr B c j) = (flipM B c M).nm (adr B c j) ∧
    M'.rm (adr B c j) = (flipM B c M).rm (adr B c j)

section pushfields
variable {B n} {M : Mem}

/-- The flipped record of `c` only depends on the record of `c`. -/
lemma flipM_congr {N : Mem} {c : ℕ} (h : Agr B M N c) : FlipAt B M (flipM B c N) c := by
  have ho : own B N c = own B M c := (h.agrC B).ownEq B
  have hr : rv B N c = rv B M c := (h.agrC B).rvEq B
  intro j hj
  simp only [flipM, setOwn, ho, hr, vl, vl2, tg, tg2, upd_apply, adr_eq_iff hj (by omega : (10:ℕ) < 16),
    adr_eq_iff hj (by omega : (9:ℕ) < 16), adr_eq_iff hj (by omega : (8:ℕ) < 16),
    adr_eq_iff hj (by omega : (7:ℕ) < 16), adr_eq_iff hj (by omega : (6:ℕ) < 16),
    adr_eq_iff hj (by omega : (5:ℕ) < 16), adr_eq_iff hj (by omega : (3:ℕ) < 16),
    adr_eq_iff hj (by omega : (2:ℕ) < 16), adr_eq_iff hj (by omega : (4:ℕ) < 16),
    adr_eq_iff hj (by omega : (1:ℕ) < 16), adr_eq_iff hj (by omega : (0:ℕ) < 16),
    (h 0 (by omega)).2, (h 5 (by omega)).2, (h 1 (by omega)).2, (h 6 (by omega)).2]
  refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | exact (h j hj).1 | exact (h j hj).2

lemma FlipAt.agr {M' : Mem} {c u : ℕ} (h : FlipAt B M M' c) (hu : u = c) :
    Agr B (flipM B c M) M' u := by
  subst hu; intro j hj; exact ⟨(h j hj).1, (h j hj).2⟩

lemma Agr.trans' {M1 M2 M3 : Mem} {u : ℕ} (h1 : Agr B M1 M2 u) (h2 : Agr B M2 M3 u) :
    Agr B M1 M3 u := fun j hj => ⟨((h2 j hj).1).trans (h1 j hj).1, ((h2 j hj).2).trans (h1 j hj).2⟩

lemma Agr.symm' {M1 M2 : Mem} {u : ℕ} (h : Agr B M1 M2 u) : Agr B M2 M1 u :=
  fun j hj => ⟨((h j hj).1).symm, ((h j hj).2).symm⟩

/-- The memory after pushing a set bit. -/
lemma pushM_fields {x : ℕ} (hx : rv B M x = true) (hxa : x ≠ lc B M x) (hxb : x ≠ rc B M x) :
    (∀ v, v ≠ x → v ≠ lc B M x → v ≠ rc B M x → Agr B M (pushM B x M) v) ∧
    (lc B M x ≠ rc B M x → FlipAt B M (pushM B x M) (lc B M x) ∧
      FlipAt B M (pushM B x M) (rc B M x)) ∧
    par B (pushM B x M) x = par B M x ∧ fpar B (pushM B x M) x = fpar B M x ∧
    own B (pushM B x M) x = own B M x ∧ vl B (pushM B x M) x = vl B M x ∧
    vl2 B (pushM B x M) x = vl2 B M x ∧ tg B (pushM B x M) x = tg B M x ∧
    tg2 B (pushM B x M) x = tg2 B M x ∧ lc B (pushM B x M) x = rc B M x ∧
    rc B (pushM B x M) x = lc B M x ∧ rv B (pushM B x M) x = false := by
  generalize ha : lc B M x = a at hxa hxb
  generalize hb : rc B M x = b at hxa hxb
  have e1 : Agr B M (flipM B b (flipM B a M)) x :=
    (flipM_agr hxa).trans' (flipM_agr hxb)
  have hP : pushM B x M = ⟨upd (upd (upd (flipM B b (flipM B a M)).nm (adr B x 1) b)
      (adr B x 2) a) (adr B x 10) 0, (flipM B b (flipM B a M)).rm⟩ := by
    simp only [pushM, hx, ↓reduceIte, ha, hb]
  have hX : ∀ v, v ≠ x → Agr B (flipM B b (flipM B a M)) (pushM B x M) v := by
    intro v hv j hj
    rw [hP]; simp [upd_adr _ _ hj, hv]
  have kN : ∀ j < 16, j ≠ 1 → j ≠ 2 → j ≠ 10 → (pushM B x M).nm (adr B x j) = M.nm (adr B x j) := by
    intro j hj h1 h2 h10
    rw [hP]; simp only [upd_adr _ _ hj (show (10 : ℕ) < 16 by omega),
      upd_adr _ _ hj (show (2 : ℕ) < 16 by omega), upd_adr _ _ hj (show (1 : ℕ) < 16 by omega)]
    simp only [h1, h2, h10, and_false, ↓reduceIte]
    exact (e1 j hj).1
  have kR : ∀ j < 16, (pushM B x M).rm (adr B x j) = M.rm (adr B x j) := by
    intro j hj; rw [hP]; exact (e1 j hj).2
  refine ⟨fun v h1 h2 h3 => ((flipM_agr h2).trans' (flipM_agr h3)).trans' (hX v h1),
    fun hab => ⟨?_, ?_⟩, kN 0 (by omega) (by omega) (by omega) (by omega),
    kN 4 (by omega) (by omega) (by omega) (by omega), ?_, kR 0 (by omega), kR 5 (by omega),
    kR 1 (by omega), kR 6 (by omega), by rw [hP]; simp [lc, upd_adr],
    by rw [hP]; simp [rc, upd_adr], by rw [hP]; simp [rv, rvw]⟩
  · intro j hj
    have h1 := hX a (Ne.symm hxa) j hj
    have h2 := (flipM_agr (B := B) (M := flipM B a M) (c := b) hab) j hj
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  · intro j hj
    have h1 := hX b (Ne.symm hxb) j hj
    have h2 := flipM_congr (B := B) (M := M) (N := flipM B a M) (c := b) (flipM_agr (Ne.symm hab)) j hj
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  · simp only [own, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm]
    rw [kR 2 (by omega), kR 3 (by omega), kR 4 (by omega), kR 7 (by omega), kR 8 (by omega),
      kN 3 (by omega) (by omega) (by omega) (by omega), kN 5 (by omega) (by omega) (by omega) (by omega),
      kN 6 (by omega) (by omega) (by omega) (by omega), kN 7 (by omega) (by omega) (by omega) (by omega),
      kN 8 (by omega) (by omega) (by omega) (by omega), kN 9 (by omega) (by omega) (by omega) (by omega)]

end pushfields

section pushmore
variable {B n} {M : Mem}

lemma pushM_keep {x v j : ℕ} (hj : j < 16) (h : j = 0 ∨ j = 4) :
    (pushM B x M).nm (adr B v j) = M.nm (adr B v j) := by
  unfold pushM
  split_ifs
  · simp only [upd_adr _ _ hj (show (10 : ℕ) < 16 by omega),
      upd_adr _ _ hj (show (2 : ℕ) < 16 by omega), upd_adr _ _ hj (show (1 : ℕ) < 16 by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), flipM_nm hj (by omega),
      flipM_nm hj (by omega)]
  · rfl

lemma pushM_rv_self (x : ℕ) : rv B (pushM B x M) x = false := by
  unfold pushM
  split_ifs with h
  · simp [rv, rvw, upd_adr]
  · simpa using h

lemma pushM_agr {x v : ℕ} (h1 : v ≠ x) (h2 : v ≠ lc B M x) (h3 : v ≠ rc B M x) :
    Agr B M (pushM B x M) v := by
  by_cases hx : rv B M x = true
  · intro j hj
    have e := ((flipM_agr (B := B) (M := M) h2).trans' (flipM_agr h3)) j hj
    simp only [pushM, hx, ↓reduceIte]
    simp [upd_adr _ _ hj, h1, e.1, e.2]
  · simp only [pushM, hx]; exact fun j _ => ⟨rfl, rfl⟩

lemma pushM_frame {x : ℕ} (hx : x ≤ n) (ha : lc B M x ≤ n) (hb : rc B M x ≤ n) :
    MemFrame B n M (pushM B x M) := by
  unfold pushM
  split_ifs
  · have e := (flipM_frame (n := n) (M := M) ha).trans B n (flipM_frame (n := n) hb)
    intro a' ha'
    refine ⟨?_, (e a' ha').2⟩
    simp only [upd_apply]; unfold adr at *
    split_ifs <;> first | omega | exact (e a' ha').1
  · exact MemFrame.refl B n M

lemma pushM_nil (hN : NilOK B n M) {x : ℕ} (hx : x < n) : NilOK B n (pushM B x M) := by
  unfold pushM
  split_ifs
  · have h := flipM_nil (n := n) (c := rc B M x) (flipM_nil (n := n) (c := lc B M x) hN)
    have hxn : n ≠ x := by omega
    exact ⟨by simp only [lc]; simp [upd_adr, hxn]; exact h.lc,
      by simp only [rc]; simp [upd_adr, hxn]; exact h.rc, h.cnt, h.sm, h.sm2⟩
  · exact hN

end pushmore

/-- **A push keeps a stored subtree**, its values, and everything outside it. -/
theorem pushLocal {M : Mem} (hN : NilOK B n M) {l r : VT} {x z : ℕ} {ds : List VT} {π : Bool}
    (hsE : Enc B n M (node l x r ds) z π) (hnd : (nodes (node l x r ds)).Nodup)
    (hlts : ∀ u ∈ nodes (node l x r ds), u < n) (hzs : ∀ u ∈ nodes (node l x r ds), u ≠ z) :
    Enc B n (pushM B x M) (node l x r ds) z π ∧
    VEq B M (pushM B x M) (node l x r ds) (node l x r ds) π ∧
    NilOK B n (pushM B x M) ∧
    (∀ u < n, u ∉ nodes (node l x r ds) → Agr B M (pushM B x M) u) ∧
    rv B (pushM B x M) x = false := by
  have hx : x < n := hlts x (by simp)
  by_cases hrv : rv B M x = false
  · have e : pushM B x M = M := by simp [pushM, hrv]
    rw [e]
    exact ⟨hsE, fun k => ⟨rfl, fun _ => Iff.rfl⟩, hN, fun u _ _ _ _ => ⟨rfl, rfl⟩, hrv⟩
  have hrv' : rv B M x = true := by simpa using hrv
  rw [enc_node_iff] at hsE
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsE
  have hσ : cσ B M π x = !π := by simp [cσ, hrv']
  rw [hσ] at h2 h3 h5 h6
  simp only [Bool.not_not] at h3
  simp only [nodes_node, List.nodup_append, List.nodup_cons] at hnd
  -- the children
  have hrtl : ∀ s : VT, s ≠ VT.leaf → (∀ u ∈ nodes s, u ≠ x) → rt n s ≠ x := fun s hs h =>
    h _ (rt_mem_nodes hs n)
  have nxl : ∀ u ∈ nodes l, u ≠ x := fun u hu e => hnd.1.2.2 u hu x (by simp) e
  have nxr : ∀ u ∈ nodes r, u ≠ x := fun u hu e => hnd.1.2.1.1 (e ▸ hu)
  have hlr : ∀ u ∈ nodes l, ∀ v ∈ nodes r, u ≠ v := fun u hu v hv => hnd.1.2.2 u hu v (by simp [hv])
  have hrt : ∀ s : VT, (∀ u ∈ nodes s, u < n) → (rt n s < n ↔ s ≠ VT.leaf) := by
    intro s hs; cases s with
    | leaf => simp
    | node a y b dy => simp [hs y (by simp)]
  have hlts_l : ∀ u ∈ nodes l, u < n := fun u hu => hlts u (by simp [hu])
  have hlts_r : ∀ u ∈ nodes r, u < n := fun u hu => hlts u (by simp [hu])
  -- `a = lc x`, `b = rc x` are the roots of `l`, `r` in some order
  have hab : (lc B M x = rt n l ∧ rc B M x = rt n r) ∨ (lc B M x = rt n r ∧ rc B M x = rt n l) := by
    cases π <;> simp only [lcS, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2 h3
    · exact Or.inr ⟨h3, h2⟩
    · exact Or.inl ⟨h2, h3⟩
  have hxa : x ≠ lc B M x := by
    rcases hab with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1]
    · by_cases hl : l = VT.leaf
      · subst hl; simp; omega
      · exact (hrtl l hl nxl).symm
    · by_cases hr : r = VT.leaf
      · subst hr; simp; omega
      · exact (hrtl r hr nxr).symm
  have hxb : x ≠ rc B M x := by
    rcases hab with ⟨-, e1⟩ | ⟨-, e1⟩ <;> rw [e1]
    · by_cases hr : r = VT.leaf
      · subst hr; simp; omega
      · exact (hrtl r hr nxr).symm
    · by_cases hl : l = VT.leaf
      · subst hl; simp; omega
      · exact (hrtl l hl nxl).symm
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12⟩ := pushM_fields hrv' hxa hxb
  have hN' : NilOK B n (pushM B x M) := pushM_nil hN hx
  -- a subtree of `x` is stored with flipped parity
  have child : ∀ s : VT, (s = l ∨ s = r) → Enc B n M s x (!π) →
      Enc B n (pushM B x M) s x π ∧ (∀ k, rs B (pushM B x M) s π k = rs B M s (!π) k) ∧
        (∀ k, dV B (pushM B x M) s k = dV B M s k) ∧
        (rt n s < n → rd B (pushM B x M) (rt n s) = (rd B M (rt n s)).mir) := by
    intro s hs hE
    have hnds : (nodes s).Nodup := by rcases hs with rfl | rfl; exact hnd.1.1; exact hnd.1.2.1.2
    have hltss : ∀ u ∈ nodes s, u < n := by rcases hs with rfl | rfl; exact hlts_l; exact hlts_r
    by_cases hsl : s = VT.leaf
    · subst hsl; exact ⟨.leaf _ _, fun _ => rfl, fun _ => rfl, fun h => absurd h (lt_irrefl n)⟩
    have hc : rt n s < n := (hrt s hltss).mpr hsl
    have hdistinct : lc B M x ≠ rc B M x := by
      rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> intro e
      · rcases hs with rfl | rfl
        · cases r with
          | leaf => simp at e; omega
          | node a' y' b' d' => exact hlr _ (rt_mem_nodes hsl n) y' (by simp) (by simpa using e)
        · cases l with
          | leaf => simp at e; omega
          | node a' y' b' d' => exact hlr y' (by simp) _ (rt_mem_nodes hsl n) (by simpa using e)
      · rcases hs with rfl | rfl
        · cases r with
          | leaf => simp at e; omega
          | node a' y' b' d' => exact hlr _ (rt_mem_nodes hsl n) y' (by simp) (by simpa using e.symm)
        · cases l with
          | leaf => simp at e; omega
          | node a' y' b' d' => exact hlr y' (by simp) _ (rt_mem_nodes hsl n) (by simpa using e.symm)
    have hflip : FlipAt B M (pushM B x M) (rt n s) := by
      obtain ⟨g1, g2⟩ := F2 hdistinct
      rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hs with rfl | rfl
      · rw [← e1]; exact g1
      · rw [← e2]; exact g2
      · rw [← e2]; exact g2
      · rw [← e1]; exact g1
    have hothers : ∀ u ∈ nodes s, u ≠ rt n s → Agr B M (pushM B x M) u := by
      intro u hu hne
      refine F1 u ?_ ?_ ?_
      · rcases hs with rfl | rfl; exact nxl u hu; exact nxr u hu
      · intro e; rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at e <;> rcases hs with rfl | rfl
        · exact hne e
        · cases l with
          | leaf => have := hltss u hu; simp at e; omega
          | node a' y' b' d' => exact hlr y' (by simp) u hu (by simpa using e.symm)
        · cases r with
          | leaf => have := hltss u hu; simp at e; omega
          | node a' y' b' d' => exact hlr u hu y' (by simp) (by simpa using e)
        · exact hne e
      · intro e; rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e2] at e <;> rcases hs with rfl | rfl
        · cases r with
          | leaf => have := hltss u hu; simp at e; omega
          | node a' y' b' d' => exact hlr u hu y' (by simp) (by simpa using e)
        · exact hne e
        · exact hne e
        · cases l with
          | leaf => have := hltss u hu; simp at e; omega
          | node a' y' b' d' => exact hlr y' (by simp) u hu (by simpa using e.symm)
    obtain ⟨E1, E2⟩ := enc_flip B n hN hE hnds hsl
    rw [Bool.not_not] at E1
    have hN1 := flipM_nil (n := n) (c := rt n s) hN
    have ag : ∀ u ∈ nodes s, Agr B (flipM B (rt n s) M) (pushM B x M) u := by
      intro u hu
      by_cases hu' : u = rt n s
      · exact hflip.agr hu'
      · exact (flipM_agr hu').symm'.trans' (hothers u hu hu')
    refine ⟨enc_frame_all B n hN1 hN' E1 hnds ag, fun k => ?_,
      fun k => dV_frame_root B n (fun u hu hne => (hothers u hu hne).agrV B) hnds k, fun _ => ?_⟩
    · rw [rs_frame B s (fun u hu => (ag u hu).agrV B), ← E2, Bool.not_not]
    · rw [(hflip.agr rfl).rdEq B, flipM_rd]
  obtain ⟨cl1, cl2, cl3, cl4⟩ := child l (Or.inl rfl) h5
  obtain ⟨cr1, cr2, cr3, cr4⟩ := child r (Or.inr rfl) h6
  have nil0 : ∀ N : Mem, NilOK B n N → (rd B N n).c = 0 ∧ (rd B N n).s1 = 0 ∧ (rd B N n).s2 = 0 := by
    intro N hN; simp [rd, own, Ag.addTags, hN.cnt, hN.sm, hN.sm2]
  have chk : ∀ s : VT, (s = l ∨ s = r) → ChildOK n (rt n s) (rd B M (rt n s)).mir
      (rd B (pushM B x M) (rt n s)) := by
    intro s hs
    have hltss : ∀ u ∈ nodes s, u < n := by rcases hs with rfl | rfl; exact hlts_l; exact hlts_r
    have e4 : rt n s < n → rd B (pushM B x M) (rt n s) = (rd B M (rt n s)).mir := by
      rcases hs with rfl | rfl; exact cl4; exact cr4
    by_cases hc : rt n s < n
    · rw [e4 hc]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ => rfl⟩
    · have : rt n s = n := by
        cases s with
        | leaf => rfl
        | node a' y' b' d' => exact absurd (hltss y' (by simp)) (by simpa using hc)
      rw [this]
      obtain ⟨a1, a2, a3⟩ := nil0 M hN
      obtain ⟨b1, b2, b3⟩ := nil0 _ hN'
      exact ⟨⟨by rw [Ag.mir_c, a1, b1], by simp only [Ag.mir]; rw [a3, b2],
        by simp only [Ag.mir]; rw [a2, b3]⟩, fun h => absurd h (lt_irrefl n)⟩
  have nds : ∀ u ∈ nodesL ds, u ≠ x ∧ u ≠ lc B M x ∧ u ≠ rc B M x := by
    intro u hu
    have hun : u < n := hlts u (by simp [hu])
    have nl : ∀ v ∈ nodes l, u ≠ v := fun v hv e => hnd.2.2 v (by simp [hv]) u hu e.symm
    have nr : ∀ v ∈ nodes r, u ≠ v := fun v hv e => hnd.2.2 v (by simp [hv]) u hu e.symm
    have nrt : ∀ s : VT, (∀ v ∈ nodes s, u ≠ v) → u ≠ rt n s := by
      intro s h; cases s with
      | leaf => simp; omega
      | node a' y' b' d' => exact h y' (by simp)
    refine ⟨fun e => hnd.2.2 x (by simp) u hu e.symm, ?_, ?_⟩ <;>
      rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1]; exact nrt l nl
    · rw [e1]; exact nrt r nr
    · rw [e2]; exact nrt r nr
    · rw [e2]; exact nrt l nl
  have agds : ∀ u ∈ nodesL ds, Agr B M (pushM B x M) u := fun u hu =>
    F1 u (nds u hu).1 (nds u hu).2.1 (nds u hu).2.2
  have hσ' : cσ B (pushM B x M) π x = π := by simp [cσ, F12]
  refine ⟨?_, ?_, hN', ?_, F12⟩
  · rw [enc_node_iff, hσ']
    refine ⟨by rw [F3]; exact h1, ?_, ?_, ?_, cl1, cr1, fun d hd =>
      enc_frame_all B n hN hN' (h7 d hd) (nodup_of_mem_nodesL hnd.2.1 hd)
        (fun u hu => agds u (mem_nodesL_of hd hu))⟩
    · cases π <;> simp only [lcS, F10, F11, Bool.false_eq_true, ↓reduceIte] at h2 h3 ⊢ <;>
        assumption
    · cases π <;> simp only [lcS, F10, F11, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at h2 h3 ⊢ <;> assumption
    · rw [aggOK_iff] at h4 ⊢
      rw [F5, h4, F12, hrv']
      simp only [Ag.mirIf_true, Ag.mirIf_false, Bool.not_true, Bool.not_false, mir_comb]
      have v1 : vlc B (pushM B x M) false x = vlc B M false x := by simp [vlc, F6]
      have v2 : vlc B (pushM B x M) true x = vlc B M true x := by simp [vlc, F7]
      rw [F10, F11, v1, v2]
      rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact comb_congr n Iff.rfl (chk r (Or.inr rfl)) Iff.rfl (chk l (Or.inl rfl))
      · rw [e1, e2]; exact comb_congr n Iff.rfl (chk l (Or.inl rfl)) Iff.rfl (chk r (Or.inr rfl))
  · intro k
    have t1 : tgc B (pushM B x M) (k ^^ π) x = tgc B M (k ^^ π) x := by
      cases (k ^^ π) <;> simp [tgc, F8, F9]
    have t2 : vlc B (pushM B x M) (k ^^ π) x = vlc B M (k ^^ π) x := by
      cases (k ^^ π) <;> simp [vlc, F6, F7]
    refine ⟨?_, fun e => ?_⟩
    · rw [rs_node, rs_node, hσ', hσ, t1, t2, cl2, cr2]
    · simp only [dV_node, List.mem_append]
      rw [cl3, cr3, dVL_frame B ds (fun u hu => (agds u hu).agrV B)]
  · intro u hu hnot
    have nrt : ∀ s : VT, (s = l ∨ s = r) → u ≠ rt n s := by
      intro s hs e
      cases s with
      | leaf => simp at e; omega
      | node a' y' b' d' =>
        simp only [rt_node] at e; subst e
        rcases hs with rfl | rfl <;> exact hnot (by simp)
    refine F1 u (fun e => hnot (by simp [e])) ?_ ?_ <;> rcases hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1]; exact nrt l (Or.inl rfl)
    · rw [e1]; exact nrt r (Or.inr rfl)
    · rw [e2]; exact nrt r (Or.inr rfl)
    · rw [e2]; exact nrt l (Or.inl rfl)

/-- The children of a stored node are at most `n`. -/
lemma Enc.children_le {M : Mem} {l r : VT} {x z : ℕ} {ds : List VT} {π : Bool}
    (h : Enc B n M (VT.node l x r ds) z π) (hlt : ∀ u ∈ nodes (VT.node l x r ds), u < n) :
    lc B M x ≤ n ∧ rc B M x ≤ n := by
  rw [enc_node_iff] at h
  obtain ⟨-, h2, h3, -⟩ := h
  have hl : rt n l ≤ n := by
    cases l with
    | leaf => simp
    | node a y b d => have := hlt y (by simp); simp; omega
  have hr : rt n r ≤ n := by
    cases r with
    | leaf => simp
    | node a y b d => have := hlt y (by simp); simp; omega
  cases e : cσ B M π x <;> simp only [lcS, e, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at h2 h3
  · exact ⟨h2 ▸ hl, h3 ▸ hr⟩
  · exact ⟨h3 ▸ hr, h2 ▸ hl⟩

/-- **A push keeps the invariant and the represented forest**, and clears the bit. -/
theorem push_okE {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G) (hR : RepE B n M G F)
    {gb ga : List VT} {t : VT} {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga)
    (ht : t ≠ VT.leaf) :
    Inv B n (pushM B (rt n t) M) G ∧ RepE B n (pushM B (rt n t) M) G F ∧
      MemFrame B n M (pushM B (rt n t) M) ∧ (∀ u, fpar B (pushM B (rt n t) M) u = fpar B M u) ∧
      rv B (pushM B (rt n t) M) (rt n t) = false := by
  have hX := rotCtx B n hI hG
  have hzs := hX.z_out
  have hout := hX.out
  have houtlt := hX.out_lt
  obtain ⟨hsE, -, hcount, hlts, hltc, hlto⟩ := hX
  obtain ⟨l, x, r, ds, rfl⟩ : ∃ l x r ds, t = node l x r ds := by
    cases t with
    | leaf => exact absurd rfl ht
    | node l x r ds => exact ⟨l, x, r, ds, rfl⟩
  simp only [rt_node]
  have hnd : (nodes (node l x r ds)).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w => by have := hcount w; omega
  obtain ⟨e1, e2, e3, e4, e5⟩ := pushLocal B n hI.nil hsE hnd hlts hzs
  have hx : x < n := hlts x (by simp)
  obtain ⟨hla, hlb⟩ := hsE.children_le B n hlts
  have hag : ∀ u, u ∈ cnodes ctx ++ nodesL (gb ++ ga) → Agr B M (pushM B x M) u :=
    fun u hu => e4 u (houtlt u hu) (fun h => hout u hu u h rfl)
  obtain ⟨hI', hR'⟩ := replace_okE B n hI hR hG e1 (Same.refl _) e2 (by simp) (by simp)
    (fun u hu _ => hag u hu)
    (fun hne => by
      have hz : hp n ctx ∈ cnodes ctx := by
        rcases hp_cases n ctx with ⟨h, -⟩ | h
        · exact absurd h hne
        · exact h
      have ha := hag _ (List.mem_append_left _ hz)
      refine ⟨ha.agrS B, (ha 0 (by omega)).1, ?_, ?_⟩
      · have e : lc B (pushM B x M) (hp n ctx) = lc B M (hp n ctx) := (ha 1 (by omega)).1
        simp only [rt_node]; rw [e]; split_ifs with h <;> simp [h]
      · have e : rc B (pushM B x M) (hp n ctx) = rc B M (hp n ctx) := (ha 2 (by omega)).1
        simp only [rt_node]; rw [e]
        by_cases h1 : lc B M (hp n ctx) = x <;> by_cases h2 : rc B M (hp n ctx) = x <;> simp [h1, h2])
    e3
  rw [← hG] at hI' hR'
  exact ⟨hI', hR', pushM_frame hx.le hla hlb, fun u => pushM_keep (by omega) (by omega), e5⟩

theorem push_ok {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G) (hR : Rep B n M G F)
    {gb ga : List VT} {t : VT} {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga)
    (ht : t ≠ VT.leaf) :
    Inv B n (pushM B (rt n t) M) G ∧ Rep B n (pushM B (rt n t) M) G F ∧
      MemFrame B n M (pushM B (rt n t) M) ∧ rv B (pushM B (rt n t) M) (rt n t) = false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := push_okE B n hI hR.toRepE hG ht
  exact ⟨h1, ⟨h2, fun u hu => by rw [h4]; exact hR.fpar u hu⟩, h3, h5⟩

end DynTree

end PlanarFlow
