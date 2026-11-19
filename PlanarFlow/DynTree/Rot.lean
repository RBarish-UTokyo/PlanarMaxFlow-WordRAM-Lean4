module

public import PlanarFlow.DynTree.Zip

/-!
# Dynamic trees: the rotation on the memory

`recomp u M` recomputes the aggregates of `u` from its children; `rotP x M` redirects the
pointers and moves the tags of a rotation of `x` above its parent `y` (with `b` the inner child of
`x` changing sides):

* `tg x := tg x + tg y`, `tg y := -tg x`, `tg b := tg b + tg x`, which keeps every true value;
* `y` takes `b` as a child, `x` takes `y`, `x` takes the parent pointer of `y`, and the child
  pointer of the grandparent `z` (if `y` was its child in the auxiliary tree) is redirected to `x`.

`rotMem x M = recomp x (recomp y (rotP x M))` is what the machine block computes; its
correctness (a stored zipper focused at `x`, with a solid frame on top, becomes the zipper with
the rotated tree, and the represented forest is unchanged) is `PlanarFlow.DynTree.rotate_ok`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- Write the aggregates `g` into the record of `u`. -/
def setOwn (u : ℕ) (g : Ag) (M : Mem) : Mem :=
  ⟨upd (upd (upd (upd (upd (upd M.nm (adr B u 3) g.a1) (adr B u 5) g.lm) (adr B u 6) g.rm)
      (adr B u 7) g.b1) (adr B u 8) g.a2) (adr B u 9) g.b2,
    upd (upd (upd (upd (upd M.rm (adr B u 2) g.m1) (adr B u 3) g.s1) (adr B u 4) g.c)
      (adr B u 7) g.m2) (adr B u 8) g.s2⟩

/-- The combination of the children of `u`, in stored order. -/
def cmb (M : Mem) (u : ℕ) : Ag :=
  comb n (lc B M u) (rd B M (lc B M u)) u (vl B M u) (vl2 B M u) (rc B M u) (rd B M (rc B M u))

/-- Recompute the aggregates of `u` (a node whose reversal bit is clear). -/
def recomp (u : ℕ) (M : Mem) : Mem := setOwn B u (cmb B n M u) M

/-- The pointer and tag part of the rotation of `x` above its parent. -/
def rotP (x : ℕ) (M : Mem) : Mem :=
  let y := par B M x
  let z := par B M y
  let b := if lc B M y = x then rc B M x else lc B M x
  let nm1 := if lc B M y = x then
      upd (upd (upd M.nm (adr B y 1) b) (adr B b 0) y) (adr B x 2) y
    else upd (upd (upd M.nm (adr B y 2) b) (adr B b 0) y) (adr B x 1) y
  let nm2 := upd (upd nm1 (adr B y 0) x) (adr B x 0) z
  ⟨if lc B M z = y then upd nm2 (adr B z 1) x else
      if rc B M z = y then upd nm2 (adr B z 2) x else nm2,
    upd (upd (upd (upd (upd (upd M.rm (adr B x 1) (tg B M x + tg B M y)) (adr B y 1)
      (-tg B M x)) (adr B b 1) (tg B M b + tg B M x)) (adr B x 6) (tg2 B M x + tg2 B M y))
      (adr B y 6) (-tg2 B M x)) (adr B b 6) (tg2 B M b + tg2 B M x)⟩

/-- The rotation of `x` above its parent, with the aggregates. -/
def rotMem (x : ℕ) (M : Mem) : Mem := recomp B n x (recomp B n (par B M x) (rotP B x M))

/-- Memory outside the region of the structure is unchanged. -/
def MemFrame (M M' : Mem) : Prop :=
  ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → M'.nm a = M.nm a ∧ M'.rm a = M.rm a

lemma MemFrame.refl (M : Mem) : MemFrame B n M M := fun _ _ => ⟨rfl, rfl⟩

lemma MemFrame.trans {M M' M'' : Mem} (h : MemFrame B n M M') (h' : MemFrame B n M' M'') :
    MemFrame B n M M'' := fun a ha => ⟨(h' a ha).1.trans (h a ha).1, (h' a ha).2.trans (h a ha).2⟩

section
variable {B n}

lemma upd_adr {α : Type} (f : ℕ → α) {u u' j j' : ℕ} (v : α) (hj : j < 16) (hj' : j' < 16) :
    upd f (adr B u' j') v (adr B u j) = if u = u' ∧ j = j' then v else f (adr B u j) := by
  rw [upd_apply]; simp only [adr_eq_iff hj hj']

lemma memFrame_upd {α : Type} (f : ℕ → α) {u j : ℕ} (v : α) (hu : u ≤ n) (hj : j < 16) {a : ℕ}
    (ha : a < B ∨ B + 16 * (n + 1) ≤ a) : upd f (adr B u j) v a = f a := by
  have : a ≠ adr B u j := by unfold adr; omega
  simp [upd, this]

end

lemma setOwn_frame {M : Mem} {u : ℕ} (g : Ag) (hu : u ≤ n) : MemFrame B n M (setOwn B u g M) := by
  intro a ha
  simp only [setOwn, upd_apply]
  unfold adr
  refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | omega

lemma setOwn_agr {M : Mem} {u v : ℕ} (g : Ag) (h : v ≠ u) : Agr B M (setOwn B u g M) v := by
  intro j hj
  simp only [setOwn]
  refine ⟨?_, ?_⟩ <;> simp [upd_adr _ _ hj, h]

lemma setOwn_nm {M : Mem} {u v j : ℕ} (g : Ag) (hj : j < 16) (h : j < 3 ∨ j = 4 ∨ 10 ≤ j) :
    (setOwn B u g M).nm (adr B v j) = M.nm (adr B v j) := by
  simp only [setOwn, upd_adr _ _ hj (show (3 : ℕ) < 16 by omega), upd_adr _ _ hj (show (5 : ℕ) < 16 by omega),
    upd_adr _ _ hj (show (6 : ℕ) < 16 by omega), upd_adr _ _ hj (show (7 : ℕ) < 16 by omega),
    upd_adr _ _ hj (show (8 : ℕ) < 16 by omega), upd_adr _ _ hj (show (9 : ℕ) < 16 by omega)]
  split_ifs <;> first | rfl | omega

lemma setOwn_rm {M : Mem} {u v j : ℕ} (g : Ag) (hj : j < 16) (h : j < 2 ∨ j = 5 ∨ j = 6 ∨ 9 ≤ j) :
    (setOwn B u g M).rm (adr B v j) = M.rm (adr B v j) := by
  simp only [setOwn, upd_adr _ _ hj (show (2 : ℕ) < 16 by omega), upd_adr _ _ hj (show (3 : ℕ) < 16 by omega),
    upd_adr _ _ hj (show (4 : ℕ) < 16 by omega), upd_adr _ _ hj (show (7 : ℕ) < 16 by omega),
    upd_adr _ _ hj (show (8 : ℕ) < 16 by omega)]
  split_ifs <;> first | rfl | omega

lemma own_setOwn {M : Mem} {u : ℕ} (g : Ag) : own B (setOwn B u g M) u = g := by
  simp only [own, setOwn, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm]
  simp [upd_adr]

/-- The fields not written by `setOwn`. -/
lemma setOwn_keep {M : Mem} {u : ℕ} (g : Ag) (v : ℕ) :
    par B (setOwn B u g M) v = par B M v ∧ lc B (setOwn B u g M) v = lc B M v ∧
    rc B (setOwn B u g M) v = rc B M v ∧ fpar B (setOwn B u g M) v = fpar B M v ∧
    vl B (setOwn B u g M) v = vl B M v ∧ tg B (setOwn B u g M) v = tg B M v ∧
    vl2 B (setOwn B u g M) v = vl2 B M v ∧ tg2 B (setOwn B u g M) v = tg2 B M v ∧
    rv B (setOwn B u g M) v = rv B M v :=
  ⟨setOwn_nm B g (by omega) (by omega), setOwn_nm B g (by omega) (by omega),
    setOwn_nm B g (by omega) (by omega), setOwn_nm B g (by omega) (by omega),
    setOwn_rm B g (by omega) (by omega), setOwn_rm B g (by omega) (by omega),
    setOwn_rm B g (by omega) (by omega), setOwn_rm B g (by omega) (by omega),
    by simp only [rv, rvw]; rw [setOwn_nm B g (by omega) (by omega)]⟩

lemma recomp_frame {M : Mem} {u : ℕ} (hu : u ≤ n) : MemFrame B n M (recomp B n u M) :=
  setOwn_frame B n _ hu

lemma recomp_agr {M : Mem} {u v : ℕ} (h : v ≠ u) : Agr B M (recomp B n u M) v :=
  setOwn_agr B _ h

lemma recomp_nm {M : Mem} {u v j : ℕ} (hj : j < 16) (h : j < 3 ∨ j = 4 ∨ 10 ≤ j) :
    (recomp B n u M).nm (adr B v j) = M.nm (adr B v j) := setOwn_nm B _ hj h

lemma recomp_rm {M : Mem} {u v j : ℕ} (hj : j < 16) (h : j < 2 ∨ j = 5 ∨ j = 6 ∨ 9 ≤ j) :
    (recomp B n u M).rm (adr B v j) = M.rm (adr B v j) := setOwn_rm B _ hj h

lemma recomp_agrS_par {M : Mem} {u v : ℕ} : par B (recomp B n u M) v = par B M v ∧
    lc B (recomp B n u M) v = lc B M v ∧ rc B (recomp B n u M) v = rc B M v ∧
    fpar B (recomp B n u M) v = fpar B M v ∧ vl B (recomp B n u M) v = vl B M v ∧
    tg B (recomp B n u M) v = tg B M v ∧ vl2 B (recomp B n u M) v = vl2 B M v ∧
    tg2 B (recomp B n u M) v = tg2 B M v ∧ rv B (recomp B n u M) v = rv B M v :=
  setOwn_keep B _ v

/-- `recomp u` makes the aggregates of `u` correct, if its reversal bit is clear. -/
lemma aggOK_recomp {M : Mem} {u : ℕ} (hl : lc B M u ≠ u) (hr : rc B M u ≠ u)
    (hrv : rv B M u = false) : AggOK B n (recomp B n u M) u := by
  obtain ⟨-, el, er, -, ev, -, ev2, -, erv⟩ := recomp_agrS_par B n (M := M) (u := u) (v := u)
  have lkl := look_of_agr B n (recomp_agr B n (M := M) (u := u) hl)
  have lkr := look_of_agr B n (recomp_agr B n (M := M) (u := u) hr)
  unfold AggOK
  rw [erv, hrv]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [(comb_eq B n ev ev2 (el ▸ lkl) (er ▸ lkr)).1]
  exact own_setOwn B _

/-! ### Values under a change of the root tag -/

lemma rs_retag {M M' : Mem} {s : VT} {π k : Bool} {d : ℝ}
    (hag : ∀ u ∈ nodes s, u ≠ rt n s → AgrV B M M' u) (hnd : (nodes s).Nodup)
    (hv : ∀ j, vlc B M' j (rt n s) = vlc B M j (rt n s)) (hrv : rv B M' (rt n s) = rv B M (rt n s))
    (ht : tgc B M' (k ^^ π) (rt n s) = tgc B M (k ^^ π) (rt n s) + d) :
    rs B M' s π k = shift d (rs B M s π k) := by
  cases s with
  | leaf => rfl
  | node l x r ds =>
    simp only [nodes_node, List.nodup_append, List.nodup_cons, List.mem_append,
      List.mem_cons] at hnd
    simp only [rt_node] at hv ht hrv
    have hl : ∀ u ∈ nodes l, AgrV B M M' u := fun u hu =>
      hag u (by simp [hu]) (fun e => hnd.1.2.2 u hu x (by simp) e)
    have hr : ∀ u ∈ nodes r, AgrV B M M' u := fun u hu =>
      hag u (by simp [hu]) (fun e => hnd.1.2.1.1 (by simp only [rt_node] at e; exact e ▸ hu))
    simp only [rs_node, cσ, hrv, rs_frame B l hl, rs_frame B r hr, hv, ht, shift_shift]

lemma dV_frame_root {M M' : Mem} {s : VT} (hag : ∀ u ∈ nodes s, u ≠ rt n s → AgrV B M M' u)
    (hnd : (nodes s).Nodup) (k : Bool) : dV B M' s k = dV B M s k := by
  cases s with
  | leaf => rfl
  | node l x r ds =>
    simp only [nodes_node, List.nodup_append, List.nodup_cons] at hnd
    have ne : ∀ u ∈ nodes l ++ nodes r ++ nodesL ds, u ≠ x := by
      intro u hu e; subst e
      simp only [List.mem_append] at hu
      rcases hu with (hu | hu) | hu
      · exact hnd.1.2.2 u hu u (by simp) rfl
      · exact hnd.1.2.1.1 hu
      · exact hnd.2.2 u (by simp) u hu rfl
    simp only [dV_node]
    rw [dV_frame B l (fun u hu => hag u (by simp [hu]) (ne u (by simp [hu]))),
      dV_frame B r (fun u hu => hag u (by simp [hu]) (ne u (by simp [hu]))),
      dVL_frame B ds (fun u hu => hag u (by simp [hu]) (ne u (by simp [hu])))]

lemma ne_of_count {A C : List ℕ} (h : ∀ w, A.count w + C.count w ≤ 1) {u v : ℕ} (hu : u ∈ A)
    (hv : v ∈ C) : u ≠ v := by
  rintro rfl
  have h1 := List.count_pos_iff.mpr hu
  have h2 := List.count_pos_iff.mpr hv
  have := h u
  omega

end DynTree

end PlanarFlow
