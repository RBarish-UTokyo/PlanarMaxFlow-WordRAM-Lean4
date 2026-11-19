module

public import PlanarFlow.DynTree.Switch

/-!
# Dynamic trees: the access of a node, on the virtual forest

`access v` splays `v`, hangs its right child, and then repeatedly splays the path-parent `w` of
the current auxiliary tree and makes that tree the right child of `w`; a final splay of `v`
makes `v` the root of the virtual tree, with no right child. The auxiliary tree of `v` then
represents the path from the root of its tree in the forest down to `v`.

* `locate`: every node is the root of a subtree of a stored virtual forest, with a zipper above.
* `AccJ`: the invariant of the access loop: the current auxiliary tree `Y` is the root of its
  auxiliary tree, and `v` sits at the end of its right spine (`Y = plug (node lv v leaf dv) sp`,
  every frame of `sp` a right frame).
* `accJ_init`, `accJ_step`, `accJ_final`: the invariant after the first splay and switch, after an
  iteration, and the final shape.
* `rootPath_of_top`: the in-order of a top-level auxiliary tree whose last node is `v` is the path
  from the root down to `v`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-! ### Locating a node -/

lemma mem_nodesL_iff {ds : List VT} {u : ℕ} : u ∈ nodesL ds ↔ ∃ d ∈ ds, u ∈ nodes d := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih]

/-- Every node of a virtual tree is the root of a subtree, with a zipper above it. -/
theorem locate : ∀ (T : VT) (u : ℕ), u ∈ nodes T →
    ∃ t ctx, T = plug t ctx ∧ rt n t = u ∧ t ≠ leaf
  | leaf, u, h => absurd h (by simp)
  | node l x r ds, u, h => by
    simp only [nodes_node, List.mem_append, List.mem_cons] at h
    rcases h with (h | h | h) | h
    · obtain ⟨t, ctx, e, h1, h2⟩ := locate l u h
      exact ⟨t, ctx ++ [.L x r ds], by rw [plug_append, ← e]; rfl, h1, h2⟩
    · exact ⟨node l x r ds, [], rfl, h.symm, by simp⟩
    · obtain ⟨t, ctx, e, h1, h2⟩ := locate r u h
      exact ⟨t, ctx ++ [.R l x ds], by rw [plug_append, ← e]; rfl, h1, h2⟩
    · obtain ⟨d, hd, hu⟩ := mem_nodesL_iff.mp h
      have := List.sizeOf_lt_of_mem hd
      obtain ⟨t, ctx, e, h1, h2⟩ := locate d u hu
      obtain ⟨bef, aft, rfl⟩ := List.append_of_mem hd
      exact ⟨t, ctx ++ [.D l x r bef aft], by rw [plug_append, ← e]; rfl, h1, h2⟩
termination_by T => sizeOf T
decreasing_by all_goals simp_wf; omega

/-- Every node `v < n` of a stored virtual forest is the root of a subtree. -/
theorem Inv.locate {M : Mem} {G : List VT} (hI : Inv B n M G) {v : ℕ} (hv : v < n) :
    ∃ gb ga t ctx, G = gb ++ plug t ctx :: ga ∧ rt n t = v ∧ t ≠ leaf := by
  obtain ⟨T, hT, hu⟩ := mem_nodesL_iff.mp ((hI.cover v).mpr hv)
  obtain ⟨gb, ga, rfl⟩ := List.append_of_mem hT
  obtain ⟨t, ctx, e, h1, h2⟩ := DynTree.locate n T v hu
  exact ⟨gb, ga, t, ctx, by rw [e], h1, h2⟩

/-! ### Sizes -/

lemma sizeL_eq_length (G : List VT) : sizeL G = (nodesL G).length := by
  induction G with
  | nil => rfl
  | cons T G ih => simp [ih, size_eq_length]

/-- The size of the virtual forest is `n`. -/
lemma Inv.sizeL {M : Mem} {G : List VT} (hI : Inv B n M G) : sizeL G = n := by
  rw [sizeL_eq_length]
  have : (nodesL G).toFinset = Finset.range n := by
    ext u; simp [hI.cover u]
  rw [← List.toFinset_card_of_nodup hI.nodup, this, Finset.card_range]

/-- A subtree of a stored virtual forest has at most `n` nodes. -/
lemma Inv.size_le {M : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT} {t : VT}
    {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga) : size (plug t ctx) ≤ n := by
  rw [← hI.sizeL B n, hG]
  simp; omega

lemma size_le_plug (t : VT) (ctx : List Frame) : size t ≤ size (plug t ctx) := by
  rw [size_plugZ]; omega

/-! ### Right spines -/

/-- All frames are right frames. -/
def AllR (sp : List Frame) : Prop := ∀ f ∈ sp, ∃ c w ds, f = Frame.R c w ds

lemma seq_plug_R {t : VT} {sp : List Frame} (h : AllR sp) :
    ∃ pre, seq (plug t sp) = pre ++ seq t := by
  induction sp generalizing t with
  | nil => exact ⟨[], rfl⟩
  | cons f sp ih =>
    obtain ⟨c, w, ds, rfl⟩ := h f (by simp)
    obtain ⟨pre, e⟩ := ih (t := Frame.plug (.R c w ds) t) (fun g hg => h g (by simp [hg]))
    exact ⟨pre ++ seq c ++ [w], by rw [plug_cons, e]; simp [Frame.plug]⟩

lemma AllR.solid {sp : List Frame} (h : AllR sp) : ∀ f ∈ sp, f.Solid := by
  intro f hf
  obtain ⟨c, w, ds, rfl⟩ := h f hf
  trivial

/-! ### The potential of a switch -/

lemma pot_switch (l r Y : VT) (w : ℕ) (bef aft : List VT) :
    pot (node l w Y (bef ++ r :: aft)) = pot (node l w r (bef ++ Y :: aft)) ∧
    size (node l w Y (bef ++ r :: aft)) = size (node l w r (bef ++ Y :: aft)) := by
  constructor
  · simp only [pot_node, size_node, potL_append, potL_cons, sizeL_append, sizeL_cons]
    ring_nf
  · simp only [size_node, sizeL_append, sizeL_cons]; ring

lemma pot_switch_nil (l r : VT) (w : ℕ) (ds : List VT) :
    pot (node l w leaf (r :: ds)) = pot (node l w r ds) ∧
    size (node l w leaf (r :: ds)) = size (node l w r ds) := by
  constructor
  · simp only [pot_node, size_node, potL_cons, sizeL_cons, pot_leaf, size_leaf]
    ring_nf
  · simp only [size_node, sizeL_cons, size_leaf]; ring

lemma potL_mid (gb ga : List VT) (T : VT) : potL (gb ++ T :: ga) = potL gb + pot T + potL ga := by
  simp; ring

/-! ### The invariant of the access loop -/

/-- The invariant of the access loop: the virtual forest is `gb ++ plug Y ctx :: ga`, `Y` is the
root of its auxiliary tree, and `v` ends the right spine of `Y`. -/
structure AccJ (F : Forest) (M : Mem) (v : ℕ) (gb ga : List VT) (Y : VT) (ctx sp : List Frame)
    (lv : VT) (dv : List VT) : Prop where
  inv : Inv B n M (gb ++ plug Y ctx :: ga)
  rep : RepE B n M (gb ++ plug Y ctx :: ga) F
  top : ¬ HeadSolid ctx
  shape : Y = plug (node lv v leaf dv) sp
  allR : AllR sp

lemma dsOf_eq {t : VT} (ht : t ≠ leaf) : ∃ l r, t = node l (rt n t) r (dsOf t) := by
  cases t with
  | leaf => exact absurd rfl ht
  | node l x r ds => exact ⟨l, r, rfl⟩

/-- **The start of the access**: after the splay of `v`, the switch with `n` hangs the right
child of `v`. -/
theorem accJ_init {M : Mem} {F : Forest} {gb ga : List VT} {t : VT} {ctx : List Frame}
    (hI : Inv B n M (gb ++ plug t ctx :: ga)) (hR : RepE B n M (gb ++ plug t ctx :: ga) F)
    (ht : t ≠ leaf) (hc : ¬ HeadSolid ctx) (hv : rv B M (rt n t) = false) :
    ∃ l r, t = node l (rt n t) r (dsOf t) ∧
      AccJ B n F (switchR B n (rt n t) n M) (rt n t) gb ga (node l (rt n t) leaf (r :: dsOf t))
        ctx [] l (r :: dsOf t) ∧
      MemFrame B n M (switchR B n (rt n t) n M) ∧
      pot (plug (node l (rt n t) leaf (r :: dsOf t)) ctx) = pot (plug t ctx) := by
  obtain ⟨l, r, e⟩ := dsOf_eq n ht
  refine ⟨l, r, e, ?_⟩
  have hG : gb ++ plug t ctx :: ga =
      gb ++ plug (node l (rt n t) r ([] ++ [] ++ dsOf t)) ctx :: ga := by
    simp only [List.nil_append]; exact congrArg (fun T => gb ++ plug T ctx :: ga) e
  obtain ⟨I1, R1, F1⟩ := switchR_okE B n hI hR (Y := VT.leaf) (Or.inr ⟨rfl, rfl⟩) hG hc hv
  simp only [rt_leaf, List.nil_append] at I1 R1 F1
  refine ⟨⟨I1, R1, hc, rfl, fun f hf => by simp at hf⟩, F1, ?_⟩
  rw [pot_plugZ, pot_plugZ, (pot_switch_nil l r (rt n t) (dsOf t)).1,
    (pot_switch_nil l r (rt n t) (dsOf t)).2]
  exact congrArg (fun T => pot T + cpot ctx (size T)) e.symm

/-- **One iteration of the access loop**: the path-parent `w` of `Y` is splayed, then `Y`
becomes its right child. -/
theorem accJ_step {M M1 : Mem} {F : Forest} {v : ℕ} {gb ga : List VT} {Y : VT}
    {l : VT} {w : ℕ} {r : VT} {bef aft : List VT} {ctx sp : List Frame} {lv : VT} {dv : List VT}
    (hJ : AccJ B n F M v gb ga Y (Frame.D l w r bef aft :: ctx) sp lv dv)
    (hI1 : Inv B n M1 (gb ++ plug (splayG (node l w r (bef ++ Y :: aft)) ctx).1
      (splayG (node l w r (bef ++ Y :: aft)) ctx).2 :: ga))
    (hR1 : RepE B n M1 (gb ++ plug (splayG (node l w r (bef ++ Y :: aft)) ctx).1
      (splayG (node l w r (bef ++ Y :: aft)) ctx).2 :: ga) F) (hw : rv B M1 w = false) :
    ∃ l' r', (splayG (node l w r (bef ++ Y :: aft)) ctx).1 = node l' w r' (bef ++ Y :: aft) ∧
      AccJ B n F (switchR B n w (rt n Y) M1) v gb ga (node l' w Y (bef ++ r' :: aft))
        (splayG (node l w r (bef ++ Y :: aft)) ctx).2 (sp ++ [Frame.R l' w (bef ++ r' :: aft)])
        lv dv ∧
      MemFrame B n M1 (switchR B n w (rt n Y) M1) ∧
      pot (plug (node l' w Y (bef ++ r' :: aft)) (splayG (node l w r (bef ++ Y :: aft)) ctx).2) =
        pot (plug (splayG (node l w r (bef ++ Y :: aft)) ctx).1
          (splayG (node l w r (bef ++ Y :: aft)) ctx).2) ∧
      size (node l' w Y (bef ++ r' :: aft)) =
        size (splayG (node l w r (bef ++ Y :: aft)) ctx).1 := by
  obtain ⟨sf, -, -, hns, -, hne, hrt, hds, -⟩ := splayG_spec (t := node l w r (bef ++ Y :: aft))
    (by simp) ctx
  generalize hS : splayG (node l w r (bef ++ Y :: aft)) ctx = S at *
  obtain ⟨W', rest⟩ := S
  simp only at hns hne hrt hds hI1 hR1 ⊢
  obtain ⟨l', r', e⟩ := dsOf_eq n hne
  rw [hrt, hds] at e
  simp only [rt_node, dsOf] at e
  refine ⟨l', r', e, ?_⟩
  have hG : gb ++ plug W' rest :: ga = gb ++ plug (node l' w r' (bef ++ [Y] ++ aft)) rest :: ga := by
    rw [e]; simp
  obtain ⟨I2, R2, F2⟩ := switchR_okE B n hI1 hR1 (Or.inl rfl) hG hns hw
  refine ⟨⟨I2, R2, hns, ?_, ?_⟩, F2, ?_, ?_⟩
  · rw [hJ.shape, plug_append]; rfl
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hJ.allR f hf
    · simp at hf; exact ⟨_, _, _, hf⟩
  · rw [pot_plugZ, pot_plugZ, (pot_switch l' r' Y w bef aft).1, (pot_switch l' r' Y w bef aft).2,
      e]
  · rw [(pot_switch l' r' Y w bef aft).2, e]

lemma seq_sublist_nodes : ∀ t : VT, (seq t).Sublist (nodes t)
  | leaf => List.Sublist.slnil
  | node l x r ds => by
    simp only [seq_node, nodes_node, List.append_assoc, List.cons_append]
    exact (seq_sublist_nodes l).append ((seq_sublist_nodes r).cons₂ x |>.trans
      (List.sublist_append_left _ _))

lemma Inv.nodup_of {M : Mem} {G : List VT} (hI : Inv B n M G) {T : VT} (hT : T ∈ G) :
    (nodes T).Nodup := nodup_of_mem_nodesL hI.nodup hT

/-- **The end of the access**: once `Y` is a top-level tree, the final splay of `v` makes `v` the
root of the virtual tree, with no right child. -/
theorem accJ_final {M M2 : Mem} {F : Forest} {v : ℕ} {gb ga : List VT} {Y : VT}
    {sp : List Frame} {lv : VT} {dv : List VT} (hJ : AccJ B n F M v gb ga Y [] sp lv dv)
    (hI2 : Inv B n M2 (gb ++ plug (splayG (node lv v leaf dv) sp).1
      (splayG (node lv v leaf dv) sp).2 :: ga)) :
    (splayG (node lv v leaf dv) sp).2 = [] ∧
      ∃ l, (splayG (node lv v leaf dv) sp).1 = node l v leaf dv ∧
        seq (node l v leaf dv) = seq Y := by
  obtain ⟨sf, e, hsf, hns, hsame, hne, hrt, hds, -⟩ := splayG_spec (t := node lv v leaf dv)
    (by simp) sp
  generalize hS : splayG (node lv v leaf dv) sp = S at *
  obtain ⟨T, rest⟩ := S
  simp only at e hns hsame hne hrt hds hI2 ⊢
  have hrest : rest = [] := by
    rcases rest with _ | ⟨f, rest⟩
    · rfl
    · exact absurd (hJ.allR.solid f (by rw [e]; simp)) hns
  subst hrest
  simp only [List.append_nil] at e
  subst e
  refine ⟨rfl, ?_⟩
  obtain ⟨a, b, eT⟩ := dsOf_eq n hne
  rw [hrt, hds] at eT
  simp only [rt_node, dsOf] at eT
  have hseq : seq T = seq Y := by rw [hsame.seq, hJ.shape]
  obtain ⟨pre, hpre⟩ := seq_plug_R (t := node lv v leaf dv) hJ.allR
  have hnd : (seq T).Nodup := by
    have := hI2.nodup_of B n (T := plug T []) (by simp)
    exact (seq_sublist_nodes T).nodup this
  have hb : seq b = [] := by
    rw [eT] at hnd hseq
    rw [hJ.shape, hpre] at hseq
    simp only [seq_node, seq_leaf] at hseq hnd
    have hr := congrArg List.reverse hseq
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.reverse_nil] at hr
    rcases hq : (seq b).reverse with _ | ⟨q, rest⟩
    · exact List.reverse_eq_nil_iff.mp hq
    · rw [hq] at hr
      simp only [List.cons_append, List.cons.injEq] at hr
      have hv : v ∈ seq b := by
        rw [← List.mem_reverse, hq, ← hr.1]; simp
      rw [List.nodup_append] at hnd
      exact absurd hv (List.nodup_cons.mp hnd.2.1).1
  rw [seq_eq_nil] at hb
  subst hb
  exact ⟨a, eT, by rw [← eT, hseq]⟩

/-! ### The represented root path -/

lemma upPath_nil (F : Forest) (fuel : ℕ) : upPath F n fuel n = [] := by
  cases fuel with
  | zero => rfl
  | succ f => simp [upPath]

lemma upPath_chain (F : Forest) : ∀ (L : List ℕ) (p fuel : ℕ) (hL : L ≠ []),
    (∀ e ∈ VT.chain p L, F.par e.1 = e.2) → (∀ x ∈ L, x < n) → L.length ≤ fuel →
    upPath F n fuel (L.getLast hL) = L.reverse ++ upPath F n (fuel - L.length) p
  | [], _, _, hL, _, _, _ => absurd rfl hL
  | [x], p, fuel, _, hc, hlt, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hx := hlt x (by simp)
    have hp := hc (x, p) (by simp)
    simp only [List.getLast_singleton, upPath, hx, ite_true, hp, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.length_singleton, Nat.add_sub_cancel,
      List.singleton_append]
  | x :: y :: L, p, fuel, _, hc, hlt, hf => by
    have ih := upPath_chain F (y :: L) x fuel (by simp)
      (fun e he => hc e (by simp only [VT.chain_cons, List.mem_cons] at he ⊢; tauto))
      (fun z hz => hlt z (by simp [hz])) (by simp at hf ⊢; omega)
    rw [List.getLast_cons (by simp), ih]
    have hx := hlt x (by simp)
    have hp := hc (x, p) (by simp)
    obtain ⟨f, hf'⟩ : ∃ f, fuel - (y :: L).length = f + 1 := ⟨fuel - (y :: L).length - 1, by
      simp at hf ⊢; omega⟩
    rw [hf']
    simp only [upPath, hx, ite_true, hp]
    have : fuel - (x :: y :: L).length = f := by simp at hf' ⊢; omega
    rw [this]
    simp

lemma length_le_of_nodup {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < n) : L.length ≤ n := by
  rw [← List.toFinset_card_of_nodup hnd]
  calc L.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card (fun x hx => by simpa using hlt x (by simpa using hx))
    _ = n := Finset.card_range n

/-- **The root path.** The in-order of a top-level virtual tree whose last node is `v` is the path
from the root of the tree of `v` in the forest down to `v`. -/
theorem rootPath_top {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {T : VT} (hG : G = gb ++ T :: ga) {xs : List ℕ}
    {v : ℕ} (hs : seq T = xs ++ [v]) : rootPath F n v = (xs ++ [v]).reverse := by
  have hT : T ∈ G := by rw [hG]; simp
  have hnd : (seq T).Nodup := (seq_sublist_nodes T).nodup (hI.nodup_of B n hT)
  have hlt : ∀ x ∈ seq T, x < n := fun x hx =>
    (hI.cover x).mp (mem_nodesL_of hT ((seq_sublist_nodes T).subset hx))
  have hc : ∀ e ∈ VT.chain n (seq T), F.par e.1 = e.2 := fun e he =>
    hR.par e.1 e.2 (by rw [hG]; simp [he])
  have h := upPath_chain n F (seq T) n n (by simp [hs]) hc hlt (length_le_of_nodup n hnd hlt)
  rw [upPath_nil, List.append_nil] at h
  rw [rootPath, ← hs, ← h]
  congr 1
  simp [hs]

end DynTree

end PlanarFlow
