module

public import PlanarFlow.DynTree.Mem

/-!
# Dynamic trees: replacing a subtree inside a stored zipper

Every operation of the link-cut tree changes the memory around one node: it replaces the subtree
`s` at the hole of a zipper `fs` by a subtree `s'` with the same nodes, and possibly a new root.
`EncC.frame` and `EncC.replace` show that the rest of the zipper stays stored (the node above the
hole has its child pointer redirected, and reads the same aggregates from the new root);
`inv_replace` and `rep_replace` lift this to the global invariant and to the represented forest.
The parities of the frames are those of the memory; they only depend on the reversal bits of
the frame nodes, which the replacements keep.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

lemma enc_frame_all {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {t : VT} {p : ℕ}
    {π : Bool} (h : Enc B n M t p π) (hnd : (nodes t).Nodup)
    (hag : ∀ u ∈ nodes t, Agr B M M' u) : Enc B n M' t p π :=
  Enc.frame B n hN hN' h hnd p (fun u hu _ => hag u hu)
    (fun hne => (hag _ (rt_mem_nodes hne n)).agrC)
    (fun hne => by
      rw [show par B M' (rt n t) = par B M (rt n t) from ((hag _ (rt_mem_nodes hne n)) 0
        (by omega)).1]
      exact h.par_rt B n hne)

lemma enc_frame_list {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {ds : List VT}
    {p : ℕ} {π : Bool} (h : ∀ d ∈ ds, Enc B n M d p π)
    (hnd : (nodesL ds).Nodup) (hag : ∀ u ∈ nodesL ds, Agr B M M' u) :
    ∀ d ∈ ds, Enc B n M' d p π := fun d hd =>
  enc_frame_all B n hN hN' (h d hd) (nodup_of_mem_nodesL hnd hd)
    (fun u hu => hag u (mem_nodesL_of hd hu))

lemma look_rt {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') (s : VT)
    (hag : ∀ u ∈ nodes s, Agr B M M' u) : Look B n M M' (rt n s) (rt n s) := by
  cases s with
  | leaf => exact look_nil B n hN hN'
  | node a y b dy => exact look_of_agr B n (hag y (by simp))

/-- The fields of `u` read by its parent and by the frame of `u` agree, except possibly `par` and
the two child pointers. -/
def AgrS (M M' : Mem) (u : ℕ) : Prop :=
  own B M' u = own B M u ∧ fpar B M' u = fpar B M u ∧ vl B M' u = vl B M u ∧
    tg B M' u = tg B M u ∧ vl2 B M' u = vl2 B M u ∧ tg2 B M' u = tg2 B M u ∧
    rv B M' u = rv B M u

lemma Agr.agrS {M M' : Mem} {u : ℕ} (h : Agr B M M' u) : AgrS B M M' u :=
  ⟨(h.agrC B).ownEq B, (h 4 (by omega)).1, (h 0 (by omega)).2, (h 1 (by omega)).2,
    (h 5 (by omega)).2, (h 6 (by omega)).2, (h.agrC B).rvEq B⟩

lemma AgrS.rdEq {M M' : Mem} {u : ℕ} (h : AgrS B M M' u) : rd B M' u = rd B M u := by
  simp only [rd]; rw [h.1, h.2.2.2.1, h.2.2.2.2.2.1]

lemma look_of_agrS {M M' : Mem} {u : ℕ} (h : AgrS B M M' u) : Look B n M M' u u := by
  have e := h.rdEq B
  exact ⟨Iff.rfl, congrArg Ag.c e, congrArg Ag.s1 e, congrArg Ag.s2 e, fun _ => e⟩

lemma AgrS.agrV {M M' : Mem} {u : ℕ} (h : AgrS B M M' u) : AgrV B M M' u :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Read the two children of `y` from its true children. -/
lemma look_lcS {M M' : Mem} {y : ℕ} (σ : Bool)
    (hl : Look B n M M' (lcS B M σ y) (lcS B M' σ y))
    (hr : Look B n M M' (lcS B M (!σ) y) (lcS B M' (!σ) y)) :
    Look B n M M' (lc B M y) (lc B M' y) ∧ Look B n M M' (rc B M y) (rc B M' y) := by
  cases σ <;> simp only [lcS, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_true, ite_false] at hl hr <;> exact ⟨by assumption, by assumption⟩

/-- The node of the frame points to the new hole root `r'`, its other child pointer unchanged
(read with the parity `π` of the frame node). -/
def Redir (M M' : Mem) (f : Frame) (r' : ℕ) (π : Bool) : Prop :=
  match f with
  | .L y _ _ => lcS B M' (cσ B M π y) y = r' ∧ lcS B M' (!cσ B M π y) y = lcS B M (!cσ B M π y) y
  | .R _ y _ => lcS B M' (cσ B M π y) y = lcS B M (cσ B M π y) y ∧ lcS B M' (!cσ B M π y) y = r'
  | .D _ y _ _ _ => lcS B M' (cσ B M π y) y = lcS B M (cσ B M π y) y ∧
      lcS B M' (!cσ B M π y) y = lcS B M (!cσ B M π y) y

/-- A frame stays stored when its node is redirected to a new hole root `r'` reading the same
aggregates, the rest agreeing. -/
lemma EncF.replace {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {f : Frame} {r r' : ℕ}
    {π : Bool} (h : EncF B n M f r π)
    (hnd : (f.fnodes).Nodup) (hag : ∀ u ∈ f.fnodes, u ≠ f.y → Agr B M M' u)
    (hy : AgrS B M M' f.y) (hlook : f.Solid → Look B n M M' r r')
    (hptr : Redir B M M' f r' π) :
    EncF B n M' f r' π := by
  obtain ⟨h0, -, hv, -, hv2, -, hrv⟩ := hy
  cases f with
  | L y c dy =>
    obtain ⟨e1, e2, hA, hc', hd⟩ := h
    simp only [Frame.y] at h0 hv hv2 hrv
    have hσ : cσ B M' π y = cσ B M π y := by simp only [cσ, hrv]
    simp only [Frame.fnodes, List.nodup_cons, List.nodup_append] at hnd
    have agc : ∀ u ∈ nodes c, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu]) (fun e => hnd.1.1 (by simp only [Frame.y] at e; exact e ▸ hu))
    have agd : ∀ u ∈ nodesL dy, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu])
        (fun e => hnd.2.2 y (by simp) u hu (by simp only [Frame.y] at e; exact e.symm))
    obtain ⟨p1, p2⟩ := hptr
    refine ⟨by rw [hσ]; exact p1, by rw [hσ, p2, e2], ?_, by
      rw [hσ]; exact enc_frame_all B n hN hN' hc' hnd.1.2 agc,
      enc_frame_list B n hN hN' hd hnd.2.1 agd⟩
    obtain ⟨k1, k2⟩ := look_lcS B n (M := M) (M' := M') (y := y) (cσ B M π y)
      (by rw [p1, e1]; exact hlook trivial)
      (by rw [p2, e2]; exact look_rt B n hN hN' c agc)
    exact hA.transfer B n h0 hv hv2 hrv k1 k2
  | R c y dy =>
    obtain ⟨e1, e2, hA, hc', hd⟩ := h
    simp only [Frame.y] at h0 hv hv2 hrv
    have hσ : cσ B M' π y = cσ B M π y := by simp only [cσ, hrv]
    simp only [Frame.fnodes, List.nodup_cons, List.nodup_append] at hnd
    have agc : ∀ u ∈ nodes c, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu]) (fun e => hnd.1.1 (by simp only [Frame.y] at e; exact e ▸ hu))
    have agd : ∀ u ∈ nodesL dy, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu])
        (fun e => hnd.2.2 y (by simp) u hu (by simp only [Frame.y] at e; exact e.symm))
    obtain ⟨p1, p2⟩ := hptr
    refine ⟨by rw [hσ, p1, e1], by rw [hσ]; exact p2, ?_, by
      rw [hσ]; exact enc_frame_all B n hN hN' hc' hnd.1.2 agc,
      enc_frame_list B n hN hN' hd hnd.2.1 agd⟩
    obtain ⟨k1, k2⟩ := look_lcS B n (M := M) (M' := M') (y := y) (cσ B M π y)
      (by rw [p1, e1]; exact look_rt B n hN hN' c agc)
      (by rw [p2, e2]; exact hlook trivial)
    exact hA.transfer B n h0 hv hv2 hrv k1 k2
  | D l y rr bef aft =>
    obtain ⟨e1, e2, hA, hl, hr, hd⟩ := h
    simp only [Frame.y] at h0 hv hv2 hrv
    have hσ : cσ B M' π y = cσ B M π y := by simp only [cσ, hrv]
    simp only [Frame.fnodes, List.nodup_cons, List.mem_append, not_or, List.nodup_append,
      List.cons_append] at hnd
    have ny : ∀ u, u ≠ (Frame.D l y rr bef aft).y ↔ u ≠ y := fun u => Iff.rfl
    have agl : ∀ u ∈ nodes l, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu]) ((ny u).2 fun e => hnd.1.1.1.1 (e ▸ hu))
    have agr : ∀ u ∈ nodes rr, Agr B M M' u := fun u hu =>
      hag u (by simp [Frame.fnodes, hu]) ((ny u).2 fun e => hnd.1.1.1.2 (e ▸ hu))
    have agd : ∀ u ∈ nodesL (bef ++ aft), Agr B M M' u := fun u hu => by
      simp only [nodesL_append, List.mem_append] at hu
      rcases hu with hu | hu
      · exact hag u (by simp [Frame.fnodes, hu]) ((ny u).2 fun e => hnd.1.1.2 (e ▸ hu))
      · exact hag u (by simp [Frame.fnodes, hu]) ((ny u).2 fun e => hnd.1.2 (e ▸ hu))
    obtain ⟨p1, p2⟩ := hptr
    refine ⟨by rw [hσ, p1, e1], by rw [hσ, p2, e2], ?_,
      by rw [hσ]; exact enc_frame_all B n hN hN' hl hnd.2.1.1.1 agl,
      by rw [hσ]; exact enc_frame_all B n hN hN' hr hnd.2.1.1.2.1 agr,
      enc_frame_list B n hN hN' hd (by
        simp only [nodesL_append, List.nodup_append]
        exact ⟨hnd.2.1.2.1, hnd.2.2.1, fun a ha b hb => hnd.2.2.2 a (Or.inr ha) b hb⟩) agd⟩
    obtain ⟨k1, k2⟩ := look_lcS B n (M := M) (M' := M') (y := y) (cσ B M π y)
      (by rw [p1, e1]; exact look_rt B n hN hN' l agl)
      (by rw [p2, e2]; exact look_rt B n hN hN' rr agr)
    exact hA.transfer B n h0 hv hv2 hrv k1 k2

lemma EncF.frame {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {f : Frame} {r : ℕ}
    {π : Bool} (h : EncF B n M f r π)
    (hnd : (f.fnodes).Nodup) (hag : ∀ u ∈ f.fnodes, Agr B M M' u) (hr : Look B n M M' r r) :
    EncF B n M' f r π := by
  have hy : Agr B M M' f.y := hag _ (by cases f <;> simp [Frame.fnodes, Frame.y])
  refine EncF.replace B n hN hN' h hnd (fun u hu _ => hag u hu) (hy.agrS B) (fun _ => hr) ?_
  have e1 : lc B M' f.y = lc B M f.y := (hy 1 (by omega)).1
  have e2 : rc B M' f.y = rc B M f.y := (hy 2 (by omega)).1
  have hS : ∀ σ, lcS B M' σ f.y = lcS B M σ f.y := by intro σ; simp only [lcS, e1, e2]
  cases f with
  | L y c dy => exact ⟨(hS _).trans h.1, hS _⟩
  | R c y dy => exact ⟨hS _, (hS _).trans h.2.1⟩
  | D l y rr bef aft => exact ⟨hS _, hS _⟩

lemma cnodes_cons (f : Frame) (fs : List Frame) : cnodes (f :: fs) = f.fnodes ++ cnodes fs := rfl

lemma y_mem_fnodes (f : Frame) : f.y ∈ f.fnodes := by
  cases f <;> simp [Frame.fnodes, Frame.y]

/-- The parity at a frame only depends on the reversal bits of the frame nodes. -/
lemma cpar_congr {M M' : Mem} : ∀ {ctx : List Frame}, (∀ u ∈ cnodes ctx, rv B M' u = rv B M u) →
    cpar B M' ctx = cpar B M ctx
  | [], _ => rfl
  | f :: fs, h => by
    have e := cpar_congr (ctx := fs) (fun u hu => h u (by simp [cnodes_cons, hu]))
    have hy := h f.y (by simp [cnodes_cons, y_mem_fnodes])
    cases f <;> simp only [cpar, hpar, cσ, e, hy, Frame.y] at hy ⊢

lemma Agr.rv {M M' : Mem} {u : ℕ} (h : Agr B M M' u) : rv B M' u = rv B M u :=
  (h.agrC B).rvEq B

/-- A stored zipper stays stored when the memory agrees on its nodes and on what is read of the
hole root. -/
lemma EncC.frame {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') :
    ∀ {ctx : List Frame} {r p : ℕ}, EncC B n M ctx r p →
    (cnodes ctx).Nodup → (∀ u ∈ cnodes ctx, Agr B M M' u) → Look B n M M' r r →
    EncC B n M' ctx r p
  | [], _, _, _, _, _, _ => trivial
  | f :: fs, r, p, ⟨h1, h2, h3⟩, hnd, hag, hr => by
    rw [cnodes_cons, List.nodup_append] at hnd
    have hcp : cpar B M' fs = cpar B M fs :=
      cpar_congr B (fun u hu => (hag u (by simp [cnodes_cons, hu])).rv B)
    refine ⟨by rw [hcp]; exact (EncF.frame B n hN hN' h1 hnd.1
      (fun u hu => hag u (by simp [cnodes_cons, hu])) hr), ?_,
      EncC.frame hN hN' h3 hnd.2.1 (fun u hu => hag u (by simp [cnodes_cons, hu]))
      (look_of_agr B n (hag f.y (by simp [cnodes_cons, y_mem_fnodes])))⟩
    rw [show par B M' f.y = par B M f.y from
      ((hag f.y (by simp [cnodes_cons, y_mem_fnodes])) 0 (by omega)).1]
    exact h2

/-- **Replacing the subtree at the hole.** The root of the hole changes from `r` to `r'`, which
reads the same aggregates; the node above the hole is redirected, the rest agrees. -/
lemma EncC.replace {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {f : Frame}
    {fs : List Frame} {r r' p : ℕ}
    (h : EncC B n M (f :: fs) r p) (hnd : (cnodes (f :: fs)).Nodup)
    (hag : ∀ u ∈ cnodes (f :: fs), u ≠ f.y → Agr B M M' u) (hy : AgrS B M M' f.y)
    (hpar : par B M' f.y = par B M f.y) (hlook : f.Solid → Look B n M M' r r')
    (hptr : Redir B M M' f r' (cpar B M fs)) :
    EncC B n M' (f :: fs) r' p := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [cnodes_cons, List.nodup_append] at hnd
  have hyf : f.y ∉ cnodes fs := fun hm => hnd.2.2 f.y (y_mem_fnodes f) f.y hm rfl
  have hcp : cpar B M' fs = cpar B M fs :=
    cpar_congr B (fun u hu => (hag u (by simp [cnodes_cons, hu]) (fun e => hyf (e ▸ hu))).rv B)
  refine ⟨by rw [hcp]; exact (EncF.replace B n hN hN' h1 hnd.1
    (fun u hu hne => hag u (by simp [cnodes_cons, hu]) hne) hy hlook hptr),
    by rw [hpar]; exact h2,
    EncC.frame B n hN hN' h3 hnd.2.1
      (fun u hu => hag u (by simp [cnodes_cons, hu]) (fun e => hyf (e ▸ hu)))
      (look_of_agrS B n hy)⟩

/-! ### The global invariant -/

lemma nodesL_split (gb ga : List VT) (s : VT) (fs : List Frame) :
    (nodesL (gb ++ plug s fs :: ga)).Perm (nodes s ++ (cnodes fs ++ nodesL (gb ++ ga))) := by
  rw [List.perm_iff_count]; intro a
  have := (nodes_plugZ s fs).count_eq a
  simp only [nodesL_append, nodesL_cons, List.count_append] at this ⊢
  omega

lemma Agr.agrV {M M' : Mem} {u : ℕ} (h : Agr B M M' u) : AgrV B M M' u :=
  (h.agrS B).agrV B

/-- **The global invariant survives a local replacement.** -/
theorem inv_replace {M M' : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT}
    {s s' : VT} {fs : List Frame} (hG : G = gb ++ plug s fs :: ga)
    (hs' : Enc B n M' s' (hp n fs) (cpar B M' fs)) (hC : EncC B n M' fs (rt n s') n)
    (hperm : (nodes s').Perm (nodes s)) (hag : ∀ u ∈ nodesL (gb ++ ga), Agr B M M' u)
    (hnil : NilOK B n M') : Inv B n M' (gb ++ plug s' fs :: ga) := by
  have hp1 := nodesL_split gb ga s fs
  have hp2 := nodesL_split gb ga s' fs
  have hp3 : (nodesL (gb ++ plug s' fs :: ga)).Perm (nodesL G) := by
    rw [hG]; exact hp2.trans ((hperm.append_right _).trans hp1.symm)
  have hnd := hI.nodup
  have hndo : (nodesL (gb ++ ga)).Nodup := by
    rw [hG] at hnd
    exact ((hp1.nodup_iff.mp hnd).sublist (List.sublist_append_right _ _)).sublist
      (List.sublist_append_right _ _)
  refine ⟨fun T hT => ?_, hp3.nodup_iff.mpr hnd, fun u => (hp3.mem_iff).trans (hI.cover u),
    hnil⟩
  rcases List.mem_append.mp hT with hT | hT
  · have hT' : T ∈ G := by rw [hG]; exact List.mem_append_left _ hT
    exact enc_frame_all B n hI.nil hnil (hI.enc T hT') (nodup_of_mem_nodesL hndo
      (List.mem_append_left _ hT)) (fun u hu => hag u (mem_nodesL_of
        (List.mem_append_left _ hT) hu))
  · rcases List.mem_cons.mp hT with rfl | hT
    · exact (enc_plugZ B n _ _ _).mpr ⟨hs', hC⟩
    · have hT' : T ∈ G := by rw [hG]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hT)
      exact enc_frame_all B n hI.nil hnil (hI.enc T hT') (nodup_of_mem_nodesL hndo
        (List.mem_append_right _ hT)) (fun u hu => hag u (mem_nodesL_of
          (List.mem_append_right _ hT) hu))

/-! ### The represented forest -/

/-- `s'` in `M'` has the same values as `s` in `M`, both read with parity `π`. -/
def VEq (M M' : Mem) (s s' : VT) (π : Bool) : Prop :=
  ∀ k, rs B M' s' π k = rs B M s π k ∧ ∀ e, e ∈ dV B M' s' k ↔ e ∈ dV B M s k

lemma VEq.plugF {M M' : Mem} {s s' : VT} {π : Bool} (f : Frame)
    (h : VEq B M M' s s' (hpar B M f π))
    (hag : ∀ u ∈ f.fnodes, AgrV B M M' u) : VEq B M M' (f.plug s) (f.plug s') π := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  have hy := hag f.y (y_mem_fnodes f)
  cases f with
  | L y c dy =>
    simp only [Frame.y] at hy
    refine ⟨?_, fun e => ?_⟩
    · simp only [Frame.plug, rs_node, cσ, hy.2.2.2.2, hy.vlc, hy.tgc]
      simp only [hpar, Frame.y, cσ] at h1
      rw [h1, rs_frame B c (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
    · simp only [Frame.plug, dV_node, List.mem_append]
      rw [h2 e, dV_frame B c (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        dVL_frame B dy (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
  | R c y dy =>
    simp only [Frame.y] at hy
    refine ⟨?_, fun e => ?_⟩
    · simp only [Frame.plug, rs_node, cσ, hy.2.2.2.2, hy.vlc, hy.tgc]
      simp only [hpar, Frame.y, cσ] at h1
      rw [h1, rs_frame B c (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
    · simp only [Frame.plug, dV_node, List.mem_append]
      rw [h2 e, dV_frame B c (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        dVL_frame B dy (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
  | D l y r bef aft =>
    simp only [Frame.y] at hy
    refine ⟨?_, fun e => ?_⟩
    · simp only [Frame.plug, rs_node, cσ, hy.2.2.2.2, hy.vlc, hy.tgc]
      rw [rs_frame B l (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        rs_frame B r (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
    · simp only [Frame.plug, dV_node, dVL_append, dVL_cons, List.mem_append]
      simp only [hpar] at h1
      rw [h1, h2 e, dV_frame B l (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        dV_frame B r (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        dVL_frame B bef (fun u hu => hag u (by simp [Frame.fnodes, hu])),
        dVL_frame B aft (fun u hu => hag u (by simp [Frame.fnodes, hu]))]

lemma VEq.plugZ {M M' : Mem} {s s' : VT} (ctx : List Frame) (h : VEq B M M' s s' (cpar B M ctx))
    (hag : ∀ u ∈ cnodes ctx, AgrV B M M' u) : VEq B M M' (plug s ctx) (plug s' ctx) false := by
  induction ctx generalizing s s' with
  | nil => exact h
  | cons f fs ih =>
    exact ih (VEq.plugF B f h fun u hu => hag u (by simp [cnodes_cons, hu]))
      (fun u hu => hag u (by simp [cnodes_cons, hu]))

/-- **The represented forest survives a local replacement** by a tree representing the same
paths with the same values. -/
theorem repE_replace {M M' : Mem} {G : List VT} {F : Forest} (hR : RepE B n M G F)
    {gb ga : List VT} {s s' : VT} {fs : List Frame} (hG : G = gb ++ plug s fs :: ga)
    (hsame : Same s' s) (hV : VEq B M M' s s' (cpar B M fs))
    (hag : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), AgrV B M M' u) :
    RepE B n M' (gb ++ plug s' fs :: ga) F := by
  subst hG
  have hS := hsame.plugZ fs
  have hW := hV.plugZ B fs (fun u hu => hag u (List.mem_append_left _ hu))
  have hgb := fun k => dVL_frame B gb (fun u hu => hag u (by simp [hu])) k
  have hga := fun k => dVL_frame B ga (fun u hu => hag u (by simp [hu])) k
  refine ⟨fun u p h => hR.par u p ?_, fun u w h => hR.val u w ?_, fun u w h => hR.val2 u w ?_⟩
  · simp only [dEL_append, dEL_cons, List.mem_append] at h ⊢
    rw [hS.seq, hS.dE] at h; exact h
  · simp only [dVL_append, dVL_cons, List.mem_append] at h ⊢
    rw [hgb, hga, (hW false).1, (hW false).2] at h; exact h
  · simp only [dVL_append, dVL_cons, List.mem_append] at h ⊢
    rw [hgb, hga, (hW true).1, (hW true).2] at h; exact h

theorem rep_replace {M M' : Mem} {G : List VT} {F : Forest} (hR : Rep B n M G F)
    {gb ga : List VT} {s s' : VT} {fs : List Frame} (hG : G = gb ++ plug s fs :: ga)
    (hsame : Same s' s) (hV : VEq B M M' s s' (cpar B M fs))
    (hag : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), AgrV B M M' u)
    (hfp : ∀ u < n, fpar B M' u = fpar B M u) : Rep B n M' (gb ++ plug s' fs :: ga) F :=
  ⟨repE_replace B n hR.toRepE hG hsame hV hag, fun u hu => by rw [hfp u hu]; exact hR.fpar u hu⟩

end DynTree

end PlanarFlow
