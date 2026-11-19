module

public import PlanarFlow.DynTree.RotOk

/-!
# Dynamic trees: the rotation theorem

`rotate_ok`: if the memory stores the virtual forest `G = gb ++ plug t (f :: fs) :: ga` with `f`
a solid frame (the root `x` of `t` is a child of `f.y` in its auxiliary tree), then `rotMem x`
stores `gb ++ plug (rotUp t f) fs :: ga`, represents the same forest, and changes nothing
outside the structure.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- The values of a rotation: moving the tags as `rotP` does keeps every value. -/
lemma rs_rot (tx ty : ℝ) (A Bs C : List (ℕ × ℝ)) (x y : ℕ) (vx vy : ℝ) :
    shift (tx + ty) (A ++ (x, vx) :: shift (-tx) (shift tx Bs ++ (y, vy) :: C)) =
      shift ty (shift tx (A ++ (x, vx) :: Bs) ++ (y, vy) :: C) := by
  simp only [shift_append, shift_cons, shift_shift, List.append_assoc, List.cons_append]
  have e1 : tx + -tx + (tx + ty) = tx + ty := by ring
  have e2 : -tx + (tx + ty) = ty := by ring
  rw [e1, e2]
  congr 2
  · ring
  · congr 2; ring

/-- The values of the other rotation. -/
lemma rs_rot' (tx ty : ℝ) (A Bs C : List (ℕ × ℝ)) (x y : ℕ) (vx vy : ℝ) :
    shift (tx + ty) (shift (-tx) (C ++ (y, vy) :: shift tx A) ++ (x, vx) :: Bs) =
      shift ty (C ++ (y, vy) :: shift tx (A ++ (x, vx) :: Bs)) := by
  simp only [shift_append, shift_cons, shift_shift, List.append_assoc, List.cons_append]
  have e1 : tx + -tx + (tx + ty) = tx + ty := by ring
  have e2 : -tx + (tx + ty) = ty := by ring
  rw [e1, e2]
  congr 2
  · congr 1; ring
  · ring

lemma count_RR (a b c : VT) (x y : ℕ) (dx dy : List VT) (w : ℕ) :
    (nodes (node c y (node a x b dx) dy)).count w = (nodes a).count w + [x].count w +
      (nodes b).count w + (nodesL dx).count w + [y].count w + (nodes c).count w +
      (nodesL dy).count w := by
  simp only [nodes_node, List.append_assoc, List.cons_append, List.count_append, List.count_cons,
    List.count_nil]
  omega

/-- The common facts of both rotations. -/
structure RotCtx (M : Mem) (G : List VT) (gb ga : List VT) (s : VT) (fs : List Frame) : Prop where
  enc : Enc B n M s (hp n fs) (cpar B M fs)
  encC : EncC B n M fs (rt n s) n
  count : ∀ w, (nodes s).count w + (cnodes fs).count w + (nodesL (gb ++ ga)).count w ≤ 1
  lts : ∀ u ∈ nodes s, u < n
  ltc : ∀ u ∈ cnodes fs, u < n
  lto : ∀ u ∈ nodesL (gb ++ ga), u < n

lemma rotCtx {M : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT} {s : VT}
    {fs : List Frame} (hG : G = gb ++ plug s fs :: ga) : RotCtx B n M G gb ga s fs := by
  obtain ⟨hcount, hlts, hltc, hlto⟩ := hI.counts B n hG
  have hT : Enc B n M (plug s fs) n false := hI.enc _ (by rw [hG]; simp)
  rw [enc_plugZ] at hT
  exact ⟨hT.1, hT.2, hcount, hlts, hltc, hlto⟩

lemma RotCtx.z_out {M : Mem} {G : List VT} {gb ga : List VT} {s : VT} {fs : List Frame}
    (h : RotCtx B n M G gb ga s fs) : ∀ u ∈ nodes s, u ≠ hp n fs := by
  intro u hu e
  rcases hp_cases n fs with ⟨-, h'⟩ | h'
  · have := h.lts u hu; omega
  · exact ne_of_count (fun w => by have := h.count w; omega) hu h' e

lemma RotCtx.out {M : Mem} {G : List VT} {gb ga : List VT} {s : VT} {fs : List Frame}
    (h : RotCtx B n M G gb ga s fs) : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), ∀ v ∈ nodes s,
      u ≠ v := by
  intro u hu v hv
  rcases List.mem_append.mp hu with hu | hu
  · exact ne_of_count (fun w => by have := h.count w; omega) hu hv
  · exact ne_of_count (fun w => by have := h.count w; omega) hu hv

lemma RotCtx.out_lt {M : Mem} {G : List VT} {gb ga : List VT} {s : VT} {fs : List Frame}
    (h : RotCtx B n M G gb ga s fs) : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), u < n := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact h.ltc u hu
  · exact h.lto u hu

lemma rt_or_nil (b : VT) : (b = VT.leaf ∧ rt n b = n) ∨ rt n b ∈ nodes b := by
  cases b with
  | leaf => exact Or.inl ⟨rfl, rfl⟩
  | node a y c d => exact Or.inr (by simp)

/-- **The rotation of a left child**, on a stored subtree with parity `false`. -/
theorem rotLocal_L {M : Mem} (hN : NilOK B n M) {a b c : VT} {x y z : ℕ} {dx dy : List VT}
    (hsE : Enc B n M (node (node a x b dx) y c dy) z false) (hvx : rv B M x = false)
    (hvy : rv B M y = false) (hnd : (nodes (node (node a x b dx) y c dy)).Nodup)
    (hlts : ∀ u ∈ nodes (node (node a x b dx) y c dy), u < n) (hzn : z ≤ n)
    (hzs : ∀ u ∈ nodes (node (node a x b dx) y c dy), u ≠ z) :
    Enc B n (rotMem B n x M) (node a x (node b y c dy) dx) z false ∧
    VEq B M (rotMem B n x M) (node (node a x b dx) y c dy) (node a x (node b y c dy) dx) false ∧
    NilOK B n (rotMem B n x M) ∧
    (∀ u < n, u ∉ nodes (node (node a x b dx) y c dy) → u ≠ z → Agr B M (rotMem B n x M) u) ∧
    (z < n → AgrS B M (rotMem B n x M) z ∧ par B (rotMem B n x M) z = par B M z ∧
      RedirZ B M (rotMem B n x M) z y x) ∧
    MemFrame B n M (rotMem B n x M) := by
  have K : ∀ w, (nodes a).count w + [x].count w + (nodes b).count w + (nodesL dx).count w +
      [y].count w + (nodes c).count w + (nodesL dy).count w ≤ 1 := fun w => by
    have := List.nodup_iff_count_le_one.mp hnd w; rw [count_LL] at this; omega
  rw [enc_node_iff_clean B n hvy] at hsE
  obtain ⟨hzy, hlc, hrc, hAy, hxE, hcE, hdyE⟩ := hsE
  rw [enc_node_iff_clean B n hvx] at hxE
  obtain ⟨hyx, hlx, hrx, hAx, haE, hbE, hdxE⟩ := hxE
  simp only [rt_node] at hlc
  generalize hbb : rt n b = bb at hrx
  have hxs : x ∈ nodes (node (node a x b dx) y c dy) := by simp
  have hys : y ∈ nodes (node (node a x b dx) y c dy) := by simp
  have hxn := hlts x hxs
  have hyn := hlts y hys
  have hxy : x ≠ y := ne_of_count (A := [x]) (C := [y]) (fun w => by have := K w; omega)
    (by simp) (by simp)
  have hxz : x ≠ z := hzs x hxs
  have hyz : y ≠ z := hzs y hys
  -- the subtrees avoid `x` and `y`
  have nx : ∀ (L : List ℕ), (∀ w, L.count w + [x].count w ≤ 1) → ∀ u ∈ L, u ≠ x :=
    fun L h u hu => ne_of_count h hu (by simp)
  have ny : ∀ (L : List ℕ), (∀ w, L.count w + [y].count w ≤ 1) → ∀ u ∈ L, u ≠ y :=
    fun L h u hu => ne_of_count h hu (by simp)
  have hbx : bb ≠ x := by
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact nx _ (fun w => by have := K w; omega) _ h
  have hby : bb ≠ y := by
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact ny _ (fun w => by have := K w; omega) _ h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    rotP_L (B := B) (M := M) hyx hzy hlc hrx hxy hxz hyz hbx hby
  -- reading the rotated memory
  have ptr := fun u => rotMem_ptr (B := B) (n := n) (M := M) (x := x) u
  have agr : ∀ u, u ≠ x → u ≠ y → u ≠ bb → u ≠ z → Agr B M (rotMem B n x M) u :=
    fun u h1 h2 h3 h4 => rotMem_agr (h1) (by rwa [hyx]) (by simpa only [hyx, hlc, eq_self_iff_true, ite_true, hrx] using h3)
      (by rwa [hyx, hzy])
  have agrS : ∀ u, u ≠ x → u ≠ y → u ≠ bb →
      AgrS B M (rotMem B n x M) u ∧ par B (rotMem B n x M) u = par B M u :=
    fun u h1 h2 h3 => rotMem_agrS (h1) (by rwa [hyx]) (by simpa only [hyx, hlc, eq_self_iff_true, ite_true, hrx] using h3)
  have agrC : ∀ u, u ≠ x → u ≠ y → u ≠ z → AgrC B M (rotMem B n x M) u :=
    fun u h1 h2 h3 => rotMem_agrC (h1) (by rwa [hyx]) (by rwa [hyx, hzy])
  have agg := fun u (h1 : u ≠ x) (h2 : u ≠ y) => rotMem_agg (B := B) (n := n) (M := M) h1
    (by rwa [hyx])
  have vl' := fun u => rotMem_vl (B := B) (n := n) (M := M) (x := x) u
  -- the nil record
  have hnx : n ≠ x := by omega
  have hny : n ≠ y := by omega
  have hnil : NilOK B n (rotMem B n x M) := by
    obtain ⟨a1, -⟩ := agg n hnx hny
    have hc4 := congrArg Ag.c a1
    have hc3 := congrArg Ag.s1 a1
    have hc8 := congrArg Ag.s2 a1
    simp only [own] at hc4 hc3 hc8
    by_cases hzn' : z = n
    · rw [hzn'] at f11 f12
      refine ⟨?_, ?_, by rw [hc4]; exact hN.cnt, by rw [hc3]; exact hN.sm, by rw [hc8]; exact hN.sm2⟩
      · rw [(ptr _).2.1, f11, hN.lc]; simp [hny]
      · rw [(ptr _).2.2.1, f12, hN.lc, hN.rc]; simp [hny]
    · have h := agrC n hnx hny (Ne.symm hzn')
      exact ⟨by rw [lc, (h 1 (by omega)).1 (by omega)]; exact hN.lc,
        by rw [rc, (h 2 (by omega)).1 (by omega)]; exact hN.rc,
        by rw [hc4]; exact hN.cnt, by rw [hc3]; exact hN.sm, by rw [hc8]; exact hN.sm2⟩
  -- nodup facts
  have nda : (nodes a).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndb : (nodes b).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndx : (nodesL dx).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndc : (nodes c).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndy : (nodesL dy).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  -- the nodes of the subtrees are none of `x, y, bb, z`
  have inS : ∀ u, u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      u ∈ nodes (node (node a x b dx) y c dy) := by
    intro u hu; rcases hu with h | h | h | h | h <;> simp [h]
  have l1 : ∀ u, (u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy) →
      (u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy) := by
    intro u h; rcases h with h | h | h | h <;> simp [h]
  have sub_xy : ∀ u, u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      u ≠ x ∧ u ≠ y := by
    intro u hu
    rcases hu with hu | hu | hu | hu | hu
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
  have bb_out : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy → u ≠ bb := by
    intro u hu e
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · have := hlts u (inS u (l1 u hu)); rw [← hbb, h] at e; omega
    · rw [← hbb] at e; subst e
      rcases hu with hu | hu | hu | hu
      · exact ne_of_count (A := nodes a) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodesL dx) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodes c) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodesL dy) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
  have agrSub : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      Agr B M (rotMem B n x M) u := fun u hu =>
    agr u (sub_xy u (l1 u hu)).1 (sub_xy u (l1 u hu)).2 (bb_out u hu)
      (hzs u (inS u (l1 u hu)))
  have agrB : ∀ u ∈ nodes b, u ≠ rt n b → Agr B M (rotMem B n x M) u := fun u hu hne =>
    agr u (sub_xy u (Or.inr (Or.inl hu))).1 (sub_xy u (Or.inr (Or.inl hu))).2 (by rwa [← hbb])
      (hzs u (inS u (Or.inr (Or.inl hu))))
  -- the encodings of the parts
  have haE' : Enc B n (rotMem B n x M) a x false :=
    enc_frame_all B n hN hnil haE nda (fun u hu => agrSub u (Or.inl hu))
  have hcE' : Enc B n (rotMem B n x M) c y false :=
    enc_frame_all B n hN hnil hcE ndc (fun u hu => agrSub u (Or.inr (Or.inr (Or.inl hu))))
  have hdxE' : ∀ d ∈ dx, Enc B n (rotMem B n x M) d x false :=
    enc_frame_list B n hN hnil hdxE ndx (fun u hu => agrSub u (Or.inr (Or.inl hu)))
  have hdyE' : ∀ d ∈ dy, Enc B n (rotMem B n x M) d y false :=
    enc_frame_list B n hN hnil hdyE ndy (fun u hu => agrSub u (Or.inr (Or.inr (Or.inr hu))))
  have hbE' : Enc B n (rotMem B n x M) b y false :=
    Enc.frame B n hN hnil hbE ndb y agrB
      (fun hne => agrC _ (by rw [hbb]; exact hbx) (by rw [hbb]; exact hby)
        (hzs _ (inS _ (Or.inr (Or.inl (rt_mem_nodes hne n))))))
      (fun _ => by rw [hbb, (ptr bb).1, f7])
  -- the aggregates of `y` and `x`
  have hM1y_l : lc B (rotP B x M) y ≠ y := by rw [f5]; exact hby
  have hM1y_r : rc B (rotP B x M) y ≠ y := by
    rw [f6, hrc]
    rcases rt_or_nil n c with ⟨-, h⟩ | h
    · rw [h]; omega
    · exact ny _ (fun w => by have := K w; omega) _ h
  have hAy2 := aggOK_recomp B n hM1y_l hM1y_r (by simp only [rv, rvw]; rw [rotP_nm (by omega) (by omega)]; exact hvy)
  obtain ⟨-, eyl, eyr, -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := rotP B x M) (u := y) (v := y)
  have hrm : rotMem B n x M = recomp B n x (recomp B n y (rotP B x M)) := by
    simp only [rotMem, hyx]
  have hAy' : AggOK B n (rotMem B n x M) y := by
    rw [hrm]
    have e := recomp_agr B n (M := recomp B n y (rotP B x M)) (u := x) hxy.symm
    refine hAy2.of_agrC B n (e.agrC B) ?_ ?_
    · rw [eyl, f5]
      exact look_of_agr B n (recomp_agr B n hbx)
    · rw [eyr, f6, hrc]
      rcases rt_or_nil n c with ⟨-, h⟩ | h
      · rw [h]; exact look_of_agr B n (recomp_agr B n hnx)
      · exact look_of_agr B n (recomp_agr B n (nx _ (fun w => by have := K w; omega) _ h))
  obtain ⟨-, exl, exr, -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := recomp B n y (rotP B x M)) (u := x)
    (v := x)
  obtain ⟨-, exl', exr', -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := rotP B x M) (u := y) (v := x)
  have hAx' : AggOK B n (rotMem B n x M) x := by
    have h1 : lc B (recomp B n y (rotP B x M)) x ≠ x := by
      rw [exl', f2, hlx]
      rcases rt_or_nil n a with ⟨-, h⟩ | h
      · rw [h]; omega
      · exact nx _ (fun w => by have := K w; omega) _ h
    have h2 : rc B (recomp B n y (rotP B x M)) x ≠ x := by rw [exr', f3]; exact hxy.symm
    have := aggOK_recomp B n h1 h2 (by simp only [rv, rvw]; rw [recomp_nm B n (by omega) (by omega), rotP_nm (by omega) (by omega)]; exact hvx)
    rwa [show recomp B n x (recomp B n y (rotP B x M)) = rotMem B n x M by
      simp only [rotMem, hyx]] at this
  -- the rotated tree is stored
  have hyE' : Enc B n (rotMem B n x M) (node b y c dy) x false := by
    rw [enc_node_iff_clean B n (by rw [rotMem_rv]; exact hvy)]
    refine ⟨by rw [(ptr y).1, f4], by rw [(ptr y).2.1, f5, hbb], by rw [(ptr y).2.2.1, f6, hrc],
      hAy', hbE', hcE', hdyE'⟩
  have hsE' : Enc B n (rotMem B n x M) (node a x (node b y c dy) dx) z false := by
    rw [enc_node_iff_clean B n (by rw [rotMem_rv]; exact hvx)]
    refine ⟨by rw [(ptr x).1, f1], by rw [(ptr x).2.1, f2, hlx], by rw [(ptr x).2.2.1, f3]; rfl,
      hAx', haE', hyE', hdxE'⟩
  -- the values
  have agv : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      AgrV B M (rotMem B n x M) u := fun u hu => (agrSub u hu).agrV B
  have rsb : ∀ k, rs B (rotMem B n x M) b false k = shift (tgc B M k x) (rs B M b false k) := by
    intro k
    refine rs_retag B n (fun u hu hne => (agrB u hu hne).agrV B) ndb (fun j => ?_)
      (by rw [hbb]; exact rotMem_rv bb) ?_
    · rw [hbb]; cases j <;> simp [vlc, (vl' bb).1, (vl' bb).2]
    · rw [hbb]; cases k <;> simp [tgc, (ptr bb).2.2.2.1, (ptr bb).2.2.2.2, f10, f15]
  have dVb : ∀ k, dV B (rotMem B n x M) b k = dV B M b k :=
    dV_frame_root B n (fun u hu hne => (agrB u hu hne).agrV B) ndb
  have ex : rv B (rotMem B n x M) x = false := by rw [rotMem_rv]; exact hvx
  have ey : rv B (rotMem B n x M) y = false := by rw [rotMem_rv]; exact hvy
  have hV : VEq B M (rotMem B n x M) (node (node a x b dx) y c dy) (node a x (node b y c dy) dx)
      false := by
    intro k
    refine ⟨?_, fun e => ?_⟩
    · simp only [rs_node, cσ, hvx, hvy, ex, ey, Bool.xor_false]
      rw [rs_frame B a (fun u hu => agv u (Or.inl hu)),
        rs_frame B c (fun u hu => agv u (Or.inr (Or.inr (Or.inl hu)))), rsb]
      cases k
      · simp only [vlc, tgc, Bool.false_eq_true, ↓reduceIte, (vl' x).1, (vl' y).1,
          (ptr x).2.2.2.1, (ptr y).2.2.2.1, f8, f9]
        exact rs_rot _ _ _ _ _ _ _ _ _
      · simp only [vlc, tgc, ↓reduceIte, (vl' x).2, (vl' y).2, (ptr x).2.2.2.2, (ptr y).2.2.2.2,
          f13, f14]
        exact rs_rot _ _ _ _ _ _ _ _ _
    · simp only [dV_node, List.mem_append]
      rw [dV_frame B a (fun u hu => agv u (Or.inl hu)) k,
        dV_frame B c (fun u hu => agv u (Or.inr (Or.inr (Or.inl hu)))) k,
        dVb, dVL_frame B dx (fun u hu => agv u (Or.inr (Or.inl hu))) k,
        dVL_frame B dy (fun u hu => agv u (Or.inr (Or.inr (Or.inr hu)))) k]
      simp only [or_assoc, or_comm, or_left_comm]
  have hzb : z < n → z ≠ bb := by
    intro hz'
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact fun e => hzs _ (inS _ (Or.inr (Or.inl h))) e.symm
  refine ⟨hsE', hV, hnil, fun u hun hu hne => ?_, fun hz' => ?_, ?_⟩
  · refine agr u (fun e => hu (e ▸ hxs)) (fun e => hu (e ▸ hys)) ?_ hne
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact fun e => hu (e ▸ inS _ (Or.inr (Or.inl h)))
  · obtain ⟨s1, s2⟩ := agrS z hxz.symm hyz.symm (hzb hz')
    exact ⟨s1, s2, by rw [(ptr z).2.1, f11], by rw [(ptr z).2.2.1, f12]⟩
  · refine rotMem_frame (by omega) (by rw [hyx]; omega) (by rw [hyx, hzy]; exact hzn) ?_
    simp only [hyx, hlc, eq_self_iff_true, ite_true, hrx]
    rw [← hbb]
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [h]
    · have := hlts _ (inS _ (Or.inr (Or.inl h))); omega

/-- **The rotation of a right child**, on a stored subtree with parity `false`. -/
theorem rotLocal_R {M : Mem} (hN : NilOK B n M) {a b c : VT} {x y z : ℕ} {dx dy : List VT}
    (hsE : Enc B n M (node c y (node b x a dx) dy) z false) (hvx : rv B M x = false)
    (hvy : rv B M y = false) (hnd : (nodes (node c y (node b x a dx) dy)).Nodup)
    (hlts : ∀ u ∈ nodes (node c y (node b x a dx) dy), u < n) (hzn : z ≤ n)
    (hzs : ∀ u ∈ nodes (node c y (node b x a dx) dy), u ≠ z) :
    Enc B n (rotMem B n x M) (node (node c y b dy) x a dx) z false ∧
    VEq B M (rotMem B n x M) (node c y (node b x a dx) dy) (node (node c y b dy) x a dx) false ∧
    NilOK B n (rotMem B n x M) ∧
    (∀ u < n, u ∉ nodes (node c y (node b x a dx) dy) → u ≠ z → Agr B M (rotMem B n x M) u) ∧
    (z < n → AgrS B M (rotMem B n x M) z ∧ par B (rotMem B n x M) z = par B M z ∧
      RedirZ B M (rotMem B n x M) z y x) ∧
    MemFrame B n M (rotMem B n x M) := by
  have K : ∀ w, (nodes a).count w + [x].count w + (nodes b).count w + (nodesL dx).count w +
      [y].count w + (nodes c).count w + (nodesL dy).count w ≤ 1 := fun w => by
    have := List.nodup_iff_count_le_one.mp hnd w; rw [count_RR] at this; omega
  rw [enc_node_iff_clean B n hvy] at hsE
  obtain ⟨hzy, hlc, hrc, hAy, hcE, hxE, hdyE⟩ := hsE
  rw [enc_node_iff_clean B n hvx] at hxE
  obtain ⟨hyx, hlx, hrx, hAx, hbE, haE, hdxE⟩ := hxE
  simp only [rt_node] at hrc
  generalize hbb : rt n b = bb at hlx
  have hxs : x ∈ nodes (node c y (node b x a dx) dy) := by simp
  have hys : y ∈ nodes (node c y (node b x a dx) dy) := by simp
  have hxn := hlts x hxs
  have hyn := hlts y hys
  have hxy : x ≠ y := ne_of_count (A := [x]) (C := [y]) (fun w => by have := K w; omega)
    (by simp) (by simp)
  have hxz : x ≠ z := hzs x hxs
  have hyz : y ≠ z := hzs y hys
  -- the subtrees avoid `x` and `y`
  have nx : ∀ (L : List ℕ), (∀ w, L.count w + [x].count w ≤ 1) → ∀ u ∈ L, u ≠ x :=
    fun L h u hu => ne_of_count h hu (by simp)
  have ny : ∀ (L : List ℕ), (∀ w, L.count w + [y].count w ≤ 1) → ∀ u ∈ L, u ≠ y :=
    fun L h u hu => ne_of_count h hu (by simp)
  have hbx : bb ≠ x := by
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact nx _ (fun w => by have := K w; omega) _ h
  have hby : bb ≠ y := by
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact ny _ (fun w => by have := K w; omega) _ h
  have hlcx : lc B M y ≠ x := by
    rw [hlc]
    rcases rt_or_nil n c with ⟨-, h⟩ | h
    · rw [h]; omega
    · exact nx _ (fun w => by have := K w; omega) _ h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    rotP_R (B := B) (M := M) hyx hzy hlcx hlx hxy hxz hyz hbx hby
  -- reading the rotated memory
  have ptr := fun u => rotMem_ptr (B := B) (n := n) (M := M) (x := x) u
  have agr : ∀ u, u ≠ x → u ≠ y → u ≠ bb → u ≠ z → Agr B M (rotMem B n x M) u :=
    fun u h1 h2 h3 h4 => rotMem_agr (h1) (by rwa [hyx]) (by simpa only [hyx, hlcx, ite_false, hlx] using h3)
      (by rwa [hyx, hzy])
  have agrS : ∀ u, u ≠ x → u ≠ y → u ≠ bb →
      AgrS B M (rotMem B n x M) u ∧ par B (rotMem B n x M) u = par B M u :=
    fun u h1 h2 h3 => rotMem_agrS (h1) (by rwa [hyx]) (by simpa only [hyx, hlcx, ite_false, hlx] using h3)
  have agrC : ∀ u, u ≠ x → u ≠ y → u ≠ z → AgrC B M (rotMem B n x M) u :=
    fun u h1 h2 h3 => rotMem_agrC (h1) (by rwa [hyx]) (by rwa [hyx, hzy])
  have agg := fun u (h1 : u ≠ x) (h2 : u ≠ y) => rotMem_agg (B := B) (n := n) (M := M) h1
    (by rwa [hyx])
  have vl' := fun u => rotMem_vl (B := B) (n := n) (M := M) (x := x) u
  -- the nil record
  have hnx : n ≠ x := by omega
  have hny : n ≠ y := by omega
  have hnil : NilOK B n (rotMem B n x M) := by
    obtain ⟨a1, -⟩ := agg n hnx hny
    have hc4 := congrArg Ag.c a1
    have hc3 := congrArg Ag.s1 a1
    have hc8 := congrArg Ag.s2 a1
    simp only [own] at hc4 hc3 hc8
    by_cases hzn' : z = n
    · rw [hzn'] at f11 f12
      refine ⟨?_, ?_, by rw [hc4]; exact hN.cnt, by rw [hc3]; exact hN.sm, by rw [hc8]; exact hN.sm2⟩
      · rw [(ptr _).2.1, f11, hN.lc]; simp [hny]
      · rw [(ptr _).2.2.1, f12, hN.lc, hN.rc]; simp [hny]
    · have h := agrC n hnx hny (Ne.symm hzn')
      exact ⟨by rw [lc, (h 1 (by omega)).1 (by omega)]; exact hN.lc,
        by rw [rc, (h 2 (by omega)).1 (by omega)]; exact hN.rc,
        by rw [hc4]; exact hN.cnt, by rw [hc3]; exact hN.sm, by rw [hc8]; exact hN.sm2⟩
  -- nodup facts
  have nda : (nodes a).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndb : (nodes b).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndx : (nodesL dx).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndc : (nodes c).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  have ndy : (nodesL dy).Nodup := List.nodup_iff_count_le_one.mpr fun w => by have := K w; omega
  -- the nodes of the subtrees are none of `x, y, bb, z`
  have inS : ∀ u, u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      u ∈ nodes (node c y (node b x a dx) dy) := by
    intro u hu; rcases hu with h | h | h | h | h <;> simp [h]
  have l1 : ∀ u, (u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy) →
      (u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy) := by
    intro u h; rcases h with h | h | h | h <;> simp [h]
  have sub_xy : ∀ u, u ∈ nodes a ∨ u ∈ nodes b ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      u ≠ x ∧ u ≠ y := by
    intro u hu
    rcases hu with hu | hu | hu | hu | hu
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
    · exact ⟨nx _ (fun w => by have := K w; omega) u hu, ny _ (fun w => by have := K w; omega) u hu⟩
  have bb_out : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy → u ≠ bb := by
    intro u hu e
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · have := hlts u (inS u (l1 u hu)); rw [← hbb, h] at e; omega
    · rw [← hbb] at e; subst e
      rcases hu with hu | hu | hu | hu
      · exact ne_of_count (A := nodes a) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodesL dx) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodes c) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
      · exact ne_of_count (A := nodesL dy) (C := nodes b) (fun w => by have := K w; omega) hu h rfl
  have agrSub : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      Agr B M (rotMem B n x M) u := fun u hu =>
    agr u (sub_xy u (l1 u hu)).1 (sub_xy u (l1 u hu)).2 (bb_out u hu)
      (hzs u (inS u (l1 u hu)))
  have agrB : ∀ u ∈ nodes b, u ≠ rt n b → Agr B M (rotMem B n x M) u := fun u hu hne =>
    agr u (sub_xy u (Or.inr (Or.inl hu))).1 (sub_xy u (Or.inr (Or.inl hu))).2 (by rwa [← hbb])
      (hzs u (inS u (Or.inr (Or.inl hu))))
  -- the encodings of the parts
  have haE' : Enc B n (rotMem B n x M) a x false :=
    enc_frame_all B n hN hnil haE nda (fun u hu => agrSub u (Or.inl hu))
  have hcE' : Enc B n (rotMem B n x M) c y false :=
    enc_frame_all B n hN hnil hcE ndc (fun u hu => agrSub u (Or.inr (Or.inr (Or.inl hu))))
  have hdxE' : ∀ d ∈ dx, Enc B n (rotMem B n x M) d x false :=
    enc_frame_list B n hN hnil hdxE ndx (fun u hu => agrSub u (Or.inr (Or.inl hu)))
  have hdyE' : ∀ d ∈ dy, Enc B n (rotMem B n x M) d y false :=
    enc_frame_list B n hN hnil hdyE ndy (fun u hu => agrSub u (Or.inr (Or.inr (Or.inr hu))))
  have hbE' : Enc B n (rotMem B n x M) b y false :=
    Enc.frame B n hN hnil hbE ndb y agrB
      (fun hne => agrC _ (by rw [hbb]; exact hbx) (by rw [hbb]; exact hby)
        (hzs _ (inS _ (Or.inr (Or.inl (rt_mem_nodes hne n))))))
      (fun _ => by rw [hbb, (ptr bb).1, f7])
  -- the aggregates of `y` and `x`
  have hM1y_r : rc B (rotP B x M) y ≠ y := by rw [f6]; exact hby
  have hM1y_l : lc B (rotP B x M) y ≠ y := by
    rw [f5, hlc]
    rcases rt_or_nil n c with ⟨-, h⟩ | h
    · rw [h]; omega
    · exact ny _ (fun w => by have := K w; omega) _ h
  have hAy2 := aggOK_recomp B n hM1y_l hM1y_r (by simp only [rv, rvw]; rw [rotP_nm (by omega) (by omega)]; exact hvy)
  obtain ⟨-, eyl, eyr, -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := rotP B x M) (u := y) (v := y)
  have hrm : rotMem B n x M = recomp B n x (recomp B n y (rotP B x M)) := by
    simp only [rotMem, hyx]
  have hAy' : AggOK B n (rotMem B n x M) y := by
    rw [hrm]
    have e := recomp_agr B n (M := recomp B n y (rotP B x M)) (u := x) hxy.symm
    refine hAy2.of_agrC B n (e.agrC B) ?_ ?_
    · rw [eyl, f5, hlc]
      rcases rt_or_nil n c with ⟨-, h⟩ | h
      · rw [h]; exact look_of_agr B n (recomp_agr B n hnx)
      · exact look_of_agr B n (recomp_agr B n (nx _ (fun w => by have := K w; omega) _ h))
    · rw [eyr, f6]
      exact look_of_agr B n (recomp_agr B n hbx)
  obtain ⟨-, exl, exr, -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := recomp B n y (rotP B x M)) (u := x)
    (v := x)
  obtain ⟨-, exl', exr', -, -, -, -, -, -⟩ := recomp_agrS_par B n (M := rotP B x M) (u := y) (v := x)
  have hAx' : AggOK B n (rotMem B n x M) x := by
    have h1 : lc B (recomp B n y (rotP B x M)) x ≠ x := by
      rw [exl', f2]; exact hxy.symm
    have h2 : rc B (recomp B n y (rotP B x M)) x ≠ x := by
      rw [exr', f3, hrx]
      rcases rt_or_nil n a with ⟨-, h⟩ | h
      · rw [h]; omega
      · exact nx _ (fun w => by have := K w; omega) _ h
    have := aggOK_recomp B n h1 h2 (by simp only [rv, rvw]; rw [recomp_nm B n (by omega) (by omega), rotP_nm (by omega) (by omega)]; exact hvx)
    rwa [show recomp B n x (recomp B n y (rotP B x M)) = rotMem B n x M by
      simp only [rotMem, hyx]] at this
  -- the rotated tree is stored
  have hyE' : Enc B n (rotMem B n x M) (node c y b dy) x false := by
    rw [enc_node_iff_clean B n (by rw [rotMem_rv]; exact hvy)]
    refine ⟨by rw [(ptr y).1, f4], by rw [(ptr y).2.1, f5, hlc], by rw [(ptr y).2.2.1, f6, hbb],
      hAy', hcE', hbE', hdyE'⟩
  have hsE' : Enc B n (rotMem B n x M) (node (node c y b dy) x a dx) z false := by
    rw [enc_node_iff_clean B n (by rw [rotMem_rv]; exact hvx)]
    refine ⟨by rw [(ptr x).1, f1], by rw [(ptr x).2.1, f2]; rfl, by rw [(ptr x).2.2.1, f3, hrx],
      hAx', hyE', haE', hdxE'⟩
  -- the values
  have agv : ∀ u, u ∈ nodes a ∨ u ∈ nodesL dx ∨ u ∈ nodes c ∨ u ∈ nodesL dy →
      AgrV B M (rotMem B n x M) u := fun u hu => (agrSub u hu).agrV B
  have rsb : ∀ k, rs B (rotMem B n x M) b false k = shift (tgc B M k x) (rs B M b false k) := by
    intro k
    refine rs_retag B n (fun u hu hne => (agrB u hu hne).agrV B) ndb (fun j => ?_)
      (by rw [hbb]; exact rotMem_rv bb) ?_
    · rw [hbb]; cases j <;> simp [vlc, (vl' bb).1, (vl' bb).2]
    · rw [hbb]; cases k <;> simp [tgc, (ptr bb).2.2.2.1, (ptr bb).2.2.2.2, f10, f15]
  have dVb : ∀ k, dV B (rotMem B n x M) b k = dV B M b k :=
    dV_frame_root B n (fun u hu hne => (agrB u hu hne).agrV B) ndb
  have ex : rv B (rotMem B n x M) x = false := by rw [rotMem_rv]; exact hvx
  have ey : rv B (rotMem B n x M) y = false := by rw [rotMem_rv]; exact hvy
  have hV : VEq B M (rotMem B n x M) (node c y (node b x a dx) dy) (node (node c y b dy) x a dx)
      false := by
    intro k
    refine ⟨?_, fun e => ?_⟩
    · simp only [rs_node, cσ, hvx, hvy, ex, ey, Bool.xor_false]
      rw [rs_frame B a (fun u hu => agv u (Or.inl hu)),
        rs_frame B c (fun u hu => agv u (Or.inr (Or.inr (Or.inl hu)))), rsb]
      cases k
      · simp only [vlc, tgc, Bool.false_eq_true, ↓reduceIte, (vl' x).1, (vl' y).1,
          (ptr x).2.2.2.1, (ptr y).2.2.2.1, f8, f9]
        exact rs_rot' _ _ _ _ _ _ _ _ _
      · simp only [vlc, tgc, ↓reduceIte, (vl' x).2, (vl' y).2, (ptr x).2.2.2.2, (ptr y).2.2.2.2,
          f13, f14]
        exact rs_rot' _ _ _ _ _ _ _ _ _
    · simp only [dV_node, List.mem_append]
      rw [dV_frame B a (fun u hu => agv u (Or.inl hu)) k,
        dV_frame B c (fun u hu => agv u (Or.inr (Or.inr (Or.inl hu)))) k,
        dVb, dVL_frame B dx (fun u hu => agv u (Or.inr (Or.inl hu))) k,
        dVL_frame B dy (fun u hu => agv u (Or.inr (Or.inr (Or.inr hu)))) k]
      simp only [or_assoc, or_comm, or_left_comm]
  have hzb : z < n → z ≠ bb := by
    intro hz'
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact fun e => hzs _ (inS _ (Or.inr (Or.inl h))) e.symm
  refine ⟨hsE', hV, hnil, fun u hun hu hne => ?_, fun hz' => ?_, ?_⟩
  · refine agr u (fun e => hu (e ▸ hxs)) (fun e => hu (e ▸ hys)) ?_ hne
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [← hbb, h]; omega
    · rw [← hbb]; exact fun e => hu (e ▸ inS _ (Or.inr (Or.inl h)))
  · obtain ⟨s1, s2⟩ := agrS z hxz.symm hyz.symm (hzb hz')
    exact ⟨s1, s2, by rw [(ptr z).2.1, f11], by rw [(ptr z).2.2.1, f12]⟩
  · refine rotMem_frame (by omega) (by rw [hyx]; omega) (by rw [hyx, hzy]; exact hzn) ?_
    simp only [hyx, hlcx, ite_false, hlx]
    rw [← hbb]
    rcases rt_or_nil n b with ⟨-, h⟩ | h
    · rw [h]
    · have := hlts _ (inS _ (Or.inr (Or.inl h))); omega

/-! ### Rotations with any parity, and the rotation theorem -/

lemma dV_mirT (M : Mem) : ∀ (t : VT) (k : Bool) (e : ℕ × ℝ), e ∈ dV B M (mirT t) k ↔ e ∈ dV B M t k
  | VT.leaf, _, _ => Iff.rfl
  | VT.node l x r ds, k, e => by
    simp only [mirT_node, dV_node, List.mem_append, dV_mirT M l k e, dV_mirT M r k e]; tauto

/-- Values read with parity `true` are those of the mirror image read with parity `false`. -/
lemma VEq.of_mirT {M M' : Mem} {s s' : VT} (h : VEq B M M' (mirT s) (mirT s') false) :
    VEq B M M' s s' true := by
  intro k
  obtain ⟨h1, -⟩ := h (!k)
  obtain ⟨-, h2⟩ := h k
  refine ⟨?_, fun e => ?_⟩
  · have e1 := rs_mirT B M' s' false (!k)
    have e2 := rs_mirT B M s false (!k)
    simp only [Bool.not_false, Bool.not_not] at e1 e2
    rw [h1, e2] at e1
    exact (List.reverse_inj.mp e1).symm
  · have := h2 e
    rwa [dV_mirT, dV_mirT] at this

/-- **The rotation of `x` above its parent `y`**, on a stored subtree with any parity, `x` and `y`
having their reversal bits clear. -/
theorem rotLocal {M : Mem} (hN : NilOK B n M) {t : VT} {f : Frame} (ht : t ≠ VT.leaf)
    (hf : f.Solid) {z : ℕ} {π : Bool} (hsE : Enc B n M (f.plug t) z π)
    (hvx : rv B M (rt n t) = false) (hvy : rv B M f.y = false)
    (hnd : (nodes (f.plug t)).Nodup) (hlts : ∀ u ∈ nodes (f.plug t), u < n) (hzn : z ≤ n)
    (hzs : ∀ u ∈ nodes (f.plug t), u ≠ z) :
    Enc B n (rotMem B n (rt n t) M) (rotUp t f) z π ∧
    VEq B M (rotMem B n (rt n t) M) (f.plug t) (rotUp t f) π ∧
    NilOK B n (rotMem B n (rt n t) M) ∧
    (∀ u < n, u ∉ nodes (f.plug t) → u ≠ z → Agr B M (rotMem B n (rt n t) M) u) ∧
    (z < n → AgrS B M (rotMem B n (rt n t) M) z ∧ par B (rotMem B n (rt n t) M) z = par B M z ∧
      RedirZ B M (rotMem B n (rt n t) M) z f.y (rt n t)) ∧
    MemFrame B n M (rotMem B n (rt n t) M) := by
  -- parity `false`
  have P0 : ∀ {t : VT} {f : Frame}, t ≠ VT.leaf → f.Solid → Enc B n M (f.plug t) z false →
      rv B M (rt n t) = false → rv B M f.y = false → (nodes (f.plug t)).Nodup →
      (∀ u ∈ nodes (f.plug t), u < n) → (∀ u ∈ nodes (f.plug t), u ≠ z) →
      Enc B n (rotMem B n (rt n t) M) (rotUp t f) z false ∧
      VEq B M (rotMem B n (rt n t) M) (f.plug t) (rotUp t f) false ∧
      NilOK B n (rotMem B n (rt n t) M) ∧
      (∀ u < n, u ∉ nodes (f.plug t) → u ≠ z → Agr B M (rotMem B n (rt n t) M) u) ∧
      (z < n → AgrS B M (rotMem B n (rt n t) M) z ∧ par B (rotMem B n (rt n t) M) z = par B M z ∧
        RedirZ B M (rotMem B n (rt n t) M) z f.y (rt n t)) ∧
      MemFrame B n M (rotMem B n (rt n t) M) := by
    intro t f ht hf hsE hvx hvy hnd hlts hzs
    obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
      cases t with
      | leaf => exact absurd rfl ht
      | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
    rcases frame_solid_cases hf with ⟨y, c, dy, rfl⟩ | ⟨c, y, dy, rfl⟩
    · exact rotLocal_L B n hN hsE hvx hvy hnd hlts hzn hzs
    · exact rotLocal_R B n hN (a := b) (b := a) hsE hvx hvy hnd hlts hzn hzs
  cases π with
  | false => exact P0 ht hf hsE hvx hvy hnd hlts hzs
  | true =>
    have hperm := nodes_mirT (f.plug t)
    rw [mirT_plugF hf] at hperm
    have hE0 : Enc B n M ((mirF f).plug (mirT t)) z false := by
      rw [← mirT_plugF hf]; exact (enc_mirror_iff B n).mpr hsE
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := P0 (t := mirT t) (f := mirF f)
      (by rwa [Ne, mirT_eq_leaf]) (mirF_solid.mpr hf) hE0 (by rw [rt_mirT]; exact hvx)
      (by rw [mirF_y]; exact hvy) (hperm.nodup_iff.mpr hnd)
      (fun u hu => hlts u (hperm.mem_iff.mp hu)) (fun u hu => hzs u (hperm.mem_iff.mp hu))
    simp only [rt_mirT, mirF_y] at e1 e2 e3 e4 e5 e6
    rw [← mirT_rotUp t hf] at e1 e2
    rw [← mirT_plugF hf] at e2
    refine ⟨(enc_mirror_iff B n).mp e1, VEq.of_mirT B e2, e3,
      fun u hu h1 h2 => e4 u hu (fun h => h1 (hperm.mem_iff.mp h)) h2, e5, e6⟩

/-- **The rotation theorem.** If the memory stores `gb ++ plug t (f :: fs) :: ga` with `f` a solid
frame, and the reversal bits of the root `x` of `t` and of its parent are clear, the rotation of
`x` stores `gb ++ plug (rotUp t f) fs :: ga`, which represents the same forest, and changes nothing
outside the structure. -/
theorem rotate_okE {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {t : VT} {f : Frame} {fs : List Frame}
    (hG : G = gb ++ plug t (f :: fs) :: ga) (hf : f.Solid) (ht : t ≠ VT.leaf)
    (hvx : rv B M (rt n t) = false) (hvy : rv B M f.y = false) :
    Inv B n (rotMem B n (rt n t) M) (gb ++ plug (rotUp t f) fs :: ga) ∧
    RepE B n (rotMem B n (rt n t) M) (gb ++ plug (rotUp t f) fs :: ga) F ∧
    MemFrame B n M (rotMem B n (rt n t) M) := by
  have hG' : G = gb ++ plug (f.plug t) fs :: ga := hG
  have hX := rotCtx B n hI hG'
  have hzs := hX.z_out
  have hout := hX.out
  have houtlt := hX.out_lt
  obtain ⟨hsE, -, hcount, hlts, hltc, hlto⟩ := hX
  have hnd : (nodes (f.plug t)).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w => by have := hcount w; omega
  have hzn : hp n fs ≤ n := by
    rcases hp_cases n fs with ⟨-, h⟩ | h
    · omega
    · have := hltc _ h; omega
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rotLocal B n hI.nil ht hf hsE hvx hvy hnd hlts hzn hzs
  have hsne : f.plug t ≠ VT.leaf := by cases f <;> simp [Frame.plug]
  have hrne : rotUp t f ≠ VT.leaf := by
    intro h; have := size_rotUp t f; rw [h, size_leaf, Frame.size_plug] at this
    have := size_pos_of_ne_leaf ht; omega
  obtain ⟨hI', hR'⟩ := replace_okE B n hI hR hG' e1 (same_rotUp hf) e2 hsne hrne
    (fun u hu hne => e4 u (houtlt u hu) (fun h => hout u hu u h rfl) hne)
    (fun hne => by
      have hz : hp n fs < n := by
        rcases hp_cases n fs with ⟨h, -⟩ | h
        · exact absurd h hne
        · exact hltc _ h
      obtain ⟨s1, s2, s3⟩ := e5 hz
      refine ⟨s1, s2, ?_⟩
      rw [rt_plugF, rt_rotUp ht hf]; exact s3)
    e3
  exact ⟨hI', hR', e6⟩

theorem rotate_ok {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G) (hR : Rep B n M G F)
    {gb ga : List VT} {t : VT} {f : Frame} {fs : List Frame}
    (hG : G = gb ++ plug t (f :: fs) :: ga) (hf : f.Solid) (ht : t ≠ VT.leaf)
    (hvx : rv B M (rt n t) = false) (hvy : rv B M f.y = false) :
    Inv B n (rotMem B n (rt n t) M) (gb ++ plug (rotUp t f) fs :: ga) ∧
    Rep B n (rotMem B n (rt n t) M) (gb ++ plug (rotUp t f) fs :: ga) F ∧
    MemFrame B n M (rotMem B n (rt n t) M) := by
  obtain ⟨h1, h2, h3⟩ := rotate_okE B n hI hR.toRepE hG hf ht hvx hvy
  exact ⟨h1, ⟨h2, fun u hu => by rw [rotMem_fpar]; exact hR.fpar u hu⟩, h3⟩

end DynTree

end PlanarFlow
