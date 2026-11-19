module

public import PlanarFlow.DynTree.Splay

/-!
# Dynamic trees: changing the preferred child

At the root `w` of an auxiliary tree (the zipper above starts with a hanging frame, or is empty),
`switchR w y` makes the root `y` of a tree hanging from `w` the right child of `w` and hangs the
old right child instead (`y = n`: the right child is just hung). The in-order of the auxiliary
tree changes, but the represented edges and values do not: `replaceTop_ok` is the replacement
theorem for this situation, where only the edges `edges p s` and the values `rs s ++ dV s` of the
replaced tree matter.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- `s` and `s'` represent the same edges below `p`. -/
def EEq (p : ℕ) (s s' : VT) : Prop := ∀ e, e ∈ edges p s' ↔ e ∈ edges p s

/-- `s` in `M` and `s'` in `M'`, both read with parity `false`, carry the same values. -/
def VEq2 (M M' : Mem) (s s' : VT) : Prop :=
  ∀ k e, e ∈ rs B M' s' false k ++ dV B M' s' k ↔ e ∈ rs B M s false k ++ dV B M s k

lemma Same.plugD {s s' : VT} {l r : VT} {y : ℕ} {bef aft : List VT} (hE : EEq y s s')
    (hperm : (nodes s').Perm (nodes s)) :
    Same ((Frame.D l y r bef aft).plug s') ((Frame.D l y r bef aft).plug s) := by
  refine ⟨rfl, fun e => ?_, ?_, ?_⟩
  · have := hE e
    simp only [edges, List.mem_append] at this
    simp only [Frame.plug, dE_node, dEL_append, dEL_cons, List.mem_append]
    tauto
  · rw [List.perm_iff_count]; intro a
    have := hperm.count_eq a
    simp only [Frame.plug, nodes_node, nodesL_append, nodesL_cons, List.count_append,
      List.count_cons]
    omega
  · have := hperm.length_eq
    rw [← size_eq_length, ← size_eq_length] at this
    simp [Frame.plug, this]

lemma VEq.plugD {M M' : Mem} {s s' : VT} {l r : VT} {y : ℕ} {bef aft : List VT} {π : Bool}
    (hV : VEq2 B M M' s s') (hag : ∀ u ∈ (Frame.D l y r bef aft).fnodes, AgrV B M M' u) :
    VEq B M M' ((Frame.D l y r bef aft).plug s) ((Frame.D l y r bef aft).plug s') π := by
  have hy := hag y (by simp [Frame.fnodes])
  intro k
  refine ⟨?_, fun e => ?_⟩
  · simp only [Frame.plug, rs_node, cσ, hy.2.2.2.2, hy.vlc, hy.tgc]
    rw [rs_frame B l (fun u hu => hag u (by simp [Frame.fnodes, hu])),
      rs_frame B r (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
  · have := hV k e
    simp only [List.mem_append] at this
    simp only [Frame.plug, dV_node, dVL_append, dVL_cons, List.mem_append]
    rw [dV_frame B l (fun u hu => hag u (by simp [Frame.fnodes, hu])),
      dV_frame B r (fun u hu => hag u (by simp [Frame.fnodes, hu])),
      dVL_frame B bef (fun u hu => hag u (by simp [Frame.fnodes, hu])),
      dVL_frame B aft (fun u hu => hag u (by simp [Frame.fnodes, hu]))]
    tauto

lemma cpar_of_not_headSolid {M : Mem} {fs : List Frame} (h : ¬ HeadSolid fs) : cpar B M fs = false := by
  rcases fs with _ | ⟨f, fs⟩
  · rfl
  · cases f with
    | L y c dy => exact absurd trivial h
    | R c y dy => exact absurd trivial h
    | D l y r bef aft => rfl

/-- **Replacement at the root of an auxiliary tree.** When the zipper above `s` does not start
with a solid frame, `s` may be replaced by any `s'` stored with the same parent pointer, with the
same nodes, edges and values. -/
theorem replaceTop_okE {M M' : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {s s' : VT} {fs : List Frame}
    (hG : G = gb ++ plug s fs :: ga) (hfs : ¬ HeadSolid fs) (hs' : Enc B n M' s' (hp n fs) false)
    (hperm : (nodes s').Perm (nodes s)) (hE : EEq (hp n fs) s s') (hV : VEq2 B M M' s s')
    (hout : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), Agr B M M' u)
    (hnil : NilOK B n M') :
    Inv B n M' (gb ++ plug s' fs :: ga) ∧ RepE B n M' (gb ++ plug s' fs :: ga) F := by
  have hX := rotCtx B n hI hG
  have hag : ∀ u ∈ nodesL (gb ++ ga), Agr B M M' u := fun u hu =>
    hout u (List.mem_append_right _ hu)
  rcases fs with _ | ⟨f, fs⟩
  · refine ⟨inv_replace B n hI hG hs' trivial hperm hag hnil, ?_⟩
    subst hG
    have hgb := fun k => dVL_frame B gb (fun u hu => (hag u (by simp [hu])).agrV B) k
    have hga := fun k => dVL_frame B ga (fun u hu => (hag u (by simp [hu])).agrV B) k
    refine ⟨fun u p h => hR.par u p ?_, fun u w h => hR.val u w ?_, fun u w h => hR.val2 u w ?_⟩
    · have := hE (u, p)
      simp only [edges, List.mem_append] at this
      simp only [plug_nil, dEL_append, dEL_cons, List.mem_append] at h ⊢
      tauto
    · have := hV false (u, w)
      simp only [List.mem_append] at this
      simp only [plug_nil, dVL_append, dVL_cons, List.mem_append] at h ⊢
      rw [hgb, hga] at h
      tauto
    · have := hV true (u, w)
      simp only [List.mem_append] at this
      simp only [plug_nil, dVL_append, dVL_cons, List.mem_append] at h ⊢
      rw [hgb, hga] at h
      tauto
  · obtain ⟨l, y, r, bef, aft, rfl⟩ : ∃ l y r bef aft, f = Frame.D l y r bef aft := by
      cases f with
      | L y c dy => exact absurd trivial hfs
      | R c y dy => exact absurd trivial hfs
      | D l y r bef aft => exact ⟨l, y, r, bef, aft, rfl⟩
    have hC := hX.encC
    have hnd : (cnodes (Frame.D l y r bef aft :: fs)).Nodup :=
      List.nodup_iff_count_le_one.mpr fun w => by have := hX.count w; omega
    rw [cnodes_cons] at hnd
    have hcp : cpar B M' fs = cpar B M fs :=
      cpar_congr B (fun u hu => (hout u (by simp [cnodes_cons, hu])).rv B)
    have hF : EncF B n M' (Frame.D l y r bef aft) n (cpar B M' fs) := by
      rw [hcp]
      exact EncF.frame B n hI.nil hnil hC.1 (List.nodup_append.mp hnd).1
        (fun u hu => hout u (by simp [cnodes_cons, hu])) (look_nil B n hI.nil hnil)
    have hC' : EncC B n M' (Frame.D l y r bef aft :: fs) (rt n s') n := by
      refine ⟨hF, ?_, ?_⟩
      · rw [show par B M' (Frame.D l y r bef aft).y = par B M (Frame.D l y r bef aft).y from
          ((hout y (by simp [cnodes_cons, Frame.fnodes, Frame.y])) 0 (by omega)).1]
        exact hC.2.1
      · exact EncC.frame B n hI.nil hnil hC.2.2 (List.nodup_append.mp hnd).2.1
          (fun u hu => hout u (by simp [cnodes_cons, hu]))
          (look_of_agr B n (hout y (by simp [cnodes_cons, Frame.fnodes])))
    refine ⟨inv_replace B n hI hG hs' hC' hperm hag hnil, ?_⟩
    have hsame := Same.plugD (l := l) (y := y) (r := r) (bef := bef) (aft := aft) hE hperm
    have hVD := VEq.plugD B (l := l) (y := y) (r := r) (bef := bef) (aft := aft)
      (π := cpar B M fs) hV
      (fun u hu => (hout u (List.mem_append_left _ (by
        rw [cnodes_cons]; exact List.mem_append_left _ hu))).agrV B)
    exact repE_replace B n hR (s := (Frame.D l y r bef aft).plug s) (fs := fs) hG hsame hVD
      (fun u hu => by
        rcases List.mem_append.mp hu with hu | hu
        · exact (hout u (List.mem_append_left _ (by
            rw [cnodes_cons]; exact List.mem_append_right _ hu))).agrV B
        · exact (hout u (List.mem_append_right _ hu)).agrV B)

/-! ### The switch of the preferred child -/

/-- The pointer and tag part of `switchR`. -/
def switchP (w y : ℕ) (M : Mem) : Mem :=
  ⟨upd M.nm (adr B w 2) y,
    upd (upd (upd (upd M.rm (adr B (rc B M w) 1) (tg B M (rc B M w) + tg B M w)) (adr B y 1)
      (tg B M y - tg B M w)) (adr B (rc B M w) 6) (tg2 B M (rc B M w) + tg2 B M w)) (adr B y 6)
      (tg2 B M y - tg2 B M w)⟩

/-- Make `y` (the root of a tree hanging from the root `w` of an auxiliary tree, or `n`) the right
child of `w`, hanging the old right child; the tags of both are adjusted by the tag of `w`. -/
def switchR (w y : ℕ) (M : Mem) : Mem := recomp B n w (switchP B w y M)

section
variable {B n}

lemma switchP_nm {M : Mem} {w y u j : ℕ} (hj : j < 16) :
    (switchP B w y M).nm (adr B u j) = if u = w ∧ j = 2 then y else M.nm (adr B u j) := by
  simp only [switchP, upd_adr _ _ hj (show 2 < 16 by omega)]

lemma switchP_rm {M : Mem} {w y u j : ℕ} (hj : j < 16) (hu : u ≠ y) (hu' : u ≠ rc B M w) :
    (switchP B w y M).rm (adr B u j) = M.rm (adr B u j) := by
  simp [switchP, upd_adr _ _ hj, hu, hu']

lemma switchR_agr {M : Mem} {w y u : ℕ} (h1 : u ≠ w) (h2 : u ≠ y) (h3 : u ≠ rc B M w) :
    Agr B M (switchR B n w y M) u := by
  intro j hj
  have e := recomp_agr B n (M := switchP B w y M) h1 j hj
  rw [switchR, e.1, e.2, switchP_nm hj, switchP_rm hj h2 h3]
  simp [h1]

lemma switchR_agrC {M : Mem} {w y u : ℕ} (h1 : u ≠ w) : AgrC B M (switchR B n w y M) u := by
  intro j hj
  have e := recomp_agr B n (M := switchP B w y M) h1 j hj
  refine ⟨fun _ => ?_, fun h0 h6 => ?_⟩
  · rw [switchR, e.1, switchP_nm hj]; simp [h1]
  · rw [switchR, e.2]; simp [switchP, upd_adr _ _ hj, h0, h6]

lemma switchR_par {M : Mem} {w y : ℕ} (u : ℕ) : par B (switchR B n w y M) u = par B M u := by
  simp only [par, switchR]; rw [recomp_nm B n (by omega) (by omega), switchP_nm (by omega)]
  simp

lemma switchR_lc {M : Mem} {w y : ℕ} (u : ℕ) : lc B (switchR B n w y M) u = lc B M u := by
  simp only [lc, switchR]; rw [recomp_nm B n (by omega) (by omega), switchP_nm (by omega)]
  simp

lemma switchR_rc {M : Mem} {w y : ℕ} : rc B (switchR B n w y M) w = y := by
  simp only [rc, switchR]; rw [recomp_nm B n (by omega) (by omega), switchP_nm (by omega)]
  simp

lemma switchR_fpar {M : Mem} {w y : ℕ} (u : ℕ) : fpar B (switchR B n w y M) u = fpar B M u := by
  simp only [fpar, switchR]; rw [recomp_nm B n (by omega) (by omega), switchP_nm (by omega)]
  simp

lemma switchR_rv {M : Mem} {w y : ℕ} (u : ℕ) : rv B (switchR B n w y M) u = rv B M u := by
  simp only [rv, rvw, switchR]; rw [recomp_nm B n (by omega) (by omega), switchP_nm (by omega)]
  simp

lemma switchR_vl {M : Mem} {w y : ℕ} (u : ℕ) :
    vl B (switchR B n w y M) u = vl B M u ∧ vl2 B (switchR B n w y M) u = vl2 B M u := by
  simp only [vl, vl2, switchR]; rw [recomp_rm B n (by omega) (by omega),
    recomp_rm B n (by omega) (by omega)]
  simp [switchP, upd_adr]

lemma switchR_vlc {M : Mem} {w y : ℕ} (u : ℕ) (k : Bool) :
    vlc B (switchR B n w y M) k u = vlc B M k u := by
  cases k <;> simp [vlc, (switchR_vl (B := B) (n := n) (M := M) (w := w) (y := y) u).1,
    (switchR_vl (B := B) (n := n) (M := M) (w := w) (y := y) u).2]

lemma switchR_tgc {M : Mem} {w y : ℕ} (u : ℕ) (k : Bool) (hw : w ≠ y) (hw' : w ≠ rc B M w) :
    tgc B (switchR B n w y M) k u =
      if u = y then tgc B M k y - tgc B M k w else if u = rc B M w then tgc B M k u + tgc B M k w
      else tgc B M k u := by
  cases k
  · simp only [tgc, Bool.false_eq_true, ↓reduceIte, tg, switchR]
    rw [recomp_rm B n (by omega) (by omega)]
    simp only [switchP, upd_adr _ _ (show 1 < 16 by omega) (show 1 < 16 by omega),
      upd_adr _ _ (show 1 < 16 by omega) (show 6 < 16 by omega), and_true, and_false,
      ↓reduceIte]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [tg]
  · simp only [tgc, ↓reduceIte, tg2, switchR]
    rw [recomp_rm B n (by omega) (by omega)]
    simp only [switchP, upd_adr _ _ (show 6 < 16 by omega) (show 1 < 16 by omega),
      upd_adr _ _ (show 6 < 16 by omega) (show 6 < 16 by omega), and_true, and_false,
      ↓reduceIte]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all [tg, tg2]

lemma switchR_frame {M : Mem} {w y : ℕ} (hw : w ≤ n) (hy : y ≤ n) (hr : rc B M w ≤ n) :
    MemFrame B n M (switchR B n w y M) := by
  refine MemFrame.trans B n ?_ (recomp_frame B n hw)
  intro a ha
  simp only [switchP]
  refine ⟨memFrame_upd _ _ hw (by omega) ha, ?_⟩
  rw [memFrame_upd _ _ hy (by omega) ha, memFrame_upd _ _ hr (by omega) ha,
    memFrame_upd _ _ hy (by omega) ha, memFrame_upd _ _ hr (by omega) ha]

end

lemma shift_zero (L : List (ℕ × ℝ)) : shift 0 L = L := by simp [shift]

lemma eeq_switch (p w : ℕ) (l r Y : VT) (bef Ys aft : List VT)
    (hYs : Ys = [Y] ∨ (Ys = [] ∧ Y = VT.leaf)) :
    EEq p (node l w r (bef ++ Ys ++ aft)) (node l w Y (bef ++ r :: aft)) := by
  intro e
  rcases hYs with rfl | ⟨rfl, rfl⟩ <;>
  simp only [edges, seq_node, chain_append, chain_cons, dE_node, dEL_append, dEL_cons,
    dEL_nil, List.mem_append, List.mem_cons, seq_leaf, chain_nil, dE_leaf, List.append_nil,
    List.not_mem_nil] <;> tauto

lemma mem_switch (e : ℕ × ℝ) (t v : ℝ) (w : ℕ) (A R Yl DL DR DY DB DA : List (ℕ × ℝ)) :
    e ∈ shift t (A ++ (w, v) :: shift (-t) Yl) ++ (DL ++ DY ++ (DB ++ (shift t R ++ DR ++ DA))) ↔
    e ∈ shift t (A ++ (w, v) :: R) ++ (DL ++ DR ++ (DB ++ (Yl ++ DY) ++ DA)) := by
  simp only [shift_append, shift_cons, shift_shift, neg_add_cancel, shift_zero, List.mem_append,
    List.mem_cons]
  tauto

/-- **The switch of the preferred child.** At the root `w` of an auxiliary tree, with `Ys` the
tree `Y` hanging from `w` (or nothing, `Y` a leaf), `switchR w (rt Y)` makes `Y` the right child
and hangs the old right child `r`. -/
theorem switchR_okE {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {l r Y : VT} {w : ℕ} {bef Ys aft : List VT}
    {fs : List Frame} (hYs : Ys = [Y] ∨ (Ys = [] ∧ Y = VT.leaf))
    (hG : G = gb ++ plug (node l w r (bef ++ Ys ++ aft)) fs :: ga) (hfs : ¬ HeadSolid fs)
    (hvw : rv B M w = false) :
    Inv B n (switchR B n w (rt n Y) M) (gb ++ plug (node l w Y (bef ++ r :: aft)) fs :: ga) ∧
    RepE B n (switchR B n w (rt n Y) M) (gb ++ plug (node l w Y (bef ++ r :: aft)) fs :: ga) F ∧
    MemFrame B n M (switchR B n w (rt n Y) M) := by
  have hX := rotCtx B n hI hG
  have hout := hX.out
  obtain ⟨hsE, hCE, hcount, hlts, hltc, hlto⟩ := hX
  -- the nodes
  have K : ∀ w', (nodes l).count w' + [w].count w' + (nodes r).count w' + (nodesL bef).count w' +
      (nodes Y).count w' + (nodesL aft).count w' ≤ 1 := fun w' => by
    have := hcount w'
    rcases hYs with rfl | ⟨rfl, rfl⟩ <;>
    simp only [nodes_node, nodesL_append, nodesL_cons, nodesL_nil, List.count_append,
      List.count_cons, List.count_nil, nodes_leaf] at this ⊢ <;> omega
  rw [cpar_of_not_headSolid B hfs, enc_node_iff_clean B n hvw] at hsE
  obtain ⟨hpw, hlw, hrw, hAw, hlE, hrE, hdE⟩ := hsE
  have hws : w ∈ nodes (node l w r (bef ++ Ys ++ aft)) := by simp
  have hwn := hlts w hws
  have hdE' : (∀ d ∈ bef, Enc B n M d w false) ∧ (∀ d ∈ aft, Enc B n M d w false) ∧
      Enc B n M Y w false := by
    refine ⟨fun d hd => hdE d (by simp [hd]), fun d hd => hdE d (by simp [hd]), ?_⟩
    rcases hYs with rfl | ⟨rfl, rfl⟩
    · exact hdE Y (by simp)
    · exact .leaf _ _
  obtain ⟨hbefE, haftE, hYE⟩ := hdE'
  have nw : ∀ (L : List ℕ), (∀ w', L.count w' + [w].count w' ≤ 1) → ∀ u ∈ L, u ≠ w :=
    fun L h u hu => ne_of_count h hu (by simp)
  have rtne : ∀ (c : VT) (L : List ℕ), (∀ w', (nodes c).count w' + L.count w' ≤ 1) →
      ∀ u ∈ L, u < n → rt n c ≠ u := by
    intro c L h u hu hun e
    rcases rt_or_nil n c with ⟨-, h'⟩ | h'
    · rw [h'] at e; omega
    · exact ne_of_count h h' hu e
  have hYw : rt n Y ≠ w := rtne Y [w] (fun w' => by have := K w'; omega) w (by simp) hwn
  have hrw' : rt n r ≠ w := rtne r [w] (fun w' => by have := K w'; omega) w (by simp) hwn
  -- outside nodes
  have nYr : ∀ u, u ∈ nodes l ∨ u ∈ nodesL bef ∨ u ∈ nodesL aft →
      u ≠ w ∧ u ≠ rt n Y ∧ u ≠ rt n r := by
    intro u hu
    have hun : u < n := hlts u (by rcases hu with h | h | h <;> simp [h])
    refine ⟨?_, ?_, ?_⟩
    · rcases hu with h | h | h
      · exact nw _ (fun w' => by have := K w'; omega) u h
      · exact nw _ (fun w' => by have := K w'; omega) u h
      · exact nw _ (fun w' => by have := K w'; omega) u h
    · rcases hu with h | h | h
      · exact (rtne Y _ (fun w' => by have := K w'; omega) u h hun).symm
      · exact (rtne Y _ (fun w' => by have := K w'; omega) u h hun).symm
      · exact (rtne Y _ (fun w' => by have := K w'; omega) u h hun).symm
    · rcases hu with h | h | h
      · exact (rtne r _ (fun w' => by have := K w'; omega) u h hun).symm
      · exact (rtne r _ (fun w' => by have := K w'; omega) u h hun).symm
      · exact (rtne r _ (fun w' => by have := K w'; omega) u h hun).symm
  have hlt_rt : ∀ c : VT, (∀ u ∈ nodes c, u < n) → rt n c ≤ n := by
    intro c hc
    rcases rt_or_nil n c with ⟨-, h⟩ | h
    · omega
    · exact (hc _ h).le
  have inS : ∀ u, u ∈ nodes l ∨ u ∈ nodes r ∨ u ∈ nodes Y ∨ u ∈ nodesL bef ∨ u ∈ nodesL aft →
      u ∈ nodes (node l w r (bef ++ Ys ++ aft)) := by
    intro u hu
    rcases hYs with rfl | ⟨rfl, rfl⟩ <;> rcases hu with h | h | h | h | h <;> simp_all
  have hYr1 : Y ≠ VT.leaf → rt n r ≠ rt n Y := fun hY =>
    rtne r (nodes Y) (fun w' => by have := K w'; omega) _ (rt_mem_nodes hY n)
      (hlts _ (inS _ (Or.inr (Or.inr (Or.inl (rt_mem_nodes hY n))))))
  have hYr2 : r ≠ VT.leaf → rt n Y ≠ rt n r := fun hr =>
    rtne Y (nodes r) (fun w' => by have := K w'; omega) _ (rt_mem_nodes hr n)
      (hlts _ (inS _ (Or.inr (Or.inl (rt_mem_nodes hr n)))))
  -- the memory after the switch
  have tgs := fun u k => switchR_tgc (B := B) (n := n) (M := M) (w := w) (y := rt n Y) u k
    hYw.symm (by rw [hrw]; exact hrw'.symm)
  have hAw' : AggOK B n (switchR B n w (rt n Y) M) w := by
    refine aggOK_recomp B n ?_ ?_ ?_
    · rw [show lc B (switchP B w (rt n Y) M) w = lc B M w from by
        simp only [lc]; rw [switchP_nm (by omega)]; simp, hlw]
      exact rtne l [w] (fun w' => by have := K w'; omega) w (by simp) hwn
    · rw [show rc B (switchP B w (rt n Y) M) w = rt n Y from by
        simp only [rc]; rw [switchP_nm (by omega)]; simp]
      exact hYw
    · simp only [rv, rvw]; rw [switchP_nm (by omega)]; simp only [rv, rvw] at hvw; simpa using hvw
  have agrO : ∀ u, u ∈ nodes l ∨ u ∈ nodesL bef ∨ u ∈ nodesL aft →
      Agr B M (switchR B n w (rt n Y) M) u := fun u hu =>
    switchR_agr (nYr u hu).1 (nYr u hu).2.1 (by rw [hrw]; exact (nYr u hu).2.2)
  have hnil : NilOK B n (switchR B n w (rt n Y) M) := by
    have h := switchR_agrC (B := B) (n := n) (M := M) (y := rt n Y) (show n ≠ w by omega)
    have hN := hI.nil
    exact ⟨by rw [lc, (h 1 (by omega)).1 (by omega)]; exact hN.lc,
      by rw [rc, (h 2 (by omega)).1 (by omega)]; exact hN.rc,
      by rw [cnt, (h 4 (by omega)).2 (by omega) (by omega)]; exact hN.cnt,
      by rw [sm, (h 3 (by omega)).2 (by omega) (by omega)]; exact hN.sm,
      by rw [sm2, (h 8 (by omega)).2 (by omega) (by omega)]; exact hN.sm2⟩
  have ndl : (nodes l).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by have := K w'; omega
  have ndr : (nodes r).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by have := K w'; omega
  have ndY : (nodes Y).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by have := K w'; omega
  have ndb : (nodesL bef).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w' => by have := K w'; omega
  have nda : (nodesL aft).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w' => by have := K w'; omega
  -- the subtrees whose roots change their tag
  have agrR : ∀ u ∈ nodes r, u ≠ rt n r → Agr B M (switchR B n w (rt n Y) M) u := by
    intro u hu hne
    have hun : u < n := hlts u (inS u (Or.inr (Or.inl hu)))
    exact switchR_agr (nw _ (fun w' => by have := K w'; omega) u hu)
      (rtne Y (nodes r) (fun w' => by have := K w'; omega) u hu hun).symm (by rw [hrw]; exact hne)
  have agrY : ∀ u ∈ nodes Y, u ≠ rt n Y → Agr B M (switchR B n w (rt n Y) M) u := by
    intro u hu hne
    have hun : u < n := hlts u (inS u (Or.inr (Or.inr (Or.inl hu))))
    exact switchR_agr (nw _ (fun w' => by have := K w'; omega) u hu) hne
      (by rw [hrw]; exact (rtne r (nodes Y) (fun w' => by have := K w'; omega) u hu hun).symm)
  -- the encodings
  have hlE' : Enc B n (switchR B n w (rt n Y) M) l w false :=
    enc_frame_all B n hI.nil hnil hlE ndl (fun u hu => agrO u (Or.inl hu))
  have hrE' : Enc B n (switchR B n w (rt n Y) M) r w false :=
    Enc.frame B n hI.nil hnil hrE ndr w agrR (fun _ => switchR_agrC hrw')
      (fun hne => by rw [switchR_par]; exact hrE.par_rt B n hne)
  have hYE' : Enc B n (switchR B n w (rt n Y) M) Y w false :=
    Enc.frame B n hI.nil hnil hYE ndY w agrY (fun _ => switchR_agrC hYw)
      (fun hne => by rw [switchR_par]; exact hYE.par_rt B n hne)
  have hbefE' := enc_frame_list B n hI.nil hnil hbefE ndb (fun u hu => agrO u (Or.inr (Or.inl hu)))
  have haftE' := enc_frame_list B n hI.nil hnil haftE nda (fun u hu => agrO u (Or.inr (Or.inr hu)))
  have hs' : Enc B n (switchR B n w (rt n Y) M) (node l w Y (bef ++ r :: aft)) (hp n fs)
      false := by
    rw [enc_node_iff_clean B n (by rw [switchR_rv]; exact hvw)]
    refine ⟨by rw [switchR_par]; exact hpw, by rw [switchR_lc, hlw], switchR_rc, hAw', hlE', hYE',
      fun d hd => ?_⟩
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact hbefE' d hd
    · exact hrE'
    · exact haftE' d hd
  have hperm : (nodes (node l w Y (bef ++ r :: aft))).Perm (nodes (node l w r (bef ++ Ys ++ aft))) := by
    rw [List.perm_iff_count]; intro a
    rcases hYs with rfl | ⟨rfl, rfl⟩ <;>
    simp only [nodes_node, nodesL_append, nodesL_cons, nodesL_nil, List.count_append,
      List.count_cons, List.count_nil, nodes_leaf] <;> omega
  have hE := eeq_switch (hp n fs) w l r Y bef Ys aft hYs
  have hrsl := rs_frame B l (fun u hu => (agrO u (Or.inl hu)).agrV B)
  have hdVl := dV_frame B l (fun u hu => (agrO u (Or.inl hu)).agrV B)
  have hdVb := dVL_frame B bef (fun u hu => (agrO u (Or.inr (Or.inl hu))).agrV B)
  have hdVa := dVL_frame B aft (fun u hu => (agrO u (Or.inr (Or.inr hu))).agrV B)
  have hdVr := dV_frame_root B n (fun u hu hne => (agrR u hu hne).agrV B) ndr
  have hdVY := dV_frame_root B n (fun u hu hne => (agrY u hu hne).agrV B) ndY
  have hrvY : rv B (switchR B n w (rt n Y) M) (rt n Y) = rv B M (rt n Y) := switchR_rv _
  have hrsY : ∀ k, rs B (switchR B n w (rt n Y) M) Y false k =
      shift (-tgc B M k w) (rs B M Y false k) := by
    intro k
    refine rs_retag B n (fun u hu hne => (agrY u hu hne).agrV B) ndY (fun j => switchR_vlc _ j)
      hrvY ?_
    rw [Bool.xor_false, tgs]; simp; ring
  have hrsr : ∀ k, rs B (switchR B n w (rt n Y) M) r false k =
      shift (tgc B M k w) (rs B M r false k) := by
    intro k
    by_cases hr0 : r = VT.leaf
    · subst hr0; rfl
    · refine rs_retag B n (fun u hu hne => (agrR u hu hne).agrV B) ndr (fun j => switchR_vlc _ j)
        (switchR_rv _) ?_
      rw [Bool.xor_false, tgs, ite_of_neg (hYr2 hr0).symm, hrw]; simp
  have htw : ∀ k, tgc B (switchR B n w (rt n Y) M) k w = tgc B M k w := by
    intro k
    rw [tgs, ite_of_neg hYw.symm, hrw, ite_of_neg hrw'.symm]
  have hV : VEq2 B M (switchR B n w (rt n Y) M) (node l w r (bef ++ Ys ++ aft))
      (node l w Y (bef ++ r :: aft)) := by
    intro k e
    have hd : dVL B M (bef ++ Ys ++ aft) k =
        dVL B M bef k ++ (rs B M Y false k ++ dV B M Y k) ++ dVL B M aft k := by
      rcases hYs with rfl | ⟨rfl, rfl⟩ <;> simp
    have ew : cσ B (switchR B n w (rt n Y) M) false w = false := by
      simp [cσ, switchR_rv, hvw]
    have ew' : cσ B M false w = false := by simp [cσ, hvw]
    rw [rs_node, rs_node, dV_node, dV_node, dVL_append, dVL_cons, ew, ew', Bool.xor_false, hrsl,
      hdVl, hdVb, hdVa, hdVr, hdVY, hrsY, hrsr, htw, switchR_vlc, hd]
    exact mem_switch _ _ _ _ _ _ _ _ _ _ _ _
  have hout' : ∀ u ∈ cnodes fs ++ nodesL (gb ++ ga), Agr B M (switchR B n w (rt n Y) M) u := by
    intro u hu
    have hun : u < n := by
      rcases List.mem_append.mp hu with h | h
      · exact hltc u h
      · exact hlto u h
    refine switchR_agr (hout u hu w hws) ?_ ?_
    · rcases rt_or_nil n Y with ⟨-, h⟩ | h
      · rw [h]; omega
      · exact hout u hu _ (inS _ (Or.inr (Or.inr (Or.inl h))))
    · rw [hrw]
      rcases rt_or_nil n r with ⟨-, h⟩ | h
      · rw [h]; omega
      · exact hout u hu _ (inS _ (Or.inr (Or.inl h)))
  obtain ⟨hI', hR'⟩ := replaceTop_okE B n hI hR hG hfs hs' hperm hE hV hout' hnil
  refine ⟨hI', hR', switchR_frame hwn.le ?_ ?_⟩
  · rcases rt_or_nil n Y with ⟨-, h⟩ | h
    · omega
    · exact (hlts _ (inS _ (Or.inr (Or.inr (Or.inl h))))).le
  · rw [hrw]
    rcases rt_or_nil n r with ⟨-, h⟩ | h
    · omega
    · exact (hlts _ (inS _ (Or.inr (Or.inl h)))).le

theorem switchR_ok {M : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : Rep B n M G F) {gb ga : List VT} {l r Y : VT} {w : ℕ} {bef Ys aft : List VT}
    {fs : List Frame} (hYs : Ys = [Y] ∨ (Ys = [] ∧ Y = VT.leaf))
    (hG : G = gb ++ plug (node l w r (bef ++ Ys ++ aft)) fs :: ga) (hfs : ¬ HeadSolid fs)
    (hvw : rv B M w = false) :
    Inv B n (switchR B n w (rt n Y) M) (gb ++ plug (node l w Y (bef ++ r :: aft)) fs :: ga) ∧
    Rep B n (switchR B n w (rt n Y) M) (gb ++ plug (node l w Y (bef ++ r :: aft)) fs :: ga) F ∧
    MemFrame B n M (switchR B n w (rt n Y) M) := by
  obtain ⟨h1, h2, h3⟩ := switchR_okE B n hI hR.toRepE hYs hG hfs hvw
  exact ⟨h1, ⟨h2, fun u hu => by rw [switchR_fpar]; exact hR.fpar u hu⟩, h3⟩

end DynTree

end PlanarFlow
