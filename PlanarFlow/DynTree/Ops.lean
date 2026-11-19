module

public import PlanarFlow.DynTree.Access

/-!
# Dynamic trees: the operations after an access, on the virtual forest

After `access v` the virtual forest is (up to order) `T :: G` with `T = node l v leaf dv`; its
auxiliary tree represents the root path of `v`.

* `query_top`: `findRoot F n v = lm v`, `pathMin F n v = (minA v, am v)`,
  `pathSum F n v = sumA v`.
* `addPath_ok`: adding `δ` to the tag of `v` adds `δ` to the values of the root path.
* `cut_ok`: detaching the left subtree of `v` cuts the edge from `v` to its parent.
* `link_ok`: hanging the tree of a root `v` (a single-node auxiliary tree) from the root `w` of
  another virtual tree links `v` below `w`.
* `top_root`: the only node of a top-level virtual tree whose parent is `n` is the first node of
  its auxiliary tree.
The invariant, the representation and the potential do not depend on the order of the virtual
trees (`Inv.perm`, `Rep.perm`).
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-! ### Order of the virtual trees -/

lemma nodesL_perm {G G' : List VT} (h : G.Perm G') : (nodesL G).Perm (nodesL G') := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons x _ ih => simp only [nodesL_cons]; exact ih.append_left _
  | swap x y l =>
    simp only [nodesL_cons, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma mem_dEL_perm {G G' : List VT} (h : G.Perm G') (p : ℕ) (e : ℕ × ℕ) :
    e ∈ dEL p G ↔ e ∈ dEL p G' := by
  induction h with
  | nil => exact Iff.rfl
  | cons x _ ih => simp only [dEL_cons, List.mem_append]; rw [ih]
  | swap x y l => simp only [dEL_cons, List.mem_append]; tauto
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma mem_dVL_perm {G G' : List VT} (h : G.Perm G') (M : Mem) (k : Bool) (e : ℕ × ℝ) :
    e ∈ dVL B M G k ↔ e ∈ dVL B M G' k := by
  induction h with
  | nil => exact Iff.rfl
  | cons x _ ih => simp only [dVL_cons, List.mem_append]; rw [ih]
  | swap x y l => simp only [dVL_cons, List.mem_append]; tauto
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma potL_perm {G G' : List VT} (h : G.Perm G') : potL G = potL G' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma Inv.perm {M : Mem} {G G' : List VT} (hI : Inv B n M G) (h : G.Perm G') : Inv B n M G' :=
  ⟨fun T hT => hI.enc T (h.mem_iff.mpr hT), (nodesL_perm h).nodup_iff.mp hI.nodup,
    fun u => ((nodesL_perm h).mem_iff.symm).trans (hI.cover u), hI.nil⟩

lemma RepE.perm {M : Mem} {G G' : List VT} {F : Forest} (hR : RepE B n M G F)
    (h : G.Perm G') : RepE B n M G' F :=
  ⟨fun u p hu => hR.par u p ((mem_dEL_perm h n _).mpr hu),
    fun u w hu => hR.val u w ((mem_dVL_perm B h M false _).mpr hu),
    fun u w hu => hR.val2 u w ((mem_dVL_perm B h M true _).mpr hu)⟩

lemma Rep.perm {M : Mem} {G G' : List VT} {F : Forest} (hR : Rep B n M G F) (h : G.Perm G') :
    Rep B n M G' F :=
  ⟨hR.toRepE.perm B n h, hR.fpar⟩

/-! ### Values -/

/-- The values of channel `k` of the forest. -/
def Forest.valc (F : Forest) (k : Bool) : ℕ → ℝ := if k then F.val2 else F.val

/-- The values of a stored top-level auxiliary tree are the values of the forest. -/
lemma rs_eq_map {M : Mem} {G : List VT} {F : Forest} (hR : RepE B n M G F) {T : VT}
    (hT : T ∈ G) (k : Bool) : rs B M T false k = (seq T).map fun u => (u, F.valc k u) := by
  rw [← rs_fst M T false k, List.map_map]
  conv_lhs => rw [← List.map_id (rs B M T false k)]
  refine List.map_congr_left fun q hq => ?_
  have : q ∈ dVL B M G k := by
    obtain ⟨gb, ga, rfl⟩ := List.append_of_mem hT
    simp [hq]
  cases k
  · simp [Forest.valc, hR.val q.1 q.2 this]
  · simp [Forest.valc, hR.val2 q.1 q.2 this]

/-- **The queries.** After the access of `v`, the aggregates at `v` answer the queries. -/
theorem query_top {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv) :
    findRoot F n v = lm B M v ∧ pathMin F n v = (minA B M v, am B M v) ∧
      pathSum F n v = sumA B M v ∧ pathMin2 F n v = (minA2 B M v, am2 B M v) ∧
      pathSum2 F n v = sumA2 B M v := by
  have hseq : seq T = seq l ++ [v] := by rw [hT]; simp
  have hrp := rootPath_top B n hI hR (gb := []) (ga := G) rfl hseq
  have hE : Enc B n M T n false := hI.enc T (by simp)
  have hlt : ∀ u ∈ nodes T, u < n := fun u hu => (hI.cover u).mp (by simp [hu])
  have hrt : rt n T = v := by rw [hT]; rfl
  have hvn : v < n := hlt v (by rw [hT]; simp)
  have hA := (hE.agg B n hI.nil hlt).2 (by rw [hrt]; exact hvn)
  rw [hrt, Ag.mirIf_false] at hA
  have hrs0 := rs_eq_map B n hR (T := T) (by simp) false
  have hrs1 := rs_eq_map B n hR (T := T) (by simp) true
  simp only [Forest.valc, Bool.false_eq_true, ↓reduceIte] at hrs0 hrs1
  have hlm := congrArg Ag.lm hA
  have hm1 := congrArg Ag.m1 hA
  have ha1 := congrArg Ag.a1 hA
  have hs1 := congrArg Ag.s1 hA
  have hm2 := congrArg Ag.m2 hA
  have ha2 := congrArg Ag.a2 hA
  have hs2 := congrArg Ag.s2 hA
  simp only [rd, own, Ag.addTags, tAg] at hlm hm1 ha1 hs1 hm2 ha2 hs2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [findRoot, hrp, hlm, hseq]
    rcases seq l with _ | ⟨a, L⟩
    · simp
    · simp [List.getLastD, List.getLast?_append]
  · rw [pathMin, downVals, hrp, ← hseq, List.reverse_reverse, ← hrs0, minA, hm1, ha1]
  · rw [pathSum, hrp, sumA, hs1, hrs0, List.map_map, List.map_reverse, List.sum_reverse, ← hseq]
    rfl
  · rw [pathMin2, downVals2, hrp, ← hseq, List.reverse_reverse, ← hrs1, minA2, hm2, ha2]
  · rw [pathSum2, hrp, sumA2, hs2, hrs1, List.map_map, List.map_reverse, List.sum_reverse, ← hseq]
    rfl

/-! ### Nodes off the auxiliary tree -/

/-- The nodes of the trees hanging below an auxiliary tree. -/
def hN : VT → List ℕ
  | leaf => []
  | node l _ r ds => hN l ++ hN r ++ nodesL ds

lemma nodes_perm_hN : ∀ t : VT, (nodes t).Perm (seq t ++ hN t)
  | leaf => List.Perm.refl _
  | node l x r ds => by
    have hl := nodes_perm_hN l
    have hr := nodes_perm_hN r
    rw [List.perm_iff_count] at hl hr ⊢
    intro a
    have := hl a; have := hr a
    simp only [nodes_node, seq_node, hN, List.count_append, List.count_cons] at *
    omega

lemma rs_fst_mem {M : Mem} {t : VT} {π k : Bool} {u : ℕ} {w : ℝ} (h : (u, w) ∈ rs B M t π k) :
    u ∈ seq t := by
  rw [← rs_fst M t π k]; exact List.mem_map.mpr ⟨_, h, rfl⟩

mutual
lemma dV_fst {M : Mem} {k : Bool} : ∀ (t : VT) {u : ℕ} {w : ℝ}, (u, w) ∈ dV B M t k → u ∈ hN t
  | leaf, _, _, h => by simp at h
  | node l x r ds, u, w, h => by
    simp only [dV_node, List.mem_append] at h
    simp only [hN, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (dV_fst l h))
    · exact Or.inl (Or.inr (dV_fst r h))
    · exact Or.inr (dVL_fst ds h)
lemma dVL_fst {M : Mem} {k : Bool} : ∀ (ds : List VT) {u : ℕ} {w : ℝ}, (u, w) ∈ dVL B M ds k →
    u ∈ nodesL ds
  | [], _, _, h => by simp at h
  | d :: ds, u, w, h => by
    simp only [dVL_cons, List.mem_append] at h
    simp only [nodesL_cons, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl ((nodes_perm_hN d).mem_iff.mpr (List.mem_append_left _ (rs_fst_mem B h)))
    · exact Or.inl ((nodes_perm_hN d).mem_iff.mpr (List.mem_append_right _ (dV_fst d h)))
    · exact Or.inr (dVL_fst ds h)
end

/-! ### Adding to the root path -/

/-- The tag field of channel `k`. -/
def tgf (k : Bool) : ℕ := if k then 6 else 1

/-- Add `δ` to the tag of channel `k` of `v`. -/
def addTagC (k : Bool) (v : ℕ) (δ : ℝ) (M : Mem) : Mem :=
  ⟨M.nm, upd M.rm (adr B v (tgf k)) (tgc B M k v + δ)⟩

/-- Add `δ` to the first tag of `v`. -/
abbrev addTag (v : ℕ) (δ : ℝ) (M : Mem) : Mem := addTagC B false v δ M

/-- Add `δ` to the second tag of `v`. -/
abbrev addTag2 (v : ℕ) (δ : ℝ) (M : Mem) : Mem := addTagC B true v δ M

lemma addTagC_agr {M : Mem} {k : Bool} {v u : ℕ} {δ : ℝ} (h : u ≠ v) :
    Agr B M (addTagC B k v δ M) u := by
  intro j hj
  simp [addTagC, upd_adr _ _ hj (show tgf k < 16 by cases k <;> simp [tgf]), h]

/-- The forest after adding `δ` to the values of channel `k` on the root path of `v`. -/
def addPathC (F : Forest) (n v : ℕ) (δ : ℝ) (k : Bool) : Forest :=
  if k then addPath2 F n v δ else addPath F n v δ

/-- **Adding to the root path**: after the access of `v`, adding `δ` to the tag of channel `k`
of `v`. -/
theorem addPath_okE {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv)
    (k : Bool) (δ : ℝ) :
    Inv B n (addTagC B k v δ M) (T :: G) ∧ RepE B n (addTagC B k v δ M) (T :: G) (addPathC F n v δ k) ∧
      MemFrame B n M (addTagC B k v δ M) ∧ (∀ u, fpar B (addTagC B k v δ M) u = fpar B M u) := by
  have hvn : v < n := (hI.cover v).mp (by rw [hT]; simp)
  have hnd := hI.nodup
  simp only [nodesL_cons, List.nodup_append] at hnd
  have hvG : ∀ u ∈ nodesL G, u ≠ v := fun u hu e => hnd.2.2 v (by rw [hT]; simp) u hu e.symm
  have hk : tgf k < 16 := by cases k <;> simp [tgf]
  have hnil : NilOK B n (addTagC B k v δ M) := by
    have h := addTagC_agr B (M := M) (k := k) (v := v) (δ := δ) (u := n) (by omega)
    exact ⟨by rw [lc, (h 1 (by omega)).1]; exact hI.nil.lc,
      by rw [rc, (h 2 (by omega)).1]; exact hI.nil.rc,
      by rw [cnt, (h 4 (by omega)).2]; exact hI.nil.cnt, by rw [sm, (h 3 (by omega)).2]; exact hI.nil.sm,
      by rw [sm2, (h 8 (by omega)).2]; exact hI.nil.sm2⟩
  have hTn : ∀ u ∈ nodes T, u ≠ rt n T → Agr B M (addTagC B k v δ M) u := fun u _ hne =>
    addTagC_agr B (by rw [hT] at hne; exact hne)
  have hroot : AgrC B M (addTagC B k v δ M) v := fun j hj =>
    ⟨fun _ => rfl, fun h1 h6 => by
      simp [addTagC, upd_adr _ _ hj hk]; intro e; cases k <;> simp [tgf] at e <;> omega⟩
  have hEnc : Enc B n (addTagC B k v δ M) T n false := by
    refine Enc.frame B n hI.nil hnil (hI.enc T (by simp)) hnd.1 n hTn
      (fun _ => by rw [hT]; exact hroot) (fun _ => ?_)
    rw [hT]
    have := (hI.enc T (by simp)).par_rt B n (by rw [hT]; simp)
    rw [hT] at this; exact this
  have hseq : seq T = seq l ++ [v] := by rw [hT]; simp
  have hrp := rootPath_top B n hI hR (gb := []) (ga := G) rfl hseq
  rw [← hseq] at hrp
  have hvl : ∀ j, vlc B (addTagC B k v δ M) j v = vlc B M j v := by
    intro j; cases j <;> cases k <;> simp [vlc, vl, vl2, addTagC, upd_adr, tgf]
  have hrv : rv B (addTagC B k v δ M) v = rv B M v := hroot.rvEq B
  have hrs : ∀ j, rs B (addTagC B k v δ M) T false j =
      if j = k then shift δ (rs B M T false j) else rs B M T false j := by
    intro j
    split_ifs with hj
    · subst hj
      refine rs_retag B n (fun u hu hne => (hTn u hu hne).agrV B) hnd.1
        (by rw [hT]; exact hvl) (by rw [hT]; exact hrv) ?_
      rw [hT]; cases j <;> simp [tgc, tg, tg2, addTagC, tgf]
    · have e := rs_retag B n (π := false) (k := j) (d := 0) (fun u hu hne => (hTn u hu hne).agrV B)
        hnd.1 (by rw [hT]; exact hvl) (by rw [hT]; exact hrv) ?_
      · rw [e]; simp [shift]
      · rw [hT]; cases j <;> cases k <;> simp_all [tgc, tg, tg2, addTagC, tgf, upd_adr]
  have hdV : ∀ j, dV B (addTagC B k v δ M) T j = dV B M T j :=
    dV_frame_root B n (fun u hu hne => (hTn u hu hne).agrV B) hnd.1
  have hdVL : ∀ j, dVL B (addTagC B k v δ M) G j = dVL B M G j :=
    dVL_frame B G (fun u hu => (addTagC_agr B (hvG u hu)).agrV B)
  have hval : ∀ j, ∀ u w, (u, w) ∈ dVL B (addTagC B k v δ M) (T :: G) j →
      (addPathC F n v δ k).valc j u = w := by
    intro j u w h
    simp only [dVL_cons, List.mem_append, hrs, hdV, hdVL] at h
    have hnmem : ∀ u, u ∉ seq T → (addPathC F n v δ k).valc j u = F.valc j u := by
      intro u hu
      cases k <;> cases j <;> simp [addPathC, addPath, addPath2, Forest.valc, hrp, hu]
    have hold : ∀ u w, (u, w) ∈ dVL B M (T :: G) j → F.valc j u = w := by
      intro u w h; cases j
      · exact hR.val u w h
      · exact hR.val2 u w h
    rcases h with (h | h) | h
    · split_ifs at h with hj
      · subst hj
        obtain ⟨⟨u', w0⟩, hq, he⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hu : u' ∈ seq T := rs_fst_mem B hq
        rw [← hold u' w0 (by simp [hq])]
        cases j <;> simp [addPathC, addPath, addPath2, Forest.valc, hrp, hu]
      · have hu : u ∈ seq T := rs_fst_mem B h
        rw [← hold u w (by simp [h])]
        cases k <;> cases j <;> simp_all [addPathC, addPath, addPath2, Forest.valc]
    · have hu : u ∈ hN T := dV_fst B T h
      have hnot : u ∉ seq T := by
        intro hs
        have := (nodes_perm_hN T).nodup_iff.mp hnd.1
        exact List.disjoint_of_nodup_append this hs hu
      rw [hnmem u hnot]; exact hold u w (by simp [h])
    · have hu : u ∈ nodesL G := dVL_fst B G h
      have hnot : u ∉ seq T := fun hs => hnd.2.2 u ((seq_sublist_nodes T).subset hs) u hu rfl
      rw [hnmem u hnot]; exact hold u w (by simp [h])
  refine ⟨⟨fun T' hT' => ?_, hI.nodup, hI.cover, hnil⟩, ⟨fun u p h => ?_,
    fun u w h => by simpa [Forest.valc] using hval false u w h,
    fun u w h => by simpa [Forest.valc] using hval true u w h⟩, ?_, fun u => rfl⟩
  · rcases List.mem_cons.mp hT' with rfl | hT'
    · exact hEnc
    · exact enc_frame_all B n hI.nil hnil (hI.enc T' (by simp [hT']))
        (nodup_of_mem_nodesL hnd.2.1 hT')
        (fun u hu => addTagC_agr B (hvG u (mem_nodesL_of hT' hu)))
  · cases k <;> exact hR.par u p h
  · intro a ha
    refine ⟨rfl, ?_⟩
    simp only [addTagC]
    rw [memFrame_upd _ _ hvn.le hk ha]

theorem addPath_ok {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : Rep B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv)
    (δ : ℝ) :
    Inv B n (addTag B v δ M) (T :: G) ∧ Rep B n (addTag B v δ M) (T :: G) (addPath F n v δ) ∧
      MemFrame B n M (addTag B v δ M) := by
  obtain ⟨h1, h2, h3, h4⟩ := addPath_okE B n hI hR.toRepE hT false δ
  exact ⟨h1, ⟨h2, fun u hu => by rw [h4]; exact hR.fpar u hu⟩, h3⟩

/-! ### The root of a top-level virtual tree -/

lemma chain_edge : ∀ (L : List ℕ) (p u : ℕ), u ∈ L →
    ∃ q, (u, q) ∈ VT.chain p L ∧ (q ∈ L ∨ (q = p ∧ L.head? = some u))
  | [], _, _, h => absurd h (by simp)
  | x :: L, p, u, h => by
    by_cases hx : u = x
    · subst hx; exact ⟨p, by simp, Or.inr ⟨rfl, rfl⟩⟩
    · have hu : u ∈ L := by simpa [hx] using h
      obtain ⟨q, hq, h'⟩ := chain_edge L x u hu
      refine ⟨q, by simp [hq], ?_⟩
      rcases h' with h' | ⟨rfl, -⟩
      · exact Or.inl (by simp [h'])
      · exact Or.inl (by simp)

lemma chain_fst {L : List ℕ} {p u q : ℕ} (h : (u, q) ∈ VT.chain p L) : u ∈ L := by
  induction L generalizing p with
  | nil => simp at h
  | cons x L ih =>
    simp only [VT.chain_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, -⟩ | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every node of a virtual tree has its edge, to a node of the tree or (for the first node of the
auxiliary tree) to `p`. -/
theorem edge_of_mem : ∀ (t : VT) (p u : ℕ), u ∈ nodes t →
    ∃ q, (u, q) ∈ edges p t ∧ (q ∈ nodes t ∨ (q = p ∧ (seq t).head? = some u))
  | leaf, _, _, h => absurd h (by simp)
  | node l x r ds, p, u, h => by
    by_cases hs : u ∈ seq (node l x r ds)
    · obtain ⟨q, hq, h'⟩ := chain_edge (seq (node l x r ds)) p u hs
      refine ⟨q, List.mem_append_left _ hq, ?_⟩
      rcases h' with h' | h'
      · exact Or.inl ((seq_sublist_nodes _).subset h')
      · exact Or.inr h'
    · simp only [nodes_node, List.mem_append, List.mem_cons] at h
      simp only [seq_node, List.mem_append, List.mem_cons, not_or] at hs
      rcases h with (h | h | h) | h
      · obtain ⟨q, hq, h'⟩ := edge_of_mem l p u h
        have hq' : (u, q) ∈ dE l := by
          rcases List.mem_append.mp hq with hq | hq
          · exact absurd (chain_fst hq) hs.1
          · exact hq
        refine ⟨q, by simp [edges, hq'], Or.inl ?_⟩
        rcases h' with h' | ⟨-, h'⟩
        · simp [h']
        · exact absurd (List.mem_of_mem_head? h') hs.1
      · exact absurd h hs.2.1
      · obtain ⟨q, hq, h'⟩ := edge_of_mem r p u h
        have hq' : (u, q) ∈ dE r := by
          rcases List.mem_append.mp hq with hq | hq
          · exact absurd (chain_fst hq) hs.2.2
          · exact hq
        refine ⟨q, by simp [edges, hq'], Or.inl ?_⟩
        rcases h' with h' | ⟨-, h'⟩
        · simp [h']
        · exact absurd (List.mem_of_mem_head? h') hs.2.2
      · obtain ⟨d, hd, hu⟩ := mem_nodesL_iff.mp h
        have := List.sizeOf_lt_of_mem hd
        obtain ⟨q, hq, h'⟩ := edge_of_mem d x u hu
        have hdel : ∀ e, e ∈ edges x d → e ∈ dEL x ds := by
          intro e he
          obtain ⟨bef, aft, rfl⟩ := List.append_of_mem hd
          simp only [edges, List.mem_append] at he
          simp only [dEL_append, dEL_cons, List.mem_append]
          tauto
        refine ⟨q, by simp [edges, hdel _ hq], Or.inl ?_⟩
        rcases h' with h' | ⟨rfl, -⟩
        · simp [mem_nodesL_of hd h']
        · simp
termination_by t => sizeOf t
decreasing_by all_goals simp_wf; omega

/-- **The root of a top-level virtual tree**: the only node of it whose parent is `n` is the first
node of its auxiliary tree. -/
theorem top_root {M : Mem} {T : VT} {G : List VT} {F : Forest} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {u : ℕ} (hu : u ∈ nodes T) (hpar : F.par u = n) :
    (seq T).head? = some u := by
  obtain ⟨q, hq, h⟩ := edge_of_mem T n u hu
  have hq' : F.par u = q := by
    refine hR.par u q ?_
    simp only [dEL_cons, List.mem_append]
    simp only [edges, List.mem_append] at hq
    exact Or.inl hq
  rcases h with h | ⟨-, h⟩
  · have := (hI.cover q).mp (by simp [h]); omega
  · exact h

/-- Two stored virtual forests differing in one tree have the same nodes in that tree. -/
lemma nodes_perm_of_inv {M M' : Mem} {gb ga : List VT} {T T' : VT}
    (hI : Inv B n M (gb ++ T :: ga)) (hI' : Inv B n M' (gb ++ T' :: ga)) :
    (nodes T').Perm (nodes T) := by
  have h1 : (nodesL (gb ++ T' :: ga)).Perm (nodesL (gb ++ T :: ga)) := by
    refine (List.perm_ext_iff_of_nodup hI'.nodup hI.nodup).mpr fun u => ?_
    rw [hI.cover u, hI'.cover u]
  simp only [nodesL_append, nodesL_cons] at h1
  have h2 := (List.perm_append_left_iff _).mp h1
  exact (List.perm_append_right_iff _).mp h2

mutual
lemma dE_fst : ∀ (t : VT) {u q : ℕ}, (u, q) ∈ dE t → u ∈ nodes t
  | leaf, _, _, h => by simp at h
  | node l x r ds, u, q, h => by
    simp only [dE_node, List.mem_append] at h
    simp only [nodes_node, List.mem_append, List.mem_cons]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (dE_fst l h))
    · exact Or.inl (Or.inr (Or.inr (dE_fst r h)))
    · exact Or.inr (dEL_fst x ds h)
lemma dEL_fst (y : ℕ) : ∀ (ds : List VT) {u q : ℕ}, (u, q) ∈ dEL y ds → u ∈ nodesL ds
  | [], _, _, h => by simp at h
  | d :: ds, u, q, h => by
    simp only [dEL_cons, List.mem_append] at h
    simp only [nodesL_cons, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl ((seq_sublist_nodes d).subset (chain_fst h))
    · exact Or.inl (dE_fst d h)
    · exact Or.inr (dEL_fst y ds h)
end

/-! ### Cut -/

/-- Detach the left subtree of `v` (the path above `v`), after the access of `v`. -/
def cutM (v : ℕ) (M : Mem) : Mem :=
  recomp B n v ⟨upd (upd (upd M.nm (adr B v 1) n) (adr B (lc B M v) 0) n) (adr B v 4) n,
    upd (upd M.rm (adr B (lc B M v) 1) (tg B M (lc B M v) + tg B M v)) (adr B (lc B M v) 6)
      (tg2 B M (lc B M v) + tg2 B M v)⟩

/-- **Cut**: after the access of `v`, detaching its left subtree removes the edge from `v` to its
parent. -/
theorem cut_okE {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv)
    (hl : l ≠ leaf) (hv : rv B M v = false) :
    Inv B n (cutM B n v M) (l :: node leaf v leaf dv :: G) ∧
      RepE B n (cutM B n v M) (l :: node leaf v leaf dv :: G) (cut F n v) ∧
      MemFrame B n M (cutM B n v M) ∧
      potL (l :: node leaf v leaf dv :: G) ≤ potL (T :: G) ∧
      (∀ u, fpar B (cutM B n v M) u = if u = v then n else fpar B M u) := by
  subst hT
  have hE := hI.enc (node l v leaf dv) (by simp)
  rw [enc_node_iff_clean B n hv] at hE
  obtain ⟨hpv, hlv, hrv, -, hlE, -, hdE⟩ := hE
  generalize ha : rt n l = a at hlv
  have hnd := hI.nodup
  have hcount : ∀ w', (nodes l).count w' + [v].count w' + (nodesL dv).count w' +
      (nodesL G).count w' ≤ 1 := fun w' => by
    have := List.nodup_iff_count_le_one.mp hnd w'
    simp only [nodesL_cons, nodes_node, nodes_leaf, List.count_append, List.count_cons,
      List.count_nil] at this ⊢
    omega
  have hlt : ∀ u, u ∈ nodesL (node l v leaf dv :: G) → u < n := fun u hu => (hI.cover u).mp hu
  have hvn : v < n := hlt v (by simp)
  have hamem : a ∈ nodes l := ha ▸ rt_mem_nodes hl n
  have han : a < n := hlt a (by simp [hamem])
  have hav : a ≠ v := ne_of_count (A := nodes l) (C := [v]) (fun w' => by have := hcount w'; omega)
    hamem (by simp)
  -- the fields after the cut
  obtain ⟨M0, hM0⟩ : ∃ M0 : Mem, M0 = ⟨upd (upd (upd M.nm (adr B v 1) n) (adr B a 0) n)
      (adr B v 4) n, upd (upd M.rm (adr B a 1) (tg B M a + tg B M v)) (adr B a 6)
        (tg2 B M a + tg2 B M v)⟩ := ⟨_, rfl⟩
  have hcut : cutM B n v M = recomp B n v M0 := by rw [cutM, hlv, hM0]
  rw [hcut]
  have m0n : ∀ u j, j < 16 → M0.nm (adr B u j) =
      if u = v ∧ j = 1 then n else if u = a ∧ j = 0 then n else if u = v ∧ j = 4 then n
      else M.nm (adr B u j) := by
    intro u j hj; rw [hM0]; simp only [upd_adr _ _ hj (show 4 < 16 by omega),
      upd_adr _ _ hj (show 0 < 16 by omega), upd_adr _ _ hj (show 1 < 16 by omega)]
    split_ifs <;> simp_all
  have m0r : ∀ u j, j < 16 → M0.rm (adr B u j) =
      if u = a ∧ j = 6 then tg2 B M a + tg2 B M v else
      if u = a ∧ j = 1 then tg B M a + tg B M v else M.rm (adr B u j) := by
    intro u j hj; rw [hM0]; simp only [upd_adr _ _ hj (show 1 < 16 by omega),
      upd_adr _ _ hj (show 6 < 16 by omega)]
  have agr : ∀ u, u ≠ v → u ≠ a → Agr B M (recomp B n v M0) u := by
    intro u h1 h2 j hj
    have e := recomp_agr B n (M := M0) h1 j hj
    rw [e.1, e.2, m0n u j hj, m0r u j hj]
    simp [h1, h2]
  have agrA : AgrC B M (recomp B n v M0) a := by
    intro j hj
    have e := recomp_agr B n (M := M0) hav j hj
    refine ⟨fun h0 => ?_, fun h1 h6 => ?_⟩
    · rw [e.1, m0n a j hj]; simp [hav, h0]
    · rw [e.2, m0r a j hj]; simp [h1, h6]
  have parA : par B (recomp B n v M0) a = n := by
    simp only [par]; rw [recomp_nm B n (by omega) (by omega), m0n a 0 (by omega)]
    simp [hav]
  have tgA : ∀ k, tgc B (recomp B n v M0) k a = tgc B M k a + tgc B M k v := by
    intro k; cases k
    · simp only [tgc, Bool.false_eq_true, ↓reduceIte, tg]
      rw [recomp_rm B n (by omega) (by omega), m0r a 1 (by omega)]; simp [tg]
    · simp only [tgc, ↓reduceIte, tg2]
      rw [recomp_rm B n (by omega) (by omega), m0r a 6 (by omega)]; simp [tg2]
  have pv : par B (recomp B n v M0) v = n := by
    simp only [par]; rw [recomp_nm B n (by omega) (by omega), m0n v 0 (by omega)]
    simp [hav.symm]; exact hpv
  have lv : lc B (recomp B n v M0) v = n := by
    simp only [lc]; rw [recomp_nm B n (by omega) (by omega), m0n v 1 (by omega)]; simp
  have rcv : rc B (recomp B n v M0) v = n := by
    simp only [rc]; rw [recomp_nm B n (by omega) (by omega), m0n v 2 (by omega)]
    simp [hav.symm]; exact hrv
  have fv : fpar B (recomp B n v M0) v = n := by
    simp only [fpar]; rw [recomp_nm B n (by omega) (by omega), m0n v 4 (by omega)]
    simp
  have rvv : rv B (recomp B n v M0) v = false := by
    simp only [rv, rvw]; rw [recomp_nm B n (by omega) (by omega), m0n v 10 (by omega)]
    simp only [rv, rvw] at hv; simpa using hv
  have vv : ∀ k, vlc B (recomp B n v M0) k v = vlc B M k v ∧
      tgc B (recomp B n v M0) k v = tgc B M k v := by
    intro k; cases k
    · simp only [vlc, tgc, Bool.false_eq_true, ↓reduceIte, vl, tg]
      rw [recomp_rm B n (by omega) (by omega), recomp_rm B n (by omega) (by omega),
        m0r v 0 (by omega), m0r v 1 (by omega)]
      simp [hav.symm]
    · simp only [vlc, tgc, ↓reduceIte, vl2, tg2]
      rw [recomp_rm B n (by omega) (by omega), recomp_rm B n (by omega) (by omega),
        m0r v 5 (by omega), m0r v 6 (by omega)]
      simp [hav.symm]
  have hAv : AggOK B n (recomp B n v M0) v := by
    refine aggOK_recomp B n ?_ ?_ ?_
    · simp only [lc]; rw [m0n v 1 (by omega)]; simp; omega
    · simp only [rc]; rw [m0n v 2 (by omega)]; simp [hav.symm]; rw [show M.nm (adr B v 2) = n
        from hrv]; omega
    · simp only [rv, rvw]; rw [m0n v 10 (by omega)]; simp only [rv, rvw] at hv; simpa using hv
  -- the nodes
  have inL : ∀ u ∈ nodes l, u ≠ v := fun u hu =>
    ne_of_count (A := nodes l) (C := [v]) (fun w' => by have := hcount w'; omega) hu (by simp)
  have inD : ∀ u ∈ nodesL dv, u ≠ v ∧ u ≠ a := fun u hu =>
    ⟨ne_of_count (A := nodesL dv) (C := [v]) (fun w' => by have := hcount w'; omega) hu (by simp),
     ne_of_count (A := nodesL dv) (C := nodes l) (fun w' => by have := hcount w'; omega) hu hamem⟩
  have inG : ∀ u ∈ nodesL G, u ≠ v ∧ u ≠ a := fun u hu =>
    ⟨ne_of_count (A := nodesL G) (C := [v]) (fun w' => by have := hcount w'; omega) hu (by simp),
     ne_of_count (A := nodesL G) (C := nodes l) (fun w' => by have := hcount w'; omega) hu hamem⟩
  have ndl : (nodes l).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by
    have := hcount w'; omega
  have ndd : (nodesL dv).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by
    have := hcount w'; omega
  have ndG : (nodesL G).Nodup := List.nodup_iff_count_le_one.mpr fun w' => by
    have := hcount w'; omega
  have hnil : NilOK B n (recomp B n v M0) := by
    have h := agr n (by omega) (by omega)
    exact ⟨by rw [lc, (h 1 (by omega)).1]; exact hI.nil.lc,
      by rw [rc, (h 2 (by omega)).1]; exact hI.nil.rc,
      by rw [cnt, (h 4 (by omega)).2]; exact hI.nil.cnt, by rw [sm, (h 3 (by omega)).2]; exact hI.nil.sm,
      by rw [sm2, (h 8 (by omega)).2]; exact hI.nil.sm2⟩
  have agrL : ∀ u ∈ nodes l, u ≠ rt n l → Agr B M (recomp B n v M0) u := fun u hu hne =>
    agr u (inL u hu) (by rw [← ha]; exact hne)
  have hlE' : Enc B n (recomp B n v M0) l n false :=
    Enc.frame B n hI.nil hnil hlE ndl n agrL (fun _ => by rw [ha]; exact agrA)
      (fun _ => by rw [ha]; exact parA)
  have hdE' := enc_frame_list B n hI.nil hnil hdE ndd (fun u hu => agr u (inD u hu).1 (inD u hu).2)
  have hNE : Enc B n (recomp B n v M0) (node leaf v leaf dv) n false :=
    (enc_node_iff_clean B n rvv).mpr ⟨pv, lv, rcv, hAv, .leaf _ _, .leaf _ _, hdE'⟩
  have hperm : (nodesL (l :: node leaf v leaf dv :: G)).Perm (nodesL (node l v leaf dv :: G)) := by
    rw [List.perm_iff_count]; intro a'
    simp only [nodesL_cons, nodes_node, nodes_leaf, List.count_append, List.count_cons,
      List.count_nil]
    omega
  have hvals : ∀ k u w, (u, w) ∈ dVL B (recomp B n v M0) (l :: node leaf v leaf dv :: G) k →
      (u, w) ∈ dVL B M (node l v leaf dv :: G) k := by
    intro k u w h
    have hrsl : rs B (recomp B n v M0) l false k = shift (tgc B M k v) (rs B M l false k) :=
      rs_retag B n (fun u hu hne => (agrL u hu hne).agrV B) ndl
        (fun j => by
          rw [ha]; cases j
          · exact ((agrA 0 (by omega)).2 (by omega) (by omega))
          · exact ((agrA 5 (by omega)).2 (by omega) (by omega)))
        (by rw [ha]; exact agrA.rvEq B) (by rw [ha, Bool.xor_false, tgA])
    have hdVl : dV B (recomp B n v M0) l k = dV B M l k :=
      dV_frame_root B n (fun u hu hne => (agrL u hu hne).agrV B) ndl k
    have hdVd : dVL B (recomp B n v M0) dv k = dVL B M dv k :=
      dVL_frame B dv (fun u hu => (agr u (inD u hu).1 (inD u hu).2).agrV B) k
    have hdVG : dVL B (recomp B n v M0) G k = dVL B M G k :=
      dVL_frame B G (fun u hu => (agr u (inG u hu).1 (inG u hu).2).agrV B) k
    simp only [dVL_cons, rs_node, dV_node, rs_leaf, dV_leaf, List.nil_append, List.append_nil,
      hrsl, hdVl, hdVd, hdVG, (vv _).1, (vv _).2, List.mem_append, cσ, rvv, hv,
      Bool.xor_false] at h ⊢
    simp only [shift_append, List.mem_append] at h ⊢
    clear * - h
    tauto
  refine ⟨⟨fun T' hT' => ?_, hperm.nodup_iff.mpr hI.nodup,
      fun u => hperm.mem_iff.trans (hI.cover u), hnil⟩, ⟨fun u p h => ?_, fun u w h => ?_,
      fun u w h => ?_⟩, ?_, ?_, fun u => ?_⟩
  · simp only [List.mem_cons] at hT'
    rcases hT' with rfl | rfl | hT'
    · exact hlE'
    · exact hNE
    · exact enc_frame_all B n hI.nil hnil (hI.enc T' (by simp [hT']))
        (nodup_of_mem_nodesL ndG hT') (fun u hu => agr u (inG u (mem_nodesL_of hT' hu)).1
          (inG u (mem_nodesL_of hT' hu)).2)
  · -- the edges
    simp only [cut]
    simp only [dEL_cons, List.mem_append, seq_leaf, seq_node, List.nil_append, VT.chain_cons,
      VT.chain_nil, List.mem_cons, List.not_mem_nil, or_false, dE_node, dE_leaf, List.append_nil,
      List.nil_append] at h
    have hold : ∀ q, (u, q) ∈ dEL n (node l v leaf dv :: G) → F.par u = q := fun q hq =>
      hR.par u q hq
    rcases h with (h | h) | (h | h) | h
    · have hu : u ∈ nodes l := (seq_sublist_nodes l).subset (chain_fst h)
      rw [ite_of_neg (inL u hu)]
      exact hold p (by simp [VT.chain_append, h])
    · have hu : u ∈ nodes l := dE_fst l h
      rw [ite_of_neg (inL u hu)]
      exact hold p (by simp [VT.chain_append, h])
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hu : u ∈ nodesL dv := dEL_fst v dv h
      rw [ite_of_neg (inD u hu).1]
      exact hold p (by simp [VT.chain_append, h])
    · have hu : u ∈ nodesL G := dEL_fst n G h
      rw [ite_of_neg (inG u hu).1]
      exact hold p (by simp [VT.chain_append, h])
  · -- the values
    simp only [cut]
    exact hR.val u w (hvals false u w h)
  · simp only [cut]
    exact hR.val2 u w (hvals true u w h)
  · refine MemFrame.trans B n ?_ (recomp_frame B n hvn.le)
    intro a' ha'
    rw [hM0]
    refine ⟨?_, ?_⟩
    · simp only
      rw [memFrame_upd _ _ hvn.le (by omega) ha', memFrame_upd _ _ han.le (by omega) ha',
        memFrame_upd _ _ hvn.le (by omega) ha']
    · simp only
      rw [memFrame_upd _ _ han.le (by omega) ha', memFrame_upd _ _ han.le (by omega) ha']
  · simp only [potL_cons, pot_node, pot_leaf, size_node, size_leaf, potL_nil]
    have := Nat.log_mono_right (b := 2) (show 0 + 0 + 1 + sizeL dv ≤ size l + 0 + 1 + sizeL dv by
      omega)
    omega
  · by_cases huv : u = v
    · subst huv; rw [fv]; simp
    · rw [ite_of_neg huv]
      by_cases hua : u = a
      · subst hua; exact (agrA 4 (by omega)).1 (by omega)
      · exact (agr u huv hua 4 (by omega)).1

theorem cut_ok {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : Rep B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv)
    (hl : l ≠ leaf) (hv : rv B M v = false) :
    Inv B n (cutM B n v M) (l :: node leaf v leaf dv :: G) ∧
      Rep B n (cutM B n v M) (l :: node leaf v leaf dv :: G) (cut F n v) ∧
      MemFrame B n M (cutM B n v M) ∧
      potL (l :: node leaf v leaf dv :: G) ≤ potL (T :: G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cut_okE B n hI hR.toRepE hT hl hv
  refine ⟨h1, ⟨h2, fun u hu => ?_⟩, h3, h4⟩
  rw [h5]; simp only [cut]
  split_ifs
  · rfl
  · exact hR.fpar u hu


/-! ### The forest parent field -/

/-- Set the forest parent of `u` to `p`. -/
def setFpar (u p : ℕ) (M : Mem) : Mem := ⟨upd M.nm (adr B u 4) p, M.rm⟩

lemma setFpar_nm {M : Mem} {u p x j : ℕ} (hj : j < 16) (h4 : j ≠ 4) :
    (setFpar B u p M).nm (adr B x j) = M.nm (adr B x j) := by
  simp [setFpar, upd_adr _ _ hj (show 4 < 16 by omega), h4]

lemma own_setFpar {M : Mem} {u p x : ℕ} : own B (setFpar B u p M) x = own B M x := by
  simp only [own, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm]
  rw [setFpar_nm B (by omega) (by omega), setFpar_nm B (by omega) (by omega),
    setFpar_nm B (by omega) (by omega), setFpar_nm B (by omega) (by omega),
    setFpar_nm B (by omega) (by omega), setFpar_nm B (by omega) (by omega)]
  rfl

lemma rd_setFpar {M : Mem} {u p x : ℕ} : rd B (setFpar B u p M) x = rd B M x := by
  simp only [rd, own_setFpar]; rfl

lemma rv_setFpar {M : Mem} {u p x : ℕ} : rv B (setFpar B u p M) x = rv B M x := by
  simp only [rv, rvw]; rw [setFpar_nm B (by omega) (by omega)]

lemma aggOK_setFpar {M : Mem} {u p x : ℕ} (h : AggOK B n M x) : AggOK B n (setFpar B u p M) x := by
  have hl : ∀ y, lc B (setFpar B u p M) y = lc B M y := fun y => setFpar_nm B (by omega) (by omega)
  have hr : ∀ y, rc B (setFpar B u p M) y = rc B M y := fun y => setFpar_nm B (by omega) (by omega)
  unfold AggOK at h ⊢
  rw [own_setFpar, rv_setFpar, hl, hr, rd_setFpar, rd_setFpar]
  exact h

lemma Enc.setFpar {M : Mem} {u p : ℕ} {t : VT} {q : ℕ} {π : Bool} (h : Enc B n M t q π) :
    Enc B n (DynTree.setFpar B u p M) t q π := by
  have hS : ∀ σ y, lcS B (DynTree.setFpar B u p M) σ y = lcS B M σ y := by
    intro σ y; simp only [lcS, lc, rc]
    rw [setFpar_nm B (by omega) (by omega), setFpar_nm B (by omega) (by omega)]
  have hσ : ∀ π y, cσ B (DynTree.setFpar B u p M) π y = cσ B M π y := by
    intro π y; simp only [cσ, rv_setFpar]
  induction h with
  | leaf p π => exact .leaf _ _
  | node h1 h2 h3 h4 _ _ _ ih5 ih6 ih7 =>
    refine .node (by rw [par, setFpar_nm B (by omega) (by omega)]; exact h1)
      (by rw [hσ, hS]; exact h2) (by rw [hσ, hS]; exact h3) (aggOK_setFpar B n h4)
      (by rw [hσ]; exact ih5) (by rw [hσ]; exact ih6) ih7

lemma rs_setFpar {M : Mem} {u p : ℕ} (t : VT) (π k : Bool) :
    rs B (setFpar B u p M) t π k = rs B M t π k :=
  rs_frame B (M := M) (M' := setFpar B u p M) t (fun _ _ => ⟨rfl, rfl, rfl, rfl, rv_setFpar B⟩) π k

lemma dVL_setFpar {M : Mem} {u p : ℕ} (G : List VT) (k : Bool) :
    dVL B (setFpar B u p M) G k = dVL B M G k :=
  dVL_frame B (M := M) (M' := setFpar B u p M) G (fun _ _ => ⟨rfl, rfl, rfl, rfl, rv_setFpar B⟩) k

lemma Inv.setFpar {M : Mem} {G : List VT} (hI : Inv B n M G) {u p : ℕ} :
    Inv B n (setFpar B u p M) G :=
  ⟨fun T hT => (hI.enc T hT).setFpar B n, hI.nodup, hI.cover,
    ⟨by rw [lc, setFpar_nm B (by omega) (by omega)]; exact hI.nil.lc,
      by rw [rc, setFpar_nm B (by omega) (by omega)]; exact hI.nil.rc, hI.nil.cnt, hI.nil.sm,
      hI.nil.sm2⟩⟩

lemma setFpar_frame {M : Mem} {u p : ℕ} (hu : u ≤ n) : MemFrame B n M (setFpar B u p M) :=
  fun _ ha => ⟨memFrame_upd _ _ hu (by omega) ha, rfl⟩

lemma fpar_setFpar {M : Mem} {u p x : ℕ} :
    fpar B (setFpar B u p M) x = if x = u then p else fpar B M x := by
  simp [fpar, setFpar, upd_adr]

/-- Cut on the memory, with the forest parent. -/
def cutF (v : ℕ) (M : Mem) : Mem := cutM B n v M

/-! ### Link -/

/-- Make `w` the path-parent and the forest parent of the root `v`. -/
def linkM (v w : ℕ) (M : Mem) : Mem := setFpar B v w ⟨upd M.nm (adr B v 0) w, M.rm⟩

/-- **Link**: after the access of the root `v` (a single-node auxiliary tree) and of `w` in another
tree, hanging the virtual tree of `v` from `w` links `v` below `w`; the potential grows by at most
`⌊log₂ n⌋`. -/
theorem link_okE {M : Mem} {G : List VT} {F : Forest} {Tw Tv : VT}
    (hI : Inv B n M (Tw :: Tv :: G))
    (hR : RepE B n M (Tw :: Tv :: G) F) {lw : VT} {v w : ℕ} {dw dv : List VT}
    (hTw : Tw = node lw w leaf dw) (hTv : Tv = node leaf v leaf dv) :
    Inv B n (linkM B v w M) (node lw w leaf (dw ++ [Tv]) :: G) ∧
      RepE B n (linkM B v w M) (node lw w leaf (dw ++ [Tv]) :: G) (link F v w) ∧
      MemFrame B n M (linkM B v w M) ∧
      potL (node lw w leaf (dw ++ [Tv]) :: G) ≤ potL (Tw :: Tv :: G) + Nat.log 2 n ∧
      (∀ u, fpar B (linkM B v w M) u = if u = v then w else fpar B M u) := by
  subst hTw
  have hnd := hI.nodup
  have hcount : ∀ x, (nodes lw).count x + [w].count x + (nodesL dw).count x + (nodes Tv).count x +
      (nodesL G).count x ≤ 1 := fun x => by
    have := List.nodup_iff_count_le_one.mp hnd x
    simp only [nodesL_cons, nodes_node, nodes_leaf, List.count_append, List.count_cons,
      List.count_nil] at this ⊢
    omega
  have hvT : v ∈ nodes Tv := by rw [hTv]; simp
  have hwv : w ≠ v := ne_of_count (A := [w]) (C := nodes Tv) (fun x => by have := hcount x; omega)
    (by simp) hvT
  have hvn : v < n := (hI.cover v).mp (by simp [hvT])
  have hwn : w < n := (hI.cover w).mp (by simp)
  obtain ⟨M1, hM1⟩ : ∃ M1 : Mem, M1 = ⟨upd M.nm (adr B v 0) w, M.rm⟩ := ⟨_, rfl⟩
  have hlink : linkM B v w M = setFpar B v w M1 := by rw [linkM, hM1]
  rw [hlink]
  have agr : ∀ u, u ≠ v → Agr B M M1 u := fun u h j hj => by
    rw [hM1]; simp [upd_adr _ _ hj, h]
  have agrV : AgrC B M M1 v := fun j hj => by
    rw [hM1]; refine ⟨fun h0 => ?_, fun _ _ => rfl⟩; simp [upd_adr _ _ hj, h0]
  have parV : par B M1 v = w := by rw [hM1]; simp [par, upd_adr]
  have hnil : NilOK B n M1 := by
    have h := agr n (by omega)
    exact ⟨by rw [lc, (h 1 (by omega)).1]; exact hI.nil.lc,
      by rw [rc, (h 2 (by omega)).1]; exact hI.nil.rc,
      by rw [cnt, (h 4 (by omega)).2]; exact hI.nil.cnt, by rw [sm, (h 3 (by omega)).2]; exact hI.nil.sm,
      by rw [sm2, (h 8 (by omega)).2]; exact hI.nil.sm2⟩
  have inV : ∀ (L : List ℕ), (∀ x, L.count x + (nodes Tv).count x ≤ 1) → ∀ u ∈ L, u ≠ v :=
    fun L h u hu => ne_of_count h hu hvT
  have hwE := hI.enc _ (by simp : node lw w leaf dw ∈ _)
  rw [enc_node_iff] at hwE
  obtain ⟨hpw, hlw, hrw, hAw, hlwE, -, hdwE⟩ := hwE
  have hTvE := hI.enc Tv (by simp)
  have ndl : (nodes lw).Nodup := List.nodup_iff_count_le_one.mpr fun x => by
    have := hcount x; omega
  have ndd : (nodesL dw).Nodup := List.nodup_iff_count_le_one.mpr fun x => by
    have := hcount x; omega
  have ndv : (nodes Tv).Nodup := List.nodup_iff_count_le_one.mpr fun x => by
    have := hcount x; omega
  have ndG : (nodesL G).Nodup := List.nodup_iff_count_le_one.mpr fun x => by
    have := hcount x; omega
  have agW := agr w hwv
  have hlwE' := enc_frame_all B n hI.nil hnil hlwE ndl
    (fun u hu => agr u (inV _ (fun x => by have := hcount x; omega) u hu))
  have hdwE' := enc_frame_list B n hI.nil hnil hdwE ndd
    (fun u hu => agr u (inV _ (fun x => by have := hcount x; omega) u hu))
  have hTvE' : Enc B n M1 Tv w false := by
    refine Enc.frame B n hI.nil hnil hTvE ndv w (fun u hu hne => agr u ?_) (fun _ => ?_)
      (fun _ => ?_)
    · rw [hTv] at hne; exact hne
    · rw [hTv]; exact agrV
    · rw [hTv]; exact parV
  have hσw : cσ B M1 false w = cσ B M false w := by simp only [cσ, agW.rv B]
  have hSw : ∀ σ, lcS B M1 σ w = lcS B M σ w := by
    intro σ; simp only [lcS, lc, rc]; rw [(agW 1 (by omega)).1, (agW 2 (by omega)).1]
  have hwE' : Enc B n M1 (node lw w leaf (dw ++ [Tv])) n false := by
    rw [enc_node_iff, hσw, hSw, hSw]
    refine ⟨by rw [par, (agW 0 (by omega)).1]; exact hpw, hlw, hrw,
      hAw.of_agrC B n agW.agrC ?_ ?_, hlwE', .leaf _ _, fun d hd => ?_⟩
    · have lk1 := look_rt B n hI.nil hnil lw
        (fun u hu => agr u (inV _ (fun x => by have := hcount x; omega) u hu))
      have lk2 := look_nil B n hI.nil hnil
      cases e : cσ B M false w <;> simp only [lcS, e, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hlw hrw
      · rw [hlw]; exact lk1
      · rw [hrw]; exact lk2
    · have lk1 := look_rt B n hI.nil hnil lw
        (fun u hu => agr u (inV _ (fun x => by have := hcount x; omega) u hu))
      have lk2 := look_nil B n hI.nil hnil
      cases e : cσ B M false w <;> simp only [lcS, e, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte] at hlw hrw
      · rw [hrw]; exact lk2
      · rw [hlw]; exact lk1
    · rcases List.mem_append.mp hd with hd | hd
      · exact hdwE' d hd
      · simp at hd; subst hd; exact hTvE'
  have hperm : (nodesL (node lw w leaf (dw ++ [Tv]) :: G)).Perm
      (nodesL (node lw w leaf dw :: Tv :: G)) := by
    rw [List.perm_iff_count]; intro a'
    simp only [nodesL_cons, nodes_node, nodes_leaf, nodesL_append, nodesL_nil, List.count_append,
      List.count_cons, List.count_nil]
    omega
  have hI1 : Inv B n M1 (node lw w leaf (dw ++ [Tv]) :: G) := by
    refine ⟨fun T hT => ?_, hperm.nodup_iff.mpr hnd, fun u => hperm.mem_iff.trans (hI.cover u),
      hnil⟩
    rcases List.mem_cons.mp hT with rfl | hT
    · exact hwE'
    · exact enc_frame_all B n hI.nil hnil (hI.enc T (by simp [hT])) (nodup_of_mem_nodesL ndG hT)
        (fun u hu => agr u (inV _ (fun x => by have := hcount x; omega) u (mem_nodesL_of hT hu)))
  refine ⟨hI1.setFpar B n, ⟨fun u p h => ?_, fun u q h => ?_, fun u q h => ?_⟩,
    MemFrame.trans B n (fun a' ha' => ⟨by rw [hM1]; exact memFrame_upd _ _ hvn.le (by omega) ha',
      by rw [hM1]⟩) (setFpar_frame B n hvn.le), ?_, fun u => ?_⟩
  · -- the edges
    simp only [link]
    simp only [dEL_cons, edges, seq_node, seq_leaf, dE_node, dE_leaf, dEL_append, dEL_nil,
      List.append_nil, List.nil_append, List.mem_append] at h
    have hold : ∀ q, (u, q) ∈ dEL n (node lw w leaf dw :: Tv :: G) → F.par u = q :=
      fun q hq => hR.par u q hq
    have hvdv : v ∉ nodesL dv := fun hm => by
      have h2 : (nodes Tv).count v ≥ 2 := by
        rw [hTv]
        simp only [nodes_node, nodes_leaf, List.nil_append, List.count_cons, List.count_append,
          beq_self_eq_true, ite_true]
        have := List.count_pos_iff.mpr hm; omega
      have := hcount v; omega
    have hvlw : v ∉ nodes lw := fun hm =>
      inV _ (fun x => by have := hcount x; omega) v hm rfl
    have hvdw : v ∉ nodesL dw := fun hm =>
      inV _ (fun x => by have := hcount x; omega) v hm rfl
    have hvG : v ∉ nodesL G := fun hm => inV _ (fun x => by have := hcount x; omega) v hm rfl
    have hsTv : seq Tv = [v] := by rw [hTv]; simp
    have hdTv : dE Tv = dEL v dv := by rw [hTv]; simp
    rw [hsTv, hdTv] at h
    by_cases huv : u = v
    · subst huv
      rw [ite_of_pos rfl]
      rcases h with (h | h | h | h | h) | h
      · have := chain_fst h
        simp only [List.mem_append, List.mem_singleton] at this
        rcases this with hm | hm
        · exact absurd ((seq_sublist_nodes lw).subset hm) hvlw
        · exact absurd hm hwv.symm
      · exact absurd (dE_fst lw h) hvlw
      · exact absurd (dEL_fst w dw h) hvdw
      · simp at h; exact h.symm
      · exact absurd (dEL_fst _ dv h) hvdv
      · exact absurd (dEL_fst n G h) hvG
    · rw [ite_of_neg huv]
      refine hold p ?_
      simp only [dEL_cons, edges, seq_node, seq_leaf, dE_node, dE_leaf, List.mem_append,
        List.nil_append, List.append_nil, hsTv, hdTv]
      have h' : ¬ (u, p) ∈ VT.chain w [v] := by simp [huv]
      clear * - h h'
      tauto
  · -- the values
    simp only [link]
    refine hR.val u q ?_
    have e1 : dVL B (setFpar B v w M1) (node lw w leaf (dw ++ [Tv]) :: G) false =
        dVL B M (node lw w leaf (dw ++ [Tv]) :: G) false := by
      rw [dVL_setFpar]
      exact dVL_frame B _ (fun u _ => by
        rw [hM1]; exact ⟨rfl, rfl, rfl, rfl, by simp [rv, rvw, upd_adr]⟩) false
    rw [e1] at h
    simp only [dVL_cons, dV_node, rs_node, dVL_append, dVL_nil, List.append_nil,
      List.mem_append] at h ⊢
    clear * - h
    tauto
  · simp only [link]
    refine hR.val2 u q ?_
    have e1 : dVL B (setFpar B v w M1) (node lw w leaf (dw ++ [Tv]) :: G) true =
        dVL B M (node lw w leaf (dw ++ [Tv]) :: G) true := by
      rw [dVL_setFpar]
      exact dVL_frame B _ (fun u _ => by
        rw [hM1]; exact ⟨rfl, rfl, rfl, rfl, by simp [rv, rvw, upd_adr]⟩) true
    rw [e1] at h
    simp only [dVL_cons, dV_node, rs_node, dVL_append, dVL_nil, List.append_nil,
      List.mem_append] at h ⊢
    clear * - h
    tauto
  · -- the potential
    have hsz := hI.sizeL B n
    simp only [sizeL_cons, sizeL_nil] at hsz
    have := Nat.log_mono_right (b := 2) (show size (node lw w leaf (dw ++ [Tv])) ≤ n by
      simp only [size_node, sizeL_append, sizeL_cons, sizeL_nil] at hsz ⊢; omega)
    have e1 : pot (node lw w leaf (dw ++ [Tv])) = pot lw + potL dw + pot Tv +
        Nat.log 2 (size (node lw w leaf (dw ++ [Tv]))) := by
      rw [pot_node']; simp only [potL_append, potL_cons, potL_nil, pot_leaf]; ring
    have e2 : pot (node lw w leaf dw) = pot lw + potL dw +
        Nat.log 2 (size (node lw w leaf dw)) := by
      rw [pot_node']; simp only [pot_leaf]; ring
    simp only [potL_cons]
    rw [e1, e2]
    omega
  · rw [fpar_setFpar]
    by_cases huv : u = v
    · simp [huv]
    · rw [ite_of_neg huv, ite_of_neg huv]
      rw [hM1]; simp [fpar, upd_adr]

theorem link_ok {M : Mem} {G : List VT} {F : Forest} {Tw Tv : VT} (hI : Inv B n M (Tw :: Tv :: G))
    (hR : Rep B n M (Tw :: Tv :: G) F) {lw : VT} {v w : ℕ} {dw dv : List VT}
    (hTw : Tw = node lw w leaf dw) (hTv : Tv = node leaf v leaf dv) :
    Inv B n (linkM B v w M) (node lw w leaf (dw ++ [Tv]) :: G) ∧
      Rep B n (linkM B v w M) (node lw w leaf (dw ++ [Tv]) :: G) (link F v w) ∧
      MemFrame B n M (linkM B v w M) ∧
      potL (node lw w leaf (dw ++ [Tv]) :: G) ≤ potL (Tw :: Tv :: G) + Nat.log 2 n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := link_okE B n hI hR.toRepE hTw hTv
  refine ⟨h1, ⟨h2, fun u hu => ?_⟩, h3, h4⟩
  rw [h5]; simp only [link]
  split_ifs
  · rfl
  · exact hR.fpar u hu

end DynTree

end PlanarFlow
