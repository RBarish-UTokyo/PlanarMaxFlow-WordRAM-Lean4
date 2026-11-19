module

public import PlanarFlow.DynTree.Rot

/-!
# Dynamic trees: the fields of a rotation, and replacement at a hole

`replace_ok`: replacing the subtree at the hole of a stored zipper by one that represents the same
paths with the same values keeps the invariant and the represented forest (used by the rotation
and by the operations of the link-cut tree). The field lemmas `rotP_L`, `rotP_R`, `rotMem_agr`, …
describe the memory after a rotation; the rotation theorem is in `PlanarFlow.DynTree.Rotate`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- The labels of a stored forest are distinct and below `n`. -/
lemma Inv.counts {M : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT} {s : VT}
    {fs : List Frame} (hG : G = gb ++ plug s fs :: ga) :
    (∀ w, (nodes s).count w + (cnodes fs).count w + (nodesL (gb ++ ga)).count w ≤ 1) ∧
    (∀ u ∈ nodes s, u < n) ∧ (∀ u ∈ cnodes fs, u < n) ∧ (∀ u ∈ nodesL (gb ++ ga), u < n) := by
  have hp := nodesL_split gb ga s fs
  rw [← hG] at hp
  have hnd := hp.nodup_iff.mp hI.nodup
  have hc : ∀ u, u ∈ nodes s ++ (cnodes fs ++ nodesL (gb ++ ga)) → u < n := fun u hu =>
    (hI.cover u).mp (hp.mem_iff.mpr hu)
  refine ⟨fun w => ?_, fun u hu => hc u (List.mem_append_left _ hu),
    fun u hu => hc u (List.mem_append_right _ (List.mem_append_left _ hu)),
    fun u hu => hc u (List.mem_append_right _ (List.mem_append_right _ hu))⟩
  have := List.nodup_iff_count_le_one.mp hnd w
  simp only [List.count_append] at this
  omega

lemma frame_solid_cases {f : Frame} (hf : f.Solid) :
    (∃ y c dy, f = .L y c dy) ∨ (∃ c y dy, f = .R c y dy) := by
  cases f with
  | L y c dy => exact Or.inl ⟨y, c, dy, rfl⟩
  | R c y dy => exact Or.inr ⟨c, y, dy, rfl⟩
  | D l y r bef aft => exact absurd hf (by simp [Frame.Solid])

lemma count_cons' (w x : ℕ) (l : List ℕ) : (x :: l).count w = l.count w + [x].count w := by
  simp [List.count_cons]

lemma hp_cases (fs : List Frame) : (fs = [] ∧ hp n fs = n) ∨ (hp n fs ∈ cnodes fs) := by
  rcases fs with _ | ⟨f, fs⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (by simp [hp, cnodes_cons, y_mem_fnodes])

/-! ### Replacing the subtree at the hole: the general statement -/

/-- What the parent reads of the root of a stored tree is determined by its represented values
and its in-order. -/
lemma look_of_enc {M M' : Mem} (hN : NilOK B n M) (hN' : NilOK B n M') {s s' : VT} {p p' : ℕ}
    {π : Bool} (h : Enc B n M s p π) (h' : Enc B n M' s' p' π) (hs : s ≠ VT.leaf)
    (hs' : s' ≠ VT.leaf) (hlt : ∀ u ∈ nodes s, u < n) (hlt' : ∀ u ∈ nodes s', u < n)
    (hrs : ∀ k, rs B M' s' π k = rs B M s π k) (hseq : seq s' = seq s) :
    Look B n M M' (rt n s) (rt n s') := by
  have hr1 : rt n s < n := hlt _ (rt_mem_nodes hs n)
  have hr2 : rt n s' < n := hlt' _ (rt_mem_nodes hs' n)
  have e1 := (h.agg B n hN hlt).2 hr1
  have e2 := (h'.agg B n hN' hlt').2 hr2
  rw [hrs, hrs, hseq, ← e1] at e2
  have e : rd B M' (rt n s') = rd B M (rt n s) := by
    have := congrArg (Ag.mirIf π) e2; simpa using this
  exact ⟨⟨fun _ => hr2, fun _ => hr1⟩, congrArg Ag.c e, congrArg Ag.s1 e, congrArg Ag.s2 e,
    fun _ => e⟩

/-- The pointer facts of a redirection of the node above the hole. -/
def RedirZ (M M' : Mem) (z r r' : ℕ) : Prop :=
  lc B M' z = (if lc B M z = r then r' else lc B M z) ∧
    rc B M' z = (if lc B M z = r then rc B M z else if rc B M z = r then r' else rc B M z)

/-- **Replacing the subtree at the hole of a stored zipper.** The new subtree `s'` is stored with
the parent pointer and the parity of the old one, represents the same paths with the same
values, the node above the hole is redirected from the old root to the new one, and nothing else
changes. Then the memory stores the new virtual forest, which represents the same forest. -/
theorem replace_okE {M M' : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : RepE B n M G F) {gb ga : List VT} {s s' : VT} {fs : List Frame}
    (hG : G = gb ++ plug s fs :: ga) (hs' : Enc B n M' s' (hp n fs) (cpar B M fs))
    (hsame : Same s' s) (hV : VEq B M M' s s' (cpar B M fs)) (hs : s ≠ VT.leaf)
    (hs'ne : s' ≠ VT.leaf)
    (hout : ∀ u, u ∈ cnodes fs ++ nodesL (gb ++ ga) → u ≠ hp n fs → Agr B M M' u)
    (hz : fs ≠ [] → AgrS B M M' (hp n fs) ∧ par B M' (hp n fs) = par B M (hp n fs) ∧
      RedirZ B M M' (hp n fs) (rt n s) (rt n s'))
    (hnil : NilOK B n M') :
    Inv B n M' (gb ++ plug s' fs :: ga) ∧ RepE B n M' (gb ++ plug s' fs :: ga) F := by
  obtain ⟨hcount, hlts, hltc, hlto⟩ := hI.counts B n hG
  have hT : Enc B n M (plug s fs) n false := hI.enc _ (by rw [hG]; simp)
  rw [enc_plugZ] at hT
  obtain ⟨hsE, hCE⟩ := hT
  have hlts' : ∀ u ∈ nodes s', u < n := fun u hu => hlts u (hsame.nodes.mem_iff.mp hu)
  have hlook : Look B n M M' (rt n s) (rt n s') :=
    look_of_enc B n hI.nil hnil hsE hs' hs hs'ne hlts hlts' (fun k => (hV k).1) hsame.seq
  have hrtne : ∀ (c : VT), (∀ w, (nodes s).count w + (nodes c).count w ≤ 1) →
      rt n c ≠ rt n s := by
    intro c hcw e
    cases c with
    | leaf =>
      have := hlts _ (rt_mem_nodes hs n)
      simp only [rt_leaf] at e; omega
    | node a y b dy =>
      exact ne_of_count hcw (rt_mem_nodes hs n) (rt_mem_nodes (by simp) n) e.symm
  -- the parities of the frames are unchanged
  have hcp : cpar B M' fs = cpar B M fs := by
    refine cpar_congr B (fun u hu => ?_)
    by_cases hu' : u = hp n fs
    · subst hu'
      have hne : fs ≠ [] := by
        rintro rfl; simp [cnodes] at hu
      exact (hz hne).1.2.2.2.2.2.2
    · exact (hout u (List.mem_append_left _ hu) hu').rv B
  have hC' : EncC B n M' fs (rt n s') n := by
    rcases fs with _ | ⟨f, fs⟩
    · trivial
    · obtain ⟨hy, hpar, hl, hr⟩ := hz (by simp)
      dsimp only [hp] at hy hpar hl hr
      have hnd : (cnodes (f :: fs)).Nodup := by
        rw [List.nodup_iff_count_le_one]; intro w; have := hcount w; omega
      refine EncC.replace B n hI.nil hnil hCE hnd
        (fun u hu hne => hout u (List.mem_append_left _ hu) hne) hy hpar (fun _ => hlook) ?_
      have hF := hCE.1
      cases f with
      | L y c dy =>
        obtain ⟨e1, e2, -⟩ := hF
        simp only [Frame.y] at hl hr e1 e2
        have hne : rt n c ≠ rt n s := hrtne c (fun w => by
          have := hcount w
          simp only [cnodes_cons, Frame.fnodes, List.count_append, List.count_cons] at this
          omega)
        refine ⟨?_, ?_⟩ <;> cases hσ : cσ B M (cpar B M fs) y <;>
          simp only [lcS, hσ, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            at e1 e2 ⊢ <;>
          simp_all
      | R c y dy =>
        obtain ⟨e1, e2, -⟩ := hF
        simp only [Frame.y] at hl hr e1 e2
        have hne : rt n c ≠ rt n s := hrtne c (fun w => by
          have := hcount w
          simp only [cnodes_cons, Frame.fnodes, List.count_append, List.count_cons] at this
          omega)
        refine ⟨?_, ?_⟩ <;> cases hσ : cσ B M (cpar B M fs) y <;>
          simp only [lcS, hσ, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            at e1 e2 ⊢ <;>
          simp_all
      | D l y r bef aft =>
        obtain ⟨e1, e2, -⟩ := hF
        simp only [Frame.y] at hl hr e1 e2
        have hne1 : rt n l ≠ rt n s := hrtne l (fun w => by
          have := hcount w
          simp only [cnodes_cons, Frame.fnodes, List.count_append, List.count_cons] at this
          omega)
        have hne2 : rt n r ≠ rt n s := hrtne r (fun w => by
          have := hcount w
          simp only [cnodes_cons, Frame.fnodes, List.count_append, List.count_cons] at this
          omega)
        refine ⟨?_, ?_⟩ <;> cases hσ : cσ B M (cpar B M fs) y <;>
          simp only [lcS, hσ, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            at e1 e2 ⊢ <;>
          simp_all
  refine ⟨inv_replace B n hI hG (by rw [hcp]; exact hs') hC' hsame.nodes (fun u hu => ?_) hnil, ?_⟩
  · refine hout u (List.mem_append_right _ hu) ?_
    rintro rfl
    rcases hp_cases n fs with ⟨-, h⟩ | h
    · have := hlto _ hu; omega
    · exact ne_of_count (fun w => by have := hcount w; omega) h hu rfl
  · refine repE_replace B n hR hG hsame hV (fun u hu => ?_)
    by_cases hu' : u = hp n fs
    · subst hu'
      have hne : fs ≠ [] := by
        rintro rfl
        simp only [cnodes, List.nil_append, hp] at hu
        have := hlto _ hu; omega
      exact (hz hne).1.agrV B
    · exact (hout u hu hu').agrV B

theorem replace_ok {M M' : Mem} {G : List VT} {F : Forest} (hI : Inv B n M G)
    (hR : Rep B n M G F) {gb ga : List VT} {s s' : VT} {fs : List Frame}
    (hG : G = gb ++ plug s fs :: ga) (hs' : Enc B n M' s' (hp n fs) (cpar B M fs))
    (hsame : Same s' s) (hV : VEq B M M' s s' (cpar B M fs)) (hs : s ≠ VT.leaf)
    (hs'ne : s' ≠ VT.leaf)
    (hout : ∀ u, u ∈ cnodes fs ++ nodesL (gb ++ ga) → u ≠ hp n fs → Agr B M M' u)
    (hz : fs ≠ [] → AgrS B M M' (hp n fs) ∧ par B M' (hp n fs) = par B M (hp n fs) ∧
      RedirZ B M M' (hp n fs) (rt n s) (rt n s'))
    (hnil : NilOK B n M') (hfp : ∀ u < n, fpar B M' u = fpar B M u) :
    Inv B n M' (gb ++ plug s' fs :: ga) ∧ Rep B n M' (gb ++ plug s' fs :: ga) F := by
  obtain ⟨h1, h2⟩ := replace_okE B n hI hR.toRepE hG hs' hsame hV hs hs'ne hout hz hnil
  exact ⟨h1, h2, fun u hu => by rw [hfp u hu]; exact hR.fpar u hu⟩

/-! ### The fields after a rotation -/

section fields
variable {B n} {M : Mem} {x y z bl : ℕ}

lemma rotP_agr {u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x)
    (h3 : u ≠ (if lc B M (par B M x) = x then rc B M x else lc B M x))
    (h4 : u ≠ par B M (par B M x)) : Agr B M (rotP B x M) u := by
  intro j hj
  simp only [rotP]
  split_ifs <;> simp_all [upd_adr _ _ hj]

lemma rotMem_agr {u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x)
    (h3 : u ≠ (if lc B M (par B M x) = x then rc B M x else lc B M x))
    (h4 : u ≠ par B M (par B M x)) : Agr B M (rotMem B n x M) u := by
  intro j hj
  have e1 := recomp_agr B n (M := recomp B n (par B M x) (rotP B x M)) (u := x) h1 j hj
  have e2 := recomp_agr B n (M := rotP B x M) (u := par B M x) h2 j hj
  have e3 := rotP_agr h1 h2 h3 h4 j hj
  exact ⟨e1.1.trans (e2.1.trans e3.1), e1.2.trans (e2.2.trans e3.2)⟩

/-- `rotP` writes only pointers (fields 0, 1, 2) and tags (real fields 1, 6). -/
lemma rotP_nm {u j : ℕ} (hj : j < 16) (h : 3 ≤ j) :
    (rotP B x M).nm (adr B u j) = M.nm (adr B u j) := by
  have a0 : j ≠ 0 := by omega
  have a1 : j ≠ 1 := by omega
  have a2 : j ≠ 2 := by omega
  simp only [rotP]
  split_ifs <;> simp [upd_adr _ _ hj, a0, a1, a2]

lemma rotP_rm {u j : ℕ} (hj : j < 16) (h : j ≠ 1 ∧ j ≠ 6) :
    (rotP B x M).rm (adr B u j) = M.rm (adr B u j) := by
  simp only [rotP]
  simp [upd_adr _ _ hj, h.1, h.2]

/-- The aggregate fields are only written by `recomp`. -/
lemma rotMem_agg {u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x) :
    own B (rotMem B n x M) u = own B M u ∧ fpar B (rotMem B n x M) u = fpar B M u ∧
      vl B (rotMem B n x M) u = vl B M u ∧ vl2 B (rotMem B n x M) u = vl2 B M u ∧
      rv B (rotMem B n x M) u = rv B M u := by
  have e1 := recomp_agr B n (M := recomp B n (par B M x) (rotP B x M)) (u := x) h1
  have e2 := recomp_agr B n (M := rotP B x M) (u := par B M x) h2
  have kN : ∀ j < 16, 3 ≤ j → (rotMem B n x M).nm (adr B u j) = M.nm (adr B u j) := by
    intro j hj h
    rw [rotMem, (e1 j hj).1, (e2 j hj).1, rotP_nm hj h]
  have kR : ∀ j < 16, j ≠ 1 → j ≠ 6 → (rotMem B n x M).rm (adr B u j) = M.rm (adr B u j) := by
    intro j hj h h'
    rw [rotMem, (e1 j hj).2, (e2 j hj).2, rotP_rm hj ⟨h, h'⟩]
  refine ⟨?_, kN 4 (by omega) (by omega), kR 0 (by omega) (by omega) (by omega),
    kR 5 (by omega) (by omega) (by omega), by simp only [rv, rvw]; rw [kN 10 (by omega) (by omega)]⟩
  simp only [own, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm]
  rw [kR 2 (by omega) (by omega) (by omega), kR 3 (by omega) (by omega) (by omega),
    kR 4 (by omega) (by omega) (by omega), kR 7 (by omega) (by omega) (by omega),
    kR 8 (by omega) (by omega) (by omega), kN 3 (by omega) (by omega), kN 5 (by omega) (by omega),
    kN 6 (by omega) (by omega), kN 7 (by omega) (by omega), kN 8 (by omega) (by omega),
    kN 9 (by omega) (by omega)]

/-- Reading pointers and tags after the rotation: they are those of `rotP`. -/
lemma rotMem_ptr (u : ℕ) :
    par B (rotMem B n x M) u = par B (rotP B x M) u ∧ lc B (rotMem B n x M) u = lc B (rotP B x M) u ∧
      rc B (rotMem B n x M) u = rc B (rotP B x M) u ∧ tg B (rotMem B n x M) u = tg B (rotP B x M) u ∧
      tg2 B (rotMem B n x M) u = tg2 B (rotP B x M) u := by
  obtain ⟨a1, a2, a3, -, -, a6, -, a8, -⟩ := recomp_agrS_par B n
    (M := recomp B n (par B M x) (rotP B x M)) (u := x) (v := u)
  obtain ⟨b1, b2, b3, -, -, b6, -, b8, -⟩ := recomp_agrS_par B n (M := rotP B x M)
    (u := par B M x) (v := u)
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a6.trans b6, a8.trans b8⟩

lemma rotMem_rv (u : ℕ) : rv B (rotMem B n x M) u = rv B M u := by
  simp only [rv, rvw, rotMem]
  rw [recomp_nm B n (by omega) (by omega), recomp_nm B n (by omega) (by omega),
    rotP_nm (by omega) (by omega)]

lemma rotMem_frame (hx : x ≤ n) (hy : par B M x ≤ n) (hz : par B M (par B M x) ≤ n)
    (hb : (if lc B M (par B M x) = x then rc B M x else lc B M x) ≤ n) :
    MemFrame B n M (rotMem B n x M) := by
  refine (MemFrame.trans B n ?_ (recomp_frame B n hy)).trans B n (recomp_frame B n hx)
  intro a ha
  simp only [rotP]
  refine ⟨?_, ?_⟩
  · unfold adr at *; split_ifs at hb ⊢ <;> simp only [upd_apply] <;>
      split_ifs <;> first | rfl | omega
  · simp only [upd_apply]; unfold adr at *; split_ifs at hb ⊢ <;> first | rfl | omega

lemma rotMem_agrC {u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x) (h4 : u ≠ par B M (par B M x)) :
    AgrC B M (rotMem B n x M) u := by
  intro j hj
  have e1 := recomp_agr B n (M := recomp B n (par B M x) (rotP B x M)) (u := x) h1 j hj
  have e2 := recomp_agr B n (M := rotP B x M) (u := par B M x) h2 j hj
  refine ⟨fun h0 => ?_, fun h0 h6 => ?_⟩
  · rw [rotMem, e1.1, e2.1]; simp only [rotP]; split_ifs <;> simp_all [upd_adr _ _ hj]
  · rw [rotMem, e1.2, e2.2]; simp only [rotP]; simp_all [upd_adr _ _ hj]

lemma rotMem_agrS {u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x)
    (h3 : u ≠ (if lc B M (par B M x) = x then rc B M x else lc B M x)) :
    AgrS B M (rotMem B n x M) u ∧ par B (rotMem B n x M) u = par B M u := by
  have e1 := recomp_agr B n (M := recomp B n (par B M x) (rotP B x M)) (u := x) h1
  have e2 := recomp_agr B n (M := rotP B x M) (u := par B M x) h2
  have kN : ∀ j < 16, j ≠ 1 → j ≠ 2 → (rotMem B n x M).nm (adr B u j) = M.nm (adr B u j) := by
    intro j hj h1' h2'
    rw [rotMem, (e1 j hj).1, (e2 j hj).1]; simp only [rotP]; split_ifs <;> simp_all [upd_adr _ _ hj]
  have kR : ∀ j < 16, (rotMem B n x M).rm (adr B u j) = M.rm (adr B u j) := by
    intro j hj
    rw [rotMem, (e1 j hj).2, (e2 j hj).2]; simp only [rotP]; simp_all [upd_adr _ _ hj]
  have hown : own B (rotMem B n x M) u = own B M u := (rotMem_agg (n := n) h1 h2).1
  exact ⟨⟨hown, kN 4 (by omega) (by omega) (by omega), kR 0 (by omega), kR 1 (by omega),
    kR 5 (by omega), kR 6 (by omega), (rotMem_rv u)⟩, kN 0 (by omega) (by omega) (by omega)⟩

lemma rotMem_fpar (u : ℕ) : fpar B (rotMem B n x M) u = fpar B M u := by
  simp only [fpar, rotMem]
  rw [recomp_nm B n (by omega) (by omega), recomp_nm B n (by omega) (by omega),
    rotP_nm (by omega) (by omega)]

lemma rotMem_vl (u : ℕ) : vl B (rotMem B n x M) u = vl B M u ∧ vl2 B (rotMem B n x M) u = vl2 B M u := by
  simp only [vl, vl2, rotMem]
  rw [recomp_rm B n (by omega) (by omega), recomp_rm B n (by omega) (by omega),
    recomp_rm B n (by omega) (by omega), recomp_rm B n (by omega) (by omega),
    rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)]
  exact ⟨rfl, rfl⟩

end fields


/-! ### The fields of the rotated nodes -/

section rotfields
variable {B n} {M : Mem} {x y z bb : ℕ}

/-- The pointers and tags after the rotation of a left child `x` of `y`. -/
lemma rotP_L (hyx : par B M x = y) (hzy : par B M y = z) (hlc : lc B M y = x)
    (hrx : rc B M x = bb) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hbx : bb ≠ x)
    (hby : bb ≠ y) :
    par B (rotP B x M) x = z ∧ lc B (rotP B x M) x = lc B M x ∧ rc B (rotP B x M) x = y ∧
    par B (rotP B x M) y = x ∧ lc B (rotP B x M) y = bb ∧ rc B (rotP B x M) y = rc B M y ∧
    par B (rotP B x M) bb = y ∧ tg B (rotP B x M) x = tg B M x + tg B M y ∧
    tg B (rotP B x M) y = - tg B M x ∧ tg B (rotP B x M) bb = tg B M bb + tg B M x ∧
    lc B (rotP B x M) z = (if lc B M z = y then x else lc B M z) ∧
    rc B (rotP B x M) z = (if lc B M z = y then rc B M z else if rc B M z = y then x else
      rc B M z) ∧
    tg2 B (rotP B x M) x = tg2 B M x + tg2 B M y ∧
    tg2 B (rotP B x M) y = - tg2 B M x ∧ tg2 B (rotP B x M) bb = tg2 B M bb + tg2 B M x := by
  have h1 := hxy.symm; have h2 := hxz.symm; have h3 := hyz.symm; have h4 := hbx.symm
  have h5 := hby.symm
  by_cases c1 : lc B M z = y <;> by_cases c2 : rc B M z = y <;>
  simp only [rotP, hyx, hzy, hlc, ite_true, hrx, c1, c2, ite_true, ite_false] <;>
  simp only [par, lc, rc, tg, tg2] at * <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd_adr]

/-- The pointers and tags after the rotation of a right child `x` of `y`. -/
lemma rotP_R (hyx : par B M x = y) (hzy : par B M y = z) (hlc : lc B M y ≠ x)
    (hlx : lc B M x = bb) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hbx : bb ≠ x)
    (hby : bb ≠ y) :
    par B (rotP B x M) x = z ∧ lc B (rotP B x M) x = y ∧ rc B (rotP B x M) x = rc B M x ∧
    par B (rotP B x M) y = x ∧ lc B (rotP B x M) y = lc B M y ∧ rc B (rotP B x M) y = bb ∧
    par B (rotP B x M) bb = y ∧ tg B (rotP B x M) x = tg B M x + tg B M y ∧
    tg B (rotP B x M) y = - tg B M x ∧ tg B (rotP B x M) bb = tg B M bb + tg B M x ∧
    lc B (rotP B x M) z = (if lc B M z = y then x else lc B M z) ∧
    rc B (rotP B x M) z = (if lc B M z = y then rc B M z else if rc B M z = y then x else
      rc B M z) ∧
    tg2 B (rotP B x M) x = tg2 B M x + tg2 B M y ∧
    tg2 B (rotP B x M) y = - tg2 B M x ∧ tg2 B (rotP B x M) bb = tg2 B M bb + tg2 B M x := by
  have h1 := hxy.symm; have h2 := hxz.symm; have h3 := hyz.symm; have h4 := hbx.symm
  have h5 := hby.symm
  by_cases c1 : lc B M z = y <;> by_cases c2 : rc B M z = y <;>
  simp only [rotP, hyx, hzy, hlc, ite_false, hlx, c1, c2, ite_true, ite_false] <;>
  simp only [par, lc, rc, tg, tg2] at * <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [upd_adr]

end rotfields

/-! ### The rotation of a left child -/

lemma count_LL (a b c : VT) (x y : ℕ) (dx dy : List VT) (w : ℕ) :
    (nodes (node (node a x b dx) y c dy)).count w = (nodes a).count w + [x].count w +
      (nodes b).count w + (nodesL dx).count w + [y].count w + (nodes c).count w +
      (nodesL dy).count w := by
  simp only [nodes_node, List.append_assoc, List.cons_append, List.count_append, List.count_cons,
    List.count_nil]
  omega

end DynTree

end PlanarFlow
