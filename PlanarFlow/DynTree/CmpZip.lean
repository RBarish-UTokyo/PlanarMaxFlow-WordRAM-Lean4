module

public import PlanarFlow.DynTree.CmpRec
public import PlanarFlow.DynTree.Ops

/-!
# Dynamic trees: the compared values of a rotation are differences of true values

The stored values of an auxiliary tree are relative to the tags above its root (`rs`); for the
root of a tree of the virtual forest, and for the root of a hanging tree, they are the true
values of the forest (`RepE`). So the values of the subtree at the hole of a stored zipper,
shifted by one number (the tags above the hole), are true values:

* `zip_vals`: the values at the hole of a zipper, shifted by some `O`, are values of the whole
  tree or of its hanging trees; `zip_bound`: in a stored virtual forest whose forest has values of
  absolute value at most `V` (`VBnd`), the shifted values at the hole are at most `V`.
* `minA_mem`: the minimum that the parent reads of a stored subtree is one of its values.
* **`rotNear_zip`**: under the hypotheses of the rotation theorem `rotate_okE` (a stored zipper,
  the reversal bits of `x` and of its parent clear), the recomputations of the rotation of `x`
  compare near values (`RotNear`), shifted values of absolute value at most `V`.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

/-- The values of the forest are at most `V` in absolute value (both channels). -/
def VBnd (V : ℝ) (n : ℕ) (F : Forest) : Prop := ∀ u < n, |F.val u| ≤ V ∧ |F.val2 u| ≤ V

section vals
variable {B n : ℕ}

lemma rs_node_mem_root (M : Mem) (l r : VT) (x : ℕ) (ds : List VT) (π k : Bool) :
    (x, vlc B M (k ^^ π) x + tgc B M (k ^^ π) x) ∈ rs B M (node l x r ds) π k := by
  rw [rs_node]; simp only [shift]
  exact List.mem_map.mpr ⟨(x, vlc B M (k ^^ π) x), by simp, rfl⟩

lemma rs_node_mem_l {M : Mem} {l r : VT} {x : ℕ} {ds : List VT} {π k : Bool} {e : ℕ × ℝ}
    (h : e ∈ rs B M l (cσ B M π x) k) :
    (e.1, e.2 + tgc B M (k ^^ π) x) ∈ rs B M (node l x r ds) π k := by
  rw [rs_node]; simp only [shift]
  exact List.mem_map.mpr ⟨e, by simp [h], rfl⟩

lemma rs_node_mem_r {M : Mem} {l r : VT} {x : ℕ} {ds : List VT} {π k : Bool} {e : ℕ × ℝ}
    (h : e ∈ rs B M r (cσ B M π x) k) :
    (e.1, e.2 + tgc B M (k ^^ π) x) ∈ rs B M (node l x r ds) π k := by
  rw [rs_node]; simp only [shift]
  exact List.mem_map.mpr ⟨e, by simp [h], rfl⟩

lemma dV_plug_mono {M : Mem} {k : Bool} {e : ℕ × ℝ} :
    ∀ (fs : List Frame) (s : VT), e ∈ dV B M s k → e ∈ dV B M (plug s fs) k
  | [], _, h => h
  | f :: fs, s, h => by
    refine dV_plug_mono fs (f.plug s) ?_
    cases f <;> simp only [Frame.plug, dV_node, dVL_append, dVL_cons, List.mem_append] <;>
      simp [h]

/-- **The values at the hole of a zipper**, shifted by one number, are values of the whole
tree (read with parity `false`) or of its hanging trees. -/
theorem zip_vals (M : Mem) (k : Bool) : ∀ (fs : List Frame) (t : VT), ∃ O : ℝ,
    ∀ e ∈ rs B M t (cpar B M fs) k,
      (e.1, e.2 + O) ∈ rs B M (plug t fs) false k ∨ (e.1, e.2 + O) ∈ dV B M (plug t fs) k
  | [], t => ⟨0, fun e he => Or.inl (by simpa [cpar, plug] using he)⟩
  | f :: fs, t => by
    obtain ⟨O', hO'⟩ := zip_vals M k fs (f.plug t)
    cases f with
    | L y r ds =>
      refine ⟨tgc B M (k ^^ cpar B M fs) y + O', fun e he => ?_⟩
      have := hO' _ (rs_node_mem_l (r := r) (ds := ds) (π := cpar B M fs) (x := y) he)
      rw [add_assoc] at this; exact this
    | R l y ds =>
      refine ⟨tgc B M (k ^^ cpar B M fs) y + O', fun e he => ?_⟩
      have := hO' _ (rs_node_mem_r (l := l) (ds := ds) (π := cpar B M fs) (x := y) he)
      rw [add_assoc] at this; exact this
    | D l y r bef aft =>
      refine ⟨0, fun e he => Or.inr ?_⟩
      refine dV_plug_mono fs _ ?_
      simp only [cpar, hpar] at he
      simp [Frame.plug, he]

/-- The values of a stored virtual forest representing `F` are values of `F`. -/
lemma rep_val_bound {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {k : Bool} {e : ℕ × ℝ} (he : e ∈ dVL B M G k) :
    |e.2| ≤ V := by
  obtain ⟨u, w⟩ := e
  have hu : u < n := (hI.cover u).mp (dVL_fst B G he)
  cases k
  · rw [← hR.val u w he]; exact (hV u hu).1
  · rw [← hR.val2 u w he]; exact (hV u hu).2

/-- **The values at the hole of a stored zipper**, shifted by one number, are at most `V`. -/
theorem zip_bound {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {gb ga : List VT} {t : VT} {fs : List Frame}
    (hG : G = gb ++ plug t fs :: ga) (k : Bool) :
    ∃ O : ℝ, ∀ e ∈ rs B M t (cpar B M fs) k, |e.2 + O| ≤ V := by
  obtain ⟨O, hO⟩ := zip_vals M k fs t
  refine ⟨O, fun e he => ?_⟩
  have h : (e.1, e.2 + O) ∈ dVL B M G k := by
    rw [hG]
    rcases hO e he with h | h <;> simp [h]
  exact rep_val_bound hI hR hV h

/-- The minimum that the parent reads of a stored subtree is one of its values. -/
lemma minA_mem {M : Mem} (hN : NilOK B n M) {a : VT} {p : ℕ} (h : Enc B n M a p false)
    (hlt : ∀ u ∈ nodes a, u < n) (ha : rt n a < n) :
    (∃ e ∈ rs B M a false false, e.2 = minA B M (rt n a)) ∧
      (∃ e ∈ rs B M a false true, e.2 = minA2 B M (rt n a)) := by
  have hc := (Enc.agg B n hN h hlt).2 ha
  have hne : a ≠ leaf := by rintro rfl; simp at ha
  obtain ⟨h1, -⟩ := lmin_spec ((rs_ne_nil M false false).mpr hne)
  obtain ⟨h2, -⟩ := lmin_spec ((rs_ne_nil M false true).mpr hne)
  have e1 : minA B M (rt n a) = (lmin (rs B M a false false)).1 := congrArg Ag.m1 hc
  have e2 : minA2 B M (rt n a) = (lmin (rs B M a false true)).1 := congrArg Ag.m2 hc
  obtain ⟨q, hq, hq'⟩ := List.mem_map.mp h1
  obtain ⟨q', hq2, hq2'⟩ := List.mem_map.mp h2
  exact ⟨⟨q, hq, hq'.trans e1.symm⟩, ⟨q', hq2, hq2'.trans e2.symm⟩⟩

end vals

/-! ### The rotation -/

section rotz
variable {B n : ℕ}

/-- The nodes of a subtree are distinct from a node outside it, and its root (or `n`). -/
lemma rt_ne_of_count {s : VT} {L : List ℕ} {v : ℕ} (hv : v ∈ L) (hvn : v < n)
    (h : ∀ w, (nodes s).count w + L.count w ≤ 1) : rt n s ≠ v := by
  rcases rt_or_nil n s with ⟨-, h'⟩ | h'
  · omega
  · exact ne_of_count h h' hv

lemma rt_ne_rt_of_count {s s' : VT} (h : ∀ w, (nodes s).count w + (nodes s').count w ≤ 1)
    (hs : rt n s < n) : rt n s ≠ rt n s' := by
  rcases rt_or_nil n s' with ⟨-, h'⟩ | h'
  · omega
  · rcases rt_or_nil n s with ⟨-, h''⟩ | h''
    · omega
    · exact ne_of_count h h'' h'

/-- The rotation with parity `false`, a left child. -/
lemma rotNear_L {M : Mem} (hN : NilOK B n M) {a b c : VT} {x y z : ℕ} {dx dy : List VT}
    (hsE : Enc B n M (node (node a x b dx) y c dy) z false) (hvx : rv B M x = false)
    (hvy : rv B M y = false) (hnd : (nodes (node (node a x b dx) y c dy)).Nodup)
    (hlts : ∀ u ∈ nodes (node (node a x b dx) y c dy), u < n)
    (hzs : ∀ u ∈ nodes (node (node a x b dx) y c dy), u ≠ z) {V : ℝ} {O : Bool → ℝ}
    (hO : ∀ k, ∀ e ∈ rs B M (node (node a x b dx) y c dy) false k, |e.2 + O k| ≤ V) :
    RotNear B n V M x := by
  have K : ∀ w, (nodes a).count w + [x].count w + (nodes b).count w + (nodesL dx).count w +
      [y].count w + (nodes c).count w + (nodesL dy).count w ≤ 1 := fun w => by
    have := List.nodup_iff_count_le_one.mp hnd w; rw [count_LL] at this; omega
  rw [enc_node_iff_clean B n hvy] at hsE
  obtain ⟨hzy, hlc, hrc, -, hxE, hcE, -⟩ := hsE
  rw [enc_node_iff_clean B n hvx] at hxE
  obtain ⟨hyx, hla, hrx, -, haE, hbE, -⟩ := hxE
  simp only [rt_node] at hlc
  have hσy : cσ B M false y = false := by simp [cσ, hvy]
  have hσx : cσ B M false x = false := by simp [cσ, hvx]
  have mX : ∀ k, ∀ e ∈ rs B M (node a x b dx) false k,
      |e.2 + tgc B M k y + O k| ≤ V := fun k e he => by
    have := hO k _ (rs_node_mem_l (r := c) (ds := dy) (x := y) (π := false) (hσy ▸ he))
    simpa only [Bool.xor_false] using this
  have mC : ∀ k, ∀ e ∈ rs B M c false k, |e.2 + tgc B M k y + O k| ≤ V := fun k e he => by
    have := hO k _ (rs_node_mem_r (l := node a x b dx) (ds := dy) (x := y) (π := false) (hσy ▸ he))
    simpa only [Bool.xor_false] using this
  have mY : ∀ k, |vlc B M k y + tgc B M k y + O k| ≤ V := fun k => by
    have := hO k _ (rs_node_mem_root M (node a x b dx) c y dy false k)
    simpa only [Bool.xor_false] using this
  have mXX : ∀ k, |vlc B M k x + tgc B M k x + tgc B M k y + O k| ≤ V := fun k => by
    have := mX k _ (rs_node_mem_root M a b x dx false k)
    simpa only [Bool.xor_false] using this
  have mA : ∀ k, ∀ e ∈ rs B M a false k, |e.2 + tgc B M k x + tgc B M k y + O k| ≤ V :=
    fun k e he => by
      have := mX k _ (rs_node_mem_l (r := b) (ds := dx) (x := x) (π := false) (hσx ▸ he))
      simpa only [Bool.xor_false] using this
  have mB : ∀ k, ∀ e ∈ rs B M b false k, |e.2 + tgc B M k x + tgc B M k y + O k| ≤ V :=
    fun k e he => by
      have := mX k _ (rs_node_mem_r (l := a) (ds := dx) (x := x) (π := false) (hσx ▸ he))
      simpa only [Bool.xor_false] using this
  have hlt : ∀ s : VT, (∀ u ∈ nodes s, u ∈ nodes (node (node a x b dx) y c dy)) →
      ∀ u ∈ nodes s, u < n := fun s hs u hu => hlts u (hs u hu)
  have sa : ∀ u ∈ nodes a, u ∈ nodes (node (node a x b dx) y c dy) := fun u hu => by simp [hu]
  have sb : ∀ u ∈ nodes b, u ∈ nodes (node (node a x b dx) y c dy) := fun u hu => by simp [hu]
  have sc : ∀ u ∈ nodes c, u ∈ nodes (node (node a x b dx) y c dy) := fun u hu => by simp [hu]
  have N : NearRot (B := B) (n := n) V M x y (rt n a) (rt n b) (rt n c) (O false) (O true) := by
    refine ⟨mY false, mY true, mXX false, mXX true, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN haE (hlt a sa) h
      have := mA false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN haE (hlt a sa) h
      have := mA true e he; rw [hev] at this; exact this
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN hbE (hlt b sb) h
      have := mB false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN hbE (hlt b sb) h
      have := mB true e he; rw [hev] at this; exact this
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN hcE (hlt c sc) h
      have := mC false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN hcE (hlt c sc) h
      have := mC true e he; rw [hev] at this; exact this
  have hxn : x < n := hlts x (by simp)
  have hyn : y < n := hlts y (by simp)
  have hxy : x ≠ y := ne_of_count (A := [x]) (C := [y]) (fun w => by have := K w; omega)
    (by simp) (by simp)
  refine rotNear_of_L N hyx hlc hla hrx hrc hxy (hzy ▸ hzs x (by simp)) (hzy ▸ hzs y (by simp))
    (rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega))
    (rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega))
    (fun h => ⟨rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega),
      rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega),
      rt_ne_rt_of_count (fun w => by have := K w; omega) h⟩)
    (fun h => ⟨rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega),
      rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega),
      rt_ne_rt_of_count (fun w => by have := K w; omega) h⟩)

/-- The rotation with parity `false`, a right child. -/
lemma rotNear_R {M : Mem} (hN : NilOK B n M) {a b c : VT} {x y z : ℕ} {dx dy : List VT}
    (hsE : Enc B n M (node c y (node a x b dx) dy) z false) (hvx : rv B M x = false)
    (hvy : rv B M y = false) (hnd : (nodes (node c y (node a x b dx) dy)).Nodup)
    (hlts : ∀ u ∈ nodes (node c y (node a x b dx) dy), u < n)
    (hzs : ∀ u ∈ nodes (node c y (node a x b dx) dy), u ≠ z) {V : ℝ} {O : Bool → ℝ}
    (hO : ∀ k, ∀ e ∈ rs B M (node c y (node a x b dx) dy) false k, |e.2 + O k| ≤ V) :
    RotNear B n V M x := by
  have K : ∀ w, (nodes a).count w + [x].count w + (nodes b).count w + (nodesL dx).count w +
      [y].count w + (nodes c).count w + (nodesL dy).count w ≤ 1 := fun w => by
    have := List.nodup_iff_count_le_one.mp hnd w; rw [count_RR] at this; omega
  rw [enc_node_iff_clean B n hvy] at hsE
  obtain ⟨hzy, hlc, hrc, -, hcE, hxE, -⟩ := hsE
  rw [enc_node_iff_clean B n hvx] at hxE
  obtain ⟨hyx, hla, hrx, -, haE, hbE, -⟩ := hxE
  simp only [rt_node] at hrc
  have hσy : cσ B M false y = false := by simp [cσ, hvy]
  have hσx : cσ B M false x = false := by simp [cσ, hvx]
  have mX : ∀ k, ∀ e ∈ rs B M (node a x b dx) false k,
      |e.2 + tgc B M k y + O k| ≤ V := fun k e he => by
    have := hO k _ (rs_node_mem_r (l := c) (ds := dy) (x := y) (π := false) (hσy ▸ he))
    simpa only [Bool.xor_false] using this
  have mC : ∀ k, ∀ e ∈ rs B M c false k, |e.2 + tgc B M k y + O k| ≤ V := fun k e he => by
    have := hO k _ (rs_node_mem_l (r := node a x b dx) (ds := dy) (x := y) (π := false) (hσy ▸ he))
    simpa only [Bool.xor_false] using this
  have mY : ∀ k, |vlc B M k y + tgc B M k y + O k| ≤ V := fun k => by
    have := hO k _ (rs_node_mem_root M c (node a x b dx) y dy false k)
    simpa only [Bool.xor_false] using this
  have mXX : ∀ k, |vlc B M k x + tgc B M k x + tgc B M k y + O k| ≤ V := fun k => by
    have := mX k _ (rs_node_mem_root M a b x dx false k)
    simpa only [Bool.xor_false] using this
  have mA : ∀ k, ∀ e ∈ rs B M a false k, |e.2 + tgc B M k x + tgc B M k y + O k| ≤ V :=
    fun k e he => by
      have := mX k _ (rs_node_mem_l (r := b) (ds := dx) (x := x) (π := false) (hσx ▸ he))
      simpa only [Bool.xor_false] using this
  have mB : ∀ k, ∀ e ∈ rs B M b false k, |e.2 + tgc B M k x + tgc B M k y + O k| ≤ V :=
    fun k e he => by
      have := mX k _ (rs_node_mem_r (l := a) (ds := dx) (x := x) (π := false) (hσx ▸ he))
      simpa only [Bool.xor_false] using this
  have hlt : ∀ s : VT, (∀ u ∈ nodes s, u ∈ nodes (node c y (node a x b dx) dy)) →
      ∀ u ∈ nodes s, u < n := fun s hs u hu => hlts u (hs u hu)
  have sa : ∀ u ∈ nodes a, u ∈ nodes (node c y (node a x b dx) dy) := fun u hu => by simp [hu]
  have sb : ∀ u ∈ nodes b, u ∈ nodes (node c y (node a x b dx) dy) := fun u hu => by simp [hu]
  have sc : ∀ u ∈ nodes c, u ∈ nodes (node c y (node a x b dx) dy) := fun u hu => by simp [hu]
  have N : NearRot (B := B) (n := n) V M x y (rt n b) (rt n a) (rt n c) (O false) (O true) := by
    refine ⟨mY false, mY true, mXX false, mXX true, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN hbE (hlt b sb) h
      have := mB false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN hbE (hlt b sb) h
      have := mB true e he; rw [hev] at this; exact this
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN haE (hlt a sa) h
      have := mA false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN haE (hlt a sa) h
      have := mA true e he; rw [hev] at this; exact this
    · obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hN hcE (hlt c sc) h
      have := mC false e he; rw [hev] at this; exact this
    · obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hN hcE (hlt c sc) h
      have := mC true e he; rw [hev] at this; exact this
  have hxn : x < n := hlts x (by simp)
  have hyn : y < n := hlts y (by simp)
  have hxy : x ≠ y := ne_of_count (A := [x]) (C := [y]) (fun w => by have := K w; omega)
    (by simp) (by simp)
  refine rotNear_of_R N hyx hlc
    (rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega))
    hrx hla hxy (hzy ▸ hzs x (by simp)) (hzy ▸ hzs y (by simp))
    (rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega))
    (rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega))
    (fun h => ⟨rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega),
      rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega),
      rt_ne_rt_of_count (fun w => by have := K w; omega) h⟩)
    (fun h => ⟨rt_ne_of_count (List.mem_singleton_self x) hxn (fun w => by have := K w; omega),
      rt_ne_of_count (List.mem_singleton_self y) hyn (fun w => by have := K w; omega),
      rt_ne_rt_of_count (fun w => by have := K w; omega) h⟩)

/-- The rotation of a stored subtree with any parity. -/
theorem rotNear_local {M : Mem} (hN : NilOK B n M) {t : VT} {f : Frame} (ht : t ≠ VT.leaf)
    (hf : f.Solid) {z : ℕ} {π : Bool} (hsE : Enc B n M (f.plug t) z π)
    (hvx : rv B M (rt n t) = false) (hvy : rv B M f.y = false)
    (hnd : (nodes (f.plug t)).Nodup) (hlts : ∀ u ∈ nodes (f.plug t), u < n)
    (hzs : ∀ u ∈ nodes (f.plug t), u ≠ z) {V : ℝ} {O : Bool → ℝ}
    (hO : ∀ k, ∀ e ∈ rs B M (f.plug t) π k, |e.2 + O k| ≤ V) :
    RotNear B n V M (rt n t) := by
  have P0 : ∀ {t : VT} {f : Frame} {O : Bool → ℝ}, t ≠ VT.leaf → f.Solid →
      Enc B n M (f.plug t) z false → rv B M (rt n t) = false → rv B M f.y = false →
      (nodes (f.plug t)).Nodup → (∀ u ∈ nodes (f.plug t), u < n) →
      (∀ u ∈ nodes (f.plug t), u ≠ z) →
      (∀ k, ∀ e ∈ rs B M (f.plug t) false k, |e.2 + O k| ≤ V) → RotNear B n V M (rt n t) := by
    intro t f O ht hf hsE hvx hvy hnd hlts hzs hO
    obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
      cases t with
      | leaf => exact absurd rfl ht
      | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
    rcases frame_solid_cases hf with ⟨y, c, dy, rfl⟩ | ⟨c, y, dy, rfl⟩
    · exact rotNear_L hN hsE hvx hvy hnd hlts hzs hO
    · exact rotNear_R hN hsE hvx hvy hnd hlts hzs hO
  cases π with
  | false => exact P0 ht hf hsE hvx hvy hnd hlts hzs hO
  | true =>
    have hperm := nodes_mirT (f.plug t)
    rw [mirT_plugF hf] at hperm
    have hE0 : Enc B n M ((mirF f).plug (mirT t)) z false := by
      rw [← mirT_plugF hf]; exact (enc_mirror_iff B n).mpr hsE
    have := P0 (t := mirT t) (f := mirF f) (O := fun k => O (!k))
      (by rwa [Ne, mirT_eq_leaf]) (mirF_solid.mpr hf) hE0 (by rw [rt_mirT]; exact hvx)
      (by rw [mirF_y]; exact hvy) (hperm.nodup_iff.mpr hnd)
      (fun u hu => hlts u (hperm.mem_iff.mp hu)) (fun u hu => hzs u (hperm.mem_iff.mp hu))
      (fun k e he => by
        rw [← mirT_plugF hf, rs_mirT, List.mem_reverse] at he
        exact hO (!k) e he)
    rwa [rt_mirT] at this

/-- **The rotation compares near values**, under the hypotheses of the rotation theorem
`rotate_okE`, when the values of the forest are at most `V`. -/
theorem rotNear_zip {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {gb ga : List VT} {t : VT} {f : Frame}
    {fs : List Frame} (hG : G = gb ++ plug t (f :: fs) :: ga) (hf : f.Solid) (ht : t ≠ VT.leaf)
    (hvx : rv B M (rt n t) = false) (hvy : rv B M f.y = false) :
    RotNear B n V M (rt n t) := by
  have hG' : G = gb ++ plug (f.plug t) fs :: ga := hG
  have hX := rotCtx B n hI hG'
  have hzs := hX.z_out
  obtain ⟨hsE, -, hcount, hlts, -, -⟩ := hX
  have hnd : (nodes (f.plug t)).Nodup :=
    List.nodup_iff_count_le_one.mpr fun w => by have := hcount w; omega
  obtain ⟨O0, h0⟩ := zip_bound hI hR hV hG' false
  obtain ⟨O1, h1⟩ := zip_bound hI hR hV hG' true
  exact rotNear_local hI.nil ht hf hsE hvx hvy hnd hlts hzs (O := fun k => if k then O1 else O0)
    (fun k => by cases k with | false => exact h0 | true => exact h1)

end rotz

end DynTree

end PlanarFlow
