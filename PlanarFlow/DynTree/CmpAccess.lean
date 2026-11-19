module

public import PlanarFlow.DynTree.CmpSplay
public import PlanarFlow.DynTree.AccessCode

/-!
# Dynamic trees: bounded real comparisons in the switch and the access

* `switchNear_okE`: under the hypotheses of `switchR_okE` (the root `w` of an auxiliary tree, a
  hanging tree `Y` or none), the recomputation of `w` after the switch compares near values: the
  stored values of `w` and of its left child are relative to the tag of `w` only, and the new
  right child `Y` had true values, its tag being decreased by the tag of `w`.
* **`switchS_cmpOK`**, **`accessS_cmpOK`**: every run of the switch, of the access compares
  numbers at distance at most `2 V`, when the forest has values at most `V`.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

section ghost
variable {B n : ℕ}

/-- The values of an auxiliary tree at the root of a stored zipper are true values. -/
lemma root_vals {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {gb ga : List VT} {t : VT} {fs : List Frame}
    (hG : G = gb ++ plug t fs :: ga) (hfs : ¬ HeadSolid fs) (k : Bool) :
    (∀ e ∈ rs B M t false k, |e.2| ≤ V) ∧ (∀ e ∈ dV B M t k, |e.2| ≤ V) := by
  have hin : ∀ e, (e ∈ rs B M (plug t fs) false k ∨ e ∈ dV B M (plug t fs) k) →
      |e.2| ≤ V := by
    intro e he
    refine rep_val_bound hI hR hV (k := k) ?_
    rw [hG]; rcases he with h | h <;> simp [h]
  refine ⟨fun e he => hin e ?_, fun e he => hin e (Or.inr (dV_plug_mono fs t he))⟩
  rcases fs with _ | ⟨f, fs⟩
  · exact Or.inl he
  · cases f with
    | L => exact absurd trivial hfs
    | R => exact absurd trivial hfs
    | D l y r bef aft =>
      refine Or.inr (dV_plug_mono fs _ ?_)
      simp [Frame.plug, he]

lemma switchP_tg_y {M : Mem} {w y : ℕ} :
    tg B (switchP B w y M) y = tg B M y - tg B M w ∧
      tg2 B (switchP B w y M) y = tg2 B M y - tg2 B M w := by
  constructor <;> simp [tg, tg2, switchP, upd_adr]

/-- **The recomputation after the switch compares near values.** -/
theorem switchNear_okE {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {gb ga : List VT} {l r Y : VT} {w : ℕ}
    {bef Ys aft : List VT} {fs : List Frame} (hYs : Ys = [Y] ∨ (Ys = [] ∧ Y = VT.leaf))
    (hG : G = gb ++ plug (node l w r (bef ++ Ys ++ aft)) fs :: ga) (hfs : ¬ HeadSolid fs)
    (hvw : rv B M w = false) :
    RecNear B n V (switchP B w (rt n Y) M) w := by
  have hX := rotCtx B n hI hG
  obtain ⟨hsE, -, hcount, hlts, -, -⟩ := hX
  have K : ∀ w', (nodes l).count w' + [w].count w' + (nodes r).count w' +
      (nodesL bef).count w' + (nodes Y).count w' + (nodesL aft).count w' ≤ 1 := fun w' => by
    have := hcount w'
    rcases hYs with rfl | ⟨rfl, rfl⟩ <;>
    simp only [nodes_node, nodesL_append, nodesL_cons, nodesL_nil, List.count_append,
      List.count_cons, List.count_nil, nodes_leaf] at this ⊢ <;> omega
  rw [cpar_of_not_headSolid B hfs, enc_node_iff_clean B n hvw] at hsE
  obtain ⟨-, hlw, hrw, -, hlE, -, hdE⟩ := hsE
  have hwn : w < n := hlts w (by simp)
  have hσ : cσ B M false w = false := by simp [cσ, hvw]
  have mW : ∀ k, |vlc B M k w + tgc B M k w| ≤ V := fun k => by
    have := (root_vals hI hR hV hG hfs k).1 _ (rs_node_mem_root M l r w _ false k)
    simpa only [Bool.xor_false] using this
  have mL : ∀ k, ∀ e ∈ rs B M l false k, |e.2 + tgc B M k w| ≤ V := fun k e he => by
    have := (root_vals hI hR hV hG hfs k).1 _
      (rs_node_mem_l (r := r) (ds := bef ++ Ys ++ aft) (x := w) (π := false) (hσ ▸ he))
    simpa only [Bool.xor_false] using this
  have hlt : ∀ s : VT, (∀ u ∈ nodes s, u ∈ nodes (node l w r (bef ++ Ys ++ aft))) →
      ∀ u ∈ nodes s, u < n := fun s hs u hu => hlts u (hs u hu)
  have hwr : w ≠ rc B M w := by
    rw [hrw]; exact (rt_ne_of_count (List.mem_singleton_self w) hwn
      (fun x => by have := K x; omega)).symm
  have hwY : w ≠ rt n Y :=
    (rt_ne_of_count (List.mem_singleton_self w) hwn (fun x => by have := K x; omega)).symm
  have hlc' : lc B (switchP B w (rt n Y) M) w = rt n l := by
    simp only [lc]; rw [switchP_nm (by omega)]; simp; exact hlw
  have hrc' : rc B (switchP B w (rt n Y) M) w = rt n Y := by
    simp only [rc]; rw [switchP_nm (by omega)]; simp
  have kv : ∀ j < 16, j = 0 ∨ j = 5 →
      (switchP B w (rt n Y) M).rm (adr B w j) = M.rm (adr B w j) :=
    fun j hj _ => switchP_rm hj hwY hwr
  obtain ⟨ty1, ty2⟩ := switchP_tg_y (B := B) (M := M) (w := w) (y := rt n Y)
  refine ⟨tg B M w, tg2 B M w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [vl]; rw [kv 0 (by omega) (Or.inl rfl)]; exact mW false
  · simp only [vl2]; rw [kv 5 (by omega) (Or.inr rfl)]; exact mW true
  · rw [hlc']; intro h
    have hlY : rt n l ≠ rt n Y := rt_ne_rt_of_count (fun x => by have := K x; omega) h
    have hlr : rt n l ≠ rc B M w := by
      rw [hrw]; exact rt_ne_rt_of_count (fun x => by have := K x; omega) h
    obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hI.nil hlE (hlt l (fun u hu => by simp [hu])) h
    have := mL false e he; rw [hev] at this
    simp only [minA, mn, tg] at this ⊢
    rw [switchP_rm (by omega) hlY hlr, switchP_rm (by omega) hlY hlr]; exact this
  · rw [hlc']; intro h
    have hlY : rt n l ≠ rt n Y := rt_ne_rt_of_count (fun x => by have := K x; omega) h
    have hlr : rt n l ≠ rc B M w := by
      rw [hrw]; exact rt_ne_rt_of_count (fun x => by have := K x; omega) h
    obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hI.nil hlE (hlt l (fun u hu => by simp [hu])) h
    have := mL true e he; rw [hev] at this
    simp only [minA2, mn2, tg2] at this ⊢
    rw [switchP_rm (by omega) hlY hlr, switchP_rm (by omega) hlY hlr]; exact this
  · rw [hrc']; intro h
    rcases hYs with rfl | ⟨-, rfl⟩
    · have hYE : Enc B n M Y w false := hdE Y (by simp)
      obtain ⟨⟨e, he, hev⟩, -⟩ := minA_mem hI.nil hYE (hlt Y (fun u hu => by simp [hu])) h
      have hYr : rt n Y ≠ rc B M w := by
        rw [hrw]; exact rt_ne_rt_of_count (fun x => by have := K x; omega) h
      have := (root_vals hI hR hV hG hfs false).2 e (by simp [he])
      rw [hev] at this
      refine abs_le_of_eq' this ?_
      have e2 : mn B (switchP B w (rt n Y) M) (rt n Y) = mn B M (rt n Y) := by
        simp [mn, switchP, upd_adr]
      simp only [minA, ty1, e2]; ring
    · simp at h
  · rw [hrc']; intro h
    rcases hYs with rfl | ⟨-, rfl⟩
    · have hYE : Enc B n M Y w false := hdE Y (by simp)
      obtain ⟨-, ⟨e, he, hev⟩⟩ := minA_mem hI.nil hYE (hlt Y (fun u hu => by simp [hu])) h
      have hYr : rt n Y ≠ rc B M w := by
        rw [hrw]; exact rt_ne_rt_of_count (fun x => by have := K x; omega) h
      have := (root_vals hI hR hV hG hfs true).2 e (by simp [he])
      rw [hev] at this
      refine abs_le_of_eq' this ?_
      have e2 : mn2 B (switchP B w (rt n Y) M) (rt n Y) = mn2 B M (rt n Y) := by
        simp [mn2, switchP, upd_adr]
      simp only [minA2, ty2, e2]; ring
    · simp at h

end ghost

/-! ### The switches of the access -/

section accghost
variable (B n : ℕ)

/-- The first switch of the access (the right child of `v` hung). -/
theorem switchNear_init {M : Mem} {F : Forest} {V : ℝ} (hV : VBnd V n F) {gb ga : List VT}
    {t : VT} {ctx : List Frame}
    (hI : Inv B n M (gb ++ plug t ctx :: ga)) (hR : RepE B n M (gb ++ plug t ctx :: ga) F)
    (ht : t ≠ leaf) (hc : ¬ HeadSolid ctx) (hv : rv B M (rt n t) = false) :
    RecNear B n V (switchP B (rt n t) n M) (rt n t) := by
  obtain ⟨l, r, e⟩ := dsOf_eq n ht
  have hG : gb ++ plug t ctx :: ga =
      gb ++ plug (node l (rt n t) r ([] ++ [] ++ dsOf t)) ctx :: ga := by
    simp only [List.nil_append]; exact congrArg (fun T => gb ++ plug T ctx :: ga) e
  have := switchNear_okE hI hR hV (Y := VT.leaf) (Or.inr ⟨rfl, rfl⟩) hG hc hv
  simpa only [rt_leaf] using this

/-- The switch of an iteration of the access loop. -/
theorem switchNear_step {M1 : Mem} {F : Forest} {V : ℝ} (hV : VBnd V n F) {gb ga : List VT}
    {Y l : VT} {w : ℕ} {r : VT} {bef aft : List VT} {ctx : List Frame}
    (hI1 : Inv B n M1 (gb ++ plug (splayG (node l w r (bef ++ Y :: aft)) ctx).1
      (splayG (node l w r (bef ++ Y :: aft)) ctx).2 :: ga))
    (hR1 : RepE B n M1 (gb ++ plug (splayG (node l w r (bef ++ Y :: aft)) ctx).1
      (splayG (node l w r (bef ++ Y :: aft)) ctx).2 :: ga) F) (hw : rv B M1 w = false) :
    RecNear B n V (switchP B w (rt n Y) M1) w := by
  obtain ⟨sf, -, -, hns, -, hne, hrt, hds, -⟩ := splayG_spec (t := node l w r (bef ++ Y :: aft))
    (by simp) ctx
  generalize hS : splayG (node l w r (bef ++ Y :: aft)) ctx = S at *
  obtain ⟨W', rest⟩ := S
  simp only at hns hne hrt hds hI1 hR1 ⊢
  obtain ⟨l', r', e⟩ := dsOf_eq n hne
  rw [hrt, hds] at e
  simp only [rt_node, dsOf] at e
  have hG : gb ++ plug W' rest :: ga =
      gb ++ plug (node l' w r' (bef ++ [Y] ++ aft)) rest :: ga := by
    rw [e]; simp
  exact switchNear_okE hI1 hR1 hV (Or.inl rfl) hG hns hw

end accghost

section accmach
variable {P : Input} {W H : ℕ}

/-- **The switch compares near values.** -/
theorem switchS_cmpOK (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {w y : ℕ}
    (hw : c.nreg 160 = w) (hy : c.nreg 178 = y) (hwn : w ≤ n) (hyn : y ≤ n) {V : ℝ}
    (hH : 2 * V ≤ H) (hN : RecNear B n V (switchP B w y (pushM B w (mem c))) w) :
    ModNat.CmpOK P W H (switchS B) c := by
  obtain ⟨c0, k0, e0, hk0, m0, f0, s0⟩ := cpushS_exec (P := P) B n hc hW hb hw hwn
  unfold switchS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B 160) _) ⟨c0, k0, e0, ?_⟩
  have hw0 := e0.wb_right
  have hb0 : Bnd B n (mem c0) := m0 ▸ hb.pushM hwn
  have h160 : c0.nreg 160 = w := by rw [s0, hw]
  have h178 : c0.nreg 178 = y := by rw [f0.2.1 178 (by omega) (by omega)]; exact hy
  have h151 : c0.nreg 151 = n := by rw [(f0.1 151 (by omega)).1]; exact hn
  obtain ⟨-, lw, rw', -, -, -⟩ := hb0.get hwn
  have rw'' := rw'
  simp only [rc, mem, adr] at rw''
  generalize hR : recompS B = R
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (noTestR_block _) _) ?_
  simp only [ld, ldR, st, stR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [h160, h178]); omega)
  subst hR
  refine cmp_gen fun c1 hc1 => ?_
  have hw1 : WordsBounded W c1 := hc1 ▸ ‹WordsBounded W _›
  have m1 : mem c1 = switchP B w y (mem c0) := by
    rw [hc1]; simp only [mem, switchP]; config_simp; simp only [h160, h178]; rfl
  have f1 : Fr c0 c1 := by
    rw [hc1]
    refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · config_simp; simp (disch := omega) only [upd_ne_of]
  have r170 : c1.nreg 170 = w := by rw [hc1]; config_simp; exact h160
  have lw1 : lc B (mem c1) w ≤ n := by
    rw [m1]; simp only [lc, switchP]; rw [upd_adr _ _ (by omega) (by omega)]
    simp only [show ¬ (1 = 2) by omega, and_false, ite_false]; exact lw
  have rw1 : rc B (mem c1) w ≤ n := by
    rw [m1]; simp only [rc, switchP]; rw [upd_adr _ _ (by omega) (by omega)]; simp [hyn]
  refine recompS_cmpOK B n hw1 hW r170 (by rw [(f1.1 151 (by omega)).1]; exact h151) hwn lw1
    rw1 hH ?_
  rw [m1, m0]; exact hN

/-- One iteration of the access loop compares near values. -/
theorem accBody_cmpOK (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {v : ℕ}
    {gb ga : List VT} {c₀ : Config} {g : AccG} {c : Config} (hI : AccI B n W F v gb ga c₀ g c)
    (ht : c.nreg 191 < c.nreg 151) {V : ℝ} (hV : VBnd V n F) (hH : 2 * V ≤ H) :
    ModNat.CmpOK P W H (accBody B) c := by
  obtain ⟨Y, ctx, sp, lv, dv⟩ := g
  obtain ⟨hw, hJ, hb, h189, h151, h190, h191, hfr, hmf, hfp⟩ := hI
  simp only at hJ h190 h191
  obtain ⟨hYn, hsY, hspY⟩ := hJ.rtY_le
  have hY : Y ≠ VT.leaf := by intro h; rw [h] at hsY hspY; simp at hspY
  obtain ⟨hpar, -, -⟩ := root_facts B n hJ.inv rfl hY
  obtain ⟨l, w, r, bef, aft, ctx', rfl⟩ : ∃ l w r bef aft ctx',
      ctx = Frame.D l w r bef aft :: ctx' := by
    rcases ctx with _ | ⟨f, ctx'⟩
    · rw [h191, h151, hpar] at ht; simp [hp] at ht
    · have := hJ.top
      cases f with
      | L => exact absurd trivial this
      | R => exact absurd trivial this
      | D l w r bef aft => exact ⟨l, w, r, bef, aft, ctx', rfl⟩
  have hwn : w < n := by rw [h191, h151, hpar] at ht; exact ht
  have e1 := Exec.copyN (P := P) hw 160 191
  have hG1 : Inv B n (mem { c with nreg := upd c.nreg 160 (c.nreg 191) })
      (gb ++ plug (node l w r (bef ++ Y :: aft)) ctx' :: ga) := hJ.inv
  have hR1 : RepE B n (mem { c with nreg := upd c.nreg 160 (c.nreg 191) })
      (gb ++ plug (node l w r (bef ++ Y :: aft)) ctx' :: ga) F := hJ.rep
  unfold accBody
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  obtain ⟨c2, k2, e2, hk2, I2, R2, hb2, hmf2, hfr2, s2, hfp2⟩ := splayS_exec (P := P) B n
    e1.wb_right hW (by config_simp; exact h151) (by exact hb) hG1 hR1 (by simp)
    (by config_simp; rw [h191, hpar]; rfl)
  refine ModNat.CmpOK.seq (splayS_cmpOK B n e1.wb_right hW (by config_simp; exact h151)
    (by exact hb) hG1 hR1 (by simp) (by config_simp; rw [h191, hpar]; rfl) hV hH)
    fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  simp only [rt_node] at s2
  obtain ⟨-, -, -, -, -, hneS, hrtS, -, -⟩ :=
    splayG_spec (t := node l w r (bef ++ Y :: aft)) (by simp) ctx'
  have hrtS' : rt n (splayG (node l w r (bef ++ Y :: aft)) ctx').1 = w := (hrtS n).trans rfl
  obtain ⟨I2', R2', -, -, v2', -, -⟩ := push_okE' B n I2 R2 rfl hneS
  rw [hrtS'] at I2' R2' v2'
  have e3 := Exec.copyN (P := P) e2.wb_right 178 190
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e3, ?_⟩
  have h190' : c2'.nreg 190 = rt n Y := by
    rw [hfr2.2.1 190 (by omega) (by omega)]; config_simp; exact h190
  refine ModNat.CmpOK.seq (switchS_cmpOK B n e3.wb_right hW
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact h151) (by exact hb2)
    (w := w) (y := rt n Y) (by config_simp; exact s2) (by config_simp; exact h190') hwn.le
    hYn.le hH (switchNear_step B n hV I2' R2' v2'))
    fun _ _ _ => ModNat.cmpOK_of_noTestR (noTestR_block _) _

/-- **The access compares near values**, when the forest has values at most `V`. -/
theorem accessS_cmpOK (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {G : List VT} {F : Forest}
    (hI : Inv B n (mem c) G) (hR : RepE B n (mem c) G F) {v : ℕ} (hv : c.nreg 189 = v)
    (hvn : v < n) {gb ga : List VT} {T0 : VT} (hG : G = gb ++ T0 :: ga) (hvT : v ∈ nodes T0)
    {V : ℝ} (hV : VBnd V n F) (hH : 2 * V ≤ H) :
    ModNat.CmpOK P W H (accessS B) c := by
  obtain ⟨t0, ctx0, eT0, hrt0, ht0⟩ := locate n T0 v hvT
  subst hG eT0
  have e1 := Exec.copyN (P := P) hc 160 189
  unfold accessS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  obtain ⟨c2, k2, e2, hk2, I2, R2, hb2, hmf2, hfr2, s2, hfp2⟩ := splayS_exec (P := P) B n
    e1.wb_right hW
    (by config_simp; exact hn) (by exact hb) (t := t0) (ctx := ctx0) hI hR ht0
    (by config_simp; rw [hv, hrt0])
  refine ModNat.CmpOK.seq (splayS_cmpOK B n e1.wb_right hW (by config_simp; exact hn)
    (by exact hb) (t := t0) (ctx := ctx0) hI hR ht0 (by config_simp; rw [hv, hrt0]) hV hH)
    fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  obtain ⟨sf0, esf0, hsf0, hns0, -, hne1, hrt1, -, hpot1⟩ := splayG_spec ht0 ctx0
  generalize hS1 : splayG t0 ctx0 = S1 at *
  obtain ⟨t1, ctx1⟩ := S1
  simp only at I2 R2 hns0 hne1 hrt1 hpot1
  have hrt1' : rt n t1 = v := (hrt1 n).trans hrt0
  have e3 := Exec.copyN (P := P) e2.wb_right 178 151
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e3, ?_⟩
  obtain ⟨c4, k4, e4, hk4, m4, f4, s4⟩ := switchS_exec (P := P) B n e3.wb_right hW
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) (by exact hb2)
    (w := v) (y := n) (by config_simp; rw [s2, hrt0])
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) hvn.le le_rfl
  obtain ⟨I2', R2', F2', P2', v2', -, -⟩ := push_okE' B n I2 R2 rfl hne1
  have hN := switchNear_init B n hV I2' R2' hne1 hns0 v2'
  rw [hrt1'] at I2' R2' F2' P2' v2' hN
  refine ModNat.CmpOK.seq (switchS_cmpOK B n e3.wb_right hW
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) (by exact hb2)
    (w := v) (y := n) (by config_simp; rw [s2, hrt0])
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) hvn.le le_rfl hH hN)
    fun c4' k4' e4' => ?_
  obtain rfl : c4' = c4 := exec_post e4 e4'
  obtain ⟨l1, r1, et1, hJ0, hmf3, hpot3⟩ :=
    accJ_init B n I2' R2' hne1 hns0 (by rw [hrt1']; exact v2')
  rw [hrt1'] at hJ0 hmf3 hpot3 et1
  have hm4 : mem c4' = switchR B n v n (pushM B v (mem c2')) := m4
  rw [← hm4] at hJ0 hmf3
  have hb4 : Bnd B n (mem c4') := by rw [hm4]; exact (hb2.pushM hvn.le).switchR hvn.le le_rfl
  have h189_4 : c4'.nreg 189 = v := by
    rw [f4.2.1 189 (by omega) (by omega)]; config_simp
    rw [hfr2.2.1 189 (by omega) (by omega)]; config_simp; exact hv
  have h151_4 : c4'.nreg 151 = n := by
    rw [(f4.1 151 (by omega)).1]; config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp
    exact hn
  have hblk : ∃ c5 k5, Exec P W (block ([.copyN 190 189] ++ ld B 191 190 0)) c4' c5 k5 ∧
      k5 ≤ 6 ∧ mem c5 = mem c4' ∧ c5.nreg 190 = v ∧ c5.nreg 191 = par B (mem c4') v ∧
      FrK 193 c4' c5 ∧ c5.nreg 189 = v ∧ c5.nreg 151 = n := by
    have hw4 := e4.wb_right
    simp only [ld, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [h189_4]); omega)
    refine ⟨by omega, rfl, by config_simp; exact h189_4, by config_simp; rw [h189_4]; rfl,
      ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, by config_simp; exact h189_4,
      by config_simp; exact h151_4⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
    · config_simp; simp (disch := omega) only [upd_ne_of]
  obtain ⟨c5, k5, e5, hk5, m5, r190, r191, f5, r189, r151⟩ := hblk
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (noTestR_block _) _) ⟨c5, k5, e5, ?_⟩
  rw [← m5] at hJ0 hmf3 hb4
  have g1 : FrK 193 c { c with nreg := upd c.nreg 160 (c.nreg 189) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have g3 : FrK 193 c2' { c2' with nreg := upd c2'.nreg 178 (c2'.nreg 151) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have fr5 : FrK 193 c c5 :=
    g1.trans ((hfr2.mono (by omega)).trans (g3.trans ((f4.mono (by omega)).trans f5)))
  have hmf5 : MemFrame B n (mem c) (mem c5) := by
    exact MemFrame.trans B n hmf2 (F2'.trans B n hmf3)
  have hfp5 : ∀ u, fpar B (mem c5) u = fpar B (mem c) u := by
    intro u; rw [m5, hm4, switchR_fpar, P2', hfp2]; rfl
  have hI5 : AccI B n W F v gb ga c (node l1 v leaf (r1 :: dsOf t1), ctx1, [], l1, r1 :: dsOf t1)
      c5 := ⟨e5.wb_right, hJ0, hb4, r189, r151, by simp only [rt_node]; exact r190,
        by simp only [rt_node]; rw [r191, m5], fr5, hmf5, hfp5⟩
  -- the loop
  obtain ⟨gE, c6, k6, e6, hI6, hstop, hk6⟩ := whileLtN_amort (P := P) (a := 191) (b := 151)
    (body := accBody B) (AccI B n W F v gb ga c) (fun g _ => accΦ n gb ga g)
    (fun _ _ h => h.1) (fun g c' h ht => accBody_exec (P := P) B n hW h ht) hI5
  refine ModNat.CmpOK.seq (ModNat.CmpOK.whileLtN (fun c' => ∃ g, AccI B n W F v gb ga c g c')
    (fun c' ⟨g, hI'⟩ ht => ⟨accBody_cmpOK B n hW hI' ht hV hH, fun c1 k1 e => by
      obtain ⟨g', c'', k, e', hI'', -⟩ := accBody_exec (P := P) B n hW hI' ht
      obtain rfl : c1 = c'' := exec_post e' e
      exact ⟨g', hI''⟩⟩) ⟨_, hI5⟩) fun c6' k6' e6' => ?_
  obtain rfl : c6' = c6 := exec_post e6 e6'
  obtain ⟨YE, ctxE, spE, lvE, dvE⟩ := gE
  obtain ⟨hw6, hJE, hb6, h189, h151, h190, h191, hfr6, hmf6, hfp6⟩ := hI6
  simp only at hJE h190 h191
  obtain ⟨hYn, hsY, hspY⟩ := hJE.rtY_le
  have hYE : YE ≠ VT.leaf := by intro h; rw [h] at hspY; simp at hspY
  have hctxE : ctxE = [] := by
    obtain ⟨hpar, -, -⟩ := root_facts B n hJE.inv rfl hYE
    rcases ctxE with _ | ⟨f, ctx'⟩
    · rfl
    · exfalso; apply hstop
      rw [h191, h151, hpar]
      simp only [hp]
      exact (rotCtx B n hJE.inv rfl).ltc f.y (by simp [cnodes_cons, y_mem_fnodes])
  subst hctxE
  have e7 := Exec.copyN (P := P) hw6 160 189
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e7, ?_⟩
  have hG7 : gb ++ plug YE [] :: ga = gb ++ plug (node lvE v leaf dvE) spE :: ga := by
    rw [plug_nil, hJE.shape]
  have I7 := hJE.inv; rw [hG7] at I7
  have R7 := hJE.rep; rw [hG7] at R7
  exact ModNat.CmpOK.seq (splayS_cmpOK B n e7.wb_right hW (by config_simp; exact h151)
    (by exact hb6) I7 R7 (by simp) (by config_simp; exact h189) hV hH)
    fun _ _ _ => ModNat.cmpOK_of_noTestR (cpushS_noTestR B 189) _

end accmach

end DynTree

end PlanarFlow
