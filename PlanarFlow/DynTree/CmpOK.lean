module

public import PlanarFlow.DynTree.CmpAccess
public import PlanarFlow.DynTree.RegList

/-!
# Dynamic trees: bounded real comparisons in the operations

For the simulation of the reals modulo a word (`WordRAM/Machine/RealsModNat.lean`), every real
comparison of a run must compare numbers at distance at most `H` (`ModNat.CmpOK`). For the
operations of the evertable link-cut tree on the machine (`LCTE`), when the represented forest
has values (both channels) of absolute value at most `V` (`VBnd V n F`) and `2 V ≤ H`:

* the operations of `PlanarFlow/DynTree/OpsCode.lean`: `opQuery_cmpOK`, `opQuery2_cmpOK`,
  `opAdd_cmpOK`, `opAdd2_cmpOK`, `opAddC_cmpOK`, `opQueryC_cmpOK`, `opEvert_cmpOK`,
  `opParentAcc_cmpOK`, `opCut_cmpOK`, `opLink_cmpOK` (the access, `accessS_cmpOK`, and the
  recomputation of `cut`, whose node has no children then);
* the register-operand blocks of `PlanarFlow/DynTree/RegOps.lean`, `…/RegVal.lean`,
  `…/RegList.lean`: `regQuery_cmpOK`, …, `regVal_cmpOK`, `regSet_cmpOK`, `rop_cmpOK`;
* `regMin_cmpOK`, `regMin2_cmpOK`: the comparison bit compares the minimum on the root path
  with the threshold, which must be within `H` of it (`pathMin_bound`: the minimum is at most
  `V` in absolute value).
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

section ops
variable {P : Input} {W H : ℕ}

/-- The access of `v = r193` followed by code without real tests. -/
theorem access_rest_cmpOK (B n : ℕ) {rest : Stmt} (hrest : rest.noTestR = true) {c : Config}
    (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT}
    (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) {V : ℝ}
    (hV : VBnd V n F) (hH : 2 * V ≤ H) :
    ModNat.CmpOK P W H (.seq (.instr (.copyN 189 193)) (.seq (accessS B) rest)) c := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  exact ModNat.CmpOK.seq (accessS_cmpOK B n e1.wb_right hW (by config_simp; exact hS.hn)
    hS.bnd hS.inv hS.rep (by config_simp; exact hv) hvn hG hvT hV hH)
    fun _ _ _ => ModNat.cmpOK_of_noTestR hrest _

variable (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
  {F : Forest} {G : List VT} (hS : LCTE B n F G c) {V : ℝ} (hV : VBnd V n F) (hH : 2 * V ≤ H)
include hc hW hS hV hH

theorem opQuery_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opQueryS B) c :=
  access_rest_cmpOK B n (noTestR_block _) hc hW hS hv hvn hV hH

theorem opQuery2_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opQuery2S B) c :=
  access_rest_cmpOK B n (noTestR_block _) hc hW hS hv hvn hV hH

theorem opQueryC_cmpOK (k : Bool) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opQueryCS B k) c := by
  cases k
  · exact opQuery_cmpOK B n hc hW hS hV hH hv hvn
  · exact opQuery2_cmpOK B n hc hW hS hV hH hv hvn

theorem opAdd_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opAddS B) c :=
  access_rest_cmpOK B n (noTestR_block _) hc hW hS hv hvn hV hH

theorem opAdd2_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opAdd2S B) c :=
  access_rest_cmpOK B n (noTestR_block _) hc hW hS hv hvn hV hH

theorem opAddC_cmpOK (k : Bool) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opAddCS B k) c :=
  access_rest_cmpOK B n (noTestR_block _) hc hW hS hv hvn hV hH

theorem opEvert_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opEvertS B) c :=
  access_rest_cmpOK B n (by simp [flipS, noTestR]) hc hW hS hv hvn hV hH

theorem opParentAcc_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opParentAccS B) c :=
  access_rest_cmpOK B n (by simp [noTestR]) hc hW hS hv hvn hV hH

/-- **`cut` compares near values**: the access, then the recomputation of `v`, which has no
children any more. -/
theorem opCut_cmpOK {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ModNat.CmpOK P W H (opCutS B) c := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV v hvn).1
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, hrv2⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  unfold opCutS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq (accessS_cmpOK B n e1.wb_right hW (by config_simp; exact hS.hn)
    hS.bnd hS.inv hS.rep (by config_simp; exact hv) hvn hG hvT hV hH) fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  have hb2 := hS2.bnd
  obtain ⟨-, la, ra, -, -, -⟩ := hb2.get hvn.le
  have hrc2 : rc B (mem c2') v = n := by
    have hE := hS2.inv.enc _ (List.mem_cons_self ..)
    rw [enc_node_iff_clean B n hrv2] at hE
    exact hE.2.2.1
  have hblk : ∃ c3 k3, Exec P W (block (ld B 192 189 1 ++ st B 189 1 151 ++ st B 192 0 151 ++
      st B 189 4 151 ++ ldR B 197 192 1 ++ ldR B 198 189 1 ++ ldR B 199 192 6 ++
      ldR B 196 189 6 ++ [.addR 197 197 198, .addR 199 199 196] ++ stR B 192 1 197 ++
      stR B 192 6 199 ++ [.copyN 170 189])) c2' c3 k3 ∧ k3 ≤ 80 ∧
      mem c3 = ⟨upd (upd (upd (mem c2').nm (adr B v 1) n) (adr B (lc B (mem c2') v) 0) n)
        (adr B v 4) n, upd (upd (mem c2').rm (adr B (lc B (mem c2') v) 1)
          (tg B (mem c2') (lc B (mem c2') v) + tg B (mem c2') v)) (adr B (lc B (mem c2') v) 6)
          (tg2 B (mem c2') (lc B (mem c2') v) + tg2 B (mem c2') v)⟩ ∧
      FrK 193 c2' c3 ∧ c3.nreg 170 = v ∧ c3.nreg 193 = c2'.nreg 193 ∧
      c3.nreg 194 = c2'.nreg 194 := by
    have hw2 := e2.wb_right
    have hn2 := hS2.hn
    simp only [lc, mem, adr] at la
    simp only [ld, ldR, st, stR, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [h189, hn2]); omega)
    refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, by config_simp; exact h189,
      by config_simp, by config_simp⟩
    · simp only [mem, lc, tg, tg2]; config_simp; rw [h189, hn2]; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · config_simp; simp (disch := omega) only [upd_ne_of]
  obtain ⟨c3, k3, e3, hk3, m3, f3, s170, s193, s194⟩ := hblk
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (noTestR_block _) _) ⟨c3, k3, e3, ?_⟩
  have l3 : lc B (mem c3) v = n := by
    rw [m3]; simp only [lc]; simp [upd_adr]
  have r3 : rc B (mem c3) v = n := by
    rw [m3]; simp only [rc]; simp [upd_adr]
    simpa only [rc] using hrc2
  refine recompS_cmpOK B n e3.wb_right hW s170 (by rw [(f3.1 151 (by omega)).1]; exact hS2.hn)
    hvn.le l3.le r3.le hH ⟨- vl B (mem c3) v, - vl2 B (mem c3) v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hV0
  · simpa using hV0
  all_goals intro h; omega

/-- **`link` compares near values**: two accesses. -/
theorem opLink_cmpOK {v w : ℕ} (hv : c.nreg 193 = v) (hw : c.nreg 194 = w) (hvn : v < n)
    (hwn : w < n) : ModNat.CmpOK P W H (opLinkS B) c := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, lv, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  unfold opLinkS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq (accessS_cmpOK B n e1.wb_right hW (by config_simp; exact hS.hn)
    hS.bnd hS.inv hS.rep (by config_simp; exact hv) hvn hG hvT hV hH) fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  have h194 : c2'.nreg 194 = w := by
    rw [hfr2.2.1 194 (by omega) (by omega)]; config_simp; exact hw
  have e3 := Exec.copyN (P := P) e2.wb_right 189 194
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e3, ?_⟩
  obtain ⟨gb', ga', T1, hG', hwT⟩ := hS2.split hwn
  exact ModNat.CmpOK.seq (accessS_cmpOK B n e3.wb_right hW (by config_simp; exact hS2.hn)
    hS2.bnd hS2.inv hS2.rep (by config_simp; exact h194) hwn hG' hwT hV hH)
    fun _ _ _ => ModNat.cmpOK_of_noTestR (noTestR_block _) _

/-! ### The register-operand blocks -/

theorem regQuery_cmpOK {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regQueryS B ra) c :=
  ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, Exec.copyN (P := P) hc 193 ra,
    opQuery_cmpOK B n (Exec.copyN (P := P) hc 193 ra).wb_right hW (hS.updN 193 _ (by omega)) hV hH
      (by simp [hv]) hvn⟩

theorem regQuery2_cmpOK {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regQuery2S B ra) c :=
  ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, Exec.copyN (P := P) hc 193 ra,
    opQuery2_cmpOK B n (Exec.copyN (P := P) hc 193 ra).wb_right hW (hS.updN 193 _ (by omega)) hV
      hH (by simp [hv]) hvn⟩

theorem regParent_cmpOK {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regParentS B ra) c :=
  ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, Exec.copyN (P := P) hc 193 ra,
    opParentAcc_cmpOK B n (Exec.copyN (P := P) hc 193 ra).wb_right hW (hS.updN 193 _ (by omega))
      hV hH (by simp [hv]) hvn⟩

theorem regEvert_cmpOK {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regEvertS B ra) c :=
  ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, Exec.copyN (P := P) hc 193 ra,
    opEvert_cmpOK B n (Exec.copyN (P := P) hc 193 ra).wb_right hW (hS.updN 193 _ (by omega))
      hV hH (by simp [hv]) hvn⟩

theorem regCut_cmpOK {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regCutS B ra) c :=
  ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, Exec.copyN (P := P) hc 193 ra,
    opCut_cmpOK B n (Exec.copyN (P := P) hc 193 ra).wb_right hW (hS.updN 193 _ (by omega))
      hV hH (by simp [hv]) hvn⟩

theorem regAdd_cmpOK {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regAddS B ra rz) c := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  exact opAdd_cmpOK B n e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) hV hH
    (by simp [hv]) hvn

theorem regAdd2_cmpOK {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regAdd2S B ra rz) c := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  exact opAdd2_cmpOK B n e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) hV hH
    (by simp [hv]) hvn

theorem regLink_cmpOK {ra rb v w : ℕ} (hrb : rb ≠ 193) (hv : c.nreg ra = v)
    (hw : c.nreg rb = w) (hvn : v < n) (hwn : w < n) :
    ModNat.CmpOK P W H (regLinkS B ra rb) c := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyN (P := P) e1.wb_right 194 rb
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  exact opLink_cmpOK B n e2.wb_right hW ((hS.updN 193 _ (by omega)).updN 194 _ (by omega)) hV hH
    (by simp [hv]) (by simp [upd_ne_of _ _ _ hrb, hw]) hvn hwn

theorem regMin_cmpOK {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n)
    (hz : |(pathMin F n v).1 - c.rreg rz| ≤ H) : ModNat.CmpOK P W H (regMinS B ra rz) c := by
  have e1 := Exec.copyR (P := P) hc 200 rz
  obtain ⟨c2, k2, e2, G2, hS2, r195, r196, q195, q196, q200, hmf, hfr, hk⟩ :=
    regQuery_exec (P := P) B n e1.wb_right hW (hS.updR 200 _) (by simpa using hv) hvn
  unfold regMinS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq (regQuery_cmpOK B n e1.wb_right hW (hS.updR 200 _) hV hH
    (by simpa using hv) hvn) fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  refine ModNat.CmpOK.ifLtR ?_ (fun _ => ModNat.cmpOK_of_noTestR rfl _)
    (fun _ => ModNat.cmpOK_of_noTestR rfl _)
  rw [q195, q200]; simpa using hz

theorem regMin2_cmpOK {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n)
    (hz : |(pathMin2 F n v).1 - c.rreg rz| ≤ H) : ModNat.CmpOK P W H (regMin2S B ra rz) c := by
  have e1 := Exec.copyR (P := P) hc 200 rz
  obtain ⟨c2, k2, e2, G2, hS2, r196, q195, q196, q200, hmf, hfr, hk⟩ :=
    regQuery2_exec (P := P) B n e1.wb_right hW (hS.updR 200 _) (by simpa using hv) hvn
  unfold regMin2S
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq (regQuery2_cmpOK B n e1.wb_right hW (hS.updR 200 _) hV hH
    (by simpa using hv) hvn) fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  refine ModNat.CmpOK.ifLtR ?_ (fun _ => ModNat.cmpOK_of_noTestR rfl _)
    (fun _ => ModNat.cmpOK_of_noTestR rfl _)
  rw [q195, q200]; simpa using hz

/-- **Reading the value of a node compares near values.** -/
theorem regVal_cmpOK (k : Bool) {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regValS B k ra) c := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c2, k2, G2, e2, hS2, s2, hmf2, hfr2, h193, hk2⟩ := opQueryC_exec (P := P) B n k
    e1.wb_right hW (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  unfold regValS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq (opQueryC_cmpOK B n e1.wb_right hW (hS.updN 193 _ (by omega)) hV hH k
    (by simp [hv]) hvn) fun c2' k2' e2' => ?_
  obtain rfl : c2' = c2 := exec_post e2 e2'
  have e3 := Exec.copyR (P := P) e2.wb_right 200 196
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e3, ?_⟩
  obtain ⟨c4, k4, G4, e4, hS4, p4, hmf4, hfr4, h193', -, hk4⟩ := opParentAcc_exec (P := P) B n
    e3.wb_right hW (hS2.updR 200 _) (by simpa using h193) hvn
  refine ModNat.CmpOK.seq (opParentAcc_cmpOK B n e3.wb_right hW (hS2.updR 200 _) hV hH
    (by simpa using h193) hvn) fun c4' k4' e4' => ?_
  obtain rfl : c4' = c4 := exec_post e4 e4'
  have hn4 : c4'.nreg 151 = n := hS4.hn
  refine ModNat.CmpOK.seq ?_ fun _ _ _ => ModNat.cmpOK_of_noTestR rfl _
  refine ModNat.CmpOK.ifLtN (fun hp => ?_) (fun _ => ModNat.cmpOK_of_noTestR rfl _)
  rw [p4, hn4] at hp
  have e5 := Exec.copyN (P := P) e4.wb_right 193 195
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e5, ?_⟩
  exact ModNat.CmpOK.seq (opQueryC_cmpOK B n e5.wb_right hW (hS4.updN 193 _ (by omega)) hV hH k
    (by simp [p4]) hp) fun _ _ _ => ModNat.cmpOK_of_noTestR rfl _

/-- **Setting the value of a root compares near values** (the forest before the setting has
values at most `V`). -/
theorem regSet_cmpOK (k : Bool) {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ModNat.CmpOK P W H (regSetS B k ra rz) c := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  obtain ⟨c3, k3, G3, e3, hS3, s3, hmf3, hfr3, h193, hk3⟩ := opQueryC_exec (P := P) B n k
    e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) (by simp [hv]) hvn
  unfold regSetS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  refine ModNat.CmpOK.seq (opQueryC_cmpOK B n e2.wb_right hW
    ((hS.updN 193 _ (by omega)).updR 200 _) hV hH k (by simp [hv]) hvn) fun c3' k3' e3' => ?_
  obtain rfl : c3' = c3 := exec_post e3 e3'
  have e4 := Exec.subR (P := P) e3.wb_right 200 200 196
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e4, ?_⟩
  exact opAddC_cmpOK B n e4.wb_right hW (hS3.updR 200 _) hV hH k (by simpa using h193) hvn

/-- **A register-operand operation compares near values.** -/
theorem rop_cmpOK (o : ROp) (zr : ℕ → ℤ) (hok : o.Ok c zr) (hv : (o.eop c zr).Valid n F) :
    ModNat.CmpOK P W H (o.stmt B) c := by
  cases o with
  | link ra rb =>
    exact regLink_cmpOK B n hc hW hS hV hH (by simp [ROp.Ok] at hok; omega) rfl rfl hv.1 hv.2.1
  | cut ra => exact regCut_cmpOK B n hc hW hS hV hH rfl hv.1
  | add ra rz => exact regAdd_cmpOK B n hc hW hS hV hH rfl hv
  | add2 ra rz => exact regAdd2_cmpOK B n hc hW hS hV hH rfl hv
  | evert ra => exact regEvert_cmpOK B n hc hW hS hV hH rfl hv

end ops

lemma upPath_lt (F : Forest) (n : ℕ) : ∀ (f v u : ℕ), u ∈ upPath F n f v → u < n
  | 0, v, u, h => by simp [upPath] at h
  | f + 1, v, u, h => by
    simp only [upPath] at h
    split_ifs at h with hv
    · rcases List.mem_cons.mp h with rfl | h
      · exact hv
      · exact upPath_lt F n f _ u h
    · simp at h

/-- The minimum on the root path is at most `V` in absolute value. -/
lemma pathMin_bound {V : ℝ} {F : Forest} {n : ℕ} (hV : VBnd V n F) {v : ℕ} (hvn : v < n) :
    |(pathMin F n v).1| ≤ V ∧ |(pathMin2 F n v).1| ≤ V := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : rootPath F (m + 1) v ≠ [] := by simp [rootPath, upPath, hvn]
  have h1 : downVals F (m + 1) v ≠ [] := by simpa [downVals] using hne
  have h2 : downVals2 F (m + 1) v ≠ [] := by simpa [downVals2] using hne
  obtain ⟨q1, -⟩ := lmin_spec h1
  obtain ⟨q2, -⟩ := lmin_spec h2
  obtain ⟨e, he, he'⟩ := List.mem_map.mp q1
  obtain ⟨e2, he2, he2'⟩ := List.mem_map.mp q2
  simp only [downVals, downVals2, List.mem_map, List.mem_reverse] at he he2
  obtain ⟨u, hu, rfl⟩ := he
  obtain ⟨u2, hu2, rfl⟩ := he2
  refine ⟨?_, ?_⟩
  · show |(lmin (downVals F (m + 1) v)).1| ≤ V
    rw [← he']; exact (hV u (upPath_lt F _ _ _ _ hu)).1
  · show |(lmin (downVals2 F (m + 1) v)).1| ≤ V
    rw [← he2']; exact (hV u2 (upPath_lt F _ _ _ _ hu2)).2


end DynTree

end PlanarFlow
