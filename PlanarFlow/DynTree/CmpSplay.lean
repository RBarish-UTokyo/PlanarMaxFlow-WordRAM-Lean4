module

public import PlanarFlow.DynTree.CmpZip

/-!
# Dynamic trees: bounded real comparisons in the splay

* `StepNear V M x`: the rotations of the splay step at `x` (`splayStepM`) compare near values;
  **`stepNear_zip`**: they do in a stored zipper whose forest has values at most `V`
  (`VBnd`), the rotations being those of `splayStep_okE`.
* **`splayStepS_cmpOK`**, **`splayS_cmpOK`**: every run of the splay step and of the splay loop
  compares numbers at distance at most `2 V`.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

section step
variable (B n : ℕ)

/-- The rotations of the splay step at `x` (`splayStepM`) compare near values. -/
def StepNear (V : ℝ) (M : Mem) (x : ℕ) : Prop :=
  if IsChild B M (par B M x) then
    if (lc B (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M))) (par B M x) = x ↔
        lc B (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M)))
          (par B M (par B M x)) = par B M x) then
      RotNear B n V (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M)))
          (par B M x) ∧
        RotNear B n V (rotMem B n (par B M x)
          (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M)))) x
    else RotNear B n V (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M))) x ∧
      RotNear B n V (rotMem B n x
        (pushM B x (pushM B (par B M x) (pushM B (par B M (par B M x)) M)))) x
  else RotNear B n V (pushM B x (pushM B (par B M x) M)) x

/-- **The splay step compares near values** in a stored zipper (the rotations of
`splayStep_okE`). -/
theorem stepNear_zip {M : Mem} {G : List VT} {F : Forest} {V : ℝ} (hI : Inv B n M G)
    (hR : RepE B n M G F) (hV : VBnd V n F) {gb ga : List VT} {t : VT} {ctx : List Frame}
    (hG : G = gb ++ plug t ctx :: ga) (ht : t ≠ leaf) (hc : HeadSolid ctx) :
    StepNear B n V M (rt n t) := by
  obtain ⟨hpar, -, -⟩ := root_facts B n hI hG ht
  rcases ctx with _ | ⟨f1, rest⟩
  · exact absurd hc (by simp [HeadSolid])
  have hf1 : f1.Solid := hc
  simp only [hp] at hpar
  have hG1 : G = gb ++ plug (f1.plug t) rest :: ga := hG
  have hy1 : f1.plug t ≠ leaf := by cases f1 <;> simp [Frame.plug]
  obtain ⟨hpar1, hch1, -⟩ := root_facts B n hI hG1 hy1
  simp only [rt_plugF, hp] at hpar1 hch1
  have zigN : ¬ HeadSolid rest →
      RotNear B n V (pushM B (rt n t) (pushM B f1.y M)) (rt n t) := by
    intro _
    obtain ⟨Ia, Ra, -, -, ya, -, -⟩ := push_okE' B n hI hR hG1 hy1
    simp only [rt_plugF] at Ia Ra ya
    obtain ⟨Ib, Rb, -, -, xb, yb, -⟩ := push_okE' B n Ia Ra hG ht
    exact rotNear_zip Ib Rb hV hG hf1 ht xb
      (by rw [yb _ (by simp [cnodes_cons, y_mem_fnodes])]; exact ya)
  unfold StepNear
  rw [hpar]
  rcases rest with _ | ⟨f2, fs⟩
  · rw [ite_of_neg (fun h' => (by simp [HeadSolid] : ¬ HeadSolid ([] : List Frame))
      (hch1.mp h'))]
    exact zigN (by simp [HeadSolid])
  by_cases hf2 : f2.Solid
  · have hch : IsChild B M f1.y := hch1.mpr hf2
    have hG2 : G = gb ++ plug (f2.plug (f1.plug t)) fs :: ga := hG
    have hz2 : f2.plug (f1.plug t) ≠ leaf := by cases f2 <;> simp [Frame.plug]
    obtain ⟨Ia, Ra, -, -, za, -, -⟩ := push_okE' B n hI hR hG2 hz2
    simp only [rt_plugF] at Ia Ra za
    obtain ⟨Ib, Rb, -, -, yb, zb, -⟩ := push_okE' B n Ia Ra hG1 hy1
    simp only [rt_plugF] at Ib Rb yb zb
    obtain ⟨Ic, Rc, -, -, xc, yc, -⟩ := push_okE' B n Ib Rb hG ht
    have hpz : par B M f1.y = f2.y := hpar1
    rw [ite_of_pos hch, hpz]
    generalize hM3 : pushM B (rt n t) (pushM B f1.y (pushM B f2.y M)) = M3 at Ic Rc xc yc ⊢
    have hyc : rv B M3 f1.y = false := by
      rw [yc _ (by simp [cnodes_cons, y_mem_fnodes])]; exact yb
    have hzc : rv B M3 f2.y = false := by
      rw [yc _ (by simp [cnodes_cons, y_mem_fnodes]), zb _ (by simp [cnodes_cons, y_mem_fnodes])]
      exact za
    obtain ⟨-, -, hL⟩ := root_facts B n Ic hG ht
    obtain ⟨-, -, hL1⟩ := root_facts B n Ic hG1 hy1
    simp only [rt_plugF] at hL1
    have e1 := hL f1 _ rfl hf1
    have e2 := hL1 f2 fs rfl hf2
    have hσ : cσ B M3 (cpar B M3 (f2 :: fs)) f1.y = cσ B M3 (cpar B M3 fs) f2.y := by
      rcases frame_solid_cases hf2 with ⟨y, c, dy, rfl⟩ | ⟨c, y, dy, rfl⟩ <;>
        simp only [cpar, DynTree.hpar, cσ, hyc, Bool.xor_false]
    have hσ2 : cσ B M3 (cpar B M3 fs) f2.y = cpar B M3 fs := by simp [cσ, hzc]
    rw [hσ, hσ2] at e1
    rw [hσ2] at e2
    have key : (lc B M3 f1.y = rt n t ↔ lc B M3 f2.y = f1.y) ↔ (f1.IsL ↔ f2.IsL) := by
      rw [e1, e2]
      by_cases a : f1.IsL <;> by_cases b : f2.IsL <;> cases cpar B M3 fs <;> simp [a, b]
    by_cases hs : (f1.IsL ↔ f2.IsL)
    · have hss : SameSide f1 f2 := ⟨hf1, hf2, hs⟩
      rw [ite_of_pos (key.mpr hs)]
      have N1 := rotNear_zip Ic Rc hV hG1 hf2 hy1 (by rw [rt_plugF]; exact hyc) hzc
      obtain ⟨I1, R1, -⟩ := rotate_okE B n Ic Rc hG1 hf2 hy1 (by rw [rt_plugF]; exact hyc) hzc
      simp only [rt_plugF] at I1 R1 N1
      rw [rotUp_plug_zz hss] at I1 R1
      exact ⟨N1, rotNear_zip I1 R1 hV (t := t) (f := zz f1 f2) (fs := fs) rfl
        (zz_solid hss) ht (by rw [rotMem_rv]; exact xc) (by rw [zz_y hss, rotMem_rv]; exact hyc)⟩
    · rw [ite_of_neg (fun h => hs (key.mp h))]
      have N1 := rotNear_zip Ic Rc hV hG hf1 ht xc hyc
      obtain ⟨I1, R1, -⟩ := rotate_okE B n Ic Rc hG hf1 ht xc hyc
      refine ⟨N1, ?_⟩
      obtain ⟨a, x, b, dx, rfl⟩ : ∃ a x b dx, t = node a x b dx := by
        cases t with
        | leaf => exact absurd rfl ht
        | node a x b dx => exact ⟨a, x, b, dx, rfl⟩
      obtain ⟨a', b', e⟩ := rotUp_shape (a := a) (b := b) (x := x) (dx := dx) hf1
      rw [e] at I1 R1
      have := rotNear_zip I1 R1 hV (t := node a' x b' dx) (f := f2) (fs := fs) rfl
        hf2 (by simp) (by rw [rt_node, rotMem_rv]; exact xc) (by rw [rotMem_rv]; exact hzc)
      simpa only [rt_node] using this
  · rw [ite_of_neg (fun h => hf2 (hch1.mp h))]
    exact zigN hf2

end step

/-! ### The splay step and the splay loop on the machine -/

section mach
variable {P : Input} {W H : ℕ}

theorem cmp_gen {s : Stmt} {c : Config} (h : ∀ c₀, c₀ = c → ModNat.CmpOK P W H s c₀) :
    ModNat.CmpOK P W H s c := h c rfl

theorem cmp_ifLtN_true {a b : ℕ} {t e : Stmt} {c : Config} (h : c.nreg a < c.nreg b)
    (ht : ModNat.CmpOK P W H t c) : ModNat.CmpOK P W H (.ifLtN a b t e) c :=
  ModNat.CmpOK.ifLtN (fun _ => ht) (fun h' => absurd h h')

theorem cmp_ifLtN_false {a b : ℕ} {t e : Stmt} {c : Config} (h : ¬ c.nreg a < c.nreg b)
    (he : ModNat.CmpOK P W H e c) : ModNat.CmpOK P W H (.ifLtN a b t e) c :=
  ModNat.CmpOK.ifLtN (fun h' => absurd h' h) (fun _ => he)

lemma cpushS_noTestR (B k : ℕ) : (cpushS B k).noTestR = true := by
  simp [cpushS, pushS, flipS, noTestR]

lemma isChildS_noTestR (B : ℕ) : (isChildS B).noTestR = true := by
  simp [isChildS, eqS, noTestR]

set_option maxHeartbeats 1000000 in
/-- **The splay step compares near values.** -/
theorem splayStepS_cmpOK (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {x : ℕ}
    (hx : c.nreg 160 = x) (hxn : x ≤ n) {V : ℝ} (hH : 2 * V ≤ H)
    (hS : StepNear B n V (mem c) x) : ModNat.CmpOK P W H (splayStepS B) c := by
  obtain ⟨py, -, -, -, -, -⟩ := hb.get hxn
  obtain ⟨pz, ly, -, -, -, -⟩ := hb.get py
  obtain ⟨-, lz, rz, -, -, -⟩ := hb.get pz
  have py' := py; have pz' := pz; have lz' := lz; have rz' := rz
  simp only [par, lc, rc, mem, adr] at py' pz' lz' rz'
  unfold splayStepS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (noTestR_block _) _) ?_
  simp only [ld, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx]); omega)
  obtain ⟨k1, e1, hk1⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 181 179 184
    (by decide) (by decide)
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e1, ?_⟩
  obtain ⟨k2, e2, hk2⟩ := eqS_exec (P := P) e1.wb_right (by omega) 182 179 185
    (by decide) (by decide)
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  have e3 := Exec.addN (P := P) e2.wb_right 186 184 185 (by config_simp; split_ifs <;> omega)
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e3, ?_⟩
  have hw3 := e3.wb_right
  refine cmp_gen fun c5 hc5 => ?_
  have hw5 : WordsBounded W c5 := hc5 ▸ hw3
  have m5 : mem c5 = mem c := by rw [hc5]; rfl
  have r151 : c5.nreg 151 = n := by rw [hc5]; config_simp; exact hn
  have r160 : c5.nreg 160 = x := by rw [hc5]; config_simp; exact hx
  have r178 : c5.nreg 178 = x := by rw [hc5]; config_simp; exact hx
  have r179 : c5.nreg 179 = par B (mem c) x := by rw [hc5]; config_simp; rw [hx]; rfl
  have r180 : c5.nreg 180 = par B (mem c) (par B (mem c) x) := by
    rw [hc5]; config_simp; rw [hx]; rfl
  have r186 : c5.nreg 186 = (if lc B (mem c) (par B (mem c) (par B (mem c) x)) = par B (mem c) x
      then 1 else 0) + (if rc B (mem c) (par B (mem c) (par B (mem c) x)) = par B (mem c) x
      then 1 else 0) := by rw [hc5]; config_simp; rw [hx]; rfl
  have r188 : c5.nreg 188 = 0 := by rw [hc5]; config_simp
  clear hc5
  have hb5 : Bnd B n (mem c5) := m5 ▸ hb
  have keep : ∀ {c c' : Config}, Fr c c' → ∀ r, 178 ≤ r → r < 197 → c'.nreg r = c.nreg r :=
    fun h r h1 h2 => h.2.1 r h1 h2
  unfold StepNear at hS
  generalize hy : par B (mem c) x = y at r179 r180 r186 py pz ly lz rz hS
  generalize hz : par B (mem c) y = z at r180 r186 pz lz rz hS
  have hCi : IsChild B (mem c) y ↔ (lc B (mem c) z = y ∨ rc B (mem c) z = y) := by
    unfold IsChild; rw [hz]
  by_cases hC : IsChild B (mem c) y
  · rw [ite_of_pos hC] at hS
    refine cmp_ifLtN_true (by rw [r188, r186, ite01_pos]; exact hCi.mp hC) ?_
    obtain ⟨c6, k6, e6, hk6, m6, f6, s6⟩ := cpushS_exec (P := P) B n hw5 hW hb5 r180 pz
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B _) _) ⟨_, _, e6, ?_⟩
    have hw6 := e6.wb_right
    have hb6 : Bnd B n (mem c6) := m6 ▸ hb5.pushM pz
    obtain ⟨c7, k7, e7, hk7, m7, f7, s7⟩ := cpushS_exec (P := P) B n hw6 hW hb6
      (by rw [keep f6 179 (by omega) (by omega)]; exact r179) py
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B _) _) ⟨_, _, e7, ?_⟩
    have hw7 := e7.wb_right
    have hb7 : Bnd B n (mem c7) := m7 ▸ hb6.pushM py
    obtain ⟨c8, k8, e8, hk8, m8, f8, s8⟩ := cpushS_exec (P := P) B n hw7 hW hb7
      (by rw [keep f7 178 (by omega) (by omega), keep f6 178 (by omega) (by omega)]; exact r178) hxn
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B _) _) ⟨_, _, e8, ?_⟩
    have hw8 := e8.wb_right
    have hb8 : Bnd B n (mem c8) := m8 ▸ hb7.pushM hxn
    generalize hM3 : pushM B x (pushM B y (pushM B z (mem c))) = M3 at hS
    have hm8 : mem c8 = M3 := by rw [m8, m7, m6, m5, hM3]
    have h179 : c8.nreg 179 = y := by
      rw [keep f8 179 (by omega) (by omega), keep f7 179 (by omega) (by omega),
        keep f6 179 (by omega) (by omega)]; exact r179
    have h180 : c8.nreg 180 = z := by
      rw [keep f8 180 (by omega) (by omega), keep f7 180 (by omega) (by omega),
        keep f6 180 (by omega) (by omega)]; exact r180
    have h178 : c8.nreg 178 = x := by
      rw [keep f8 178 (by omega) (by omega), keep f7 178 (by omega) (by omega),
        keep f6 178 (by omega) (by omega)]; exact r178
    have h160 : c8.nreg 160 = x := by rw [s8, s7, s6]; exact r160
    have h151 : c8.nreg 151 = n := by
      rw [(f8.1 151 (by omega)).1, (f7.1 151 (by omega)).1, (f6.1 151 (by omega)).1]; exact r151
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (noTestR_block _) _) ?_
    exec_block
    any_goals (config_simp; (try simp only [h179, h180]); omega)
    obtain ⟨k9, e9, hk9⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 181 179 184
      (by decide) (by decide)
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e9, ?_⟩
    obtain ⟨k10, e10, hk10⟩ := eqS_exec (P := P) e9.wb_right (by omega) 183 160 187
      (by decide) (by decide)
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e10, ?_⟩
    have hw10 := e10.wb_right
    refine cmp_gen fun c11 hc11 => ?_
    have hw11 : WordsBounded W c11 := hc11 ▸ hw10
    have m11 : mem c11 = M3 := by rw [hc11, ← hm8]; rfl
    have q151 : c11.nreg 151 = n := by rw [hc11]; config_simp; exact h151
    have q160 : c11.nreg 160 = x := by rw [hc11]; config_simp; exact h160
    have q178 : c11.nreg 178 = x := by rw [hc11]; config_simp; exact h178
    have q179 : c11.nreg 179 = y := by rw [hc11]; config_simp; exact h179
    have q184 : c11.nreg 184 = if lc B M3 z = y then 1 else 0 := by
      rw [hc11]; config_simp; rw [h180, h179, ← hm8]; rfl
    have q187 : c11.nreg 187 = if lc B M3 y = x then 1 else 0 := by
      rw [hc11]; config_simp; rw [h179, h160, ← hm8]; rfl
    clear hc11
    have hb11 : Bnd B n (mem c11) := by rw [m11, ← hm8]; exact hb8
    by_cases hs : (lc B M3 y = x ↔ lc B M3 z = y)
    · -- zig-zig
      rw [ite_of_pos hs] at hS
      refine cmp_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, h'⟩ => h (hs.mp h')) ?_
      refine cmp_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, h'⟩ => h (hs.mpr h')) ?_
      have e12 := Exec.copyN (P := P) hw11 160 179
      refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e12, ?_⟩
      have hw12 := e12.wb_right
      obtain ⟨c13, k13, e13, hk13, m13, f13, s13⟩ := rotS_exec (P := P) B n hw12 hW
        (by config_simp; exact q151) (by exact hb11) (by config_simp; exact q179) py
      refine ModNat.CmpOK.seq (rotS_cmpOK B n hw12 hW (by config_simp; exact q151) hb11
        (by config_simp; exact q179) py hH (by change RotNear B n V (mem c11) y; rw [m11]; exact hS.1))
        fun c13' k13' e13' => ?_
      obtain rfl : c13' = c13 := exec_post e13 e13'
      have hw13 := e13.wb_right
      have e14 := Exec.copyN (P := P) hw13 160 178
      refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e14, ?_⟩
      have hw14 := e14.wb_right
      have h178' : c13'.nreg 178 = x := by
        rw [f13.2.1 178 (by omega) (by omega)]; config_simp; exact q178
      have hb13 : Bnd B n (mem c13') := m13 ▸ hb11.rotMem py
      refine rotS_cmpOK B n hw14 hW
        (by config_simp; rw [(f13.1 151 (by omega)).1]; config_simp; exact q151) hb13
        (by config_simp; exact h178') hxn hH ?_
      change RotNear B n V (mem c13') x
      rw [m13]
      change RotNear B n V (rotMem B n y (mem c11)) x
      rw [m11]; exact hS.2
    · rw [ite_of_neg hs] at hS
      have hR2 : ModNat.CmpOK P W H (.seq (rotS B) (rotS B)) c11 := by
        obtain ⟨c12, k12, e12, hk12, m12, f12, s12⟩ := rotS_exec (P := P) B n hw11 hW q151 hb11
          q160 hxn
        refine ModNat.CmpOK.seq (rotS_cmpOK B n hw11 hW q151 hb11 q160 hxn hH
          (by rw [m11]; exact hS.1)) fun c12' k12' e12' => ?_
        obtain rfl : c12' = c12 := exec_post e12 e12'
        refine rotS_cmpOK B n e12.wb_right hW (by rw [(f12.1 151 (by omega)).1]; exact q151)
          (m12 ▸ hb11.rotMem hxn) s12 hxn hH ?_
        rw [m12, m11]; exact hS.2
      by_cases h1 : lc B M3 z = y
      · refine cmp_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, _⟩ => h h1) ?_
        exact cmp_ifLtN_true (by
          rw [q184, q187, ite01_lt]; exact ⟨fun hc => hs ⟨fun _ => h1, fun _ => hc⟩, h1⟩) hR2
      · exact cmp_ifLtN_true (by
          rw [q184, q187, ite01_lt]
          exact ⟨h1, by_contra fun hc => hs ⟨fun c => absurd c hc, fun a => absurd a h1⟩⟩) hR2
  · rw [ite_of_neg hC] at hS
    refine cmp_ifLtN_false (by rw [r188, r186, ite01_pos]; exact fun h => hC (hCi.mpr h)) ?_
    obtain ⟨c6, k6, e6, hk6, m6, f6, s6⟩ := cpushS_exec (P := P) B n hw5 hW hb5 r179 py
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B _) _) ⟨_, _, e6, ?_⟩
    have hw6 := e6.wb_right
    have hb6 : Bnd B n (mem c6) := m6 ▸ hb5.pushM py
    obtain ⟨c7, k7, e7, hk7, m7, f7, s7⟩ := cpushS_exec (P := P) B n hw6 hW hb6
      (by rw [keep f6 178 (by omega) (by omega)]; exact r178) hxn
    refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (cpushS_noTestR B _) _) ⟨_, _, e7, ?_⟩
    have hb7 : Bnd B n (mem c7) := m7 ▸ hb6.pushM hxn
    refine rotS_cmpOK B n e7.wb_right hW
      (by rw [(f7.1 151 (by omega)).1, (f6.1 151 (by omega)).1]; exact r151) hb7
      (by rw [s7, s6]; exact r160) hxn hH ?_
    rw [m7, m6, m5]; exact hS

/-- **The splay loop compares near values**, from a stored zipper whose forest has values at
most `V`. -/
theorem splayS_cmpOK (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {F : Forest} {gb ga : List VT} {t : VT}
    {ctx : List Frame} (hI : Inv B n (mem c) (gb ++ plug t ctx :: ga))
    (hR : RepE B n (mem c) (gb ++ plug t ctx :: ga) F) (ht : t ≠ VT.leaf)
    (hx : c.nreg 160 = rt n t) {V : ℝ} (hV : VBnd V n F) (hH : 2 * V ≤ H) :
    ModNat.CmpOK P W H (splayS B) c := by
  have hxn : rt n t < n := hI.rt_lt rfl ht
  obtain ⟨c1, k1, e1, hk1, m1, f1, s160, s188, s186⟩ :=
    isChildS_exec (P := P) B n hc hW hb hx hxn.le
  unfold splayS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (isChildS_noTestR B) _) ⟨c1, k1, e1, ?_⟩
  let I : Config → Prop := fun c' => ∃ g : VT × List Frame,
    WordsBounded W c' ∧ Inv B n (mem c') (gb ++ plug g.1 g.2 :: ga) ∧
    RepE B n (mem c') (gb ++ plug g.1 g.2 :: ga) F ∧ g.1 ≠ VT.leaf ∧ rt n g.1 = rt n t ∧
    c'.nreg 160 = rt n t ∧ c'.nreg 151 = n ∧ c'.nreg 188 = 0 ∧
    (0 < c'.nreg 186 ↔ HeadSolid g.2) ∧ Bnd B n (mem c')
  have hI1 : I c1 := by
    refine ⟨(t, ctx), e1.wb_right, m1 ▸ hI, m1 ▸ hR, ht, rfl, s160, ?_, s188, ?_, m1 ▸ hb⟩
    · rw [(f1.1 151 (by omega)).1]; exact hn
    · rw [s186]; exact root_facts B n hI rfl ht |>.2.1
  refine ModNat.CmpOK.whileLtN I (fun c' hI' htest => ?_) hI1
  obtain ⟨g, hw, hInv, hRep, hne, hrt, h160, h151, h188, h186, hbd⟩ := hI'
  have hhs : HeadSolid g.2 := h186.mp (by omega)
  obtain ⟨c3, k3, e3, hk3, m3, f3, s3⟩ := splayStepS_exec (P := P) B n hw hW h151 hbd h160
    hxn.le
  have hb3 : Bnd B n (mem c3) := m3 ▸ hbd.splayStepM hxn.le
  obtain ⟨c4, k4, e4, hk4, m4, f4, s4, s4', s4''⟩ := isChildS_exec (P := P) B n e3.wb_right hW
    hb3 s3 hxn.le
  obtain ⟨I3, R3, -, -⟩ := splayStep_okE B n hInv hRep rfl hne hhs
  rw [hrt] at I3 R3
  obtain ⟨hne', hrt'⟩ := splay1_node hne hhs n
  refine ⟨ModNat.CmpOK.seq (splayStepS_cmpOK B n hw hW h151 hbd h160 hxn.le hH
    (by rw [← hrt]; exact stepNear_zip B n hInv hRep hV rfl hne hhs))
    (fun _ _ _ => ModNat.cmpOK_of_noTestR (isChildS_noTestR B) _), fun c1' k1' e1' => ?_⟩
  obtain rfl : c1' = c4 := exec_post (.seq e3 e4) e1'
  refine ⟨splay1 g.1 g.2, e4.wb_right, ?_, ?_, hne', hrt'.trans hrt, s4, ?_, s4', ?_, m4 ▸ hb3⟩
  · rw [m4, m3]; exact I3
  · rw [m4, m3]; exact R3
  · rw [(f4.1 151 (by omega)).1, (f3.1 151 (by omega)).1]; exact h151
  · rw [s4'', m3]
    have := root_facts B n I3 rfl hne'
    rw [hrt'.trans hrt] at this
    exact this.2.1

end mach

end DynTree

end PlanarFlow
