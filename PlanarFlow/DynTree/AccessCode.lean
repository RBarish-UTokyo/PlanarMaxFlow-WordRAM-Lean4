module

public import PlanarFlow.DynTree.CodeSplay
public import PlanarFlow.DynTree.Access

/-!
# Dynamic trees: the access on the machine

`accessS B` accesses the node `v = r189`: it splays `v`, hangs its right child, then while the
current auxiliary tree (root `r190`) has a path-parent `w = r191` it splays `w` and makes the tree
the right child of `w`, and finally splays `v` again.

**`accessS_exec`.** From a stored virtual forest `G` representing `F`, `accessS` ends with a
stored virtual forest `gb ++ node l v leaf dv :: ga` representing `F`, and its cost `k` satisfies
the amortised bound `k + 4100 · Φ(G') ≤ 4100 · Φ(G) + 36900 · ⌊log₂ n⌋ + 5000`, with `Φ = potL`
the rank potential of the virtual forest. The final splay pays for the iterations of the loop
(each splay step of it releases `3000` units of potential).
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

section
variable {P : Input} {W : ℕ}

/-- Loop rule with a ghost state and an amortised cost: the cost of the loop plus the final
potential is at most the initial potential plus `2`. -/
theorem whileLtN_amort {α : Type} {a b : ℕ} {body : Stmt} (I : α → Config → Prop)
    (Φ : α → Config → ℕ) (hI : ∀ x c, I x c → WordsBounded W c)
    (hbody : ∀ x c, I x c → c.nreg a < c.nreg b →
      ∃ x' c' k, Exec P W body c c' k ∧ I x' c' ∧ Φ x' c' + k + 2 ≤ Φ x c)
    {x : α} {c : Config} (hc : I x c) :
    ∃ x' c' k, Exec P W (.whileLtN a b body) c c' k ∧ I x' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ x' c' ≤ Φ x c + 2 := by
  induction hn : Φ x c using Nat.strong_induction_on generalizing x c with
  | _ N ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, k₁, hb, hI₁, hΦ⟩ := hbody x c hc ht
      obtain ⟨x', c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ x₁ c₁) (by omega) hI₁ rfl
      exact ⟨x', c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨x, c, 2, .whileLtN_false ht (hI x c hc), hc, ht, by omega⟩

end

lemma length_le_csize : ∀ sp : List Frame, sp.length ≤ csize sp
  | [] => le_refl _
  | f :: sp => by
    have := length_le_csize sp
    have : 1 ≤ f.fsize := by cases f <;> simp [Frame.fsize] <;> omega
    simp only [List.length_cons, csize]; omega

lemma log_le_of_size {s n : ℕ} (h : s ≤ n) : Nat.log 2 s ≤ Nat.log 2 n := Nat.log_mono_right h

/-- The body of the access loop: `w = r191` is splayed and the tree of `y = r190` becomes its
right child; then `y := w` and `r191 := par w`. -/
def accBody (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 160 191)) <| .seq (splayS B) <| .seq (.instr (.copyN 178 190)) <|
  .seq (switchS B) (block ([.copyN 190 160] ++ ld B 191 190 0))

/-- **The access of `v = r189`.** -/
def accessS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 160 189)) <| .seq (splayS B) <| .seq (.instr (.copyN 178 151)) <|
  .seq (switchS B) <| .seq (block ([.copyN 190 189] ++ ld B 191 190 0)) <|
  .seq (.whileLtN 191 151 (accBody B)) <| .seq (.instr (.copyN 160 189)) <|
  .seq (splayS B) (cpushS B 189)

/-- The ghost state of the access loop. -/
abbrev AccG : Type := VT × List Frame × List Frame × VT × List VT

/-- The invariant of the access loop on the machine. -/
def AccI (B n W : ℕ) (F : Forest) (v : ℕ) (gb ga : List VT) (c₀ : Config) (g : AccG)
    (c : Config) : Prop :=
  WordsBounded W c ∧ AccJ B n F (mem c) v gb ga g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 ∧
    Bnd B n (mem c) ∧ c.nreg 189 = v ∧ c.nreg 151 = n ∧ c.nreg 190 = rt n g.1 ∧
    c.nreg 191 = par B (mem c) (rt n g.1) ∧ FrK 193 c₀ c ∧ MemFrame B n (mem c₀) (mem c) ∧
    ∀ u, fpar B (mem c) u = fpar B (mem c₀) u

/-- The potential of the access loop. -/
def accΦ (n : ℕ) (gb ga : List VT) (g : AccG) : ℕ :=
  16400 * potL (gb ++ plug g.1 g.2.1 :: ga) + 49200 * (Nat.log 2 n - Nat.log 2 (size g.1)) +
    6000 * (n - g.2.2.1.length)


lemma AccJ.rtY_le {B n : ℕ} {F : Forest} {M : Mem} {v : ℕ} {gb ga : List VT} {Y : VT}
    {ctx sp : List Frame} {lv : VT} {dv : List VT} (hJ : AccJ B n F M v gb ga Y ctx sp lv dv) :
    rt n Y < n ∧ size Y ≤ n ∧ sp.length + 1 ≤ size Y := by
  have hY : Y ≠ VT.leaf := by
    rw [hJ.shape]; intro h
    have := congrArg size h
    rw [size_plugZ] at this; simp at this
  refine ⟨hJ.inv.rt_lt rfl hY, (size_le_plug Y ctx).trans (hJ.inv.size_le B n rfl), ?_⟩
  rw [hJ.shape, size_plugZ]
  have := length_le_csize sp
  simp; omega

section
variable {P : Input} {W : ℕ}

/-- One iteration of the access loop. -/
theorem accBody_exec (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {v : ℕ}
    {gb ga : List VT} {c₀ : Config} {g : AccG} {c : Config} (hI : AccI B n W F v gb ga c₀ g c)
    (ht : c.nreg 191 < c.nreg 151) :
    ∃ g' c' k, Exec P W (accBody B) c c' k ∧ AccI B n W F v gb ga c₀ g' c' ∧
      accΦ n gb ga g' + k + 2 ≤ accΦ n gb ga g := by
  obtain ⟨Y, ctx, sp, lv, dv⟩ := g
  obtain ⟨hw, hJ, hb, h189, h151, h190, h191, hfr, hmf, hfp⟩ := hI
  simp only at hJ h190 h191 ⊢
  obtain ⟨hYn, hsY, hspY⟩ := hJ.rtY_le
  have hY : Y ≠ VT.leaf := by intro h; rw [h] at hsY hspY; simp at hspY
  obtain ⟨hpar, -, -⟩ := root_facts B n hJ.inv rfl hY
  -- the zipper starts with the hanging frame of `w`
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
  -- splay `w`
  have e1 := Exec.copyN (P := P) hw 160 191
  have hG1 : Inv B n (mem { c with nreg := upd c.nreg 160 (c.nreg 191) })
      (gb ++ plug (node l w r (bef ++ Y :: aft)) ctx' :: ga) := hJ.inv
  have hR1 : RepE B n (mem { c with nreg := upd c.nreg 160 (c.nreg 191) })
      (gb ++ plug (node l w r (bef ++ Y :: aft)) ctx' :: ga) F := hJ.rep
  obtain ⟨c2, k2, e2, hk2, I2, R2, hb2, hmf2, hfr2, s2, hfp2⟩ := splayS_exec (P := P) B n
    e1.wb_right hW (by config_simp; exact h151) (by exact hb) hG1 hR1 (by simp)
    (by config_simp; rw [h191, hpar]; rfl)
  simp only [rt_node] at s2
  -- the push of `w`
  obtain ⟨-, -, -, -, -, hneS, hrtS, -, -⟩ :=
    splayG_spec (t := node l w r (bef ++ Y :: aft)) (by simp) ctx'
  have hrtS' : rt n (splayG (node l w r (bef ++ Y :: aft)) ctx').1 = w := (hrtS n).trans rfl
  obtain ⟨I2', R2', F2', P2', v2', -, -⟩ := push_okE' B n I2 R2 rfl hneS
  rw [hrtS'] at I2' R2' F2' P2' v2' 
  -- switch
  have e3 := Exec.copyN (P := P) e2.wb_right 178 190
  have h190' : c2.nreg 190 = rt n Y := by
    rw [hfr2.2.1 190 (by omega) (by omega)]; config_simp; exact h190
  obtain ⟨c4, k4, e4, hk4, m4, f4, s4⟩ := switchS_exec (P := P) B n e3.wb_right hW
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact h151) (by exact hb2)
    (w := w) (y := rt n Y) (by config_simp; exact s2) (by config_simp; exact h190') hwn.le hYn.le
  obtain ⟨l', r', eW, hJ', hmf4, hpot4, hsize4⟩ := accJ_step B n hJ I2' R2' v2'
  have hm4 : mem c4 = switchR B n w (rt n Y) (pushM B w (mem c2)) := m4
  rw [← hm4] at hJ' hmf4
  -- update the registers
  have hb4 : Bnd B n (mem c4) := by rw [hm4]; exact (hb2.pushM hwn.le).switchR hwn.le hYn.le
  have hblk : ∃ c5 k5, Exec P W (block ([.copyN 190 160] ++ ld B 191 190 0)) c4 c5 k5 ∧ k5 ≤ 6 ∧
      mem c5 = mem c4 ∧ c5.nreg 190 = w ∧ c5.nreg 191 = par B (mem c4) w ∧ FrK 193 c4 c5 ∧
      c5.nreg 189 = c4.nreg 189 := by
    have hw4 := e4.wb_right
    simp only [ld, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [s4]); omega)
    refine ⟨by omega, rfl, by config_simp; exact s4, by config_simp; rw [s4]; rfl,
      ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, by config_simp⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
    · config_simp; simp (disch := omega) only [upd_ne_of]
  obtain ⟨c5, k5, e5, hk5, m5, r190, r191, f5, r189⟩ := hblk
  rw [← m5] at hJ' hb4 hmf4
  -- the frames
  have g1 : FrK 193 c { c with nreg := upd c.nreg 160 (c.nreg 191) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have g3 : FrK 193 c2 { c2 with nreg := upd c2.nreg 178 (c2.nreg 190) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have fr5 : FrK 193 c c5 :=
    g1.trans ((hfr2.mono (by omega)).trans (g3.trans ((f4.mono (by omega)).trans f5)))
  -- the potential
  obtain ⟨sf, esf, hsf, hns, -, -, -, -, hpotS⟩ :=
    splayG_spec (t := node l w r (bef ++ Y :: aft)) (by simp) ctx'
  have hsp : VT.sp ctx' = sf.length := by
    conv_lhs => rw [esf]
    exact sp_append hsf hns
  obtain ⟨-, hsY', hspY'⟩ := hJ'.rtY_le
  have hrYW : Nat.log 2 (size Y) ≤ Nat.log 2 (size (node l w r (bef ++ Y :: aft))) :=
    Nat.log_mono_right (by simp; omega)
  have hrY'L : Nat.log 2 (size (node l' w Y (bef ++ r' :: aft))) ≤ Nat.log 2 n :=
    Nat.log_mono_right hsY'
  have hrYL : Nat.log 2 (size Y) ≤ Nat.log 2 n := Nat.log_mono_right hsY
  rw [← hsize4] at hpotS
  rw [← hpot4] at hpotS
  simp only [List.length_append, List.length_singleton] at hspY'
  refine ⟨(node l' w Y (bef ++ r' :: aft), (splayG (node l w r (bef ++ Y :: aft)) ctx').2,
    sp ++ [Frame.R l' w (bef ++ r' :: aft)], lv, dv), c5, 1 + (k2 + (1 + (k4 + k5))),
    .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    ⟨e5.wb_right, hJ', hb4, ?_, ?_, by simp only [rt_node]; exact r190, ?_, hfr.trans fr5, ?_, ?_⟩,
    ?_⟩
  · rw [r189, f4.2.1 189 (by omega) (by omega)]; config_simp
    rw [hfr2.2.1 189 (by omega) (by omega)]; config_simp; exact h189
  · rw [(fr5.1 151 (by omega)).1]; exact h151
  · simp only [rt_node]; rw [r191, m5]
  · exact hmf.trans B n (MemFrame.trans B n hmf2 (F2'.trans B n hmf4))
  · intro u; rw [m5, hm4, switchR_fpar, P2', hfp2]; exact hfp u
  · simp only [accΦ, potL_mid, List.length_append, List.length_singleton]
    have hplug : plug Y (Frame.D l w r bef aft :: ctx') = plug (node l w r (bef ++ Y :: aft)) ctx' :=
      rfl
    rw [hplug]
    rw [hsp] at hk2
    have : 4400 * ((sf.length + 1) / 2) ≤ 4400 * (sf.length / 2) + 4400 := by omega
    have hn1 : sp.length + 2 ≤ n := by omega
    omega

/-- **The access on the machine.** `accessS` makes `v = r189` the root of its virtual tree, with
no right child and its reversal bit clear, keeps the represented forest (and the field `fpar`),
and has amortised cost `147600 ⌊log₂ n⌋ + 21000` for the potential `16400 · potL`. -/
theorem accessS_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {G : List VT} {F : Forest}
    (hI : Inv B n (mem c) G) (hR : RepE B n (mem c) G F) {v : ℕ} (hv : c.nreg 189 = v)
    (hvn : v < n) {gb ga : List VT} {T0 : VT} (hG : G = gb ++ T0 :: ga) (hvT : v ∈ nodes T0) :
    ∃ c' k l dv, Exec P W (accessS B) c c' k ∧
      Inv B n (mem c') (gb ++ node l v leaf dv :: ga) ∧
      RepE B n (mem c') (gb ++ node l v leaf dv :: ga) F ∧ Bnd B n (mem c') ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 193 c c' ∧ c'.nreg 189 = v ∧ c'.nreg 151 = n ∧
      k + 16400 * potL (gb ++ node l v leaf dv :: ga) ≤
        16400 * potL G + 147600 * Nat.log 2 n + 21000 ∧
      (∀ u, fpar B (mem c') u = fpar B (mem c) u) ∧ rv B (mem c') v = false := by
  obtain ⟨t0, ctx0, eT0, hrt0, ht0⟩ := locate n T0 v hvT
  subst hG eT0
  -- the first splay
  have e1 := Exec.copyN (P := P) hc 160 189
  obtain ⟨c2, k2, e2, hk2, I2, R2, hb2, hmf2, hfr2, s2, hfp2⟩ := splayS_exec (P := P) B n
    e1.wb_right hW
    (by config_simp; exact hn) (by exact hb) (t := t0) (ctx := ctx0) hI hR ht0
    (by config_simp; rw [hv, hrt0])
  obtain ⟨sf0, esf0, hsf0, hns0, -, hne1, hrt1, -, hpot1⟩ := splayG_spec ht0 ctx0
  have hsp0 : VT.sp ctx0 = sf0.length := by conv_lhs => rw [esf0]
                                            exact sp_append hsf0 hns0
  generalize hS1 : splayG t0 ctx0 = S1 at *
  obtain ⟨t1, ctx1⟩ := S1
  simp only at I2 R2 hns0 hne1 hrt1 hpot1
  have hrt1' : rt n t1 = v := (hrt1 n).trans hrt0
  -- the first switch
  have e3 := Exec.copyN (P := P) e2.wb_right 178 151
  obtain ⟨c4, k4, e4, hk4, m4, f4, s4⟩ := switchS_exec (P := P) B n e3.wb_right hW
    (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) (by exact hb2)
    (w := v) (y := n) (by config_simp; rw [s2, hrt0]) (by config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp; exact hn) hvn.le le_rfl
  obtain ⟨I2', R2', F2', P2', v2', -, -⟩ := push_okE' B n I2 R2 rfl hne1
  rw [hrt1'] at I2' R2' F2' P2' v2'
  obtain ⟨l1, r1, et1, hJ0, hmf3, hpot3⟩ := accJ_init B n I2' R2' hne1 hns0 (by rw [hrt1']; exact v2')
  rw [hrt1'] at hJ0 hmf3 hpot3 et1
  have hm4 : mem c4 = switchR B n v n (pushM B v (mem c2)) := m4
  rw [← hm4] at hJ0 hmf3
  have hb4 : Bnd B n (mem c4) := by rw [hm4]; exact (hb2.pushM hvn.le).switchR hvn.le le_rfl
  have h189_4 : c4.nreg 189 = v := by
    rw [f4.2.1 189 (by omega) (by omega)]; config_simp
    rw [hfr2.2.1 189 (by omega) (by omega)]; config_simp; exact hv
  have h151_4 : c4.nreg 151 = n := by
    rw [(f4.1 151 (by omega)).1]; config_simp; rw [(hfr2.1 151 (by omega)).1]; config_simp
    exact hn
  have hblk : ∃ c5 k5, Exec P W (block ([.copyN 190 189] ++ ld B 191 190 0)) c4 c5 k5 ∧ k5 ≤ 6 ∧
      mem c5 = mem c4 ∧ c5.nreg 190 = v ∧ c5.nreg 191 = par B (mem c4) v ∧ FrK 193 c4 c5 ∧
      c5.nreg 189 = v ∧ c5.nreg 151 = n := by
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
  rw [← m5] at hJ0 hmf3 hb4
  have g1 : FrK 193 c { c with nreg := upd c.nreg 160 (c.nreg 189) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have g3 : FrK 193 c2 { c2 with nreg := upd c2.nreg 178 (c2.nreg 151) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have fr5 : FrK 193 c c5 :=
    g1.trans ((hfr2.mono (by omega)).trans (g3.trans ((f4.mono (by omega)).trans f5)))
  have hmf5 : MemFrame B n (mem c) (mem c5) := by
    exact MemFrame.trans B n hmf2 (F2'.trans B n hmf3)
  have hfp5 : ∀ u, fpar B (mem c5) u = fpar B (mem c) u := by
    intro u; rw [m5, hm4, switchR_fpar, P2', hfp2]; rfl
  -- the loop
  have hI5 : AccI B n W F v gb ga c (node l1 v leaf (r1 :: dsOf t1), ctx1, [], l1, r1 :: dsOf t1)
      c5 := ⟨e5.wb_right, hJ0, hb4, r189, r151, by simp only [rt_node]; exact r190,
        by simp only [rt_node]; rw [r191, m5], fr5, hmf5, hfp5⟩
  obtain ⟨gE, c6, k6, e6, hI6, hstop, hk6⟩ := whileLtN_amort (P := P) (a := 191) (b := 151)
    (body := accBody B) (AccI B n W F v gb ga c) (fun g _ => accΦ n gb ga g)
    (fun _ _ h => h.1) (fun g c' h ht => accBody_exec (P := P) B n hW h ht) hI5
  obtain ⟨YE, ctxE, spE, lvE, dvE⟩ := gE
  obtain ⟨hw6, hJE, hb6, h189, h151, h190, h191, hfr6, hmf6, hfp6⟩ := hI6
  simp only at hJE h190 h191 hk6
  obtain ⟨hYn, hsY, hspY⟩ := hJE.rtY_le
  have hYE : YE ≠ VT.leaf := by intro h; rw [h] at hspY; simp at hspY
  have hctxE : ctxE = [] := by
    obtain ⟨hpar, -, -⟩ := root_facts B n hJE.inv rfl hYE
    rcases ctxE with _ | ⟨f, ctx'⟩
    · rfl
    · exfalso; apply hstop
      rw [h191, h151, hpar]
      simp only [hp]
      have := (rotCtx B n hJE.inv rfl).ltc f.y (by simp [cnodes_cons, y_mem_fnodes])
      exact this
  subst hctxE
  -- the final splay
  have e7 := Exec.copyN (P := P) hw6 160 189
  have hG7 : gb ++ plug YE [] :: ga = gb ++ plug (node lvE v leaf dvE) spE :: ga := by
    rw [plug_nil, hJE.shape]
  have I7 := hJE.inv; rw [hG7] at I7
  have R7 := hJE.rep; rw [hG7] at R7
  obtain ⟨c8, k8, e8, hk8, I8, R8, hb8, hmf8, hfr8, s8, hfp8⟩ := splayS_exec (P := P) B n
    e7.wb_right hW (by config_simp; exact h151) (by exact hb6) I7 R7 (by simp)
    (by config_simp; exact h189)
  obtain ⟨hrest, l, eT, -⟩ := accJ_final B n hJE I8
  obtain ⟨sfE, esfE, hsfE, hnsE, -, -, -, -, hpotE⟩ := splayG_spec (t := node lvE v leaf dvE)
    (by simp) spE
  rw [hrest, eT] at I8 R8 hpotE
  rw [hrest] at esfE
  simp only [List.append_nil] at esfE
  subst esfE
  have hspE : VT.sp spE = spE.length := by
    have := sp_append hsfE (rest := []) (by simp [HeadSolid])
    simpa using this
  rw [hspE] at hk8
  -- the final push
  have h189_8 : c8.nreg 189 = v := by
    rw [hfr8.2.1 189 (by omega) (by omega)]; config_simp; exact h189
  obtain ⟨c9, k9, e9, hk9, m9, f9, s9⟩ := cpushS_exec (P := P) B n e8.wb_right hW hb8 h189_8 hvn.le
  obtain ⟨I9, R9, F9, P9, v9, -, -⟩ := push_okE' B n (gb := gb) (ga := ga) (ctx := [])
    (t := node l v leaf dvE) I8 R8 rfl (by simp)
  simp only [rt_node] at I9 R9 F9 P9 v9
  rw [← m9] at I9 R9 F9 P9 v9
  refine ⟨c9, 1 + (k2 + (1 + (k4 + (k5 + (k6 + (1 + (k8 + k9))))))), l, dvE,
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 e9))))))), I9, R9,
    m9 ▸ hb8.pushM hvn.le, hmf6.trans B n (hmf8.trans B n F9), ?_, ?_, ?_, ?_,
    fun u => by rw [P9, hfp8]; exact hfp6 u, v9⟩
  · have g7 : FrK 193 c6 { c6 with nreg := upd c6.nreg 160 (c6.nreg 189) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
    exact hfr6.trans (g7.trans ((hfr8.mono (by omega)).trans (f9.mono (by omega))))
  · rw [f9.2.1 189 (by omega) (by omega)]; exact h189_8
  · rw [(f9.1 151 (by omega)).1, (hfr8.1 151 (by omega)).1]; config_simp; exact h151
  · -- the amortised cost
    simp only [accΦ, potL_mid, List.length_nil, plug_nil] at hk6 ⊢
    rw [hJE.shape] at hk6
    have hsz1 : size (node l1 v leaf (r1 :: dsOf t1)) = size t1 := by
      rw [(pot_switch_nil l1 r1 v (dsOf t1)).2, ← et1]
    rw [hpot3] at hk6
    rw [hsp0] at hk2
    have hL1 : Nat.log 2 (size t1) ≤ Nat.log 2 n :=
      Nat.log_mono_right ((size_le_plug t1 ctx1).trans (I2.size_le B n rfl))
    have hLT : Nat.log 2 (size (node l v leaf dvE)) ≤ Nat.log 2 n :=
      Nat.log_mono_right ((size_le_plug _ []).trans (I8.size_le B n rfl))
    simp only [plug_nil] at hpotE
    rw [hsz1] at hk6
    have hd : spE.length ≤ n := by
      have := hJE.rtY_le.2.2; omega
    omega

theorem accessS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {G : List VT} {F : Forest}
    (hI : Inv B n (mem c) G) (hR : Rep B n (mem c) G F) {v : ℕ} (hv : c.nreg 189 = v)
    (hvn : v < n) {gb ga : List VT} {T0 : VT} (hG : G = gb ++ T0 :: ga) (hvT : v ∈ nodes T0) :
    ∃ c' k l dv, Exec P W (accessS B) c c' k ∧
      Inv B n (mem c') (gb ++ node l v leaf dv :: ga) ∧
      Rep B n (mem c') (gb ++ node l v leaf dv :: ga) F ∧ Bnd B n (mem c') ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 193 c c' ∧ c'.nreg 189 = v ∧ c'.nreg 151 = n ∧
      k + 16400 * potL (gb ++ node l v leaf dv :: ga) ≤
        16400 * potL G + 147600 * Nat.log 2 n + 21000 ∧ rv B (mem c') v = false := by
  obtain ⟨c', k, l, dv, e, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    accessS_execE (P := P) B n hc hW hn hb hI hR.toRepE hv hvn hG hvT
  exact ⟨c', k, l, dv, e, h1, ⟨h2, fun u hu => by rw [h9]; exact hR.fpar u hu⟩, h3, h4, h5, h6,
    h7, h8, h10⟩

end

end DynTree

end PlanarFlow
