module

public import PlanarFlow.DynTree.OpsCode
public import Mathlib.Tactic.IntervalCases

/-!
# Dynamic trees: initialisation on the machine

`initS B` writes the records of the nodes `0, …, n` (`n = r151`): every pointer is `n`, the
argmin and the leftmost node of `u` are `u`, the value, tag, minimum and sum are `0`, the count is
`1` (`0` for the nil record `n`). Then the memory stores the virtual forest of the `n` isolated
nodes, which represents `Forest.init n` and has potential `0` (`init_exec`, within
`80 (n + 1) + 20` steps).
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- The body of the initialisation loop: the record of `u = r193`. -/
def initBody (B : ℕ) : Stmt :=
  block (st B 193 0 151 ++ st B 193 1 151 ++ st B 193 2 151 ++ st B 193 3 193 ++ st B 193 4 151 ++
    st B 193 5 193 ++ st B 193 6 193 ++ st B 193 7 193 ++ st B 193 8 193 ++ st B 193 9 193 ++
    st B 193 10 196 ++ st B 193 11 151 ++ st B 193 12 151 ++ st B 193 13 151 ++
    st B 193 14 151 ++ st B 193 15 151 ++
    stR B 193 0 195 ++ stR B 193 1 195 ++ stR B 193 2 195 ++ stR B 193 3 195 ++
    stR B 193 4 196 ++ stR B 193 5 195 ++ stR B 193 6 195 ++ stR B 193 7 195 ++
    stR B 193 8 195 ++ [.addN 193 193 195])

/-- **Initialisation** of the structure at base `B` for `n = r151` nodes. -/
def initS (B : ℕ) : Stmt :=
  .seq (block [.constN 193 0, .constN 195 1, .addN 194 151 195, .constN 196 0, .constR 195 0,
    .constR 196 1]) <|
  .seq (.whileLtN 193 194 (initBody B)) (block ([.copyN 193 151] ++ stR B 193 4 195))

lemma upd_adr' {α : Type} (f : ℕ → α) {B u u' j j' : ℕ} (v : α) (hj : j < 16) (hj' : j' < 16) :
    upd f (u' * 16 + (B + j')) v (u * 16 + (B + j)) =
      if u = u' ∧ j = j' then v else f (u * 16 + (B + j)) := upd_adr f v hj hj'

lemma memFrame_upd' {α : Type} (f : ℕ → α) {B n u j : ℕ} (v : α) (hu : u ≤ n) (hj : j < 16)
    {a : ℕ} (ha : a < B ∨ B + 16 * (n + 1) ≤ a) : upd f (u * 16 + (B + j)) v a = f a :=
  memFrame_upd (B := B) (n := n) f v hu hj ha

/-- The virtual forest of `n` isolated nodes. -/
def G0 (n : ℕ) : List VT := (List.range n).map fun u => node leaf u leaf []

/-- The words of an initialised record. -/
def initN (n x j : ℕ) : ℕ :=
  if j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 then x else if j = 10 then 0 else n

section
variable {P : Input} {W : ℕ}

/-- The loop invariant of the initialisation. -/
def InitI (B n : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 151 = n ∧ c.nreg 194 = n + 1 ∧ c.nreg 195 = 1 ∧ c.rreg 195 = 0 ∧
    c.rreg 196 = 1 ∧ c.nreg 193 ≤ n + 1 ∧
    c.nreg 196 = 0 ∧
    (∀ x < c.nreg 193, ∀ j < 16, c.nmem (adr B x j) = initN n x j) ∧
    (∀ x < c.nreg 193, ∀ j < 9, j ≠ 4 → c.rmem (adr B x j) = 0) ∧
    (∀ x < c.nreg 193, c.rmem (adr B x 4) = 1) ∧
    MemFrame B n (mem c₀) (mem c) ∧ FrK 197 c₀ c

set_option maxHeartbeats 2000000 in
theorem initBody_exec (B n : ℕ) (hW : B + 16 * (n + 1) ≤ W) {c₀ c : Config}
    (hI : InitI (W := W) B n c₀ c) (ht : c.nreg 193 < c.nreg 194) :
    ∃ c' k, Exec P W (initBody B) c c' k ∧ InitI (W := W) B n c₀ c' ∧ k ≤ 130 ∧
      n + 1 - c'.nreg 193 < n + 1 - c.nreg 193 := by
  obtain ⟨hw, h151, h194, h195, r195, r196, hle, h196, hN, hR, hC, hmf, hfr⟩ := hI
  generalize hu : c.nreg 193 = u at *
  have hun : u ≤ n := by omega
  unfold initBody
  simp only [st, stR, ad, List.cons_append, List.nil_append, List.append_assoc]
  exec_block
  any_goals (config_simp; (try simp only [hu, h151, h195]); omega)
  refine ⟨⟨‹WordsBounded W _›, by config_simp; exact h151, by config_simp; exact h194,
    by config_simp; exact h195, by config_simp; exact r195, by config_simp; exact r196,
    by config_simp; rw [hu, h195]; omega, by config_simp; exact h196, ?_, ?_, ?_, ?_, ?_⟩,
    by omega, ?_⟩
  · intro x hx j hj
    config_simp at hx
    rw [hu, h195] at hx
    have hN' := hN
    simp only [adr] at hN' ⊢
    config_simp
    simp only [hu, h151, h196]
    by_cases hxu : x = u
    · subst hxu
      simp only [upd, Nat.add_left_cancel_iff]
      interval_cases j <;> simp [initN]
    · have hne : ∀ k < 16, x * 16 + (B + j) ≠ u * 16 + (B + k) := by intro k hk; omega
      simp (disch := omega) only [upd_ne_of]
      exact hN' x (by omega) j hj
  · intro x hx j hj hj4
    config_simp at hx
    rw [hu, h195] at hx
    have hR' := hR
    simp only [adr] at hR' ⊢
    config_simp
    simp only [hu, r195, r196]
    by_cases hxu : x = u
    · subst hxu
      simp only [upd, Nat.add_left_cancel_iff]
      interval_cases j <;> simp_all
    · have hne : ∀ k < 16, x * 16 + (B + j) ≠ u * 16 + (B + k) := by intro k hk; omega
      simp (disch := omega) only [upd_ne_of]
      exact hR' x (by omega) j hj hj4
  · intro x hx
    config_simp at hx
    rw [hu, h195] at hx
    have hC' := hC
    simp only [adr] at hC' ⊢
    config_simp
    simp only [hu, r195, r196]
    by_cases hxu : x = u
    · subst hxu
      simp only [upd, Nat.add_left_cancel_iff]
      simp
    · have hne : ∀ k < 16, x * 16 + (B + 4) ≠ u * 16 + (B + k) := by intro k hk; omega
      simp (disch := omega) only [upd_ne_of]
      exact hC' x (by omega)
  · have hun' : u ≤ n := by omega
    refine hmf.trans B n fun a ha => ⟨?_, ?_⟩
    · config_simp; (try simp only [hu, mem])
      simp (disch := omega) only [upd_ne_of]
    · config_simp; (try simp only [hu, mem])
      simp (disch := omega) only [upd_ne_of]
  · refine hfr.trans ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩
    config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
  · config_simp; rw [hu, h195]; omega


lemma potL_G0 (n : ℕ) : potL (G0 n) = 0 := by
  unfold G0
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, potL_append, ih]
    simp [pot_node]

lemma nodesL_G0 (n : ℕ) : nodesL (G0 n) = List.range n := by
  unfold G0
  induction n with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, nodesL_append, ih]; simp

lemma mem_G0 {n : ℕ} {T : VT} (h : T ∈ G0 n) : ∃ u < n, T = node leaf u leaf [] := by
  unfold G0 at h
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
  exact ⟨u, List.mem_range.mp hu, rfl⟩

/-- **Initialisation.** -/
theorem init_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) :
    ∃ c' k, Exec P W (initS B) c c' k ∧ k ≤ 140 * (n + 1) + 20 ∧
      LCT B n (Forest.init n) (G0 n) c' ∧ potL (G0 n) = 0 ∧ MemFrame B n (mem c) (mem c') ∧
      FrK 197 c c' := by
  unfold initS
  refine spec_seq ?_
  exec_block
  any_goals (config_simp; (try simp only [hn]); omega)
  refine spec_gen fun c1 hc1 => ?_
  have hI1 : InitI (W := W) B n c c1 := by
    rw [hc1]
    refine ⟨‹WordsBounded W _›, by config_simp; exact hn, by config_simp; rw [hn],
      by config_simp, by config_simp; simp, by config_simp; simp, by config_simp; omega,
      by config_simp,
      fun x hx => by config_simp at hx; omega, fun x hx => by config_simp at hx; omega,
      fun x hx => by config_simp at hx; omega, MemFrame.refl B n _,
      ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩⟩
    config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
    exact ⟨trivial, trivial⟩
  obtain ⟨c2, k2, e2, hI2, hstop, hk2⟩ := Exec.whileLtN_bounded (P := P) (a := 193) (b := 194)
    (body := initBody B) (InitI (W := W) B n c) (fun c' => n + 1 - c'.nreg 193) 130
    (fun _ h => h.1) (fun c' h ht => by
      obtain ⟨c'', k, e, h', hk, hμ⟩ := initBody_exec (P := P) B n hW h ht
      exact ⟨c'', k, e, h', hk, hμ⟩) hI1
  refine spec_seq_known e2 (fun hw2 => ?_)
  obtain ⟨-, h151, h194, h195, r195, r196, hle, -, hN, hR, hC, hmf, hfr⟩ := hI2
  have h193 : c2.nreg 193 = n + 1 := by omega
  have hblk : ∃ c3 k3, Exec P W (block ([.copyN 193 151] ++ stR B 193 4 195)) c2 c3 k3 ∧
      k3 ≤ 6 ∧ c3.nmem = c2.nmem ∧ c3.rmem = upd c2.rmem (adr B n 4) 0 ∧ c3.nreg 151 = n ∧
      FrK 197 c2 c3 := by
    simp only [stR, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [h151]); omega)
    refine ⟨by omega, rfl, ?_, by config_simp; exact h151,
      ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩⟩
    · config_simp; rw [h151, r195]; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
  obtain ⟨c3, k3, e3, hk3, hnm, hrm, h151', f3⟩ := hblk
  -- the fields
  have fN : ∀ u ≤ n, ∀ j < 16, (mem c3).nm (adr B u j) = initN n u j := fun u hu j hj => by
    simp only [mem]; rw [hnm]; exact hN u (by omega) j hj
  have fR : ∀ u ≤ n, ∀ j < 9, j ≠ 4 → (mem c3).rm (adr B u j) = 0 := fun u hu j hj hj4 => by
    simp only [mem]; rw [hrm, upd_adr _ _ (by omega) (by omega)]
    simp only [hj4, and_false, ite_false]; exact hR u (by omega) j hj hj4
  have fC : ∀ u < n, cnt B (mem c3) u = 1 := fun u hu => by
    simp only [cnt, mem]; rw [hrm, upd_adr _ _ (by omega) (by omega)]
    simp only [show u ≠ n by omega, false_and, ite_false]; exact hC u (by omega)
  have fCn : cnt B (mem c3) n = 0 := by simp [cnt, mem, hrm]
  have pr : ∀ u ≤ n, par B (mem c3) u = n := fun u hu => by
    rw [par, fN u hu 0 (by omega)]; simp [initN]
  have lcn : ∀ u ≤ n, lc B (mem c3) u = n := fun u hu => by
    rw [lc, fN u hu 1 (by omega)]; simp [initN]
  have rcn : ∀ u ≤ n, rc B (mem c3) u = n := fun u hu => by
    rw [rc, fN u hu 2 (by omega)]; simp [initN]
  have fpn : ∀ u ≤ n, fpar B (mem c3) u = n := fun u hu => by
    rw [fpar, fN u hu 4 (by omega)]; simp [initN]
  have rvn : ∀ u ≤ n, rv B (mem c3) u = false := fun u hu => by
    simp only [rv, rvw]; rw [fN u hu 10 (by omega)]; simp [initN]
  have hnil : NilOK B n (mem c3) := ⟨lcn n le_rfl, rcn n le_rfl, fCn,
    fR n le_rfl 3 (by omega) (by omega), fR n le_rfl 8 (by omega) (by omega)⟩
  have hEnc : ∀ u < n, Enc B n (mem c3) (node leaf u leaf []) n false := by
    intro u hu
    rw [enc_node_iff_clean B n (rvn u hu.le)]
    refine ⟨pr u hu.le, lcn u hu.le, rcn u hu.le, ?_, .leaf _ _, .leaf _ _, by simp⟩
    unfold AggOK
    rw [rvn u hu.le, lcn u hu.le, rcn u hu.le]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e : ∀ j, j < 16 → (mem c3).nm (adr B u j) = initN n u j := fun j hj => fN u hu.le j hj
    simp only [own, rd, Ag.addTags, comb, lmn, cnt, sm, sm2, mn, mn2, am, amr, am2, am2r, lm, rtm,
      tg, tg2, vl, vl2, lt_irrefl, false_and, ite_false, e 3 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega), initN]
    rw [fR u hu.le 0 (by omega) (by omega), fR u hu.le 2 (by omega) (by omega),
      fR u hu.le 3 (by omega) (by omega), fR u hu.le 5 (by omega) (by omega),
      fR u hu.le 7 (by omega) (by omega), fR u hu.le 8 (by omega) (by omega),
      fR n le_rfl 3 (by omega) (by omega), fR n le_rfl 8 (by omega) (by omega),
      fR n le_rfl 1 (by omega) (by omega), fR n le_rfl 6 (by omega) (by omega)]
    have h4 : (mem c3).rm (adr B u 4) = 1 := fC u hu
    have h4n : (mem c3).rm (adr B n 4) = 0 := fCn
    rw [h4, h4n]
    ext <;> simp
  have keyV : ∀ {u : ℕ} {w : ℝ} (k : Bool) (L : List ℕ), (∀ x ∈ L, x < n) →
      (u, w) ∈ dVL B (mem c3) (L.map fun u => node leaf u leaf []) k → w = 0 := by
    intro u w k L hlt hL
    induction L with
    | nil => simp at hL
    | cons x L ih =>
      simp only [List.map_cons, dVL_cons, rs_node, rs_leaf, List.nil_append, shift_cons,
        shift_nil, dV_node, dV_leaf, dVL_nil, List.append_nil, List.mem_append,
        List.mem_singleton, Prod.mk.injEq] at hL
      rcases hL with ⟨-, h⟩ | hL
      · have hx := hlt x (by simp)
        rw [h]
        cases k <;> simp [vlc, tgc, vl, tg, vl2, tg2, fR x hx.le 0 (by omega) (by omega),
          fR x hx.le 1 (by omega) (by omega), fR x hx.le 5 (by omega) (by omega),
          fR x hx.le 6 (by omega) (by omega)]
      · exact ih (fun y hy => hlt y (by simp [hy])) hL
  refine ⟨c3, k3, e3, by omega, ⟨⟨fun T hT => ?_, ?_, ?_, hnil⟩,
    ⟨⟨fun u p h => ?_, fun u w h => ?_, fun u w h => ?_⟩, fun u hu => by rw [fpn u hu.le]; rfl⟩,
    fun u hu j hj hj' => by rw [fN u hu j hj]; simp only [initN]; split_ifs <;> omega, ?_⟩,
    potL_G0 n, ?_, ?_⟩
  · obtain ⟨u, hu, rfl⟩ := mem_G0 hT
    exact hEnc u hu
  · rw [nodesL_G0]; exact List.nodup_range
  · intro u; rw [nodesL_G0]; simp
  · have key : ∀ L : List ℕ, (u, p) ∈ dEL n (L.map fun u => node leaf u leaf []) → p = n := by
      intro L hL
      induction L with
      | nil => simp at hL
      | cons x L ih =>
        simp only [List.map_cons, dEL_cons, seq_node, seq_leaf, List.nil_append, VT.chain_cons,
          VT.chain_nil, dE_node, dE_leaf, dEL_nil, List.append_nil, List.mem_append,
          List.mem_singleton, Prod.mk.injEq] at hL
        rcases hL with ⟨-, h⟩ | hL
        · exact h
        · exact ih hL
    unfold G0 at h
    exact (key _ h).symm
  · unfold G0 at h
    exact (keyV false _ (fun x hx => List.mem_range.mp hx) h).symm
  · unfold G0 at h
    exact (keyV true _ (fun x hx => List.mem_range.mp hx) h).symm
  · exact h151'
  · refine hmf.trans B n fun a ha => ⟨by simp only [mem]; rw [hnm], ?_⟩
    simp only [mem]; rw [hrm]
    exact memFrame_upd _ _ le_rfl (by omega) ha
  · exact hfr.trans f3

end

end DynTree

end PlanarFlow
