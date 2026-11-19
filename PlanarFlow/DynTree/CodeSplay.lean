module

public import PlanarFlow.DynTree.Code

/-!
# Dynamic trees: the rotation, the push, the splay loop and the switch on the machine

* `rotS B`: the rotation of `x = r160` above its parent (`rotMem`), at most `1100` steps;
* `flipS B`: the flip of `r173` (`flipM`), at most `200` steps;
* `pushS B`: the push of the reversal bit of `r174` (`pushM`), at most `500` steps;
* `splayStepS B`: a splay step: the pushes of the grandparent, the parent and `x`, then one or
  two rotations (`splayStepM`), at most `4000` steps;
* `splayS B`: the splay loop, at most `4400` steps per splay step;
* `switchS B`: the push of `w = r160` and the switch of its preferred child (`switchR`), at most
  `1000` steps.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

section
variable {P : Input} {W : ℕ}

/-! ### Pointers are at most `n` -/

/-- Every natural field of the structure, except the reversal bit, holds a word at most `n`. -/
def Bnd (B n : ℕ) (M : Mem) : Prop := ∀ u ≤ n, ∀ j < 16, j ≠ 10 → M.nm (adr B u j) ≤ n

lemma Bnd.get {B n : ℕ} {M : Mem} (h : Bnd B n M) {u : ℕ} (hu : u ≤ n) :
    par B M u ≤ n ∧ lc B M u ≤ n ∧ rc B M u ≤ n ∧ am B M u ≤ n ∧ fpar B M u ≤ n ∧ lm B M u ≤ n :=
  ⟨h u hu 0 (by omega) (by omega), h u hu 1 (by omega) (by omega), h u hu 2 (by omega) (by omega),
    h u hu 3 (by omega) (by omega), h u hu 4 (by omega) (by omega), h u hu 5 (by omega) (by omega)⟩

lemma Bnd.get2 {B n : ℕ} {M : Mem} (h : Bnd B n M) {u : ℕ} (hu : u ≤ n) :
    rtm B M u ≤ n ∧ amr B M u ≤ n ∧ am2 B M u ≤ n ∧ am2r B M u ≤ n :=
  ⟨h u hu 6 (by omega) (by omega), h u hu 7 (by omega) (by omega), h u hu 8 (by omega) (by omega),
    h u hu 9 (by omega) (by omega)⟩

lemma Bnd.of {B n : ℕ} {M M' : Mem} (h : Bnd B n M) (h' : ∀ a, M'.nm a = M.nm a ∨ M'.nm a ≤ n) :
    Bnd B n M' := by
  intro u hu j hj hj'
  rcases h' (adr B u j) with e | e
  · rw [e]; exact h u hu j hj hj'
  · exact e

/-- `Bnd` only constrains the fields other than the reversal bit. -/
lemma Bnd.of' {B n : ℕ} {M M' : Mem} (h : Bnd B n M)
    (h' : ∀ u ≤ n, ∀ j < 16, j ≠ 10 → M'.nm (adr B u j) = M.nm (adr B u j) ∨
      M'.nm (adr B u j) ≤ n) : Bnd B n M' := by
  intro u hu j hj hj'
  rcases h' u hu j hj hj' with e | e
  · rw [e]; exact h u hu j hj hj'
  · exact e

lemma Bnd.rotP {B n : ℕ} {M : Mem} (h : Bnd B n M) {x : ℕ} (hx : x ≤ n) :
    Bnd B n (rotP B x M) := by
  obtain ⟨py, lx, rx, -, -, -⟩ := h.get hx
  obtain ⟨pz, -, -, -, -, -⟩ := h.get py
  refine h.of fun a => ?_
  simp only [DynTree.rotP]
  split_ifs <;> simp only [upd_apply] <;> split_ifs <;>
    first | exact Or.inl rfl | exact Or.inr (by assumption)

lemma Bnd.recomp {B n : ℕ} {M : Mem} (h : Bnd B n M) {u : ℕ} (hu : u ≤ n) :
    Bnd B n (recomp B n u M) := by
  obtain ⟨-, la, lb, -, -, -⟩ := h.get hu
  obtain ⟨-, -, -, ama, -, lma⟩ := h.get la
  obtain ⟨-, -, -, amb, -, -⟩ := h.get lb
  obtain ⟨-, amra, am2a, am2ra⟩ := h.get2 la
  obtain ⟨rmb, amrb, am2b, am2rb⟩ := h.get2 lb
  refine h.of fun a => ?_
  simp only [DynTree.recomp, setOwn, cmb, comb, lmn_snd]
  simp only [upd_apply]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr (by assumption)

lemma Bnd.rotMem {B n : ℕ} {M : Mem} (h : Bnd B n M) {x : ℕ} (hx : x ≤ n) :
    Bnd B n (rotMem B n x M) :=
  ((h.rotP hx).recomp (h.get hx).1).recomp hx

/-- The rotation of `x = r160` above its parent (`rotMem`). -/
def rotS (B : ℕ) : Stmt :=
  .seq (rotPS B) (.seq (.instr (.copyN 170 161)) (.seq (recompS B)
    (.seq (.instr (.copyN 170 160)) (recompS B))))

theorem rotS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n) :
    ∃ c' k, Exec P W (rotS B) c c' k ∧ k ≤ 1100 ∧ mem c' = rotMem B n x (mem c) ∧ Fr c c' ∧
      c'.nreg 160 = x := by
  obtain ⟨py, lx, rx, -, -, -⟩ := hb.get hxn
  obtain ⟨pz, -, -, -, -, -⟩ := hb.get py
  obtain ⟨c1, k1, e1, hk1, m1, f1, s160, s161⟩ := rotPS_exec (P := P) B n hc hW hx hxn py pz lx rx
  have hb1 : Bnd B n (mem c1) := m1 ▸ hb.rotP hxn
  refine spec_seq_known e1 (fun hw1 => ?_)
  have e2 := Exec.copyN (P := P) hw1 170 161
  refine spec_seq_known e2 (fun hw2 => ?_)
  have hb2 : Bnd B n (mem { c1 with nreg := upd c1.nreg 170 (c1.nreg 161) }) := hb1
  obtain ⟨-, l2, r2, -, -, -⟩ := hb2.get py
  obtain ⟨c3, k3, e3, hk3, m3, f3, s170, t160⟩ := recompS_exec (P := P) B n hw2 hW
    (u := par B (mem c) x) (by config_simp; exact s161)
    (by config_simp; rw [(f1.1 151 (by omega)).1]; exact hn) py l2 r2
  refine spec_seq_known e3 (fun hw3 => ?_)
  have e4 := Exec.copyN (P := P) hw3 170 160
  refine spec_seq_known e4 (fun hw4 => ?_)
  have hb3 : Bnd B n (mem c3) := m3 ▸ hb2.recomp py
  have hb4 : Bnd B n (mem { c3 with nreg := upd c3.nreg 170 (c3.nreg 160) }) := hb3
  obtain ⟨-, l4, r4, -, -, -⟩ := hb4.get hxn
  have h160 : c3.nreg 160 = x := by
    rw [t160]; config_simp; exact s160
  have h151 : c3.nreg 151 = n := by
    rw [(f3.1 151 (by omega)).1]; config_simp; rw [(f1.1 151 (by omega)).1]; exact hn
  obtain ⟨c5, k5, e5, hk5, m5, f5, s5, t5⟩ := recompS_exec (P := P) B n hw4 hW (u := x)
    (by config_simp; exact h160) (by config_simp; exact h151) hxn l4 r4
  refine ⟨c5, k5, e5, by omega, ?_, ?_, ?_⟩
  · rw [m5]
    change recomp B n x (mem c3) = _
    rw [m3]
    change recomp B n x (recomp B n (par B (mem c) x) (mem c1)) = _
    rw [m1]; rfl
  · have g2 : Fr c1 { c1 with nreg := upd c1.nreg 170 (c1.nreg 161) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
    have g4 : Fr c3 { c3 with nreg := upd c3.nreg 170 (c3.nreg 160) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
    exact f1.trans (g2.trans (f3.trans (g4.trans f5)))
  · rw [t5]; config_simp; exact h160


/-! ### Flipping a node and pushing a reversal bit -/

/-- Flip the node `c = r173` (`flipM`): its aggregates mirrored, its two values and tags
exchanged, its reversal bit toggled. Natural registers `r161 … r169`, reals `r160 … r168`. -/
def flipS (B : ℕ) : Stmt :=
  .seq (block (ld B 161 173 3 ++ ld B 162 173 5 ++ ld B 163 173 6 ++ ld B 164 173 7 ++
    ld B 165 173 8 ++ ld B 166 173 9 ++ ld B 167 173 10 ++
    ldR B 160 173 2 ++ ldR B 161 173 3 ++ ldR B 162 173 4 ++ ldR B 163 173 7 ++
    ldR B 164 173 8 ++ ldR B 165 173 0 ++ ldR B 166 173 5 ++ ldR B 167 173 1 ++ ldR B 168 173 6 ++
    st B 173 3 166 ++ st B 173 5 163 ++ st B 173 6 162 ++ st B 173 7 165 ++ st B 173 8 164 ++
    st B 173 9 161 ++ stR B 173 2 163 ++ stR B 173 3 164 ++ stR B 173 4 162 ++
    stR B 173 7 160 ++ stR B 173 8 161 ++ [.constN 168 0, .constN 169 1])) <|
  .seq (.ifLtN 168 167 (.instr (.copyN 169 168)) .skip) <|
  block (st B 173 10 169 ++ stR B 173 0 166 ++ stR B 173 5 165 ++ stR B 173 1 168 ++
    stR B 173 6 167)

lemma rv_iff_pos {B : ℕ} {M : Mem} {u : ℕ} : rv B M u = true ↔ 0 < M.nm (adr B u 10) := by
  simp only [rv, rvw, bne_iff_ne, ne_eq]; omega

set_option maxHeartbeats 1000000 in
theorem flipS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {u : ℕ} (hu : c.nreg 173 = u) (hun : u ≤ n) :
    ∃ c' k, Exec P W (flipS B) c c' k ∧ k ≤ 200 ∧ mem c' = flipM B u (mem c) ∧ FrK 174 c c' ∧
      c'.nreg 173 = u ∧ c'.nreg 160 = c.nreg 160 := by
  unfold flipS
  refine spec_seq ?_
  simp only [ld, ldR, st, stR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hu]); omega)
  obtain ⟨k1, e1, hk1⟩ := cmovN_exec (P := P) ‹WordsBounded W _› 168 167 169 168
  refine spec_seq_known e1 (fun hw1 => ?_)
  exec_block
  any_goals (config_simp; (try simp only [hu]); omega)
  refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_, ?_⟩
  · simp only [mem]
    config_simp
    simp only [hu]
    have e : ∀ M : Mem, (if rv B M u = true then (0 : ℕ) else 1) =
        if 0 < M.nm (adr B u 10) then 0 else 1 := by
      intro M; simp only [rv_iff_pos]
    simp only [flipM, e]
    simp only [setOwn, own, Ag.mir, mem, vl, vl2, tg, tg2, cnt, sm, sm2, mn, mn2, am,
      amr, am2, am2r, lm, rtm, adr]
    rfl
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
    exact ⟨trivial, trivial⟩
  · config_simp; simp (disch := omega) only [upd_ne_of]
  · config_simp; exact hu
  · config_simp


/-- Push the reversal bit of `x = r174` (`pushM`): if it is set, flip both children, swap them,
and clear the bit. Natural registers `r161 … r177`, reals `r160 … r168`. -/
def pushS (B : ℕ) : Stmt :=
  .seq (block (ld B 167 174 10 ++ [.constN 168 0])) <|
  .ifLtN 168 167
    (.seq (block (ld B 175 174 1 ++ ld B 176 174 2 ++ [.copyN 173 175])) <|
     .seq (flipS B) <| .seq (block [.copyN 173 176]) <| .seq (flipS B) <|
     block (st B 174 1 176 ++ st B 174 2 175 ++ [.constN 177 0] ++ st B 174 10 177))
    .skip

lemma Bnd.flipM {B n : ℕ} {M : Mem} (h : Bnd B n M) {u : ℕ} (hu : u ≤ n) :
    Bnd B n (flipM B u M) := by
  obtain ⟨-, -, -, am', -, lm'⟩ := h.get hu
  obtain ⟨rm', amr', am2', am2r'⟩ := h.get2 hu
  refine h.of' fun v hv j hj hj' => ?_
  simp only [DynTree.flipM, setOwn, own, Ag.mir, upd_adr _ _ hj (show 10 < 16 by omega),
    upd_adr _ _ hj (show 9 < 16 by omega), upd_adr _ _ hj (show 8 < 16 by omega),
    upd_adr _ _ hj (show 7 < 16 by omega), upd_adr _ _ hj (show 6 < 16 by omega),
    upd_adr _ _ hj (show 5 < 16 by omega), upd_adr _ _ hj (show 3 < 16 by omega)]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr (by assumption) | omega

lemma Bnd.pushM {B n : ℕ} {M : Mem} (h : Bnd B n M) {x : ℕ} (hx : x ≤ n) :
    Bnd B n (pushM B x M) := by
  obtain ⟨-, la, lb, -, -, -⟩ := h.get hx
  unfold DynTree.pushM
  split_ifs
  · have h2 := (h.flipM la).flipM lb
    refine h2.of' fun v hv j hj hj' => ?_
    simp only [upd_adr _ _ hj (show 10 < 16 by omega), upd_adr _ _ hj (show 2 < 16 by omega),
      upd_adr _ _ hj (show 1 < 16 by omega)]
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr (by assumption) | omega
  · exact h

theorem pushS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hb : Bnd B n (mem c)) {x : ℕ} (hx : c.nreg 174 = x) (hxn : x ≤ n) :
    ∃ c' k, Exec P W (pushS B) c c' k ∧ k ≤ 500 ∧ mem c' = pushM B x (mem c) ∧ Fr c c' ∧
      c'.nreg 174 = x ∧ c'.nreg 160 = c.nreg 160 := by
  obtain ⟨-, la, lb, -, -, -⟩ := hb.get hxn
  have la' := la; have lb' := lb
  simp only [lc, rc, mem, adr] at la' lb'
  unfold pushS
  refine spec_seq ?_
  simp only [ld, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx]); omega)
  refine spec_gen fun c1 hc1 => ?_
  have hw1 : WordsBounded W c1 := hc1 ▸ ‹WordsBounded W _›
  have m1 : mem c1 = mem c := by rw [hc1]; rfl
  have r167 : c1.nreg 167 = c.nmem (adr B x 10) := by rw [hc1]; config_simp; rw [hx]; rfl
  have r168 : c1.nreg 168 = 0 := by rw [hc1]; config_simp
  have r174 : c1.nreg 174 = x := by rw [hc1]; config_simp; exact hx
  have r160 : c1.nreg 160 = c.nreg 160 := by rw [hc1]; config_simp
  have f1 : Fr c c1 := by
    rw [hc1]
    refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · config_simp; simp (disch := omega) only [upd_ne_of]
  clear hc1
  by_cases hrv : 0 < c.nmem (adr B x 10)
  · have hrv' : rv B (mem c) x = true := rv_iff_pos.mpr hrv
    refine spec_ifLtN_true (by rw [r168, r167]; exact hrv) ?_
    refine spec_seq ?_
    exec_block
    any_goals (config_simp; (try simp only [r174]); omega)
    refine spec_gen fun c2 hc2 => ?_
    have hw2 : WordsBounded W c2 := hc2 ▸ ‹WordsBounded W _›
    have m2 : mem c2 = mem c := by rw [hc2, ← m1]; rfl
    have r173 : c2.nreg 173 = lc B (mem c) x := by
      rw [hc2]; config_simp; rw [r174, ← m1]; rfl
    have r175 : c2.nreg 175 = lc B (mem c) x := by
      rw [hc2]; config_simp; rw [r174, ← m1]; rfl
    have r176 : c2.nreg 176 = rc B (mem c) x := by
      rw [hc2]; config_simp; rw [r174, ← m1]; rfl
    have r174' : c2.nreg 174 = x := by rw [hc2]; config_simp; exact r174
    have r160' : c2.nreg 160 = c.nreg 160 := by rw [hc2]; config_simp; exact r160
    have f2 : Fr c1 c2 := by
      rw [hc2]
      refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
      · config_simp
        simp (disch := omega) only [upd_out _ _ _ hr]
        try exact ⟨trivial, trivial⟩
      · config_simp; simp (disch := omega) only [upd_ne_of]
    clear hc2
    obtain ⟨c3, k3, e3, hk3, m3, f3, s173, s160⟩ := flipS_exec (P := P) B n hw2 hW r173 la
    refine spec_seq_known e3 (fun hw3 => ?_)
    have r176' : c3.nreg 176 = rc B (mem c) x := by
      rw [f3.2.1 176 (by omega) (by omega)]; exact r176
    have r175' : c3.nreg 175 = lc B (mem c) x := by
      rw [f3.2.1 175 (by omega) (by omega)]; exact r175
    have r174'' : c3.nreg 174 = x := by rw [f3.2.1 174 (by omega) (by omega)]; exact r174'
    have e4 := Exec.copyN (P := P) hw3 173 176
    refine spec_seq_known (Exec.block_cons e4 (Exec.block_nil e4.wb_right)) (fun hw4 => ?_)
    obtain ⟨c5, k5, e5, hk5, m5, f5, s173', s160'⟩ := flipS_exec (P := P) B n hw4 hW
      (u := rc B (mem c) x) (by config_simp; exact r176') lb
    refine spec_seq_known e5 (fun hw5 => ?_)
    have g4 : FrK 174 c3 { c3 with nreg := upd c3.nreg 173 (c3.nreg 176) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
    have r174_5 : c5.nreg 174 = x := by
      rw [f5.2.1 174 (by omega) (by omega)]; config_simp; exact r174''
    have r175_5 : c5.nreg 175 = lc B (mem c) x := by
      rw [f5.2.1 175 (by omega) (by omega)]; config_simp; exact r175'
    have r176_5 : c5.nreg 176 = rc B (mem c) x := by
      rw [f5.2.1 176 (by omega) (by omega)]; config_simp; exact r176'
    have r160_5 : c5.nreg 160 = c.nreg 160 := by
      rw [s160']; config_simp; rw [s160, r160']
    exec_block
    any_goals (config_simp; (try simp only [r174_5]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · have hm : mem c5 = flipM B (rc B (mem c) x) (flipM B (lc B (mem c) x) (mem c)) := by
        rw [m5]; change flipM B _ (mem c3) = _; rw [m3, m2]
      have hpush : pushM B x (mem c) = ⟨upd (upd (upd (flipM B (rc B (mem c) x)
          (flipM B (lc B (mem c) x) (mem c))).nm (adr B x 1) (rc B (mem c) x)) (adr B x 2)
          (lc B (mem c) x)) (adr B x 10) 0,
          (flipM B (rc B (mem c) x) (flipM B (lc B (mem c) x) (mem c))).rm⟩ := by
        simp only [DynTree.pushM, hrv', ↓reduceIte]
      rw [hpush, ← hm]
      simp only [mem]
      config_simp
      simp only [r174_5, r175_5, r176_5, adr]
      rfl
    · refine f1.trans (f2.trans ((f3.mono (by omega)).trans ((g4.mono (by omega)).trans
        ((f5.mono (by omega)).trans ?_))))
      refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
      · config_simp
        simp (disch := omega) only [upd_out _ _ _ hr]
        try exact ⟨trivial, trivial⟩
      · config_simp; simp (disch := omega) only [upd_ne_of]
    · config_simp; exact r174_5
    · config_simp; exact r160_5
  · have hrv' : rv B (mem c) x = false := by
      have := mt (rv_iff_pos (B := B) (M := mem c) (u := x)).mp hrv; simpa using this
    refine spec_ifLtN_false (by rw [r168, r167]; exact hrv) (spec_skip hw1 ?_)
    refine ⟨by omega, ?_, f1, r174, r160⟩
    rw [m1]; simp [DynTree.pushM, hrv']


/-- Push the reversal bit of the node in register `k`. -/
def cpushS (B k : ℕ) : Stmt := .seq (block [.copyN 174 k]) (pushS B)

theorem cpushS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hb : Bnd B n (mem c)) {k x : ℕ} (hk : c.nreg k = x) (hxn : x ≤ n) :
    ∃ c' k', Exec P W (cpushS B k) c c' k' ∧ k' ≤ 501 ∧ mem c' = pushM B x (mem c) ∧ Fr c c' ∧
      c'.nreg 160 = c.nreg 160 := by
  have e1 := Exec.copyN (P := P) hc 174 k
  refine spec_seq_known (Exec.block_cons e1 (Exec.block_nil e1.wb_right)) (fun hw1 => ?_)
  obtain ⟨c2, k2, e2, hk2, m2, f2, -, s160⟩ := pushS_exec (P := P) B n hw1 hW (x := x) hb
    (by config_simp; exact hk) hxn
  refine ⟨c2, k2, e2, by omega, m2, ?_, by rw [s160]; config_simp⟩
  have g : Fr c { c with nreg := upd c.nreg 174 (c.nreg k) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)]; try exact ⟨rfl, rfl⟩,
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  exact g.trans f2

/-! ### The splay step -/

/-- One splay step at `x = r160` (`splayStepM`). Registers: `r178 = x`, `r179 = y`, `r180 = z`,
`r181 = lc z`, `r182 = rc z`, `r183 = lc y`, flags `r184 = [lc z = y]`, `r185 = [rc z = y]`,
`r186 = r184 + r185`, `r187 = [lc y = x]`, `r188 = 0`. The test "`y` is a child of `z`" is read
before the pushes (they keep it); the directions are read after them. -/
def splayStepS (B : ℕ) : Stmt :=
  .seq (block ([.copyN 178 160] ++ ld B 179 160 0 ++ ld B 180 179 0 ++ ld B 181 180 1 ++
    ld B 182 180 2 ++ [.constN 188 0])) <|
  .seq (eqS 181 179 184) <| .seq (eqS 182 179 185) <| .seq (.instr (.addN 186 184 185)) <|
  .ifLtN 188 186
    (.seq (cpushS B 180) <| .seq (cpushS B 179) <| .seq (cpushS B 178) <|
     .seq (block (ld B 181 180 1 ++ ld B 183 179 1)) <|
     .seq (eqS 181 179 184) <| .seq (eqS 183 160 187) <|
     .ifLtN 184 187 (.seq (rotS B) (rotS B))
      (.ifLtN 187 184 (.seq (rotS B) (rotS B))
        (.seq (.instr (.copyN 160 179)) (.seq (rotS B) (.seq (.instr (.copyN 160 178)) (rotS B))))))
    (.seq (cpushS B 179) <| .seq (cpushS B 178) (rotS B))

lemma ite01_lt {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : ℕ) < if q then 1 else 0) ↔ (¬ p ∧ q) := by
  split_ifs <;> simp_all

lemma ite01_pos {p q : Prop} [Decidable p] [Decidable q] :
    (0 < (if p then 1 else 0 : ℕ) + if q then 1 else 0) ↔ (p ∨ q) := by
  split_ifs <;> simp_all

/-- Two rotations of `x = r160`. -/
theorem rot2_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n) :
    ∃ c' k, Exec P W (.seq (rotS B) (rotS B)) c c' k ∧ k ≤ 2200 ∧
      mem c' = rotMem B n x (rotMem B n x (mem c)) ∧ Fr c c' ∧ c'.nreg 160 = x := by
  obtain ⟨c1, k1, e1, hk1, m1, f1, s1⟩ := rotS_exec (P := P) B n hc hW hn hb hx hxn
  obtain ⟨c2, k2, e2, hk2, m2, f2, s2⟩ := rotS_exec (P := P) B n e1.wb_right hW
    (by rw [(f1.1 151 (by omega)).1]; exact hn) (m1 ▸ hb.rotMem hxn) s1 hxn
  exact ⟨c2, k1 + k2, .seq e1 e2, by omega, by rw [m2, m1], f1.trans f2, s2⟩


theorem splayStepS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {x : ℕ}
    (hx : c.nreg 160 = x) (hxn : x ≤ n) :
    ∃ c' k, Exec P W (splayStepS B) c c' k ∧ k ≤ 4000 ∧ mem c' = splayStepM B n x (mem c) ∧
      FrK 189 c c' ∧ c'.nreg 160 = x := by
  obtain ⟨py, -, -, -, -, -⟩ := hb.get hxn
  obtain ⟨pz, ly, -, -, -, -⟩ := hb.get py
  obtain ⟨-, lz, rz, -, -, -⟩ := hb.get pz
  have py' := py; have pz' := pz; have lz' := lz; have rz' := rz
  simp only [par, lc, rc, mem, adr] at py' pz' lz' rz'
  unfold splayStepS
  refine spec_seq ?_
  simp only [ld, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx]); omega)
  obtain ⟨k1, e1, hk1⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 181 179 184
    (by decide) (by decide)
  refine spec_seq_known e1 (fun hw1 => ?_)
  obtain ⟨k2, e2, hk2⟩ := eqS_exec (P := P) hw1 (by omega) 182 179 185 (by decide) (by decide)
  refine spec_seq_known e2 (fun hw2 => ?_)
  refine spec_seq (spec_instr (Exec.addN hw2 186 184 185 (by config_simp; split_ifs <;> omega))
    (fun hw3 => ?_))
  refine spec_gen fun c5 hc5 => ?_
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
  have f5 : FrK 189 c c5 := by
    rw [hc5]
    refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
    · config_simp; simp (disch := omega) only [upd_ne_of]
  clear hc5
  have hb5 : Bnd B n (mem c5) := m5 ▸ hb
  -- keeping registers across a push
  have keep : ∀ {c c' : Config}, Fr c c' → ∀ r, 178 ≤ r → r < 197 → c'.nreg r = c.nreg r :=
    fun h r h1 h2 => h.2.1 r h1 h2
  generalize hy : par B (mem c) x = y at r179 r180 r186 py pz ly lz rz
  generalize hz : par B (mem c) y = z at r180 r186 pz lz rz
  have hCi : IsChild B (mem c) y ↔ (lc B (mem c) z = y ∨ rc B (mem c) z = y) := by
    unfold IsChild; rw [hz]
  by_cases hC : IsChild B (mem c) y
  · refine spec_ifLtN_true (by rw [r188, r186, ite01_pos]; exact hCi.mp hC) ?_
    -- the three pushes
    obtain ⟨c6, k6, e6, hk6, m6, f6, s6⟩ := cpushS_exec (P := P) B n hw5 hW hb5 r180 pz
    refine spec_seq_known e6 (fun hw6 => ?_)
    have hb6 : Bnd B n (mem c6) := m6 ▸ hb5.pushM pz
    obtain ⟨c7, k7, e7, hk7, m7, f7, s7⟩ := cpushS_exec (P := P) B n hw6 hW hb6
      (by rw [keep f6 179 (by omega) (by omega)]; exact r179) py
    refine spec_seq_known e7 (fun hw7 => ?_)
    have hb7 : Bnd B n (mem c7) := m7 ▸ hb6.pushM py
    obtain ⟨c8, k8, e8, hk8, m8, f8, s8⟩ := cpushS_exec (P := P) B n hw7 hW hb7
      (by rw [keep f7 178 (by omega) (by omega), keep f6 178 (by omega) (by omega)]; exact r178) hxn
    refine spec_seq_known e8 (fun hw8 => ?_)
    have hb8 : Bnd B n (mem c8) := m8 ▸ hb7.pushM hxn
    generalize hM3 : pushM B x (pushM B y (pushM B z (mem c))) = M3
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
    have f68 : FrK 189 c5 c8 := (f6.mono (by omega)).trans ((f7.mono (by omega)).trans
      (f8.mono (by omega)))
    -- read the directions
    refine spec_seq ?_
    exec_block
    any_goals (config_simp; (try simp only [h179, h180]); omega)
    obtain ⟨k9, e9, hk9⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 181 179 184
      (by decide) (by decide)
    refine spec_seq_known e9 (fun hw9 => ?_)
    obtain ⟨k10, e10, hk10⟩ := eqS_exec (P := P) hw9 (by omega) 183 160 187 (by decide) (by decide)
    refine spec_seq_known e10 (fun hw10 => ?_)
    refine spec_gen fun c11 hc11 => ?_
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
    have f11 : FrK 189 c8 c11 := by
      rw [hc11]
      refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
      · config_simp
        simp (disch := omega) only [upd_out _ _ _ hr]
      · config_simp; simp (disch := omega) only [upd_ne_of]
    clear hc11
    have hb11 : Bnd B n (mem c11) := by rw [m11, ← hm8]; exact hb8
    have hstepM : splayStepM B n x (mem c) = if (lc B M3 y = x ↔ lc B M3 z = y)
        then rotMem B n x (rotMem B n y M3) else rotMem B n x (rotMem B n x M3) := by
      unfold splayStepM; rw [hy, ite_of_pos hC, hz, hM3]
    have fr : FrK 189 c c11 := f5.trans (f68.trans f11)
    by_cases hs : (lc B M3 y = x ↔ lc B M3 z = y)
    · -- zig-zig
      refine spec_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, h'⟩ => h (hs.mp h')) ?_
      refine spec_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, h'⟩ => h (hs.mpr h')) ?_
      have e12 := Exec.copyN (P := P) hw11 160 179
      refine spec_seq_known e12 (fun hw12 => ?_)
      obtain ⟨c13, k13, e13, hk13, m13, f13, s13⟩ := rotS_exec (P := P) B n hw12 hW
        (by config_simp; exact q151) (by exact hb11) (by config_simp; exact q179) py
      refine spec_seq_known e13 (fun hw13 => ?_)
      have e14 := Exec.copyN (P := P) hw13 160 178
      refine spec_seq_known e14 (fun hw14 => ?_)
      have h178' : c13.nreg 178 = x := by
        rw [f13.2.1 178 (by omega) (by omega)]; config_simp; exact q178
      have hb13 : Bnd B n (mem c13) := m13 ▸ hb11.rotMem py
      obtain ⟨c15, k15, e15, hk15, m15, f15, s15⟩ := rotS_exec (P := P) B n hw14 hW
        (by config_simp; rw [(f13.1 151 (by omega)).1]; config_simp; exact q151) (by exact hb13)
        (by config_simp; exact h178') hxn
      refine ⟨c15, k15, e15, by omega, ?_, ?_, s15⟩
      · rw [m15]
        change rotMem B n x (mem c13) = _
        rw [m13]
        change rotMem B n x (rotMem B n y (mem c11)) = _
        rw [m11, hstepM, ite_of_pos hs]
      · have g12 : FrK 189 c11 { c11 with nreg := upd c11.nreg 160 (c11.nreg 179) } :=
          ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
            fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
        have g14 : FrK 189 c13 { c13 with nreg := upd c13.nreg 160 (c13.nreg 178) } :=
          ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
            fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
        exact fr.trans (g12.trans ((f13.mono (by omega)).trans (g14.trans (f15.mono (by omega)))))
    · have zz : ∀ c' k, Exec P W (.seq (rotS B) (rotS B)) c11 c' k → k ≤ 2200 →
          mem c' = rotMem B n x (rotMem B n x M3) → Fr c11 c' → c'.nreg 160 = x →
          k ≤ 3000 ∧ mem c' = splayStepM B n x (mem c) ∧ FrK 189 c c' ∧ c'.nreg 160 = x := by
        intro c' k _ hk hm hf h
        exact ⟨by omega, by rw [hm, hstepM, ite_of_neg hs], fr.trans (hf.mono (by omega)), h⟩
      by_cases h1 : lc B M3 z = y
      · refine spec_ifLtN_false (by rw [q184, q187, ite01_lt]; exact fun ⟨h, _⟩ => h h1) ?_
        refine spec_ifLtN_true (by
          rw [q184, q187, ite01_lt]; exact ⟨fun hc => hs ⟨fun _ => h1, fun _ => hc⟩, h1⟩) ?_
        obtain ⟨c', k, e, hk, hm, hf, h160'⟩ := rot2_exec (P := P) B n hw11 hW q151 hb11 q160 hxn
        rw [m11] at hm
        obtain ⟨hk', hm', hf', h'⟩ := zz c' k e hk hm hf h160'
        exact ⟨c', k, e, by omega, hm', hf', h'⟩
      · refine spec_ifLtN_true (by
          rw [q184, q187, ite01_lt]
          exact ⟨h1, by_contra fun hc => hs ⟨fun c => absurd c hc, fun a => absurd a h1⟩⟩) ?_
        obtain ⟨c', k, e, hk, hm, hf, h160'⟩ := rot2_exec (P := P) B n hw11 hW q151 hb11 q160 hxn
        rw [m11] at hm
        obtain ⟨hk', hm', hf', h'⟩ := zz c' k e hk hm hf h160'
        exact ⟨c', k, e, by omega, hm', hf', h'⟩
  · refine spec_ifLtN_false (by rw [r188, r186, ite01_pos]; exact fun h => hC (hCi.mpr h)) ?_
    obtain ⟨c6, k6, e6, hk6, m6, f6, s6⟩ := cpushS_exec (P := P) B n hw5 hW hb5 r179 py
    refine spec_seq_known e6 (fun hw6 => ?_)
    have hb6 : Bnd B n (mem c6) := m6 ▸ hb5.pushM py
    obtain ⟨c7, k7, e7, hk7, m7, f7, s7⟩ := cpushS_exec (P := P) B n hw6 hW hb6
      (by rw [keep f6 178 (by omega) (by omega)]; exact r178) hxn
    refine spec_seq_known e7 (fun hw7 => ?_)
    have hb7 : Bnd B n (mem c7) := m7 ▸ hb6.pushM hxn
    obtain ⟨c8, k8, e8, hk8, m8, f8, s8⟩ := rotS_exec (P := P) B n hw7 hW
      (by rw [(f7.1 151 (by omega)).1, (f6.1 151 (by omega)).1]; exact r151) hb7
      (by rw [s7, s6]; exact r160) hxn
    refine ⟨c8, k8, e8, by omega, ?_, ?_, s8⟩
    · rw [m8, m7, m6, m5]; unfold splayStepM; rw [hy, ite_of_neg hC]
    · exact f5.trans ((f6.mono (by omega)).trans ((f7.mono (by omega)).trans (f8.mono (by omega))))


/-! ### The splay loop -/

/-- `r186 > r188 = 0` iff `x = r160` is a child of its parent. -/
def isChildS (B : ℕ) : Stmt :=
  .seq (block (ld B 179 160 0 ++ ld B 181 179 1 ++ ld B 182 179 2 ++ [.constN 188 0])) <|
  .seq (eqS 181 160 184) <| .seq (eqS 182 160 185) (.instr (.addN 186 184 185))

theorem isChildS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hb : Bnd B n (mem c)) {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n) :
    ∃ c' k, Exec P W (isChildS B) c c' k ∧ k ≤ 40 ∧ mem c' = mem c ∧ FrK 189 c c' ∧
      c'.nreg 160 = x ∧ c'.nreg 188 = 0 ∧ (0 < c'.nreg 186 ↔ IsChild B (mem c) x) := by
  obtain ⟨py, -, -, -, -, -⟩ := hb.get hxn
  simp only [par, mem, adr] at py
  unfold isChildS
  refine spec_seq ?_
  simp only [ld, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx]); omega)
  obtain ⟨k1, e1, hk1⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 181 160 184
    (by decide) (by decide)
  refine spec_seq_known e1 (fun hw1 => ?_)
  obtain ⟨k2, e2, hk2⟩ := eqS_exec (P := P) hw1 (by omega) 182 160 185 (by decide) (by decide)
  refine spec_seq_known e2 (fun hw2 => ?_)
  refine spec_instr (Exec.addN hw2 186 184 185 (by config_simp; split_ifs <;> omega))
    (fun hw3 => ?_)
  refine ⟨by omega, rfl, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_, ?_, ?_⟩
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
  · config_simp; simp (disch := omega) only [upd_ne_of]
  · config_simp; exact hx
  · config_simp
  · config_simp
    rw [ite01_pos, hx]
    rfl

/-- Splay `x = r160` to the root of its auxiliary tree. -/
def splayS (B : ℕ) : Stmt :=
  .seq (isChildS B) (.whileLtN 188 186 (.seq (splayStepS B) (isChildS B)))

lemma Inv.rt_lt {B n : ℕ} {M : Mem} {G : List VT} (hI : Inv B n M G) {gb ga : List VT} {t : VT}
    {ctx : List Frame} (hG : G = gb ++ plug t ctx :: ga) (ht : t ≠ VT.leaf) : rt n t < n :=
  (rotCtx B n hI hG).lts _ (rt_mem_nodes ht n)

lemma Bnd.splayStepM {B n : ℕ} {M : Mem} (h : Bnd B n M) {x : ℕ} (hx : x ≤ n) :
    Bnd B n (splayStepM B n x M) := by
  have py := (h.get hx).1
  have pz := (h.get py).1
  unfold DynTree.splayStepM
  split_ifs
  · have h3 := ((h.pushM pz).pushM py).pushM hx
    exact (h3.rotMem py).rotMem hx
  · have h3 := ((h.pushM pz).pushM py).pushM hx
    exact (h3.rotMem hx).rotMem hx
  · exact ((h.pushM py).pushM hx).rotMem hx

/-- **The splay loop.** It realises `splayG` and costs at most `4400` steps per splay step. -/
theorem splayS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {F : Forest} {gb ga : List VT} {t : VT}
    {ctx : List Frame} (hI : Inv B n (mem c) (gb ++ plug t ctx :: ga))
    (hR : RepE B n (mem c) (gb ++ plug t ctx :: ga) F) (ht : t ≠ VT.leaf)
    (hx : c.nreg 160 = rt n t) :
    ∃ c' k, Exec P W (splayS B) c c' k ∧ k ≤ 4400 * ((sp ctx + 1) / 2) + 50 ∧
      Inv B n (mem c') (gb ++ plug (splayG t ctx).1 (splayG t ctx).2 :: ga) ∧
      RepE B n (mem c') (gb ++ plug (splayG t ctx).1 (splayG t ctx).2 :: ga) F ∧
      Bnd B n (mem c') ∧ MemFrame B n (mem c) (mem c') ∧ FrK 189 c c' ∧
      c'.nreg 160 = rt n t ∧ (∀ u, fpar B (mem c') u = fpar B (mem c) u) := by
  have hxn : rt n t < n := hI.rt_lt rfl ht
  obtain ⟨c1, k1, e1, hk1, m1, f1, s160, s188, s186⟩ :=
    isChildS_exec (P := P) B n hc hW hb hx hxn.le
  refine spec_seq_known e1 (fun hw1 => ?_)
  -- the loop invariant
  let I : VT × List Frame → Config → Prop := fun g c' =>
    WordsBounded W c' ∧ Inv B n (mem c') (gb ++ plug g.1 g.2 :: ga) ∧
    RepE B n (mem c') (gb ++ plug g.1 g.2 :: ga) F ∧ g.1 ≠ VT.leaf ∧ rt n g.1 = rt n t ∧
    splayG g.1 g.2 = splayG t ctx ∧ c'.nreg 160 = rt n t ∧ c'.nreg 151 = n ∧
    c'.nreg 188 = 0 ∧ (0 < c'.nreg 186 ↔ HeadSolid g.2) ∧ Bnd B n (mem c') ∧
    FrK 189 c c' ∧ MemFrame B n (mem c) (mem c') ∧ (∀ u, fpar B (mem c') u = fpar B (mem c) u)
  have hI1 : I (t, ctx) c1 := by
    refine ⟨hw1, m1 ▸ hI, m1 ▸ hR, ht, rfl, rfl, s160, ?_, s188, ?_, m1 ▸ hb, f1,
      m1 ▸ MemFrame.refl B n _, fun u => by rw [m1]⟩
    · rw [(f1.1 151 (by omega)).1]; exact hn
    · rw [s186]; exact root_facts B n hI rfl ht |>.2.1
  obtain ⟨g, c2, k2, e2, hI2, hstop, hk2⟩ := Exec.whileLtN_ghost (P := P) (a := 188) (b := 186)
    (body := .seq (splayStepS B) (isChildS B)) I (fun g _ => 4400 * ((sp g.2 + 1) / 2))
    (fun _ _ h => h.1) (fun g c' hI' htest => by
      obtain ⟨hw, hInv, hRep, hne, hrt, hsp, h160, h151, h188, h186, hbd, hfr, hmf, hfp⟩ := hI'
      have hhs : HeadSolid g.2 := h186.mp (by omega)
      obtain ⟨c3, k3, e3, hk3, m3, f3, s3⟩ := splayStepS_exec (P := P) B n hw hW h151 hbd h160
        hxn.le
      have hb3 : Bnd B n (mem c3) := m3 ▸ hbd.splayStepM hxn.le
      obtain ⟨c4, k4, e4, hk4, m4, f4, s4, s4', s4''⟩ := isChildS_exec (P := P) B n e3.wb_right hW
        hb3 s3 hxn.le
      obtain ⟨I3, R3, F3, P3⟩ := splayStep_okE B n hInv hRep rfl hne hhs
      rw [hrt] at I3 R3 F3 P3
      obtain ⟨hne', hrt'⟩ := splay1_node hne hhs n
      have hsp1 := splay1_sp hne hhs
      refine ⟨splay1 g.1 g.2, c4, k3 + k4, .seq e3 e4, ⟨e4.wb_right, ?_, ?_, hne', hrt'.trans hrt,
        (splayG_step hne hhs).trans hsp, s4, ?_, s4', ?_, m4 ▸ hb3, hfr.trans (f3.trans
          (f4.mono (by omega))), ?_, fun u => by rw [m4, m3, P3, hfp]⟩, ?_⟩
      · rw [m4, m3]; exact I3
      · rw [m4, m3]; exact R3
      · rw [(f4.1 151 (by omega)).1, (f3.1 151 (by omega)).1]; exact h151
      · rw [s4'', m3]
        have := root_facts B n I3 rfl hne'
        rw [hrt'.trans hrt] at this
        exact this.2.1
      · rw [m4, m3]; exact hmf.trans B n F3
      · have : 4400 * ((sp (splay1 g.1 g.2).2 + 1) / 2) + 4400 ≤ 4400 * ((sp g.2 + 1) / 2) := by
          have := Nat.mul_le_mul_left 4400 hsp1
          rw [Nat.mul_add] at this; omega
        omega) hI1
  obtain ⟨hw, hInv, hRep, hne, hrt, hsp, h160, h151, h188, h186, hbd, hfr, hmf, hfp⟩ := hI2
  have hns : ¬ HeadSolid g.2 := fun h => hstop (by rw [h188]; exact h186.mpr h)
  rw [splayG_stop _ hns] at hsp
  refine ⟨c2, k2, e2, ?_, ?_, ?_, hbd, hmf, hfr, h160, hfp⟩
  · simp only at hk2; omega
  · rw [← hsp]; exact hInv
  · rw [← hsp]; exact hRep

/-! ### The switch of the preferred child -/

/-- The push of `w = r160`, then `switchR w y` with `y = r178`: `r162 = rc w`; reals
`r160 = tg w`, `r161 = tg r`, `r162 = tg y`, `r164 = tg2 w`, `r165 = tg2 r`, `r166 = tg2 y`. -/
def switchS (B : ℕ) : Stmt :=
  .seq (cpushS B 160) <|
  .seq (block (ld B 162 160 2 ++ ldR B 160 160 1 ++ ldR B 161 162 1 ++ ldR B 162 178 1 ++
    ldR B 164 160 6 ++ ldR B 165 162 6 ++ ldR B 166 178 6 ++
    st B 160 2 178 ++ [.addR 163 161 160] ++ stR B 162 1 163 ++ [.subR 163 162 160] ++
    stR B 178 1 163 ++ [.addR 167 165 164] ++ stR B 162 6 167 ++ [.subR 167 166 164] ++
    stR B 178 6 167 ++ [.copyN 170 160])) (recompS B)

lemma Bnd.switchP {B n : ℕ} {M : Mem} (h : Bnd B n M) {w y : ℕ} (hy : y ≤ n) :
    Bnd B n (switchP B w y M) := by
  refine h.of fun a => ?_
  simp only [DynTree.switchP, upd_apply]; split_ifs
  · exact Or.inr hy
  · exact Or.inl rfl

theorem switchS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {w y : ℕ} (hw : c.nreg 160 = w)
    (hy : c.nreg 178 = y) (hwn : w ≤ n) (hyn : y ≤ n) :
    ∃ c' k, Exec P W (switchS B) c c' k ∧ k ≤ 1000 ∧
      mem c' = switchR B n w y (pushM B w (mem c)) ∧ Fr c c' ∧ c'.nreg 160 = w := by
  obtain ⟨c0, k0, e0, hk0, m0, f0, s0⟩ := cpushS_exec (P := P) B n hc hW hb hw hwn
  unfold switchS
  refine spec_seq_known e0 (fun hw0 => ?_)
  have hb0 : Bnd B n (mem c0) := m0 ▸ hb.pushM hwn
  have h160 : c0.nreg 160 = w := by rw [s0, hw]
  have h178 : c0.nreg 178 = y := by rw [f0.2.1 178 (by omega) (by omega)]; exact hy
  have h151 : c0.nreg 151 = n := by rw [(f0.1 151 (by omega)).1]; exact hn
  obtain ⟨-, lw, rw', -, -, -⟩ := hb0.get hwn
  have rw'' := rw'
  simp only [rc, mem, adr] at rw''
  generalize hR : recompS B = R
  refine spec_seq ?_
  simp only [ld, ldR, st, stR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [h160, h178]); omega)
  subst hR
  refine spec_gen fun c1 hc1 => ?_
  have hw1 : WordsBounded W c1 := hc1 ▸ ‹WordsBounded W _›
  have m1 : mem c1 = switchP B w y (mem c0) := by
    rw [hc1]; simp only [mem, switchP]; config_simp; simp only [h160, h178]; rfl
  have hb1 : Bnd B n (mem c1) := by rw [m1]; exact hb0.switchP hyn
  have f1 : Fr c0 c1 := by
    rw [hc1]
    refine ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · config_simp; simp (disch := omega) only [upd_ne_of]
  have r170 : c1.nreg 170 = w := by rw [hc1]; config_simp; exact h160
  have r160 : c1.nreg 160 = w := by rw [hc1]; config_simp; exact h160
  have lw1 : lc B (mem c1) w ≤ n := by
    rw [m1]; simp only [lc, switchP]; rw [upd_adr _ _ (by omega) (by omega)]
    simp only [show ¬ (1 = 2) by omega, and_false, ite_false]; exact lw
  have rw1 : rc B (mem c1) w ≤ n := by
    rw [m1]; simp only [rc, switchP]; rw [upd_adr _ _ (by omega) (by omega)]; simp [hyn]
  obtain ⟨c2, k2, e2, hk2, m2, f2, s2, t2⟩ := recompS_exec (P := P) B n hw1 hW r170
    (by rw [(f1.1 151 (by omega)).1]; exact h151) hwn lw1 rw1
  refine ⟨c2, k2, e2, by omega, ?_, f0.trans (f1.trans f2), by rw [t2, r160]⟩
  rw [m2, m1, m0]; rfl

lemma Bnd.switchR {B n : ℕ} {M : Mem} (h : Bnd B n M) {w y : ℕ} (hw : w ≤ n) (hy : y ≤ n) :
    Bnd B n (switchR B n w y M) :=
  (h.switchP hy).recomp hw


end

end DynTree

end PlanarFlow
