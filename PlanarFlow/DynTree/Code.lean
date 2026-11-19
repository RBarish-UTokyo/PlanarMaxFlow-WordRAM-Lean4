module

public import PlanarFlow.DynTree.Switch

/-!
# Dynamic trees: the machine blocks for the memory operations

The structure lives at a base address `B` (a literal of the code): field `j` of node `u` is the
word `adr B u j = u * 16 + (B + j)`, computed into `r199` by `ad B u j` (`r198` is a second
scratch register). The blocks use the registers `r160 … r199` (natural and real) as scratch and
read `n` from `r151`; they change no other register and no memory outside the structure. Every
block has an exec lemma in the style of `WordRAM.Programs`: an explicit cost and the memory after
the block, as one of the functions of `PlanarFlow.DynTree.Rot`, `…Push`, `…Splay`, `…Switch`.

* `rotPS B`: the pointers and tags of the rotation of `x = r160` (`rotP`), at most `230` steps;
* `recompS B`: the aggregates of `u = r170` (`recomp`), at most `400` steps.

The rotation, the push, the splay loop and the switch are in `PlanarFlow.DynTree.CodeSplay`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- `r199 := adr B (r u) j`. -/
def ad (B u j : ℕ) : List Instr :=
  [.constN 199 16, .mulN 199 u 199, .constN 198 (B + j), .addN 199 199 198]

/-- `r d := field j of node r u`. -/
def ld (B d u j : ℕ) : List Instr := ad B u j ++ [.loadN d 199]
/-- `field j of node r u := r v`. -/
def st (B u j v : ℕ) : List Instr := ad B u j ++ [.storeN 199 v]
/-- Real `r d := real field j of node r u`. -/
def ldR (B d u j : ℕ) : List Instr := ad B u j ++ [.loadR d 199]
/-- Real field `j` of node `r u := ` real `r v`. -/
def stR (B u j v : ℕ) : List Instr := ad B u j ++ [.storeR 199 v]

/-- `r f := 1` if `r a = r b`, else `0`. -/
def eqS (a b f : ℕ) : Stmt :=
  .seq (.instr (.constN f 1)) (.seq (.ifLtN a b (.instr (.constN f 0)) .skip)
    (.ifLtN b a (.instr (.constN f 0)) .skip))


/-- Reading the fields for the rotation of `x = r160`: `r161 = y`, `r162 = z`, `r163 = lc y`,
`r164 = lc x`, `r165 = rc x`, `r166 = lc z`, `r167 = rc z`, `r197 = 0`; reals `r160 = tg x`,
`r161 = tg y`, `r170 = tg2 x`, `r171 = tg2 y`. -/
def rotRead (B : ℕ) : Stmt :=
  block (ld B 161 160 0 ++ ld B 162 161 0 ++ ld B 163 161 1 ++ ld B 164 160 1 ++
      ld B 165 160 2 ++ ld B 166 162 1 ++ ld B 167 162 2 ++ ldR B 160 160 1 ++ ldR B 161 161 1 ++
      ldR B 170 160 6 ++ ldR B 171 161 6 ++ [.constN 197 0])

/-- The inner child `b = r169` changes sides; reals `r162 = tg b`, `r172 = tg2 b`. -/
def rotBranch (B : ℕ) : Stmt :=
  .seq (eqS 163 160 168) <|
  .ifLtN 197 168
      (block ([.copyN 169 165] ++ ldR B 162 169 1 ++ ldR B 172 169 6 ++ st B 161 1 169 ++
        st B 169 0 161 ++ st B 160 2 161))
      (block ([.copyN 169 164] ++ ldR B 162 169 1 ++ ldR B 172 169 6 ++ st B 161 2 169 ++
        st B 169 0 161 ++ st B 160 1 161))

/-- The parent pointers, the grandparent's child pointer and the tags. -/
def rotTail (B : ℕ) : Stmt :=
  .seq (block (st B 161 0 160 ++ st B 160 0 162)) <|
  .seq (eqS 166 161 168) <|
  .seq (.ifLtN 197 168 (block (st B 162 1 160))
    (.seq (eqS 167 161 168) (.ifLtN 197 168 (block (st B 162 2 160)) .skip))) <|
  block ([.addR 163 160 161] ++ stR B 160 1 163 ++ [.constR 164 0, .subR 163 164 160] ++
    stR B 161 1 163 ++ [.addR 163 162 160] ++ stR B 169 1 163 ++
    [.addR 173 170 171] ++ stR B 160 6 173 ++ [.constR 174 0, .subR 173 174 170] ++
    stR B 161 6 173 ++ [.addR 173 172 170] ++ stR B 169 6 173)

/-- The pointer and tag part of the rotation of `x = r160` (`rotP`). -/
def rotPS (B : ℕ) : Stmt := .seq (rotRead B) (.seq (rotBranch B) (rotTail B))

/-- The registers outside the scratch window `r160 … r199` and the output are unchanged. -/
def FrK (lo : ℕ) (c c' : Config) : Prop :=
  (∀ r, (r < 160 ∨ 200 ≤ r) → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧
    (∀ r, lo ≤ r → r < 197 → c'.nreg r = c.nreg r) ∧ c'.output = c.output

/-- The frame of the basic blocks: they also keep the natural registers `r178 … r196`, which
the blocks built on them use (`r178 … r188` the splay and the switch, `r189 … r192` the access,
`r193 … r196` the operations). -/
abbrev Fr : Config → Config → Prop := FrK 178

lemma FrK.refl (lo : ℕ) (c : Config) : FrK lo c c := ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, rfl⟩

lemma FrK.trans {lo : ℕ} {c c' c'' : Config} (h : FrK lo c c') (h' : FrK lo c' c'') :
    FrK lo c c'' :=
  ⟨fun r hr => ⟨((h'.1 r hr).1).trans (h.1 r hr).1, ((h'.1 r hr).2).trans (h.1 r hr).2⟩,
    fun r h1 h2 => (h'.2.1 r h1 h2).trans (h.2.1 r h1 h2), h'.2.2.trans h.2.2⟩

lemma FrK.mono {lo lo' : ℕ} (hl : lo ≤ lo') {c c' : Config} (h : FrK lo c c') : FrK lo' c c' :=
  ⟨h.1, fun r h1 h2 => h.2.1 r (by omega) h2, h.2.2⟩

lemma Fr.refl (c : Config) : Fr c c := FrK.refl 178 c

lemma Fr.trans {c c' c'' : Config} (h : Fr c c') (h' : Fr c' c'') : Fr c c'' := FrK.trans h h'

lemma upd_ne_of {α : Type} (f : ℕ → α) (k : ℕ) (v : α) {r : ℕ} (h : r ≠ k) :
    upd f k v r = f r := by
  rw [upd_apply]; exact ite_eq_right_iff.mpr (fun e => absurd e h)

lemma upd_out {α : Type} (f : ℕ → α) (k : ℕ) (v : α) {r : ℕ} (hr : r < 160 ∨ 200 ≤ r)
    (hk : 160 ≤ k ∧ k < 200) : upd f k v r = f r := by
  rw [upd_apply]; exact ite_eq_right_iff.mpr (by omega)

/-- The memory of a configuration. -/
def mem (c : Config) : Mem := ⟨c.nmem, c.rmem⟩

section
variable {P : Input} {W : ℕ}

/-- Name the current configuration of a spec goal. -/
theorem spec_gen {s : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∀ c₀, c₀ = c → ∃ c' k, Exec P W s c₀ c' k ∧ Q c' k) :
    ∃ c' k, Exec P W s c c' k ∧ Q c' k := h c rfl

/-- Chain a sub-statement whose final configuration is known. -/
theorem spec_seq_known {s t : Stmt} {c c₁ : Config} {k₁ : ℕ} {Q : Config → ℕ → Prop}
    (h₁ : Exec P W s c c₁ k₁)
    (h₂ : WordsBounded W c₁ → ∃ c' k, Exec P W t c₁ c' k ∧ Q c' (k₁ + k)) :
    ∃ c' k, Exec P W (.seq s t) c c' k ∧ Q c' k := by
  obtain ⟨c', k, e, q⟩ := h₂ h₁.wb_right
  exact ⟨c', k₁ + k, .seq h₁ e, q⟩

theorem eqS_exec' {c : Config} (hc : WordsBounded W c) (hW : 1 ≤ W) (a b f : ℕ) (ha : a ≠ f)
    (hb : b ≠ f) :
    ∃ c' k, Exec P W (eqS a b f) c c' k ∧ k ≤ 5 ∧
      c' = { c with nreg := upd c.nreg f (if c.nreg a = c.nreg b then 1 else 0) } := by
  refine spec_seq (spec_instr (Exec.constN hc f 1 hW) fun hw1 => ?_)
  by_cases h1 : c.nreg a < c.nreg b
  · refine spec_seq (spec_ifLtN_true (by simp [ha, hb]; omega)
      (spec_instr (Exec.constN hw1 f 0 (by omega)) fun hw2 => ?_))
    by_cases h2 : c.nreg b < c.nreg a
    · omega
    · refine spec_ifLtN_false (by simp [ha, hb]; omega) (spec_skip (by
        simpa using hw2) ?_)
      refine ⟨by omega, ?_⟩
      simp only [upd_upd_same, show c.nreg a ≠ c.nreg b by omega, ite_false]
  · refine spec_seq (spec_ifLtN_false (by simp [ha, hb]; omega) (spec_skip hw1 ?_))
    by_cases h2 : c.nreg b < c.nreg a
    · refine spec_ifLtN_true (by simp [ha, hb]; omega)
        (spec_instr (Exec.constN hw1 f 0 (by omega)) fun hw2 => ?_)
      refine ⟨by omega, ?_⟩
      simp only [upd_upd_same, show c.nreg a ≠ c.nreg b by omega, ite_false]
    · refine spec_ifLtN_false (by simp [ha, hb]; omega) (spec_skip hw1 ?_)
      refine ⟨by omega, ?_⟩
      simp only [show c.nreg a = c.nreg b by omega, ite_true]

theorem eqS_exec {c : Config} (hc : WordsBounded W c) (hW : 1 ≤ W) (a b f : ℕ) (ha : a ≠ f)
    (hb : b ≠ f) : ∃ k, Exec P W (eqS a b f) c
      { c with nreg := upd c.nreg f (if c.nreg a = c.nreg b then 1 else 0) } k ∧ k ≤ 5 := by
  obtain ⟨c', k, e, hk, rfl⟩ := eqS_exec' hc hW a b f ha hb
  exact ⟨k, e, hk⟩

theorem rotRead_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n) (hy : par B (mem c) x ≤ n)
    (hz : par B (mem c) (par B (mem c) x) ≤ n) :
    ∃ c' k, Exec P W (rotRead B) c c' k ∧ k ≤ 70 ∧ mem c' = mem c ∧ Fr c c' ∧
      c'.nreg 160 = x ∧ c'.nreg 161 = par B (mem c) x ∧
      c'.nreg 162 = par B (mem c) (par B (mem c) x) ∧
      c'.nreg 163 = lc B (mem c) (par B (mem c) x) ∧ c'.nreg 164 = lc B (mem c) x ∧
      c'.nreg 165 = rc B (mem c) x ∧ c'.nreg 166 = lc B (mem c) (par B (mem c) (par B (mem c) x)) ∧
      c'.nreg 167 = rc B (mem c) (par B (mem c) (par B (mem c) x)) ∧ c'.nreg 197 = 0 ∧
      c'.rreg 160 = tg B (mem c) x ∧ c'.rreg 161 = tg B (mem c) (par B (mem c) x) ∧
      c'.rreg 170 = tg2 B (mem c) x ∧ c'.rreg 171 = tg2 B (mem c) (par B (mem c) x) := by
  simp only [par, lc, rc, tg, tg2, mem, adr] at hy hz ⊢
  unfold rotRead
  simp only [ld, ldR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx]); omega)
  refine ⟨by omega, rfl, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_⟩
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
    exact ⟨trivial, trivial⟩
  · config_simp; simp (disch := omega) only [upd_ne_of]
  · config_simp
    simp only [hx, and_self]


theorem rotBranch_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {x y ly lx rx : ℕ} (hx : c.nreg 160 = x) (hy : c.nreg 161 = y) (hly : c.nreg 163 = ly)
    (hlx : c.nreg 164 = lx) (hrx : c.nreg 165 = rx) (h0 : c.nreg 197 = 0) (hxn : x ≤ n)
    (hyn : y ≤ n) (hlxn : lx ≤ n) (hrxn : rx ≤ n) :
    ∃ c' k, Exec P W (rotBranch B) c c' k ∧ k ≤ 40 ∧
      c'.nmem = (if ly = x then
        upd (upd (upd c.nmem (adr B y 1) rx) (adr B rx 0) y) (adr B x 2) y else
        upd (upd (upd c.nmem (adr B y 2) lx) (adr B lx 0) y) (adr B x 1) y) ∧
      c'.rmem = c.rmem ∧ c'.nreg 169 = (if ly = x then rx else lx) ∧
      c'.rreg 162 = c.rmem (adr B (if ly = x then rx else lx) 1) ∧
      c'.rreg 172 = c.rmem (adr B (if ly = x then rx else lx) 6) ∧
      (∀ r, r ≠ 168 → r ≠ 169 → r ≠ 198 → r ≠ 199 → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 162 → r ≠ 172 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  unfold rotBranch
  obtain ⟨k1, e1, hk1⟩ := eqS_exec (P := P) hc (by omega) 163 160 168 (by decide) (by decide)
  refine spec_seq_known e1 (fun hw1 => ?_)
  by_cases hL : ly = x
  · refine spec_ifLtN_true (by config_simp; simp only [hly, hx, hL, h0, ite_true]; decide) ?_
    simp only [ldR, st, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [hx, hy, hrx, hlx]); omega)
    refine ⟨by omega, ?_, rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; simp only [hx, hy, hrx, hL, ite_true]; rfl
    · config_simp; simp only [hrx, hL, ite_true]
    · config_simp; simp only [hrx, hL, ite_true]; rfl
    · config_simp; simp only [hrx, hL, ite_true]; rfl
    · config_simp; simp only [upd_apply, h1, h2, h3, h4, ite_false]
    · config_simp; simp only [upd_apply, h1, h2, ite_false]
  · refine spec_ifLtN_false (by config_simp; simp only [hly, hx, hL, h0, ite_false]; decide) ?_
    simp only [ldR, st, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [hx, hy, hrx, hlx]); omega)
    refine ⟨by omega, ?_, rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; simp only [hx, hy, hlx, hL, ite_false]; rfl
    · config_simp; simp only [hlx, hL, ite_false]
    · config_simp; simp only [hlx, hL, ite_false]; rfl
    · config_simp; simp only [hlx, hL, ite_false]; rfl
    · config_simp; simp only [upd_apply, h1, h2, h3, h4, ite_false]
    · config_simp; simp only [upd_apply, h1, h2, ite_false]


theorem rotTail_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {x y z lz rz b : ℕ} (hx : c.nreg 160 = x) (hy : c.nreg 161 = y) (hz : c.nreg 162 = z)
    (hlz : c.nreg 166 = lz) (hrz : c.nreg 167 = rz) (hb : c.nreg 169 = b) (h0 : c.nreg 197 = 0)
    (hxn : x ≤ n) (hyn : y ≤ n) (hzn : z ≤ n) (hbn : b ≤ n) :
    ∃ c' k, Exec P W (rotTail B) c c' k ∧ k ≤ 110 ∧
      c'.nmem = (if lz = y then
        upd (upd (upd c.nmem (adr B y 0) x) (adr B x 0) z) (adr B z 1) x else if rz = y then
        upd (upd (upd c.nmem (adr B y 0) x) (adr B x 0) z) (adr B z 2) x else
        upd (upd c.nmem (adr B y 0) x) (adr B x 0) z) ∧
      c'.rmem = upd (upd (upd (upd (upd (upd c.rmem (adr B x 1) (c.rreg 160 + c.rreg 161))
        (adr B y 1) (-c.rreg 160)) (adr B b 1) (c.rreg 162 + c.rreg 160)) (adr B x 6)
        (c.rreg 170 + c.rreg 171)) (adr B y 6) (-c.rreg 170)) (adr B b 6)
        (c.rreg 172 + c.rreg 170) ∧
      Fr c c' ∧ c'.nreg 160 = x ∧ c'.nreg 161 = y := by
  unfold rotTail
  refine spec_seq ?_
  simp only [st, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hx, hy, hz]); omega)
  obtain ⟨k1, e1, hk1⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 166 161 168
    (by decide) (by decide)
  refine spec_seq_known e1 (fun hw1 => ?_)
  by_cases hz1 : lz = y
  · refine spec_seq (spec_ifLtN_true (by config_simp; simp only [hlz, hy, hz1, h0, ite_true]; decide) ?_)
    simp only [st, stR, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [hx, hy, hz, hb]); omega)
    · refine ⟨by omega, ?_, ?_, ⟨fun r hr' => ?_, fun r h1 h2 => ?_, rfl⟩, ?_⟩
      · config_simp; simp only [hx, hy, hz, hz1, ite_true]; (try rfl)
      · config_simp; simp only [hx, hy, hb, Int.cast_zero, zero_sub]; (try rfl)
      · config_simp
        simp (disch := omega) only [upd_out _ _ _ hr']
        exact ⟨trivial, trivial⟩
      · config_simp; simp (disch := omega) only [upd_ne_of]
      · config_simp; exact ⟨hx, hy⟩
  · refine spec_seq (spec_ifLtN_false (by config_simp; simp only [hlz, hy, hz1, h0, ite_false]; decide) ?_)
    obtain ⟨k2, e2, hk2⟩ := eqS_exec (P := P) ‹WordsBounded W _› (by omega) 167 161 168
      (by decide) (by decide)
    refine spec_seq_known e2 (fun hw2 => ?_)
    by_cases hz2 : rz = y
    · refine spec_ifLtN_true (by config_simp; simp only [hrz, hy, hz2, h0, ite_true]; decide) ?_
      simp only [st, stR, ad, List.cons_append, List.nil_append]
      exec_block
      any_goals (config_simp; (try simp only [hx, hy, hz, hb]); omega)
      · refine ⟨by omega, ?_, ?_, ⟨fun r hr' => ?_, fun r h1 h2 => ?_, rfl⟩, ?_⟩
        · config_simp; simp only [hx, hy, hz, hz1, hz2, ite_true, ite_false]; (try rfl)
        · config_simp; simp only [hx, hy, hb, Int.cast_zero, zero_sub]; (try rfl)
        · config_simp
          simp (disch := omega) only [upd_out _ _ _ hr']
          exact ⟨trivial, trivial⟩
        · config_simp; simp (disch := omega) only [upd_ne_of]
        · config_simp; exact ⟨hx, hy⟩
    · refine spec_ifLtN_false (by config_simp; simp only [hrz, hy, hz2, h0, ite_false]; decide) ?_
      refine spec_skip ‹WordsBounded W _› ?_
      simp only [stR, ad, List.cons_append, List.nil_append]
      exec_block
      any_goals (config_simp; (try simp only [hx, hy, hz, hb]); omega)
      · refine ⟨by omega, ?_, ?_, ⟨fun r hr' => ?_, fun r h1 h2 => ?_, rfl⟩, ?_⟩
        · config_simp; simp only [hx, hy, hz, hz1, hz2, ite_false]; (try rfl)
        · config_simp; simp only [hx, hy, hb, Int.cast_zero, zero_sub]; (try rfl)
        · config_simp
          simp (disch := omega) only [upd_out _ _ _ hr']
          exact ⟨trivial, trivial⟩
        · config_simp; simp (disch := omega) only [upd_ne_of]
        · config_simp; exact ⟨hx, hy⟩


theorem rotPS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n) (hy : par B (mem c) x ≤ n)
    (hz : par B (mem c) (par B (mem c) x) ≤ n) (hlx : lc B (mem c) x ≤ n)
    (hrx : rc B (mem c) x ≤ n) :
    ∃ c' k, Exec P W (rotPS B) c c' k ∧ k ≤ 230 ∧ mem c' = rotP B x (mem c) ∧ Fr c c' ∧
      c'.nreg 160 = x ∧ c'.nreg 161 = par B (mem c) x := by
  unfold rotPS
  obtain ⟨c1, k1, e1, hk1, m1, f1, r160, r161, r162, r163, r164, r165, r166, r167, r197, q160,
    q161, q170, q171⟩ := rotRead_exec (P := P) B n hc hW hx hxn hy hz
  refine spec_seq_known e1 (fun hw1 => ?_)
  obtain ⟨c2, k2, e2, hk2, n2, m2, s169, q162, q172, keep2, keepR2, o2⟩ :=
    rotBranch_exec (P := P) B n hw1 hW r160 r161 r163 r164 r165 r197 hxn hy hlx hrx
  refine spec_seq_known e2 (fun hw2 => ?_)
  have hb : (if lc B (mem c) (par B (mem c) x) = x then rc B (mem c) x else lc B (mem c) x) ≤ n := by
    split_ifs <;> assumption
  have kp : ∀ r, r ≠ 168 → r ≠ 169 → r ≠ 198 → r ≠ 199 → c2.nreg r = c1.nreg r := keep2
  obtain ⟨c3, k3, e3, hk3, n3, m3, f3, s160, s161⟩ := rotTail_exec (P := P) B n hw2 hW
    (x := x) (y := par B (mem c) x) (z := par B (mem c) (par B (mem c) x))
    (lz := lc B (mem c) (par B (mem c) (par B (mem c) x)))
    (rz := rc B (mem c) (par B (mem c) (par B (mem c) x)))
    (b := if lc B (mem c) (par B (mem c) x) = x then rc B (mem c) x else lc B (mem c) x)
    ((kp 160 (by decide) (by decide) (by decide) (by decide)).trans r160)
    ((kp 161 (by decide) (by decide) (by decide) (by decide)).trans r161)
    ((kp 162 (by decide) (by decide) (by decide) (by decide)).trans r162)
    ((kp 166 (by decide) (by decide) (by decide) (by decide)).trans r166)
    ((kp 167 (by decide) (by decide) (by decide) (by decide)).trans r167)
    s169
    ((kp 197 (by decide) (by decide) (by decide) (by decide)).trans r197)
    hxn hy hz hb
  refine ⟨c3, k3, e3, by omega, ?_, ?_, s160, s161⟩
  · have em1 : c1.nmem = c.nmem := congrArg Mem.nm m1
    have er1 : c1.rmem = c.rmem := congrArg Mem.rm m1
    simp only [mem] at *
    rw [n3, m3, n2, m2, em1, er1, q162, q172, keepR2 160 (by decide) (by decide),
      keepR2 161 (by decide) (by decide), keepR2 170 (by decide) (by decide),
      keepR2 171 (by decide) (by decide), q160, q161, q170, q171, er1]
    by_cases hL : lc B ⟨c.nmem, c.rmem⟩ (par B ⟨c.nmem, c.rmem⟩ x) = x <;>
      simp only [rotP, hL, ite_true, ite_false] <;> rfl
  · refine f1.trans (Fr.trans ⟨fun r hr => ⟨keep2 r (by omega) (by omega) (by omega) (by omega),
      keepR2 r (by omega) (by omega)⟩, fun r h1 h2 => keep2 r (by omega) (by omega) (by omega)
      (by omega), o2⟩ f3)


/-! ### Conditional moves -/

theorem cmovN_exec {c : Config} (hc : WordsBounded W c) (a b d e : ℕ) :
    ∃ k, Exec P W (.ifLtN a b (.instr (.copyN d e)) .skip) c
      { c with nreg := upd c.nreg d (if c.nreg a < c.nreg b then c.nreg e else c.nreg d) } k ∧
      k ≤ 2 := by
  by_cases h : c.nreg a < c.nreg b
  · simp only [h, ite_true]
    exact ⟨_, .ifLtN_true h (Exec.copyN hc d e), by omega⟩
  · simp only [h, ite_false, upd_eq_self]
    exact ⟨_, .ifLtN_false h (.skip hc), le_refl _⟩

/-- `if r a < r b ∧ ¬ (real r x < real r y) then (real r rr, r nr) := (real r sr, r sn)`. -/
theorem cmov1_exec {c : Config} (hc : WordsBounded W c) (a b x y rr sr nr sn : ℕ) :
    ∃ k, Exec P W (.ifLtN a b (.ifLtR x y .skip (block [.copyR rr sr, .copyN nr sn])) .skip) c
      { c with
        nreg := upd c.nreg nr
          (if c.nreg a < c.nreg b ∧ ¬ c.rreg x < c.rreg y then c.nreg sn else c.nreg nr),
        rreg := upd c.rreg rr
          (if c.nreg a < c.nreg b ∧ ¬ c.rreg x < c.rreg y then c.rreg sr else c.rreg rr) } k ∧
      k ≤ 6 := by
  by_cases h1 : c.nreg a < c.nreg b
  · by_cases h2 : c.rreg x < c.rreg y
    · simp only [h1, h2, not_true, and_false, ite_false, upd_eq_self]
      exact ⟨_, .ifLtN_true h1 (.ifLtR_true h2 (.skip hc)), by omega⟩
    · simp only [h1, h2, not_false_eq_true, and_self, ite_true]
      have e1 := Exec.copyR (P := P) hc rr sr
      have e2 := Exec.copyN (P := P) e1.wb_right nr sn
      exact ⟨_, .ifLtN_true h1 (.ifLtR_false h2 (Exec.block_cons e1 (Exec.block_cons e2
        (Exec.block_nil e2.wb_right)))), by omega⟩
  · simp only [h1, false_and, ite_false, upd_eq_self]
    exact ⟨_, .ifLtN_false h1 (.skip hc), by omega⟩

/-- `if r a < r b ∧ real r x < real r y then (real r rr, r nr) := (real r sr, r sn)`. -/
theorem cmov2_exec {c : Config} (hc : WordsBounded W c) (a b x y rr sr nr sn : ℕ) :
    ∃ k, Exec P W (.ifLtN a b (.ifLtR x y (block [.copyR rr sr, .copyN nr sn]) .skip) .skip) c
      { c with
        nreg := upd c.nreg nr
          (if c.nreg a < c.nreg b ∧ c.rreg x < c.rreg y then c.nreg sn else c.nreg nr),
        rreg := upd c.rreg rr
          (if c.nreg a < c.nreg b ∧ c.rreg x < c.rreg y then c.rreg sr else c.rreg rr) } k ∧
      k ≤ 6 := by
  by_cases h1 : c.nreg a < c.nreg b
  · by_cases h2 : c.rreg x < c.rreg y
    · simp only [h1, h2, and_self, ite_true]
      have e1 := Exec.copyR (P := P) hc rr sr
      have e2 := Exec.copyN (P := P) e1.wb_right nr sn
      exact ⟨_, .ifLtN_true h1 (.ifLtR_true h2 (Exec.block_cons e1 (Exec.block_cons e2
        (Exec.block_nil e2.wb_right)))), by omega⟩
    · simp only [h1, h2, and_false, ite_false, upd_eq_self]
      exact ⟨_, .ifLtN_true h1 (.ifLtR_false h2 (.skip hc)), by omega⟩
  · simp only [h1, false_and, ite_false, upd_eq_self]
    exact ⟨_, .ifLtN_false h1 (.skip hc), by omega⟩


/-! ### Recomputing the aggregates -/

lemma lmn_fst (n a : ℕ) (A : ℝ × ℕ) (v : ℝ) (u b : ℕ) (Bq : ℝ × ℕ) : (lmn n a A v u b Bq).1 =
    if b < n ∧ Bq.1 < (if a < n ∧ ¬ v < A.1 then A.1 else v) then Bq.1 else
      (if a < n ∧ ¬ v < A.1 then A.1 else v) := by
  unfold lmn; by_cases h1 : a < n ∧ ¬ v < A.1 <;> simp only [h1, ite_true, ite_false] <;>
    split_ifs <;> rfl

lemma lmn_snd (n a : ℕ) (A : ℝ × ℕ) (v : ℝ) (u b : ℕ) (Bq : ℝ × ℕ) : (lmn n a A v u b Bq).2 =
    if b < n ∧ Bq.1 < (if a < n ∧ ¬ v < A.1 then A.1 else v) then Bq.2 else
      (if a < n ∧ ¬ v < A.1 then A.2 else u) := by
  unfold lmn; by_cases h1 : a < n ∧ ¬ v < A.1 <;> simp only [h1, ite_true, ite_false] <;>
    split_ifs <;> rfl

/-- The conditional moves of `recompS`. -/
def cmov1 (a b x y rr sr nr sn : ℕ) : Stmt :=
  .ifLtN a b (.ifLtR x y .skip (block [.copyR rr sr, .copyN nr sn])) .skip
/-- The conditional moves of `recompS`. -/
def cmov2 (a b x y rr sr nr sn : ℕ) : Stmt :=
  .ifLtN a b (.ifLtR x y (block [.copyR rr sr, .copyN nr sn]) .skip) .skip

/-- Recompute the aggregates of `u = r170` (`recomp`). Natural registers: `r171 = a = lc u`,
`r172 = b = rc u`, `r161 … r168` the argmins `am`, `amr`, `am2`, `am2r` of `a` and `b`,
`r169 = lm a`, `r173 = rtm b`; results `r174 … r177` (the four argmins), `r161`, `r162` (the end
nodes). Reals: `r170 = vl u`, `r171 = vl2 u`, `r172 … r178` the count, sums, tags and minima of
`a`, `r179 … r185` those of `b`, `r187` the count, `r190`, `r191` the sums, `r192 … r195` the
minima `minA a`, `minA2 a`, `minA b`, `minA2 b` as the parent reads them, `r196 … r199` the four
running minima. All loads come before all stores. -/
def recompS (B : ℕ) : Stmt :=
  .seq (block (ld B 171 170 1 ++ ld B 172 170 2 ++ ldR B 170 170 0 ++ ldR B 171 170 5 ++
     ldR B 172 171 4 ++ ldR B 173 171 3 ++ ldR B 174 171 8 ++ ldR B 175 171 1 ++
     ldR B 176 171 6 ++ ldR B 177 171 2 ++ ldR B 178 171 7 ++
     ldR B 179 172 4 ++ ldR B 180 172 3 ++ ldR B 181 172 8 ++ ldR B 182 172 1 ++
     ldR B 183 172 6 ++ ldR B 184 172 2 ++ ldR B 185 172 7 ++
     ld B 161 171 3 ++ ld B 162 172 3 ++ ld B 163 171 7 ++ ld B 164 172 7 ++
     ld B 165 171 8 ++ ld B 166 172 8 ++ ld B 167 171 9 ++ ld B 168 172 9 ++
     ld B 169 171 5 ++ ld B 173 172 6 ++
     [.constR 186 1, .addR 187 172 179, .addR 187 187 186,
      .mulR 188 175 172, .addR 188 173 188, .mulR 189 182 179, .addR 189 180 189,
      .addR 190 188 170, .addR 190 190 189,
      .mulR 188 176 172, .addR 188 174 188, .mulR 189 183 179, .addR 189 181 189,
      .addR 191 188 171, .addR 191 191 189,
      .addR 192 177 175, .addR 193 178 176, .addR 194 184 182, .addR 195 185 183,
      .copyR 196 170, .copyN 174 170])) <|
  .seq (cmov1 171 151 170 192 196 192 174 161) <|
  .seq (cmov2 172 151 194 196 196 194 174 162) <|
  .seq (block [.copyR 197 170, .copyN 175 170]) <|
  .seq (cmov1 172 151 170 194 197 194 175 164) <|
  .seq (cmov2 171 151 192 197 197 192 175 163) <|
  .seq (block [.copyR 198 171, .copyN 176 170]) <|
  .seq (cmov1 171 151 171 193 198 193 176 165) <|
  .seq (cmov2 172 151 195 198 198 195 176 166) <|
  .seq (block [.copyR 199 171, .copyN 177 170]) <|
  .seq (cmov1 172 151 171 195 199 195 177 168) <|
  .seq (cmov2 171 151 193 199 199 193 177 167) <|
  .seq (block [.copyN 161 170]) <|
  .seq (.ifLtN 171 151 (.instr (.copyN 161 169)) .skip) <|
  .seq (block [.copyN 162 170]) <|
  .seq (.ifLtN 172 151 (.instr (.copyN 162 173)) .skip) <|
  block (st B 170 3 174 ++ st B 170 5 161 ++ st B 170 6 162 ++ st B 170 7 175 ++
    st B 170 8 176 ++ st B 170 9 177 ++ stR B 170 2 196 ++ stR B 170 3 190 ++ stR B 170 4 187 ++
    stR B 170 7 198 ++ stR B 170 8 191)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem recompS_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {u : ℕ} (hu : c.nreg 170 = u) (hn : c.nreg 151 = n) (hun : u ≤ n)
    (ha : lc B (mem c) u ≤ n) (hb : rc B (mem c) u ≤ n) :
    ∃ c' k, Exec P W (recompS B) c c' k ∧ k ≤ 400 ∧ mem c' = recomp B n u (mem c) ∧ Fr c c' ∧
      c'.nreg 170 = u ∧ c'.nreg 160 = c.nreg 160 := by
  simp only [lc, rc, mem, adr] at ha hb
  unfold recompS
  refine spec_seq ?_
  simp only [ld, ldR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hu]); omega)
  obtain ⟨k1, e1, hk1⟩ := cmov1_exec (P := P) ‹WordsBounded W _› 171 151 170 192 196 192 174 161
  refine spec_seq_known e1 (fun hw1 => ?_)
  obtain ⟨k2, e2, hk2⟩ := cmov2_exec (P := P) hw1 172 151 194 196 196 194 174 162
  refine spec_seq_known e2 (fun hw2 => ?_)
  refine spec_seq ?_
  exec_block
  obtain ⟨k3, e3, hk3⟩ := cmov1_exec (P := P) ‹WordsBounded W _› 172 151 170 194 197 194 175 164
  refine spec_seq_known e3 (fun hw3 => ?_)
  obtain ⟨k4, e4, hk4⟩ := cmov2_exec (P := P) hw3 171 151 192 197 197 192 175 163
  refine spec_seq_known e4 (fun hw4 => ?_)
  refine spec_seq ?_
  exec_block
  obtain ⟨k5, e5, hk5⟩ := cmov1_exec (P := P) ‹WordsBounded W _› 171 151 171 193 198 193 176 165
  refine spec_seq_known e5 (fun hw5 => ?_)
  obtain ⟨k6, e6, hk6⟩ := cmov2_exec (P := P) hw5 172 151 195 198 198 195 176 166
  refine spec_seq_known e6 (fun hw6 => ?_)
  refine spec_seq ?_
  exec_block
  obtain ⟨k7, e7, hk7⟩ := cmov1_exec (P := P) ‹WordsBounded W _› 172 151 171 195 199 195 177 168
  refine spec_seq_known e7 (fun hw7 => ?_)
  obtain ⟨k8, e8, hk8⟩ := cmov2_exec (P := P) hw7 171 151 193 199 199 193 177 167
  refine spec_seq_known e8 (fun hw8 => ?_)
  refine spec_seq ?_
  exec_block
  obtain ⟨k9, e9, hk9⟩ := cmovN_exec (P := P) ‹WordsBounded W _› 171 151 161 169
  refine spec_seq_known e9 (fun hw9 => ?_)
  refine spec_seq ?_
  exec_block
  obtain ⟨k10, e10, hk10⟩ := cmovN_exec (P := P) ‹WordsBounded W _› 172 151 162 173
  refine spec_seq_known e10 (fun hw10 => ?_)
  simp only [st, stR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hu]); omega)
  refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_, ?_⟩
  · simp only [mem]
    config_simp
    simp only [hu, hn, Int.cast_one]
    simp only [recomp, setOwn, cmb, comb, lmn_fst, lmn_snd, rd, own, Ag.addTags, lc, rc, vl, vl2,
      cnt, sm, sm2, tg, tg2, mn, mn2, am, amr, am2, am2r, lm, rtm, adr]
    rfl
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
    exact ⟨trivial, trivial⟩
  · config_simp; simp (disch := omega) only [upd_ne_of]
  · config_simp; exact hu
  · config_simp



end

end DynTree

end PlanarFlow
