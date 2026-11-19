module

public import NestedDissection.DetModBuild

/-!
# Signs of listed entries from a bit and two parities, on the machine

The input `[n, p, m, S, u₀, v₀, i₀, j₀, …, a₀, …, a_{S-1}, b₀, …, b_{S-1}]` lists `m` entries
`(u_k, v_k)`, each with two slots `i_k, j_k < S`, followed by a bit `a_t` and a count `b_t` per
slot. The sign of entry `k` is computed from the bit of its first slot and the parities of the
counts of its two slots: `s_k = (a_{i_k} + 1 + b_{i_k} + b_{j_k}) mod 2`. The program
`DetMod.signs` prints `[n, p, m, u₀, v₀, s₀, …]`, the input of `DetMod.build`, within
`O(m)` steps (`DetMod.signs_runsWithin`).
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The input -/

/-- The number of slots, and the words of the `k`-th listed entry. -/
def sS (d : List ℕ) : ℕ := d.getD 3 0
def su (d : List ℕ) (k : ℕ) : ℕ := d.getD (4 + 4 * k) 0
def sv (d : List ℕ) (k : ℕ) : ℕ := d.getD (5 + 4 * k) 0
def si (d : List ℕ) (k : ℕ) : ℕ := d.getD (6 + 4 * k) 0
def sj (d : List ℕ) (k : ℕ) : ℕ := d.getD (7 + 4 * k) 0

/-- The bit and the count of slot `t`. -/
def sa (d : List ℕ) (t : ℕ) : ℕ := d.getD (4 + 4 * bm d + t) 0
def sb (d : List ℕ) (t : ℕ) : ℕ := d.getD (4 + 4 * bm d + sS d + t) 0

/-- The sign of entry `k`: from the bit of its first slot and the parities of its two slots. -/
def ss (d : List ℕ) (k : ℕ) : ℕ := (sa d (si d k) + 1 + sb d (si d k) + sb d (sj d k)) % 2

/-- Word `t` of the listed part of the output: `u_k, v_k, s_k` for `k = t / 3`. -/
def sword (d : List ℕ) (t : ℕ) : ℕ :=
  if t % 3 = 0 then su d (t / 3) else if t % 3 = 1 then sv d (t / 3) else ss d (t / 3)

/-- The output: `[n, p, m]` and the `m` entries with their signs, the input of `build`. -/
def sout (d : List ℕ) : List ℕ := [dim d, prm d, bm d] ++ (List.range (3 * bm d)).map (sword d)

/-- Well-formed inputs. -/
structure SEnc (d : List ℕ) (W : ℕ) : Prop where
  word_le : ∀ i, d.getD i 0 ≤ W
  slot_lt : ∀ k < bm d, si d k < sS d ∧ sj d k < sS d
  size : 4 * bm d + 2 * sS d + 6 ≤ W

/-! ### The program -/

/-- Set up: `r1 = 1`, `r2 = 4`, `r7 = 2`, `r3 = m`, `r4 = S`, `r5 = 4 + 4m`, `r6 = 4 + 4m + S`;
print `n, p, m`. -/
def ssetup : Stmt := block [.constN 1 1, .constN 2 4, .constN 7 2, .readIn 3 7, .constN 8 3,
  .readIn 4 8, .mulN 5 3 2, .addN 5 5 2, .addN 6 5 4, .readIn 8 0, .outN 8, .readIn 8 1,
  .outN 8, .outN 3, .copyN 10 0]

/-- Print entry `r10` (its words at `r11 = 4 + 4 r10`) with its sign. -/
def sentry : Stmt := block [.mulN 11 10 2, .addN 11 11 2, .readIn 12 11, .outN 12, .addN 11 11 1,
  .readIn 12 11, .outN 12, .addN 11 11 1, .readIn 13 11, .addN 11 11 1, .readIn 14 11,
  .addN 15 5 13, .readIn 16 15, .modN 16 16 7, .addN 15 6 13, .readIn 17 15, .modN 17 17 7,
  .addN 15 6 14, .readIn 18 15, .modN 18 18 7, .addN 16 16 1, .addN 16 16 17, .addN 16 16 18,
  .modN 16 16 7, .outN 16, .addN 10 10 1]

/-- **The signs of the listed entries.** -/
def signs : Stmt := .seq ssetup (.whileLtN 10 3 sentry)

/-! ### Correctness and cost -/

/-- The constant registers of `signs`. -/
def SRegs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = 4 ∧ c.nreg 3 = bm d ∧ c.nreg 4 = sS d ∧
    c.nreg 5 = 4 + 4 * bm d ∧ c.nreg 6 = 4 + 4 * bm d + sS d ∧ c.nreg 7 = 2

/-- The state of the loop. -/
structure ISg (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : SRegs d c
  r10 : c.nreg 10 ≤ bm d
  out : c.output = [dim d, prm d, bm d] ++ (List.range (3 * c.nreg 10)).map (sword d)

section signs
variable {d : List ℕ} {W : ℕ}

theorem sregs_of {c c' : Config} (hR : SRegs d c)
    (h : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 →
      c'.nreg x = c.nreg x) : SRegs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-- The output grows by one entry. -/
theorem sout_succ (k : ℕ) : (List.range (3 * (k + 1))).map (sword d) =
    (List.range (3 * k)).map (sword d) ++ [su d k, sv d k, ss d k] := by
  rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, List.range_succ, List.range_succ,
    List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append, List.append_cancel_left_eq, List.cons.injEq, and_true]
  unfold sword
  refine ⟨?_, ?_, ?_⟩
  · rw [iteP (by omega)]; congr 1; omega
  · rw [iteN (by omega), iteP (by omega)]; congr 1; omega
  · rw [iteN (by omega), iteN (by omega)]; congr 1; omega

theorem sentry_exec (he : SEnc d W) (c : Config) (hI : ISg d W c) (hlt : c.nreg 10 < c.nreg 3) :
    ∃ c' k, Exec (inp d) W sentry c c' k ∧ ISg d W c' ∧
      (bm d - c'.nreg 10) * 28 + k + 2 ≤ (bm d - c.nreg 10) * 28 := by
  have hc := hI.wb
  have hW := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hI.regs
  rw [h3] at hlt
  obtain ⟨hi, hj⟩ := he.slot_lt _ hlt
  have hU : (inp d).data.getD (c.nreg 10 * c.nreg 2 + c.nreg 2) 0 = su d (c.nreg 10) := by
    simp only [inp, su, h2]; congr 1; ring
  have hV : (inp d).data.getD (c.nreg 10 * c.nreg 2 + c.nreg 2 + c.nreg 1) 0 =
      sv d (c.nreg 10) := by
    simp only [inp, sv, h2, h1]; congr 1; ring
  have hI' : (inp d).data.getD (c.nreg 10 * c.nreg 2 + c.nreg 2 + c.nreg 1 + c.nreg 1) 0 =
      si d (c.nreg 10) := by
    simp only [inp, si, h2, h1]; congr 1; ring
  have hJ : (inp d).data.getD
      (c.nreg 10 * c.nreg 2 + c.nreg 2 + c.nreg 1 + c.nreg 1 + c.nreg 1) 0 = sj d (c.nreg 10) := by
    simp only [inp, sj, h2, h1]; congr 1; ring
  have hA : (inp d).data.getD (c.nreg 5 + si d (c.nreg 10)) 0 = sa d (si d (c.nreg 10)) := by
    simp only [inp, sa, h5]
  have hB : (inp d).data.getD (c.nreg 6 + si d (c.nreg 10)) 0 = sb d (si d (c.nreg 10)) := by
    simp only [inp, sb, h6]
  have hB' : (inp d).data.getD (c.nreg 6 + sj d (c.nreg 10)) 0 = sb d (sj d (c.nreg 10)) := by
    simp only [inp, sb, h6]
  unfold sentry
  exec_block
  any_goals exact he.word_le _
  any_goals
    config_simp
    try simp only [hU, hV, hI', hJ, hA, hB, hB']
    try simp only [h1, h2, h5, h6, h7]
    omega
  refine ⟨⟨‹_›, sregs_of hI.regs fun x hx => ?_, by config_simp; rw [h1]; omega, ?_⟩, ?_⟩
  · config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp
    simp only [hU, hV, hI', hJ, hA, hB, hB']
    rw [h1, h7, hI.out, sout_succ]
    have hpar : ∀ a b e : ℕ, (a % 2 + 1 + b % 2 + e % 2) % 2 = (a + 1 + b + e) % 2 := by
      intros; omega
    simp only [List.append_assoc, List.cons_append, List.nil_append, ss, hpar]
  · config_simp; rw [h1]; omega

/-- **The signs on the machine.** -/
theorem signs_exec (he : SEnc d W) :
    ∃ c' k, Exec (inp d) W signs initConfig c' k ∧ c'.output = sout d ∧ k ≤ 28 * bm d + 17 := by
  have hW := he.size
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have e₁ : ∃ c₁ k₁, Exec (inp d) W ssetup initConfig c₁ k₁ ∧ ISg d W c₁ ∧ k₁ = 15 := by
    unfold ssetup
    exec_block
    any_goals exact he.word_le _
    any_goals
      config_simp
      try simp only [inp, bm, sS] at *
      omega
    refine ⟨⟨‹_›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.zero_le _, ?_⟩, rfl⟩
    all_goals config_simp
    any_goals rfl
    any_goals (simp only [inp, bm, sS]; ring)
  obtain ⟨c₁, k₁, e₁, hC₁, rfl⟩ := e₁
  obtain ⟨c₂, k₂, e₂, hC₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 10)
    (b := 3) (body := sentry) (ISg d W) (fun c => (bm d - c.nreg 10) * 28)
    (fun c h => h.wb) (fun c hc hlt => sentry_exec he c hc hlt) hC₁
  have h10 : c₂.nreg 10 = bm d := by
    have := hC₂.r10; rw [hC₂.regs.2.2.2.1] at hn₂; omega
  refine ⟨c₂, _, .seq e₁ e₂, by rw [hC₂.out, h10]; rfl, ?_⟩
  have := Nat.sub_le (bm d) (c₁.nreg 10)
  omega

/-- **The signs of the listed entries**: the compiled program halts within `28 m + 18` steps
and prints `[n, p, m]` followed by `u_k, v_k, s_k` for every listed entry `k`, with
`s_k = (a_{i_k} + 1 + b_{i_k} + b_{j_k}) mod 2`. -/
theorem signs_runsWithin (he : SEnc d W) :
    RunsWithin (compile signs 0 ++ [Instr.halt]) (inp d) W (28 * bm d + 18) (sout d) := by
  obtain ⟨c', k, e, hout, hk⟩ := signs_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨k', by omega, h1, h2⟩

end signs

end DetMod

end NestedDissection
