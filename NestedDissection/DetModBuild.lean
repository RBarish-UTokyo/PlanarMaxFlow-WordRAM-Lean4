module

public import NestedDissection.DetModRun

/-!
# Building a skew matrix modulo a prime from an edge list, on the machine

The input `[n, p, m, u₀, v₀, s₀, …]` lists `m` entries: `A u v = ±1` and `A v u = ∓1`
(`s = 0` for `+1`, `s = 1` for `-1`, residues `1` and `p - 1`), all other entries `0`. The program
`DetMod.build` prints `[n, p] ++` the entries of `A` modulo `p` row by row, the input of
`DetMod.detMod`, within `O(n² + m)` steps (`DetMod.build_runsWithin`). Later entries overwrite
earlier ones (`DetMod.bmat`).
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The input -/

/-- The number of listed entries, and the `k`-th entry. -/
def bm (d : List ℕ) : ℕ := d.getD 2 0
def bu (d : List ℕ) (k : ℕ) : ℕ := d.getD (3 + 3 * k) 0
def bv (d : List ℕ) (k : ℕ) : ℕ := d.getD (4 + 3 * k) 0
def bs (d : List ℕ) (k : ℕ) : ℕ := d.getD (5 + 3 * k) 0

/-- The residue of the sign `s`: `1` for `0`, `p - 1` otherwise. -/
def sres (p s : ℕ) : ℕ := if s = 0 then 1 else p - 1

/-- The memory after the first `k` entries (row by row, address `u n + v`). -/
def bmem (d : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a =>
    if a = bv d k * dim d + bu d k then (prm d - sres (prm d) (bs d k)) % prm d
    else if a = bu d k * dim d + bv d k then sres (prm d) (bs d k)
    else bmem d k a

/-- The matrix of the listed entries. -/
def bmat (d : List ℕ) (t : ℕ) : ℕ := bmem d (bm d) t

/-- The output: the input of `detMod`. -/
def bout (d : List ℕ) : List ℕ :=
  [dim d, prm d] ++ (List.range (dim d * dim d)).map (bmat d)

/-- Well-formed inputs. -/
structure BEnc (d : List ℕ) (W : ℕ) : Prop where
  prime : (prm d).Prime
  word_le : ∀ i, d.getD i 0 ≤ W
  dim_sq : dim d * dim d + 2 ≤ W
  ent_lt : ∀ k < bm d, bu d k < dim d ∧ bv d k < dim d
  size : 3 * bm d + 6 ≤ W
  sq : prm d * prm d + prm d ≤ W

/-! ### The program -/

/-- Set up: `r1 = 1`, `r2 = n`, `r3 = p`, `r4 = n²`, `r5 = m`, `r6 = 3`, `r12 = p - 1`. -/
def bsetup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .mulN 4 2 2, .constN 9 2,
  .readIn 5 9, .constN 6 3, .subN 12 3 1, .copyN 7 0]

/-- Clear one cell `r7`. -/
def bclear : Stmt := block [.storeN 7 0, .addN 7 7 1]

/-- Write one listed entry `r7` (its words at `r8 = 3 + 3 r7`). -/
def bentry : Stmt :=
  .seq (block [.mulN 8 7 6, .addN 8 8 6, .readIn 9 8, .addN 8 8 1, .readIn 10 8, .addN 8 8 1,
      .readIn 11 8, .copyN 13 1])
    (.seq (.ifLtN 0 11 (.instr (.copyN 13 12)) .skip)
      (block [.mulN 14 9 2, .addN 14 14 10, .storeN 14 13, .subN 15 3 13, .modN 15 15 3,
        .mulN 14 10 2, .addN 14 14 9, .storeN 14 15, .addN 7 7 1]))

/-- Print one cell `r7`. -/
def bprint : Stmt := block [.loadN 9 7, .outN 9, .addN 7 7 1]

/-- **Build the matrix.** -/
def build : Stmt :=
  .seq bsetup <| .seq (.whileLtN 7 4 bclear) <| .seq (.instr (.copyN 7 0)) <|
  .seq (.whileLtN 7 5 bentry) <| .seq (block [.outN 2, .outN 3, .copyN 7 0])
    (.whileLtN 7 4 bprint)

/-! ### Correctness and cost -/

/-- The constant registers of `build`. -/
def BRegs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = dim d ∧ c.nreg 3 = prm d ∧ c.nreg 4 = dim d * dim d ∧
    c.nreg 5 = bm d ∧ c.nreg 6 = 3 ∧ c.nreg 12 = prm d - 1

theorem bregs_of {d : List ℕ} {c c' : Config} (hR : BRegs d c)
    (h : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 12 →
      c'.nreg x = c.nreg x) : BRegs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h12⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-- The state of the clearing loop. -/
structure IClr (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : BRegs d c
  r7 : c.nreg 7 ≤ dim d * dim d
  mem : ∀ t < c.nreg 7, c.nmem t = 0
  out : c.output = []

/-- The state of the entry loop. -/
structure IEnt (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : BRegs d c
  r7 : c.nreg 7 ≤ bm d
  mem : ∀ t < dim d * dim d, c.nmem t = bmem d (c.nreg 7) t
  out : c.output = []

/-- The state of the printing loop. -/
structure IPr (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : BRegs d c
  r7 : c.nreg 7 ≤ dim d * dim d
  mem : ∀ t < dim d * dim d, c.nmem t = bmat d t
  out : c.output = [dim d, prm d] ++ (List.range (c.nreg 7)).map (bmat d)

section build
variable {d : List ℕ} {W : ℕ}

theorem bmem_lt (he : BEnc d W) (k t : ℕ) : bmem d k t < prm d := by
  have hp := he.prime.two_le
  induction k with
  | zero => simp [bmem]; omega
  | succ k ih =>
    unfold bmem sres
    split_ifs <;> first | exact Nat.mod_lt _ (by omega) | omega | exact ih

theorem bclear_exec (he : BEnc d W) (c : Config) (hI : IClr d W c) (hlt : c.nreg 7 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W bclear c c' k ∧ IClr d W c' ∧
      (dim d * dim d - c'.nreg 7) * 4 + k + 2 ≤ (dim d * dim d - c.nreg 7) * 4 := by
  have hc := hI.wb
  have hW := he.dim_sq
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h12⟩ := hI.regs
  rw [h4] at hlt
  unfold bclear
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, bregs_of hI.regs fun x hx => ?_, by config_simp; rw [h1]; omega, fun t ht => ?_,
    by config_simp; exact hI.out⟩, by config_simp; rw [h1]; omega⟩
  · config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp at ht; config_simp; rw [h1] at ht
    rw [h0]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.mem t ht
    · rw [upd_same]

theorem bentry_post (he : BEnc d W) {c c' : Config} (hI : IEnt d W c) (hk : c.nreg 7 < bm d)
    (hw : WordsBounded W c')
    (hr : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 12 →
      c'.nreg x = c.nreg x)
    (h7 : c'.nreg 7 = c.nreg 7 + 1) (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd c.nmem (bu d (c.nreg 7) * dim d + bv d (c.nreg 7))
      (sres (prm d) (bs d (c.nreg 7)))) (bv d (c.nreg 7) * dim d + bu d (c.nreg 7))
      ((prm d - sres (prm d) (bs d (c.nreg 7))) % prm d)) : IEnt d W c' := by
  refine ⟨hw, bregs_of hI.regs hr, by rw [h7]; omega, fun t ht => ?_, hout.trans hI.out⟩
  rw [hmem, h7]
  simp only [upd_apply, bmem]
  split_ifs <;> first | rfl | exact hI.mem t ht

theorem bentry_exec (he : BEnc d W) (c : Config) (hI : IEnt d W c) (hlt : c.nreg 7 < c.nreg 5) :
    ∃ c' k, Exec (inp d) W bentry c c' k ∧ IEnt d W c' ∧
      (bm d - c'.nreg 7) * 22 + k + 2 ≤ (bm d - c.nreg 7) * 22 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWs := he.size; have hWp := he.sq
  have hp := he.prime.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h12⟩ := hI.regs
  rw [h5] at hlt
  obtain ⟨hun, hvn⟩ := he.ent_lt _ hlt
  have hu : (inp d).data.getD (c.nreg 7 * c.nreg 6 + c.nreg 6) 0 = bu d (c.nreg 7) := by
    simp only [inp, bu, h6]; congr 1; ring
  have hv : (inp d).data.getD (c.nreg 7 * c.nreg 6 + c.nreg 6 + c.nreg 1) 0 = bv d (c.nreg 7) := by
    simp only [inp, bv, h6, h1]; congr 1; ring
  have hs : (inp d).data.getD (c.nreg 7 * c.nreg 6 + c.nreg 6 + c.nreg 1 + c.nreg 1) 0 =
      bs d (c.nreg 7) := by
    simp only [inp, bs, h6, h1]; congr 1; ring
  have huv := idx_lt hun hvn; have hvu := idx_lt hvn hun
  have hK : ∀ c' : Config, (∀ x, x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 13 → x ≠ 14 → x ≠ 15 →
      c'.nreg x = c.nreg x) → ∀ x, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 12 →
      c'.nreg x = c.nreg x := fun c' h x hx => h x (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  unfold bentry
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h6]; omega
  · config_simp; rw [h6]; omega
  · exact he.word_le _
  · config_simp; rw [h6, h1]; omega
  · exact he.word_le _
  · config_simp; rw [h6, h1]; omega
  · exact he.word_le _
  config_simp
  simp only [hu, hv, hs] at *
  refine spec_seq ?_
  by_cases hs0 : bs d (c.nreg 7) = 0
  · refine spec_ifLtN_false (by config_simp; rw [h0, hs0]; omega) ?_
    refine spec_skip ‹_› ?_
    exec_block
    · config_simp; rw [h2]; exact (Nat.mul_le_mul_right _ hun.le).trans (by omega)
    · config_simp; rw [h2]; omega
    · config_simp; rw [h2]; exact (Nat.mul_le_mul_right _ hvn.le).trans (by omega)
    · config_simp; rw [h2]; omega
    · config_simp; rw [h1]; omega
    refine ⟨bentry_post he hI hlt ‹_› (hK _ fun x a b e f g h l m => ?_) (by config_simp; rw [h1])
      (by config_simp) ?_, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, h, l, m, ↓reduceIte]
    · config_simp; rw [h2, h3, h1]; simp [sres, hs0]
    · config_simp; rw [h1]; omega
  · refine spec_ifLtN_true (by config_simp; rw [h0]; omega) ?_
    refine spec_instr (Exec.copyN ‹_› _ _) fun hw => ?_
    exec_block
    · config_simp; rw [h2]; exact (Nat.mul_le_mul_right _ hun.le).trans (by omega)
    · config_simp; rw [h2]; omega
    · config_simp; rw [h2]; exact (Nat.mul_le_mul_right _ hvn.le).trans (by omega)
    · config_simp; rw [h2]; omega
    · config_simp; rw [h1]; omega
    refine ⟨bentry_post he hI hlt ‹_› (hK _ fun x a b e f g h l m => ?_) (by config_simp; rw [h1])
      (by config_simp) ?_, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, h, l, m, ↓reduceIte]
    · config_simp; rw [h2, h3, h12]; simp [sres, hs0]
    · config_simp; rw [h1]; omega

theorem bprint_exec (he : BEnc d W) (c : Config) (hI : IPr d W c) (hlt : c.nreg 7 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W bprint c c' k ∧ IPr d W c' ∧
      (dim d * dim d - c'.nreg 7) * 5 + k + 2 ≤ (dim d * dim d - c.nreg 7) * 5 := by
  have hc := hI.wb
  have hW := he.dim_sq
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h12⟩ := hI.regs
  rw [h4] at hlt
  unfold bprint
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, bregs_of hI.regs fun x hx => ?_, by config_simp; rw [h1]; omega,
    fun t ht => by config_simp; exact hI.mem t ht, ?_⟩, by config_simp; rw [h1]; omega⟩
  · config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [h1, hI.out, List.range_succ, List.map_append, hI.mem _ hlt]; simp

/-- **Building the matrix on the machine.** -/
theorem build_exec (he : BEnc d W) :
    ∃ c' k, Exec (inp d) W build initConfig c' k ∧ c'.output = bout d ∧
      k ≤ 9 * (dim d * dim d) + 22 * bm d + 20 := by
  have hW := he.dim_sq; have hWs := he.size
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have e₁ : ∃ c₁ k₁, Exec (inp d) W bsetup initConfig c₁ k₁ ∧ IClr d W c₁ ∧ k₁ = 9 := by
    unfold bsetup
    exec_block
    · omega
    · exact he.word_le _
    · exact he.word_le _
    · exact (Nat.le_add_right _ 2).trans hW
    · omega
    · exact he.word_le _
    · omega
    refine ⟨⟨‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Nat.zero_le _,
      fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩, rfl⟩
  obtain ⟨c₁, k₁, e₁, hC₁, rfl⟩ := e₁
  obtain ⟨c₂, k₂, e₂, hC₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 4) (body := bclear) (IClr d W) (fun c => (dim d * dim d - c.nreg 7) * 4)
    (fun c h => h.wb) (fun c hc hlt => bclear_exec he c hc hlt) hC₁
  have h7₂ : c₂.nreg 7 = dim d * dim d := by
    have := hC₂.r7; rw [hC₂.regs.2.2.2.2.1] at hn₂; omega
  have e₃ := Exec.copyN (P := inp d) hC₂.wb 7 0
  have hE₃ : IEnt d W { c₂ with nreg := upd c₂.nreg 7 (c₂.nreg 0) } :=
    ⟨e₃.wb_right, bregs_of hC₂.regs fun x hx => by
      config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp,
      by config_simp; rw [hC₂.regs.1]; omega,
      fun t ht => by config_simp; rw [hC₂.regs.1, hC₂.mem t (by omega)]; rfl, hC₂.out⟩
  obtain ⟨c₄, k₄, e₄, hE₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 5) (body := bentry) (IEnt d W) (fun c => (bm d - c.nreg 7) * 22)
    (fun c h => h.wb) (fun c hc hlt => bentry_exec he c hc hlt) hE₃
  have h7₄ : c₄.nreg 7 = bm d := by
    have := hE₄.r7; rw [hE₄.regs.2.2.2.2.2.1] at hn₄; omega
  have e₅ : ∃ c₅ k₅, Exec (inp d) W (block [.outN 2, .outN 3, .copyN 7 0]) c₄ c₅ k₅ ∧
      IPr d W c₅ ∧ k₅ = 3 := by
    have hw₄ := hE₄.wb
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g12⟩ := hE₄.regs
    exec_block
    refine ⟨⟨‹_›, bregs_of hE₄.regs fun x hx => ?_, by config_simp; rw [g0]; omega,
      fun t ht => by config_simp; rw [hE₄.mem t ht, h7₄]; rfl, ?_⟩, rfl⟩
    · config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · config_simp; rw [hE₄.out, g2, g3, g0]; simp
  obtain ⟨c₅, k₅, e₅, hP₅, rfl⟩ := e₅
  obtain ⟨c₆, k₆, e₆, hP₆, hn₆, hk₆⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 4) (body := bprint) (IPr d W) (fun c => (dim d * dim d - c.nreg 7) * 5)
    (fun c h => h.wb) (fun c hc hlt => bprint_exec he c hc hlt) hP₅
  have h7₆ : c₆.nreg 7 = dim d * dim d := by
    have := hP₆.r7; rw [hP₆.regs.2.2.2.2.1] at hn₆; omega
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, ?_⟩
  · rw [hP₆.out, h7₆]; rfl
  · beta_reduce at hk₂ hk₄ hk₆
    have a1 := Nat.sub_le (dim d * dim d) (c₁.nreg 7)
    have a2 := Nat.sub_le (bm d) (({ c₂ with nreg := upd c₂.nreg 7 (c₂.nreg 0) } : Config).nreg 7)
    have a3 := Nat.sub_le (dim d * dim d) (c₅.nreg 7)
    omega

/-- **Building the matrix**: the compiled program halts within `9 n² + 22 m + 21` steps and
prints `[n, p]` followed by the entries of the matrix modulo `p`. -/
theorem build_runsWithin (he : BEnc d W) :
    RunsWithin (compile build 0 ++ [Instr.halt]) (inp d) W (9 * (dim d * dim d) + 22 * bm d + 21)
      (bout d) := by
  obtain ⟨c', k, e, hout, hk⟩ := build_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨k', by omega, h1, h2⟩

end build

end DetMod

end NestedDissection
