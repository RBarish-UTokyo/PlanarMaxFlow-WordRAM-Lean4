module

public import PlanarFlow.Monge.FRRoutines

/-!
# FR-Dijkstra on the machine: the parameters and the entries of a half block

`Prm` bundles the input of a run (the sizes, the base addresses, the word bound, and the data:
the lengths `D`, the prices `p`, the explicit arcs); `Lay` is the layout of the memory (the
input, the settled flags and the distances, the heap of the vertices from `wb`, the triplet
structures of the half blocks from `tb`, the heap of the half blocks from `bh`, their
range-minimum structures from `rb`) and the word bound; `Glob` the fixed registers; `HCtx` the
registers of the current half block; `Data` the input data in the memory; `Env` the three
together.

* `evF_exec`, `evE_exec`: an entry of the matrix of the half block, within `11` and `15` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The input of a run. -/
structure Prm where
  /-- The number of vertices. -/
  N : ℕ
  /-- The number of corners (the vertices `0, …, b - 1`). -/
  b : ℕ
  /-- The number of explicit arcs. -/
  m : ℕ
  /-- The base of the lengths of the dense distance graph (real memory). -/
  Db : ℕ
  /-- The base of the prices (real memory). -/
  pb : ℕ
  /-- The base of the explicit arcs (natural memory). -/
  ob : ℕ
  /-- The base of the lengths of the explicit arcs (real memory). -/
  lb : ℕ
  /-- The base of the settled flags (natural memory). -/
  sb : ℕ
  /-- The base of the distances (real memory). -/
  db : ℕ
  /-- The base of the work space. -/
  wb : ℕ
  /-- The word bound. -/
  W : ℕ
  /-- The lengths of the dense distance graph. -/
  D : ℕ → ℕ → ℤ
  /-- The prices. -/
  p : ℕ → ℤ
  /-- The first explicit arc leaving a vertex. -/
  off : ℕ → ℕ
  /-- The head of an explicit arc. -/
  dst : ℕ → ℕ
  /-- The length of an explicit arc. -/
  len : ℕ → ℤ
  /-- The root. -/
  r : ℕ

/-- The end of the heap of the vertices; the next `16 b Lv` cells are not used, the triplet
structures start at `tb`. -/
def Prm.hb (P : Prm) : ℕ := P.wb + 3 * P.N

/-- The number of levels reserved for the half blocks. -/
def Prm.Lv (P : Prm) : ℕ := Nat.log 2 P.b + 1

/-- The base of the triplet structures of the half blocks (`16 s` cells for a half block of `s`
rows, `32 b` cells for a level). -/
def Prm.tb (P : Prm) : ℕ := P.hb + 16 * P.b * P.Lv

/-- The heap of the half blocks has `2 ^ TB > b Lv` leaves. -/
def Prm.TB (P : Prm) : ℕ := Nat.log 2 (P.b * P.Lv) + 1

/-- The base of the heap of the half blocks (`16 · 2 ^ TB` cells). -/
def Prm.bh (P : Prm) : ℕ := P.tb + 32 * P.b * P.Lv

/-- The base of the range-minimum structures of the half blocks (`4 Lv s` cells for a half
block of `s` rows, `8 b Lv` cells for a level). -/
def Prm.rb (P : Prm) : ℕ := P.bh + 16 * 2 ^ P.TB

/-- The layout of the memory and the word bound. -/
structure Lay (P : Prm) : Prop where
  b_pos : 1 ≤ P.b
  bN : P.b ≤ P.N
  r_lt : P.r < P.N
  m1 : P.Db + P.b * P.b ≤ P.pb
  m2 : P.pb + P.N ≤ P.ob
  m3 : P.ob + P.N + 1 + P.m ≤ P.lb
  m4 : P.lb + P.m ≤ P.sb
  m5 : P.sb + P.N ≤ P.db
  m6 : P.db + P.N ≤ P.wb
  w : P.wb + 3 * P.N + 16 * P.b * P.Lv + 16 * P.b + 16 ≤ P.W
  wx : P.rb + 8 * P.b * P.Lv * P.Lv + 4 * P.b + 16 ≤ P.W
  off_mono : ∀ x < P.N, P.off x ≤ P.off (x + 1)
  off_last : P.off P.N = P.m
  dst_lt : ∀ e < P.m, P.dst e < P.N

/-- The fixed registers. -/
structure Glob (P : Prm) (c : Config) : Prop where
  r100 : c.nreg 100 = P.N
  r101 : c.nreg 101 = P.b
  r102 : c.nreg 102 = P.Db
  r103 : c.nreg 103 = P.pb
  r104 : c.nreg 104 = P.ob
  r105 : c.nreg 105 = P.lb
  r106 : c.nreg 106 = P.r
  r107 : c.nreg 107 = P.sb
  r108 : c.nreg 108 = P.db
  r109 : c.nreg 109 = P.wb
  r110 : c.nreg 110 = 1
  r111 : c.nreg 111 = 2
  r112 : c.nreg 112 = P.hb
  r113 : c.nreg 113 = P.b * 16
  r114 : c.nreg 114 = P.wb + P.N
  r115 : c.nreg 115 = P.b - 1
  r116 : c.nreg 116 = 4
  r117 : c.nreg 117 = 0
  r118 : c.nreg 118 = 8

theorem Glob.of {P : Prm} {c c' : Config} (h : Glob P c)
    (hr : ∀ r, 100 ≤ r → r < 119 → c'.nreg r = c.nreg r) : Glob P c' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  exact ⟨(hr 100 (by omega) (by omega)).trans a0, (hr 101 (by omega) (by omega)).trans a1,
    (hr 102 (by omega) (by omega)).trans a2, (hr 103 (by omega) (by omega)).trans a3,
    (hr 104 (by omega) (by omega)).trans a4, (hr 105 (by omega) (by omega)).trans a5,
    (hr 106 (by omega) (by omega)).trans a6, (hr 107 (by omega) (by omega)).trans a7,
    (hr 108 (by omega) (by omega)).trans a8, (hr 109 (by omega) (by omega)).trans a9,
    (hr 110 (by omega) (by omega)).trans a10, (hr 111 (by omega) (by omega)).trans a11,
    (hr 112 (by omega) (by omega)).trans a12, (hr 113 (by omega) (by omega)).trans a13,
    (hr 114 (by omega) (by omega)).trans a14, (hr 115 (by omega) (by omega)).trans a15,
    (hr 116 (by omega) (by omega)).trans a16, (hr 117 (by omega) (by omega)).trans a17,
    (hr 118 (by omega) (by omega)).trans a18⟩

/-- The registers of the half block `k` of the level `s`, with the base `B` (in the program,
the base of its range-minimum structure, `PlanarFlow.Monge.FR.rbB`). -/
structure HCtx (P : Prm) (B s k : ℕ) (c : Config) : Prop where
  r120 : c.nreg 120 = B
  r121 : c.nreg 121 = s
  r122 : c.nreg 122 = k * s
  r123 : c.nreg 123 = sib k * s
  r124 : c.nreg 124 = hbNc P.b s k
  r125 : c.nreg 125 = min s (P.b - k * s)

theorem HCtx.of {P : Prm} {B s k : ℕ} {c c' : Config} (h : HCtx P B s k c)
    (hr : ∀ r, 120 ≤ r → r < 126 → c'.nreg r = c.nreg r) : HCtx P B s k c' :=
  ⟨(hr 120 (by omega) (by omega)).trans h.r120, (hr 121 (by omega) (by omega)).trans h.r121,
    (hr 122 (by omega) (by omega)).trans h.r122, (hr 123 (by omega) (by omega)).trans h.r123,
    (hr 124 (by omega) (by omega)).trans h.r124, (hr 125 (by omega) (by omega)).trans h.r125⟩

/-- The input data in the memory. -/
structure Data (P : Prm) (c : Config) : Prop where
  dmem : ∀ i j, i < P.b → j < P.b → c.rmem (P.Db + i * P.b + j) = P.D i j
  pmem : ∀ x < P.N, c.rmem (P.pb + x) = P.p x
  omem : ∀ x ≤ P.N, c.nmem (P.ob + x) = P.off x
  emem : ∀ e < P.m, c.nmem (P.ob + P.N + 1 + e) = P.dst e
  lmem : ∀ e < P.m, c.rmem (P.lb + e) = P.len e

theorem Data.of {P : Prm} {c c' : Config} (hL : Lay P) (h : Data P c)
    (hn : ∀ a, a < P.sb → c'.nmem a = c.nmem a) (hr : ∀ a, a < P.sb → c'.rmem a = c.rmem a) :
    Data P c' := by
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4
  refine ⟨fun i j hi hj => ?_, fun x hx => ?_, fun x hx => ?_, fun e he => ?_, fun e he => ?_⟩
  · have : i * P.b + P.b ≤ P.b * P.b := by nlinarith
    rw [hr _ (by omega)]; exact h.dmem i j hi hj
  · rw [hr _ (by omega)]; exact h.pmem x hx
  · rw [hn _ (by omega)]; exact h.omem x hx
  · rw [hn _ (by omega)]; exact h.emem e he
  · rw [hr _ (by omega)]; exact h.lmem e he

/-! ### Kept registers -/

/-- The registers outside `[lo, hi)` are kept. -/
def KN (lo hi : ℕ) (c c' : Config) : Prop := ∀ r, (r < lo ∨ hi ≤ r) → c'.nreg r = c.nreg r
/-- The real registers outside `[lo, hi)` are kept. -/
def KR (lo hi : ℕ) (c c' : Config) : Prop := ∀ r, (r < lo ∨ hi ≤ r) → c'.rreg r = c.rreg r

variable {P : Prm} {I : Input}

/-! ### The entries -/

/-- **An entry of the matrix of the half block.** -/
theorem evF_exec (hL : Lay P) {B s k : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hH : HCtx P B s k c) (hD : Data P c) (hks : k * s < P.b) (hρ : c.nreg 130 ≤ s)
    (hσ : sib k * s + c.nreg 131 < P.b) :
    ∃ c' k', Exec I P.W evF c c' k' ∧ k' ≤ 11 ∧
      (c'.rreg 130 = hbF P.b P.D P.p s k (c.nreg 130) (c.nreg 131) ∧ KN 132 134 c c' ∧
        KR 130 132 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hw := hL.w
  have hb := hL.b_pos
  have h1 := hL.m1
  have h2 := hL.m2
  have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hN := hL.bN
  obtain ⟨g100, g101, g102, g103, -, -, -, -, -, -, -, -, -, -, -, g115, -, -, -⟩ := hG
  obtain ⟨-, -, g122, g123, -, -⟩ := hH
  generalize hρ' : c.nreg 130 = ρ at hρ
  generalize hσ' : c.nreg 131 = σ at hσ
  generalize ht : cl P.b (k * s + ρ) = t
  have htb : t < P.b := by rw [← ht]; unfold cl; omega
  have hsb : s < P.b + 1 := by
    have hsm := sib_mul k s
    split_ifs at hsm with hpar
    · omega
    · have : s ≤ k * s := Nat.le_mul_of_pos_left s (by omega)
      omega
  have hm : (sib k * s + σ) * P.b + P.b ≤ P.b * P.b := by
    have := Nat.mul_le_mul_right P.b (show sib k * s + σ + 1 ≤ P.b by omega)
    rwa [Nat.add_mul, Nat.one_mul] at this
  unfold evF
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 132 122 130 (by rw [g122, hρ']; omega)) fun hw₁ => ?_
  refine spec_seq ?_
  have hcl : ∃ c₂ k₂, Exec I P.W (.ifLtN 115 132 (.instr (.copyN 132 115)) .skip)
      { c with nreg := upd c.nreg 132 (c.nreg 122 + c.nreg 130) } c₂ k₂ ∧ k₂ = 2 ∧
      c₂ = { c with nreg := upd c.nreg 132 t } := by
    by_cases hlt : P.b - 1 < k * s + ρ
    · refine spec_ifLtN_true (by config_simp; rw [g115, g122, hρ']; exact hlt) ?_
      refine spec_instr (Exec.copyN hw₁ 132 115) fun _ => ⟨rfl, ?_⟩
      config_simp; rw [g115, ← ht]; unfold cl; congr 1; funext r; simp only [upd_apply]
      split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rw [g115, g122, hρ']; exact hlt) ?_
      refine spec_skip hw₁ ⟨rfl, ?_⟩
      rw [g122, hρ', ← ht]; unfold cl; congr 2; omega
  obtain ⟨c₂, k₂, e₂, hk₂, rfl⟩ := hcl
  refine ⟨_, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  exec_block
  · config_simp; rw [g123, hσ']; omega
  · config_simp; rw [g123, hσ', g101]; omega
  · config_simp; rw [g123, hσ', g101]; omega
  · config_simp; rw [g123, hσ', g101, g102]; omega
  · config_simp; rw [g103]; omega
  refine ⟨by omega, ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
    rw [g123, hσ', g101, g102, g103]
    rw [show (sib k * s + σ) * P.b + t + P.Db = P.Db + (sib k * s + σ) * P.b + t by ring,
      hD.dmem _ _ hσ htb, hD.pmem _ (by omega)]
    unfold hbF; rw [ht]; push_cast; ring
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega

/-- **An entry plus the distance of its source.** -/
theorem evE_exec (hL : Lay P) {B s k : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hH : HCtx P B s k c) (hD : Data P c) (hks : k * s < P.b) (hρ : c.nreg 130 ≤ s)
    (hσ : sib k * s + c.nreg 131 < P.b) :
    ∃ c' k', Exec I P.W evE c c' k' ∧ k' ≤ 15 ∧
      (c'.rreg 130 = c.rmem (P.db + (sib k * s + c.nreg 131)) +
          hbF P.b P.D P.p s k (c.nreg 130) (c.nreg 131) ∧ KN 132 134 c c' ∧
        KR 130 132 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hw := hL.w
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have := hL.bN
  unfold evE
  refine spec_seq ?_
  refine spec_use (evF_exec (I := I) hL c hc hG hH hD hks hρ hσ) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨e130, hN, hR, hnm, hrm, ho⟩
  have g123 : c₁.nreg 123 = sib k * s := (hN 123 (by omega)).trans hH.r123
  have g131 : c₁.nreg 131 = c.nreg 131 := hN 131 (by omega)
  have g108 : c₁.nreg 108 = P.db := (hN 108 (by omega)).trans hG.r108
  exec_block
  · rw [g123, g131]; omega
  · config_simp; rw [g123, g131, g108]; omega
  refine ⟨by omega, ?_, fun r hr => ?_, fun r hr => ?_, hnm, hrm, ho⟩
  · config_simp; rw [g123, g131, g108, e130, hrm, Nat.add_comm P.db]
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hN r hr
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hR r hr

/-! ### The nodes below the leaves -/

lemma valid_lt_iff {s j v : ℕ} (hv : Valid s j v) : v < s ↔ 0 < j := by
  constructor
  · intro h; by_contra hj0
    have : j = 0 := by omega
    subst this; exact absurd (valid_zero.1 hv).2.1 (by omega)
  · intro hj0; obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; exact valid_lt hv

/-! ### The context of a half block -/

/-- The fixed part of the context. -/
structure Env (P : Prm) (B s k : ℕ) (c : Config) : Prop where
  g : Glob P c
  h : HCtx P B s k c
  d : Data P c

theorem Env.of {P : Prm} {B s k : ℕ} {c c' : Config} (hL : Lay P) (h : Env P B s k c)
    (hr : ∀ r, 100 ≤ r → r < 126 → c'.nreg r = c.nreg r) (hn : ∀ a, a < P.sb → c'.nmem a = c.nmem a)
    (hrm : ∀ a, a < P.sb → c'.rmem a = c.rmem a) : Env P B s k c' :=
  ⟨h.g.of fun r h1 h2 => hr r h1 (by omega), h.h.of fun r h1 h2 => hr r (by omega) h2,
    h.d.of hL hn hrm⟩

end FR

end Monge

end PlanarFlow
