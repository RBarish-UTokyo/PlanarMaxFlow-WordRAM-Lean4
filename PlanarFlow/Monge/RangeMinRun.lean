module

public import PlanarFlow.Monge.RangeMinMerge

/-!
# Range minima in an anti-Monge matrix on the machine: the build

`rmBuild` builds the structure bottom-up: the constants (`rmSetup`), the leaves (`leaves`), then
one iteration of the level loop per height `j + 1 ≤ T` (`levelBody`; the children have the size
`2 ^ j = r331`, their level starts at `r333`), and in it one iteration of the node loop per
node (`nodeBody`, the offset `o = r330`): the registers of the node (`NCtx`), its threshold
(`thrS`) and the merge (`merge`).

`rmBuild_exec`: from the parameters in `r300 … r307` (`RPar`) and an anti-Monge matrix, the
structure is built (`Built`) within `83 s lg nc + 70 s T + 9 s + 12` steps. The cost of a node of
height `j + 1` is `O(j lg nc + 2 ^ j)`; the potential of the level loop
`2 ^ (T - j) (18 j + 83) lg nc + 70 s (T - j)` sums these costs (`Σ_j (j + 1) s / 2 ^ j = O(s)`).
The build writes the natural memory only in `[B, B + 4 (T + 1) s)`, the natural registers only in
`r308 … r369` and the real registers only in `r301 … r303`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs FR Heap

variable {p : RMP} {I : Input}

/-! ### The programs -/

/-- One node: its registers, its threshold, the merge, and `o := o + 2 ^ (j + 1)`. -/
def nodeBody : Stmt :=
  .seq (block [.addN 334 333 330, .addN 335 334 331, .addN 336 334 301, .addN 336 336 301,
    .addN 336 336 301, .addN 337 336 331, .addN 338 332 330]) <|
  .seq thrS <| .seq merge (block [.addN 330 330 331, .addN 330 330 331])

/-- One level: the nodes of height `j + 1`. -/
def levelBody : Stmt :=
  .seq (block [.addN 332 333 311, .subN 339 331 308, .constN 330 0]) <|
  .seq (.whileLtN 330 301 nodeBody) (block [.copyN 333 332, .addN 331 331 331])

/-- **The build of the structure.** -/
def rmBuild : Stmt :=
  .seq rmSetup <| .seq leaves <|
  .seq (block [.constN 331 1, .copyN 333 300]) (.whileLtN 331 301 levelBody)

/-! ### Alignment -/

lemma dvd_add_le {d a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) (h : a < b) : a + d ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have : x < y := Nat.lt_of_mul_lt_mul_left h
  have : d * (x + 1) ≤ d * y := Nat.mul_le_mul_left _ this
  linarith

/-! ### The node loop -/

/-- The cost of a node of height `j + 1`, with the loop test. -/
def nodeCost (p : RMP) (j : ℕ) : ℕ := (18 * j + 47) * lg p.nc + 50 * 2 ^ j + 35

/-- The registers of the level: children of height `j`. -/
structure LCtx (p : RMP) (j : ℕ) (c : Config) : Prop where
  r331 : c.nreg 331 = 2 ^ j
  r332 : c.nreg 332 = cell p (j + 1) 0 0
  r333 : c.nreg 333 = cell p j 0 0
  r339 : c.nreg 339 = 2 ^ j - 1

/-- **The state of the node loop** at the level `j + 1`, `n` nodes to go, from `c₀`: the levels
`≤ j` and the nodes of the level `j + 1` before `o = r330` are correct. -/
structure INd (p : RMP) (j : ℕ) (c₀ : Config) (n : ℕ) (c : Config) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, (r < 316 ∨ r = 331 ∨ r = 332 ∨ r = 333 ∨ r = 339 ∨ 364 ≤ r) →
    c.nreg r = c₀.nreg r
  rr : KR 301 304 c₀ c
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  pos : c.nreg 330 + 2 ^ (j + 1) * n = p.s
  dvd : 2 ^ (j + 1) ∣ c.nreg 330
  low : ∀ j' ≤ j, ∀ o, 2 ^ j' ∣ o → o < p.s → NodeOK (rmF c₀.rmem p) p c.nmem j' o
  cur : ∀ o < c.nreg 330, 2 ^ (j + 1) ∣ o → NodeOK (rmF c₀.rmem p) p c.nmem (j + 1) o
  fr : ∀ a, (a < p.B ∨ p.B + 4 * (p.T + 1) * p.s ≤ a) → c.nmem a = c₀.nmem a

set_option maxHeartbeats 1000000 in
/-- **One node**: its threshold and its merge. -/
theorem nodeBody_exec (hL : RMLay p) {j : ℕ} (hj : j + 1 ≤ p.T) {c₀ : Config}
    (hR₀ : RCtx p c₀) (hLv : LCtx p j c₀) (hA : AntiM p.s p.nc (rmF c₀.rmem p)) (n : ℕ)
    (c : Config) (hI : INd p j c₀ n c) (hlt : c.nreg 330 < c.nreg 301) :
    ∃ n' c' k, Exec I p.W nodeBody c c' k ∧ INd p j c₀ n' c' ∧
      n' * nodeCost p j + k + 2 ≤ n * nodeCost p j := by
  have hc := hI.wb
  have hW := W_bound hL
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega)
  have g331 : c.nreg 331 = 2 ^ j := (hI.keep 331 (by omega)).trans hLv.r331
  have g332 : c.nreg 332 = cell p (j + 1) 0 0 := (hI.keep 332 (by omega)).trans hLv.r332
  have g333 : c.nreg 333 = cell p j 0 0 := (hI.keep 333 (by omega)).trans hLv.r333
  have g339 : c.nreg 339 = 2 ^ j - 1 := (hI.keep 339 (by omega)).trans hLv.r339
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hpos := Nat.one_le_two_pow (n := j)
  rw [hR.r301] at hlt
  have hpos' := hI.pos
  have hdvd := hI.dvd
  generalize ho : c.nreg 330 = o at hlt hpos' hdvd
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    rcases n with _ | n'
    · omega
    · exact ⟨n', rfl⟩
  have hds := off_le hdvd (pow_dvd_s hj) hlt
  have hcb := cell_bound (p := p) (j := j + 1) hj
  have hcs := cell_succ (p := p) j 0 0
  have hs : p.s ≤ p.W := by have := hL.wB; nlinarith
  unfold nodeBody
  refine ⟨n', ?_⟩
  refine spec_seq ?_
  exec_block
  · rw [g333, ho]; omega
  · config_simp; rw [g333, ho, g331]; omega
  · config_simp; rw [g333, ho, hR.r301]; omega
  · config_simp; rw [g333, ho, hR.r301]; omega
  · config_simp; rw [g333, ho, hR.r301]; omega
  · config_simp; rw [g333, ho, hR.r301, g331]; omega
  · config_simp; rw [g332, ho]; omega
  refine spec_named (fun c₁ hc₁ hw₁ => ?_) ‹_›
  rw [← hc₁] at hw₁
  have k1 : ∀ r, (r < 334 ∨ 339 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hc₁]; config_simp; upd_tac
  have hN1 : NCtx p j o c₁ := by
    refine ⟨by rw [k1 330 (by omega), ho], by rw [k1 331 (by omega), g331],
      by rw [k1 332 (by omega), g332], by rw [k1 333 (by omega), g333], ?_, ?_, ?_, ?_, ?_,
      by rw [k1 339 (by omega), g339]⟩ <;> rw [hc₁] <;> config_simp <;>
      simp only [g331, g332, g333, ho, hR.r301] <;> unfold cell <;> ring
  have hR1 : RCtx p c₁ := hR.of fun r h1 h2 => k1 r (by omega)
  have hn1 : c₁.nmem = c.nmem := by rw [hc₁]
  have hrm1 : c₁.rmem = c.rmem := by rw [hc₁]
  have hrr1 : c₁.rreg = c.rreg := by rw [hc₁]
  have ho1 : c₁.output = c.output := by rw [hc₁]
  clear hc₁
  have hF : rmF c₁.rmem p = rmF c₀.rmem p := by rw [hrm1, hI.rm]
  have hC : ChildOK (rmF c₁.rmem p) p c₁.nmem j o := by
    rw [hF, hn1]
    have h2 : 2 ^ j ∣ o := (pow_dvd_pow 2 (by omega)).trans hdvd
    exact ⟨hI.low j le_rfl o h2 hlt, hI.low j le_rfl (o + 2 ^ j) (Nat.dvd_add h2 dvd_rfl)
      (by omega)⟩
  refine spec_seq ?_
  refine spec_use (thrS_exec (I := I) hL c₁ hw₁ hR1 hN1 hj hdvd hlt (by rw [hF]; exact hA) hC) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hθ, hlo, hhi, hK2, hrr2, hn2, hrm2, ho2⟩
  have hR2 : RCtx p c₂ := hR1.of fun r h1 h2 => hK2 r (by omega)
  have hN2 : NCtx p j o c₂ := hN1.of fun r h1 h2 => hK2 r (by omega)
  refine spec_seq ?_
  refine spec_use (merge_exec (I := I) hL c₂ hw₂ hR2 hN2 hj hdvd hlt
    (by rw [hn2, hrm2]; exact hC) hθ (by rw [hn2, hrm2]; exact hlo)
    (by rw [hn2, hrm2]; exact hhi)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hok, hfr3, hK3, hrr3, hrm3, ho3⟩
  have v330 : c₃.nreg 330 = o := by
    rw [hK3 330 (by omega), hK2 330 (by omega), k1 330 (by omega), ho]
  have v331 : c₃.nreg 331 = 2 ^ j := by
    rw [hK3 331 (by omega), hK2 331 (by omega), k1 331 (by omega), g331]
  exec_block
  · rw [v330, v331]; omega
  · config_simp; rw [v330, v331]; omega
  have hF3 : rmF c₂.rmem p = rmF c₀.rmem p := by rw [hrm2, hF]
  rw [hF3] at hok
  have hfr' : ∀ a, ¬ InLev p (j + 1) o (o + 2 ^ (j + 1)) a → c₃.nmem a = c.nmem a :=
    fun a ha => by rw [hfr3 a ha, hn2, hn1]
  refine ⟨⟨‹_›, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_,
    fun j' hj' o' h1 h2 => ?_, fun o' h1 h2 => ?_, fun a ha => ?_⟩, ?_⟩
  · config_simp
    rw [upd_other _ _ _ (by omega), hK3 r (by omega), hK2 r (by omega), k1 r (by omega)]
    exact hI.keep r hr
  · config_simp; rw [hrr3, hrr2 r hr, hrr1]; exact hI.rr r hr
  · config_simp; rw [hrm3, hrm2, hrm1, hI.rm]
  · config_simp; rw [ho3, ho2, ho1, hI.out]
  · config_simp; rw [v330, v331]
    have : 2 ^ (j + 1) * (n' + 1) = 2 ^ (j + 1) * n' + 2 ^ (j + 1) := by ring
    omega
  · config_simp; rw [v330, v331, show o + 2 ^ j + 2 ^ j = o + 2 ^ (j + 1) by omega]
    exact Nat.dvd_add hdvd dvd_rfl
  · config_simp
    have hd' := off_le h1 (pow_dvd_s (by omega)) h2
    exact NodeOK.frame hd' hds hfr' (Or.inl ⟨by omega, by omega⟩) (hI.low j' hj' o' h1 h2)
  · config_simp at h1; rw [v330, v331] at h1
    config_simp
    rcases Nat.lt_or_ge o' o with h | h
    · exact NodeOK.frame (off_le h2 (pow_dvd_s hj) (by omega)) hds hfr'
        (Or.inr (Or.inl (dvd_add_le h2 hdvd h))) (hI.cur o' (by rw [ho]; exact h) h2)
    · have : o' = o := by
        by_contra hne
        have := dvd_add_le hdvd h2 (by omega)
        omega
      subst this; exact hok
  · config_simp
    have hn : ¬ InLev p (j + 1) o (o + 2 ^ (j + 1)) a := fun h => by
      have := h.bound hj hds; omega
    rw [hfr' a hn]; exact hI.fr a ha
  · unfold nodeCost at *
    have : (n' + 1) * ((18 * j + 47) * lg p.nc + 50 * 2 ^ j + 35) =
        n' * ((18 * j + 47) * lg p.nc + 50 * 2 ^ j + 35) +
          ((18 * j + 47) * lg p.nc + 50 * 2 ^ j + 35) := by ring
    omega

/-! ### The level loop -/

/-- The potential of the level loop at the children height `j`: the cost of the levels
`j + 1, …, T`. -/
def lvPot (p : RMP) (j : ℕ) : ℕ :=
  2 ^ (p.T - j) * (18 * j + 83) * lg p.nc + 70 * p.s * (p.T - j)

/-- **The state of the level loop** at the children height `j`, from `c₀`: the levels `≤ j` are
correct. -/
structure ILv (p : RMP) (c₀ : Config) (j : ℕ) (c : Config) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, (r < 316 ∨ 364 ≤ r) → c.nreg r = c₀.nreg r
  rr : KR 301 304 c₀ c
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  jT : j ≤ p.T
  r331 : c.nreg 331 = 2 ^ j
  r333 : c.nreg 333 = cell p j 0 0
  low : ∀ j' ≤ j, ∀ o, 2 ^ j' ∣ o → o < p.s → NodeOK (rmF c₀.rmem p) p c.nmem j' o
  fr : ∀ a, (a < p.B ∨ p.B + 4 * (p.T + 1) * p.s ≤ a) → c.nmem a = c₀.nmem a

set_option maxHeartbeats 1000000 in
/-- **One level**: all its nodes. -/
theorem levelBody_exec (hL : RMLay p) {c₀ : Config} (hR₀ : RCtx p c₀)
    (hA : AntiM p.s p.nc (rmF c₀.rmem p)) (j : ℕ) (c : Config) (hI : ILv p c₀ j c)
    (hlt : c.nreg 331 < c.nreg 301) :
    ∃ j' c' k, Exec I p.W levelBody c c' k ∧ ILv p c₀ j' c' ∧ lvPot p j' + k + 2 ≤ lvPot p j := by
  have hc := hI.wb
  have hW := W_bound hL
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega)
  have hs1 := hL.s_pos
  have hs : p.s ≤ p.W := by have := hL.wB; nlinarith
  rw [hR.r301, hI.r331] at hlt
  have hjT : j + 1 ≤ p.T := by
    by_contra h
    have : p.s ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hsn : p.s = 2 ^ (j + 1) * 2 ^ (p.T - (j + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hjT]; rfl
  have hcb := cell_bound (p := p) (j := j + 1) hjT
  have hcs := cell_succ (p := p) j 0 0
  refine ⟨j + 1, ?_⟩
  unfold levelBody
  refine spec_seq ?_
  exec_block
  · rw [hI.r333, hR.r311]; omega
  · omega
  refine spec_named (fun c₁ hc₁ hw₁ => ?_) ‹_›
  rw [← hc₁] at hw₁
  have k1 : ∀ r, r ≠ 330 → r ≠ 332 → r ≠ 339 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [hc₁]; config_simp; upd_tac
  have hLv : LCtx p j c₁ := ⟨by rw [k1 331 (by omega) (by omega) (by omega), hI.r331],
    by rw [hc₁]; config_simp; rw [hI.r333, hR.r311, hcs],
    by rw [k1 333 (by omega) (by omega) (by omega), hI.r333],
    by rw [hc₁]; config_simp; rw [hI.r331, hR.r308]⟩
  have hR1 : RCtx p c₁ := hR.of fun r h1 h2 => k1 r (by omega) (by omega) (by omega)
  have hn1 : c₁.nmem = c.nmem := by rw [hc₁]
  have hrm1 : c₁.rmem = c.rmem := by rw [hc₁]
  have hrr1 : c₁.rreg = c.rreg := by rw [hc₁]
  have ho1 : c₁.output = c.output := by rw [hc₁]
  have h330 : c₁.nreg 330 = 0 := by rw [hc₁]; config_simp
  clear hc₁
  have hF : rmF c₁.rmem p = rmF c₀.rmem p := by rw [hrm1, hI.rm]
  have hN₀ : INd p j c₁ (2 ^ (p.T - (j + 1))) c₁ :=
    ⟨hw₁, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, by rw [h330, ← hsn]; omega,
      by rw [h330]; exact dvd_zero _,
      fun j' hj' o h1 h2 => by rw [hF, hn1]; exact hI.low j' (by omega) o h1 h2,
      fun o ho => by rw [h330] at ho; omega, fun _ _ => rfl⟩
  refine spec_seq ?_
  obtain ⟨nf, c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_ghost (P := I) (W := p.W) (a := 330)
    (b := 301) (body := nodeBody) (fun n c' => INd p j c₁ n c')
    (fun n _ => n * nodeCost p j) (fun _ _ h => h.wb)
    (fun n c' hI' hlt' => nodeBody_exec hL hjT hR1 hLv (by rw [hF]; exact hA) n c' hI' hlt') hN₀
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := hI₂.wb
  have hR2 : RCtx p c₂ := hR1.of fun r h1 h2 => hI₂.keep r (by omega)
  have hpos := hI₂.pos
  rw [hR2.r301] at hn₂
  have h2s : c₂.nreg 330 = p.s := by
    have : 2 ^ (j + 1) * nf = 0 ∨ 0 < 2 ^ (j + 1) * nf := Nat.eq_zero_or_pos _
    rcases this with h | h <;> omega
  have v331 : c₂.nreg 331 = 2 ^ j := (hI₂.keep 331 (by omega)).trans hLv.r331
  have v332 : c₂.nreg 332 = cell p (j + 1) 0 0 := (hI₂.keep 332 (by omega)).trans hLv.r332
  exec_block
  · config_simp; rw [v331]; omega
  refine ⟨⟨‹_›, fun r hr => ?_, fun r hr => ?_, ?_, ?_, hjT, ?_, ?_,
    fun j' hj' o h1 h2 => ?_, fun a ha => ?_⟩, ?_⟩
  · config_simp
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hI₂.keep r (by omega),
      k1 r (by omega) (by omega) (by omega)]
    exact hI.keep r hr
  · config_simp; rw [hI₂.rr r hr, hrr1]; exact hI.rr r hr
  · config_simp; rw [hI₂.rm, hrm1, hI.rm]
  · config_simp; rw [hI₂.out, ho1, hI.out]
  · config_simp; rw [v331, hpow]; ring
  · config_simp; rw [v332]
  · config_simp
    have hF' : rmF c₀.rmem p = rmF c₁.rmem p := hF.symm
    rw [hF']
    rcases Nat.lt_or_ge j' (j + 1) with h | h
    · exact hI₂.low j' (by omega) o h1 h2
    · obtain rfl : j' = j + 1 := by omega
      exact hI₂.cur o (by rw [h2s]; exact h2) h1
  · config_simp; rw [hI₂.fr a ha, hn1]; exact hI.fr a ha
  · -- the cost
    unfold lvPot
    unfold nodeCost at hk₂
    generalize hn0 : 2 ^ (p.T - (j + 1)) = n0 at hsn hk₂
    generalize hL' : lg p.nc = L at hk₂ ⊢
    have e1 : 2 ^ (p.T - j) = 2 * n0 := by
      rw [← hn0, show p.T - j = p.T - (j + 1) + 1 by omega, pow_succ]; ring
    have e2 : p.T - j = p.T - (j + 1) + 1 := by omega
    rw [e1, e2]
    have f2 : n0 * ((18 * j + 47) * L + 50 * 2 ^ j + 35) =
        18 * (j * (n0 * L)) + 47 * (n0 * L) + 25 * (2 * 2 ^ j * n0) + 35 * n0 := by ring
    have f3 : 2 * n0 * (18 * j + 83) * L = 36 * (j * (n0 * L)) + 166 * (n0 * L) := by ring
    have f4 : n0 * (18 * (j + 1) + 83) * L = 18 * (j * (n0 * L)) + 101 * (n0 * L) := by ring
    have f5 : 70 * p.s * (p.T - (j + 1) + 1) = 70 * p.s * (p.T - (j + 1)) + 70 * p.s := by ring
    have f6 : p.s = 2 * 2 ^ j * n0 := by rw [hsn, hpow]
    have f7 : n0 ≤ p.s := by
      rw [f6]; have := Nat.one_le_two_pow (n := j); nlinarith
    rw [f2] at hk₂
    rw [f3, f4, f5]
    omega

/-- The cost of the build. -/
def rmBuildCost (p : RMP) : ℕ := 83 * p.s * lg p.nc + 70 * p.s * p.T + 9 * p.s + 12

lemma rmBuildCost_le (p : RMP) : rmBuildCost p ≤ 83 * p.s * (p.T + lg p.nc + 1) + 12 := by
  unfold rmBuildCost
  have : 83 * p.s * (p.T + lg p.nc + 1) = 83 * p.s * lg p.nc + 83 * p.s * p.T + 83 * p.s := by
    ring
  have : 70 * p.s * p.T ≤ 83 * p.s * p.T := Nat.mul_le_mul_right _ (by omega)
  omega

set_option maxHeartbeats 1000000 in
/-- **The build of the structure.** From the parameters in `r300 … r307` and an anti-Monge
matrix (`rmF`, read in the real memory), `rmBuild` builds the structure (`Built`) within
`83 s lg nc + 70 s T + 9 s + 12` steps. It writes the natural memory only in
`[B, B + 4 (T + 1) s)`, the natural registers only in `r308 … r369`, the real registers only in
`r301 … r303`, and no real memory. -/
theorem rmBuild_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hP : RPar p c)
    (hA : AntiM p.s p.nc (rmF c.rmem p)) :
    ∃ c' k, Exec I p.W rmBuild c c' k ∧ k ≤ rmBuildCost p ∧
      (Built (rmF c.rmem p) p c'.nmem ∧
        (∀ a, (a < p.B ∨ p.B + 4 * (p.T + 1) * p.s ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, (r < 308 ∨ 370 ≤ r) → c'.nreg r = c.nreg r) ∧ KR 301 304 c c' ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hW := W_bound hL
  have hs1 := hL.s_pos
  unfold rmBuild
  refine spec_seq ?_
  refine spec_use (rmSetup_exec (I := I) hL c hc hP) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hR1, hK1, hrr1, hn1, hrm1, ho1⟩
  refine spec_seq ?_
  refine spec_use (leaves_exec (I := I) hL c₁ hw₁ hR1) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hok2, hfr2, hK2, hrr2, hrm2, ho2⟩
  have hR2 : RCtx p c₂ := hR1.of fun r h1 h2 => hK2 r (by omega) (by omega)
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_named (fun c₃ hc₃ hw₃ => ?_) ‹_›
  rw [← hc₃] at hw₃
  have k3 : ∀ r, r ≠ 331 → r ≠ 333 → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [hc₃]; config_simp; upd_tac
  have hn3 : c₃.nmem = c₂.nmem := by rw [hc₃]
  have hrm3 : c₃.rmem = c₂.rmem := by rw [hc₃]
  have hrr3 : c₃.rreg = c₂.rreg := by rw [hc₃]
  have ho3 : c₃.output = c₂.output := by rw [hc₃]
  have h331 : c₃.nreg 331 = 1 := by rw [hc₃]; config_simp
  have h333 : c₃.nreg 333 = p.B := by rw [hc₃]; config_simp; exact hR2.r300
  clear hc₃
  have hR3 : RCtx p c₃ := hR2.of fun r h1 h2 => k3 r (by omega) (by omega)
  have hF : rmF c₃.rmem p = rmF c.rmem p := by rw [hrm3, hrm2, hrm1]
  have hI₀ : ILv p c₃ 0 c₃ := ⟨hw₃, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, Nat.zero_le _,
    by rw [h331]; rfl, by rw [h333]; unfold cell; ring,
    fun j' hj' o h1 h2 => by
      obtain rfl : j' = 0 := by omega
      rw [hn3]; exact leaf_ok (hok2 o h2).1 (hok2 o h2).2,
    fun _ _ => rfl⟩
  obtain ⟨jf, c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_ghost (P := I) (W := p.W) (a := 331)
    (b := 301) (body := levelBody) (fun j c' => ILv p c₃ j c') (fun j _ => lvPot p j)
    (fun _ _ h => h.wb) (fun j c' hI' hlt' => levelBody_exec hL hR3 (by rw [hF]; exact hA) j c'
      hI' hlt') hI₀
  refine ⟨c₄, k₄, e₄, ?_⟩
  have hR4 : RCtx p c₄ := hR3.of fun r h1 h2 => hI₄.keep r (by omega)
  rw [hR4.r301, hI₄.r331] at hn₄
  have hjf : jf = p.T := by
    have := hI₄.jT
    by_contra h
    have : 2 ^ jf < 2 ^ p.T := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact hn₄ this
  subst hjf
  have hrmF : rmF c₃.rmem p = rmF c.rmem p := hF
  refine ⟨?_, fun j hj o h1 h2 => ?_, fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · have e : lvPot p 0 = 83 * p.s * lg p.nc + 70 * p.s * p.T := by
      unfold lvPot; simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_add]; unfold RMP.s; ring
    unfold rmBuildCost
    rw [e] at hk₄
    generalize 83 * p.s * lg p.nc = X at hk₄ ⊢
    generalize 70 * p.s * p.T = Y at hk₄ ⊢
    omega
  · rw [← hrmF]; exact hI₄.low j hj o h1 h2
  · rw [hI₄.fr a ha, hn3]
    have hn : ¬ InLev p 0 0 p.s a := fun h => by
      have := h.bound (Nat.zero_le _) le_rfl; omega
    rw [hfr2 a hn, hn1]
  · rw [hI₄.keep r (by omega), k3 r (by omega) (by omega), hK2 r (by omega) (by omega),
      hK1 r (by omega)]
  · rw [hI₄.rr r hr, hrr3, hrr2, hrr1]
  · rw [hI₄.rm, hrm3, hrm2, hrm1]
  · rw [hI₄.out, ho3, ho2, ho1]

end RM

end Monge

end PlanarFlow
