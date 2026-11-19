module

public import PlanarFlow.Monge.RangeMinRun

/-!
# FR-Dijkstra on the machine: the minimum of a column over an interval of rows

The bipartite Monge heap with lazy extraction (`PlanarFlow.Monge.FR.MHInv`) needs, for a
triplet (a source `σ` and an interval `[j1, j2)` of target rows of the current half block), the
least entry `E ρ σ = d σ + F ρ σ` over the rows of the interval. Since a triplet never contains
an extracted row (`PlanarFlow.Monge.FR.MHInv.activate`), the query is on the *static* matrix
`F = hbF` of the run (the lengths minus the prices of the targets).

**The routine `rmq` and its contract (`rmq_exec`).**

* Before: the context of the half block (`Env`: `r120 … r125`), the structure of the half block
  is built at `B = r120` (`QReady`), the source `σ < hbNc` in `r200`, the rows `j1 < j2 ≤ nr` in
  `r201`, `r202`.
* After: a row `ρ* ∈ [j1, j2)` in `r203` with `F ρ* σ ≤ F ρ σ` for every `ρ ∈ [j1, j2)`, and the
  value `d σ + F ρ* σ` in the real register `r200` (`QB`); the natural registers outside
  `[130, 139) ∪ [203, 208) ∪ [300, 400)`, the real registers outside
  `{130, 131} ∪ [200, 208) ∪ [300, 400)`, the memory and the output are kept (`KQ`).
* Cost: `rmqCost T = 84 T + 110` for a half block with `s = 2 ^ T` rows, `O(T)`.

**The implementation.** The range-minimum structure of `PlanarFlow.Monge.RM` (built once per
run by `PlanarFlow.Monge.RM.rmBuild`; `QReady`) with the parameters `rmp` of the half block: the
height `T` of its tree by halving `s` (`rmqLg`), the parameters in `r300 … r307`, the query
`PlanarFlow.Monge.RM.rmQuery` on the closed interval `[j1, j2 - 1]`, then the row in `r203` and
the value plus the distance of the source in the real `r200`. The matrix read by the structure is
the matrix of the half block on its rows `< s` (`rmF_rmp`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The structure of a half block -/

/-- The number of rows of the half block `k` of the level `s`. -/
def hbNr (b s k : ℕ) : ℕ := min s (b - k * s)

/-- The parameters of the range-minimum structure of the half block `k` of the level `s`, at
the base `B`. -/
def rmp (P : Prm) (B s k : ℕ) : RM.RMP where
  B := B
  T := Nat.log 2 s
  nr := hbNr P.b s k
  nc := hbNc P.b s k
  Ab := P.Db + sib k * s * P.b + k * s
  Ls := P.b
  Pb := P.pb + k * s
  W := P.W

/-- **The structure of the half block is built** at `B`: the range-minimum structure of its
matrix fits below the word bound and every node is correct. -/
def QReady (P : Prm) (B s k : ℕ) (nm : ℕ → ℕ) : Prop :=
  RM.RMLay (rmp P B s k) ∧ RM.Built (hbF P.b P.D P.p s k) (rmp P B s k) nm

/-- **The best row** `r203` (value `e + F` in the real `r200`) in `[j1, j2)`, not worse than the
rows `S`. -/
structure QB (P : Prm) (s k σ j1 j2 : ℕ) (e : ℝ) (S : ℕ → Prop) (c : Config) : Prop where
  lo : j1 ≤ c.nreg 203
  hi : c.nreg 203 < j2
  val : c.rreg 200 = e + hbF P.b P.D P.p s k (c.nreg 203) σ
  min : ∀ ρ, S ρ → hbF P.b P.D P.p s k (c.nreg 203) σ ≤ hbF P.b P.D P.p s k ρ σ

/-- What `rmq` keeps. -/
structure KQ (c c' : Config) : Prop where
  nreg : ∀ r, (r < 130 ∨ (139 ≤ r ∧ r < 203) ∨ (208 ≤ r ∧ r < 300) ∨ 400 ≤ r) →
    c'.nreg r = c.nreg r
  rreg : ∀ r, r ≠ 130 → r ≠ 131 → (r < 200 ∨ (208 ≤ r ∧ r < 300) ∨ 400 ≤ r) →
    c'.rreg r = c.rreg r
  nmem : c'.nmem = c.nmem
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

variable {P : Prm} {I : Input}

lemma rmp_T {B s k T : ℕ} (h : s = 2 ^ T) : (rmp P B s k).T = T := by
  subst h; exact Nat.log_pow (by norm_num : 1 < 2) T

lemma rmp_s {B s k T : ℕ} (h : s = 2 ^ T) : (rmp P B s k).s = s := by
  unfold RM.RMP.s; rw [rmp_T h, h]

/-- **The matrix read by the structure is the matrix of the half block** on its rows `< s`. -/
lemma rmF_rmp {B s k ρ σ : ℕ} {rm : ℕ → ℝ}
    (hD : ∀ i j, i < P.b → j < P.b → rm (P.Db + i * P.b + j) = P.D i j)
    (hp : ∀ x < P.b, rm (P.pb + x) = P.p x) (hks : k * s < P.b) (hρ : ρ < s)
    (hσ : σ < hbNc P.b s k) :
    RM.rmF rm (rmp P B s k) ρ σ = hbF P.b P.D P.p s k ρ σ := by
  unfold hbNc at hσ
  have hm : cl P.b (k * s + ρ) = k * s + min ρ (hbNr P.b s k - 1) := by
    unfold cl hbNr; omega
  have hlt : k * s + min ρ (hbNr P.b s k - 1) < P.b := by unfold hbNr; omega
  have e1 : P.Db + sib k * s * P.b + k * s + σ * P.b + min ρ (hbNr P.b s k - 1) =
      P.Db + (sib k * s + σ) * P.b + (k * s + min ρ (hbNr P.b s k - 1)) := by ring
  have e2 : P.pb + k * s + min ρ (hbNr P.b s k - 1) =
      P.pb + (k * s + min ρ (hbNr P.b s k - 1)) := by ring
  unfold RM.rmF hbF
  dsimp only [rmp]
  rw [e1, e2, hm, hD _ _ (by omega) hlt, hp _ hlt]
  push_cast; ring

/-- A built structure is built for a matrix equal on the rows `< s` and the sources `< nc`. -/
lemma built_congr_F {F F' : ℕ → ℕ → ℝ} {p : RM.RMP} {nm : ℕ → ℕ} (h : RM.Built F p nm)
    (hF : ∀ ρ < p.s, ∀ σ < p.nc, F ρ σ = F' ρ σ) : RM.Built F' p nm := by
  intro j hj o ho hos
  obtain ⟨hlok, hσ⟩ := h j hj o ho hos
  have hle : o + 2 ^ j ≤ p.s := RM.off_le ho (RM.pow_dvd_s hj) hos
  refine ⟨hlok, fun σ hσ' => ⟨?_, (hσ σ hσ').2⟩⟩
  obtain ⟨a1, a2, a3⟩ := (hσ σ hσ').1
  refine ⟨a1, a2, fun ρ' h1 h2 => ?_⟩
  rw [← hF _ (by omega) σ hσ', ← hF _ (by omega) σ hσ']
  exact a3 ρ' h1 h2

/-- **The structure answers on a memory equal to the built one on its region**
`[B, B + 4 (T + 1) s)`. -/
theorem QReady.congr_reg {B s k : ℕ} {nm nm' : ℕ → ℕ} (h : QReady P B s k nm)
    (hn : ∀ a, B ≤ a → a < B + 4 * ((rmp P B s k).T + 1) * (rmp P B s k).s → nm' a = nm a) :
    QReady P B s k nm' := by
  refine ⟨h.1, fun j hj o ho hos => (h.2 j hj o ho hos).congr fun j' hj' f hf e he => ?_⟩
  have hle : o + 2 ^ j ≤ (rmp P B s k).s := RM.off_le ho (RM.pow_dvd_s hj) hos
  refine hn _ ?_ (RM.cell_lt (by omega) hf (by omega))
  unfold RM.cell; show B ≤ B + _ + _; omega

/-- **The structure answers on a memory equal to the built one from `B` on.** -/
theorem QReady.congr {B s k : ℕ} {nm nm' : ℕ → ℕ} (h : QReady P B s k nm)
    (hn : ∀ a, B ≤ a → nm' a = nm a) : QReady P B s k nm' :=
  h.congr_reg fun a h1 _ => hn a h1

/-! ### The program -/

/-- The height `T` of the tree of the current half block (`s = 2 ^ T` in `r121`) in `r307`. -/
def rmqLg : Stmt :=
  .seq (block [.constN 307 0, .copyN 371 121])
    (.whileLtN 110 371 (block [.divN 371 371 111, .addN 307 307 110]))

/-- **The least entry of the column `r200` over the rows `[r201, r202)`** of the current half
block: the row in `r203`, the value in the real `r200`. -/
def rmq : Stmt :=
  .seq rmqLg <|
  .seq (block [.copyN 300 120, .copyN 301 121, .copyN 302 124, .mulN 303 123 101,
    .addN 303 303 102, .addN 303 303 122, .copyN 304 101, .addN 305 103 122, .subN 306 125 110,
    .copyN 312 200, .copyN 313 201, .subN 314 202 110]) <|
  .seq RM.rmQuery <|
  block [.copyN 203 315, .addN 370 108 123, .addN 370 370 200, .loadR 201 370,
    .addR 200 201 300]

/-- **The height of the tree.** -/
theorem rmqLg_exec {T : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (h121 : c.nreg 121 = 2 ^ T) (hT : T ≤ P.W) :
    ∃ c' k', Exec I P.W rmqLg c c' k' ∧ k' ≤ 4 * T + 4 ∧
      (c'.nreg 307 = T ∧ (∀ r, r ≠ 307 → r ≠ 371 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold rmqLg
  refine spec_seq ?_
  exec_block
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f371 : c₁.nreg 371 = 2 ^ T := by rw [← hc₁]; config_simp; exact h121
  have f307 : c₁.nreg 307 = 0 := by rw [← hc₁]; config_simp
  have fK : ∀ r, r ≠ 307 → r ≠ 371 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  obtain ⟨j', c', k', e, ⟨hw', h371, h307, hK, hR, hN, hM, hO⟩, hn, hk⟩ :=
    Exec.whileLtN_ghost (P := I) (W := P.W) (a := 110) (b := 371)
    (body := block [.divN 371 371 111, .addN 307 307 110])
    (fun j c' => WordsBounded P.W c' ∧ c'.nreg 371 = 2 ^ j ∧ c'.nreg 307 + j = T ∧
      (∀ r, r ≠ 307 → r ≠ 371 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun j _ => 4 * j) (fun _ _ h => h.1)
    (fun j c₂ ⟨hw₂, h371, h307, hK, hR, hN, hM, hO⟩ hlt => by
      have g110 : c₂.nreg 110 = 1 := (hK 110 (by omega) (by omega)).trans hG.r110
      have g111 : c₂.nreg 111 = 2 := (hK 111 (by omega) (by omega)).trans hG.r111
      rw [g110, h371] at hlt
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hlt
        · omega⟩
      refine ⟨j, ?_⟩
      exec_block
      · config_simp; rw [g110]; omega
      refine ⟨⟨‹_›, ?_, ?_, fun r h1 h2 => ?_, hR, hN, hM, hO⟩, by omega⟩
      · config_simp; rw [h371, g111, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      · config_simp; rw [g110]; omega
      · config_simp; rw [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact hK r h1 h2)
    (x := T) ⟨hw₁, f371, by rw [f307]; omega, fK, fR, fN, fM, fO⟩
  refine ⟨c', k', e, by omega, ?_, hK, hR, hN, hM, hO⟩
  have g110 : c'.nreg 110 = 1 := (hK 110 (by omega) (by omega)).trans hG.r110
  rw [g110, h371] at hn
  have : j' = 0 := by
    by_contra h0
    exact hn (Nat.one_lt_two_pow h0)
  omega

/-- The cost of a query in a half block with `2 ^ T` rows: `O(T)`. -/
def rmqCost (T : ℕ) : ℕ := 84 * T + 110

set_option maxHeartbeats 1000000 in
/-- **The least entry of a column over an interval of rows** (the contract of `rmq`, see the
module docstring): within `rmqCost T` steps, `r203` holds a least row `ρ*` of the column `σ` over
`[j1, j2)`, and the real `r200` its value `d σ + F ρ* σ`. -/
theorem rmq_exec (hL : Lay P) {B s k σ j1 j2 T : ℕ} (c : Config) (hc : WordsBounded P.W c)
    (hE : Env P B s k c) (_hB : B + 8 * s ≤ P.W) (hpow : s = 2 ^ T)
    (hQ : QReady P B s k c.nmem) (h200 : c.nreg 200 = σ) (hσ : σ < hbNc P.b s k)
    (h201 : c.nreg 201 = j1) (h202 : c.nreg 202 = j2) (hj : j1 < j2)
    (hj2 : j2 ≤ hbNr P.b s k) :
    ∃ c' k', Exec I P.W rmq c c' k' ∧ k' ≤ rmqCost T ∧
      QB P s k σ j1 j2 (c.rmem (P.db + (sib k * s + σ))) (fun ρ => j1 ≤ ρ ∧ ρ < j2) c' ∧
      KQ c c' := by
  have hnr : hbNr P.b s k ≤ s := Nat.min_le_left _ _
  have hks : k * s < P.b := by unfold hbNr at hj2; omega
  have hsσ : sib k * s + σ < P.b := by unfold hbNc at hσ; omega
  have hw := hL.w
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hbN := hL.bN
  have hG := hE.g; have hH := hE.h; have hD := hE.d
  have hs1 : 1 ≤ s := by rw [hpow]; exact Nat.one_le_two_pow
  have hsb : s ≤ P.b := by
    have hsm := sib_mul k s
    split_ifs at hsm with hpar
    · omega
    · have : s ≤ k * s := Nat.le_mul_of_pos_left s (by omega)
      omega
  have hTs : T < s := by rw [hpow]; exact Nat.lt_two_pow_self
  have hsb' : sib k * s * P.b + P.b ≤ P.b * P.b := by
    have := Nat.mul_le_mul_right P.b (show sib k * s + 1 ≤ P.b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; linarith
  have hDb : P.Db + P.b * P.b ≤ P.W := by omega
  obtain ⟨hlay, hbuilt⟩ := hQ
  have pT := rmp_T (P := P) (B := B) (k := k) hpow
  have ps := rmp_s (P := P) (B := B) (k := k) hpow
  unfold rmq
  refine spec_seq ?_
  refine spec_use (rmqLg_exec (I := I) (T := T) c hc hG (by rw [hH.r121, hpow]) (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨h307, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  have k1 : ∀ r, r ≠ 307 → r ≠ 371 → c₁.nreg r = c.nreg r := hK₁
  have g101 : c₁.nreg 101 = P.b := (k1 101 (by omega) (by omega)).trans hG.r101
  have g102 : c₁.nreg 102 = P.Db := (k1 102 (by omega) (by omega)).trans hG.r102
  have g103 : c₁.nreg 103 = P.pb := (k1 103 (by omega) (by omega)).trans hG.r103
  have g110 : c₁.nreg 110 = 1 := (k1 110 (by omega) (by omega)).trans hG.r110
  have g120 : c₁.nreg 120 = B := (k1 120 (by omega) (by omega)).trans hH.r120
  have g121 : c₁.nreg 121 = s := (k1 121 (by omega) (by omega)).trans hH.r121
  have g122 : c₁.nreg 122 = k * s := (k1 122 (by omega) (by omega)).trans hH.r122
  have g123 : c₁.nreg 123 = sib k * s := (k1 123 (by omega) (by omega)).trans hH.r123
  have g124 : c₁.nreg 124 = hbNc P.b s k := (k1 124 (by omega) (by omega)).trans hH.r124
  have g125 : c₁.nreg 125 = hbNr P.b s k := (k1 125 (by omega) (by omega)).trans hH.r125
  have g200 : c₁.nreg 200 = σ := (k1 200 (by omega) (by omega)).trans h200
  have g201 : c₁.nreg 201 = j1 := (k1 201 (by omega) (by omega)).trans h201
  have g202 : c₁.nreg 202 = j2 := (k1 202 (by omega) (by omega)).trans h202
  refine spec_seq ?_
  exec_block
  · config_simp; rw [g123, g101]; omega
  · config_simp; rw [g123, g101, g102]; omega
  · config_simp; rw [g123, g101, g102, g122]; omega
  · config_simp; rw [g103, g122]; omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have hP : RM.RPar (rmp P B s k) c₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hc₂] <;> config_simp
    · exact g120
    · rw [g121, ps]
    · exact g124
    · rw [g123, g101, g102, g122]; dsimp only [rmp]; ring
    · exact g101
    · rw [g103, g122]; rfl
    · rw [g125, g110]; rfl
    · rw [h307, pT]
  have f312 : c₂.nreg 312 = σ := by rw [← hc₂]; config_simp; exact g200
  have f313 : c₂.nreg 313 = j1 := by rw [← hc₂]; config_simp; exact g201
  have f314 : c₂.nreg 314 = j2 - 1 := by rw [← hc₂]; config_simp; rw [g202, g110]
  have f2K : ∀ r, (r < 300 ∨ (315 ≤ r ∧ r ≠ 371)) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [← hc₂]; config_simp; rw [← k1 r (by omega) (by omega)]; upd_tac
  have f2R : c₂.rreg = c.rreg := by rw [← hc₂]; exact hR₁
  have f2N : c₂.nmem = c.nmem := by rw [← hc₂]; exact hN₁
  have f2M : c₂.rmem = c.rmem := by rw [← hc₂]; exact hM₁
  have f2O : c₂.output = c.output := by rw [← hc₂]; exact hO₁
  have hF : ∀ ρ < s, ∀ σ' < hbNc P.b s k,
      RM.rmF c.rmem (rmp P B s k) ρ σ' = hbF P.b P.D P.p s k ρ σ' := fun ρ hρ σ' hσ' =>
    rmF_rmp (fun i j hi hj => hD.dmem i j hi hj) (fun x hx => hD.pmem x (by omega)) hks hρ hσ'
  have hB₂ : RM.Built (RM.rmF c₂.rmem (rmp P B s k)) (rmp P B s k) c₂.nmem := by
    rw [f2N, f2M]
    exact built_congr_F hbuilt fun ρ hρ σ' hσ' => (hF ρ (by rw [ps] at hρ; exact hρ) σ' hσ').symm
  refine spec_seq ?_
  refine spec_use (RM.rmQuery_exec (I := I) hlay c₂ hw₂ hP hB₂ (by rw [f312]; exact hσ)
    (by rw [f313, f314]; omega) (by rw [f314, ps]; omega)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hmin, hval, hK₃, hR₃, hN₃, hM₃, hO₃⟩
  rw [f312, f313, f314, show j2 - 1 + 1 = j2 by omega, f2M] at hmin
  rw [f312, f2M] at hval
  have k3 : ∀ r, (r < 300 ∨ (370 ≤ r ∧ r ≠ 371)) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hK₃ r (by omega)]; exact f2K r (by omega)
  have h108 : c₃.nreg 108 = P.db := (k3 108 (by omega)).trans hG.r108
  have h123 : c₃.nreg 123 = sib k * s := (k3 123 (by omega)).trans hH.r123
  have h200' : c₃.nreg 200 = σ := (k3 200 (by omega)).trans h200
  exec_block
  · config_simp; rw [h108, h123]; omega
  · config_simp; rw [h108, h123, h200']; omega
  obtain ⟨m1, m2, m3⟩ := hmin
  have hr315 : c₃.nreg 315 < s := by omega
  refine ⟨?_, ⟨?_, ?_, ?_, fun ρ hρ => ?_⟩, ⟨fun r hr => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩⟩
  · rw [pT] at hk₃; unfold rmqCost; omega
  · config_simp; exact m1
  · config_simp; exact m2
  · config_simp
    rw [h108, h123, h200', hval, hF _ hr315 σ hσ, hM₃, f2M,
      show P.db + sib k * s + σ = P.db + (sib k * s + σ) by ring]
  · config_simp
    rw [← hF _ hr315 σ hσ, ← hF ρ (by omega) σ hσ]
    exact m3 ρ hρ.1 hρ.2
  · config_simp; simp only [upd_apply]
    split_ifs <;> first | omega | exact k3 r (by omega)
  · config_simp; simp only [upd_apply]
    split_ifs <;> first | omega | (rw [hR₃ r (by omega), f2R])
  · config_simp; rw [hN₃, f2N]
  · config_simp; rw [hM₃, f2M]
  · config_simp; rw [hO₃, f2O]

end FR

end Monge

end PlanarFlow
