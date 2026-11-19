module

public import PlanarFlow.Monge.RangeMinQuery

/-!
# Range minima in an anti-Monge matrix on the machine: the threshold of a node

The build computes the nodes level by level, bottom-up. At a node of height `j + 1` at the offset
`o` (its children have `h = 2 ^ j` rows each), the registers `r330 … r339` hold the node
(`NCtx`): `o`, `h`, the bases of the two levels, of the threshold and row arrays of the two
children, of the threshold array of the node, and `h - 1`.

`thrS_exec`: the **threshold** of the node, by a binary search over the sources: the probe at a
source `σ` locates `σ` in the two children (two binary searches, `rmCnt`), reads their rows and
compares the two entries (`Pw`: the right child is strictly better). The sources where the right
child is strictly better form an initial segment (`win_down`), so the search finds its end within
`(18 j + 47) lg nc + 2` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs FR Heap

variable {p : RMP} {I : Input}

/-- The registers of the node of height `j + 1` at the offset `o`. -/
structure NCtx (p : RMP) (j o : ℕ) (c : Config) : Prop where
  r330 : c.nreg 330 = o
  r331 : c.nreg 331 = 2 ^ j
  r332 : c.nreg 332 = cell p (j + 1) 0 0
  r333 : c.nreg 333 = cell p j 0 0
  r334 : c.nreg 334 = cell p j 0 o
  r335 : c.nreg 335 = cell p j 0 (o + 2 ^ j)
  r336 : c.nreg 336 = cell p j 3 o
  r337 : c.nreg 337 = cell p j 3 (o + 2 ^ j)
  r338 : c.nreg 338 = cell p (j + 1) 0 o
  r339 : c.nreg 339 = 2 ^ j - 1

theorem NCtx.of {j o : ℕ} {c c' : Config} (h : NCtx p j o c)
    (hr : ∀ r, 330 ≤ r → r < 340 → c'.nreg r = c.nreg r) : NCtx p j o c' :=
  ⟨(hr 330 (by omega) (by omega)).trans h.r330, (hr 331 (by omega) (by omega)).trans h.r331,
    (hr 332 (by omega) (by omega)).trans h.r332, (hr 333 (by omega) (by omega)).trans h.r333,
    (hr 334 (by omega) (by omega)).trans h.r334, (hr 335 (by omega) (by omega)).trans h.r335,
    (hr 336 (by omega) (by omega)).trans h.r336, (hr 337 (by omega) (by omega)).trans h.r337,
    (hr 338 (by omega) (by omega)).trans h.r338, (hr 339 (by omega) (by omega)).trans h.r339⟩

/-- The right child of the node of height `j + 1` at `o` is strictly better for `σ`. -/
def Pw (F : ℕ → ℕ → ℝ) (nm : ℕ → ℕ) (p : RMP) (j o σ : ℕ) : Prop :=
  F (Arr nm p j 3 (o + 2 ^ j) (gapAt nm p j (o + 2 ^ j) σ)) σ <
    F (Arr nm p j 3 o (gapAt nm p j o σ)) σ

/-- One probe of the binary search for the threshold, in `[r327, r328)`. -/
def thrBody : Stmt :=
  .seq (block [.addN 329 327 328, .divN 329 329 309, .copyN 320 334, .copyN 321 339,
    .copyN 322 329]) <|
  .seq rmCnt <|
  .seq (block [.addN 349 336 323, .loadN 341 349, .copyN 320 335]) <|
  .seq rmCnt <|
  .seq (block [.addN 349 337 323, .loadN 342 349, .copyN 316 342, .copyN 317 329]) <|
  .seq rmEv <|
  .seq (block [.copyR 303 301, .copyN 316 341]) <|
  .seq rmEv (.ifLtR 303 301 (.instr (.addN 327 329 308)) (.instr (.copyN 328 329)))

/-- The threshold of the node, in `r327`. -/
def thrS : Stmt := .seq (block [.constN 327 0, .copyN 328 302]) (.whileLtN 327 328 thrBody)

/-- The state of the binary search for the threshold, from `c₀`. -/
structure ITh (p : RMP) (j o : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded p.W c
  keep : ∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) → c.nreg r = c₀.nreg r
  rr : KR 301 304 c₀ c
  nm : c.nmem = c₀.nmem
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  lohi : c.nreg 327 ≤ c.nreg 328
  hin : c.nreg 328 ≤ p.nc
  lo : ∀ σ < c.nreg 327, Pw (rmF c₀.rmem p) c₀.nmem p j o σ
  hi : ∀ σ, c.nreg 328 ≤ σ → σ < p.nc → ¬ Pw (rmF c₀.rmem p) c₀.nmem p j o σ

lemma cell_add (j f o e : ℕ) : cell p j f o + e = cell p j f (o + e) := by unfold cell; ring

/-- The children of a node are correct. -/
def ChildOK (F : ℕ → ℕ → ℝ) (p : RMP) (nm : ℕ → ℕ) (j o : ℕ) : Prop :=
  NodeOK F p nm j o ∧ NodeOK F p nm j (o + 2 ^ j)

set_option maxHeartbeats 1000000 in
theorem thrBody_exec (hL : RMLay p) {j o : ℕ} {c₀ : Config} (hR₀ : RCtx p c₀)
    (hN₀ : NCtx p j o c₀) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o) (hos : o < p.s)
    (hA : AntiM p.s p.nc (rmF c₀.rmem p))
    (hC : ChildOK (rmF c₀.rmem p) p c₀.nmem j o) (c : Config) (hI : ITh p j o c₀ c)
    (hlt : c.nreg 327 < c.nreg 328) :
    ∃ c' k, Exec I p.W thrBody c c' k ∧ ITh p j o c₀ c' ∧
      (18 * j + 47) * lg (c'.nreg 328 - c'.nreg 327) + k + 2 ≤
        (18 * j + 47) * lg (c.nreg 328 - c.nreg 327) := by
  have hc := hI.wb
  have hW := W_bound hL
  have hwnc := hL.wnc
  have hcb := cell_bound (p := p) (j := j) (by omega)
  have e3 := cell_eq (p := p) j 3 o
  have e3' := cell_eq (p := p) j 3 (o + 2 ^ j)
  have e0 := cell_eq (p := p) j 0 o
  have e0' := cell_eq (p := p) j 0 (o + 2 ^ j)
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have hds := off_le ho (pow_dvd_s hj) hos
  have hlgm : lg (2 ^ j - 1) ≤ j := lg_lt_pow (by have := Nat.one_le_two_pow (n := j); omega)
  have hR : RCtx p c := hR₀.of fun r h1 h2 => hI.keep r (by omega)
  have hN : NCtx p j o c := hN₀.of fun r h1 h2 => hI.keep r (by omega)
  obtain ⟨hl, hr⟩ := hC
  generalize hlo : c.nreg 327 = lo at hlt
  generalize hhi : c.nreg 328 = hi at hlt
  have hhin : hi ≤ p.nc := by rw [← hhi]; exact hI.hin
  generalize hm : (lo + hi) / 2 = m
  have hm1 : lo ≤ m := by omega
  have hm2 : m < hi := by omega
  have hsz : ∀ x, x ≤ (hi - lo) / 2 → lg x + 1 ≤ lg (hi - lo) := fun x hx =>
    lg_half' (by omega) hx
  have hsl : SortedTo (Arr c₀.nmem p j 0 o) (2 ^ j - 1) := hl.1.1.mono (by omega)
  have hsr : SortedTo (Arr c₀.nmem p j 0 (o + 2 ^ j)) (2 ^ j - 1) := hr.1.1.mono (by omega)
  -- the monotonicity of `Pw`
  have hdown : ∀ σ σ', σ < σ' → σ' < p.nc → Pw (rmF c₀.rmem p) c₀.nmem p j o σ' →
      Pw (rmF c₀.rmem p) c₀.nmem p j o σ := fun σ σ' h1 h2 h3 =>
    win_down hA (o := o) (h := 2 ^ j)
      (rl := fun σ => Arr c₀.nmem p j 3 o (gapAt c₀.nmem p j o σ))
      (rr := fun σ => Arr c₀.nmem p j 3 (o + 2 ^ j) (gapAt c₀.nmem p j (o + 2 ^ j) σ))
      (by omega) (fun σ hσ => (hl.2 σ hσ).1)
      (fun σ hσ => by have := (hr.2 σ hσ).1; rwa [show o + 2 ^ j + 2 ^ j = o + 2 * 2 ^ j by ring]
        at this) h1 h2 h3
  have hgl := gapAt_lt c₀.nmem (p := p) j o m
  have hgr := gapAt_lt c₀.nmem (p := p) j (o + 2 ^ j) m
  unfold thrBody
  refine spec_seq ?_
  exec_block
  · rw [hlo, hhi]; omega
  refine spec_seq ?_
  refine spec_use (rmCnt_exec (I := I) (f := Arr c₀.nmem p j 0 o) (n := 2 ^ j - 1) _ ‹_›
    (hR.of fun r h1 h2 => by config_simp; upd_tac) hsl
    (fun e he => by config_simp; rw [hN.r334, hI.nm, cell_add]; rfl)
    (by config_simp; rw [hN.r339]) (by config_simp; rw [hN.r334]; omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨e1, hK1, hrr1, hn1, hrm1, ho1⟩
  config_simp at e1; config_simp at hrr1; config_simp at hn1; config_simp at hrm1
  config_simp at ho1
  rw [hR.r309, hlo, hhi, hm] at e1
  have k1 : ∀ r, (r < 323 ∨ 327 ≤ r) → r ≠ 329 → r ≠ 320 → r ≠ 321 → r ≠ 322 →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by rw [hK1 r h1]; config_simp; upd_tac
  have f229 : c₁.nreg 329 = m := by rw [hK1 329 (by omega)]; config_simp; rw [hR.r309, hlo, hhi, hm]
  refine spec_seq ?_
  exec_block
  · rw [k1 336 (by omega) (by omega) (by omega) (by omega) (by omega), hN.r336, e1]
    unfold gapAt at hgl; omega
  have g221 : c₁.nreg 321 = 2 ^ j - 1 := by rw [hK1 321 (by omega)]; config_simp; exact hN.r339
  have g222 : c₁.nreg 322 = m := by rw [hK1 322 (by omega)]; config_simp; rw [hR.r309, hlo, hhi, hm]
  have g223 : c₁.nreg 323 = gapAt c₀.nmem p j o m := e1
  have ρl : c₁.nmem (c₁.nreg 336 + c₁.nreg 323) = Arr c₀.nmem p j 3 o (gapAt c₀.nmem p j o m) := by
    rw [k1 336 (by omega) (by omega) (by omega) (by omega) (by omega), hN.r336, g223, hn1, hI.nm,
      cell_add]; rfl
  have hR1 : RCtx p c₁ := hR.of fun r h1 h2 => k1 r (by omega) (by omega) (by omega)
    (by omega) (by omega)
  refine spec_seq ?_
  refine spec_use (rmCnt_exec (I := I) (f := Arr c₀.nmem p j 0 (o + 2 ^ j)) (n := 2 ^ j - 1) _ ‹_›
    (hR1.of fun r h1 h2 => by config_simp; upd_tac) hsr
    (fun e he => by
      config_simp; rw [k1 335 (by omega) (by omega) (by omega) (by omega) (by omega), hN.r335,
        hn1, hI.nm, cell_add]; rfl)
    (by config_simp; exact g221)
    (by config_simp; rw [k1 335 (by omega) (by omega) (by omega) (by omega) (by omega), hN.r335]
        omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨e2, hK2, hrr2, hn2, hrm2, ho2⟩
  config_simp at e2; config_simp at hrr2; config_simp at hn2; config_simp at hrm2
  config_simp at ho2
  rw [g222] at e2
  have k2 : ∀ r, (r < 323 ∨ 327 ≤ r) → r ≠ 349 → r ≠ 341 → r ≠ 320 → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 h4 => by rw [hK2 r h1]; config_simp; upd_tac
  have g241 : c₂.nreg 341 = Arr c₀.nmem p j 3 o (gapAt c₀.nmem p j o m) := by
    rw [hK2 341 (by omega)]; config_simp; exact ρl
  have k21 : ∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r hr => by rw [k2 r (by omega) (by omega) (by omega) (by omega)]
                   exact k1 r (by omega) (by omega) (by omega) (by omega) (by omega)
  have hR2 : RCtx p c₂ := hR.of fun r h1 h2 => k21 r (by omega)
  have hN2 : NCtx p j o c₂ := hN.of fun r h1 h2 => k21 r (by omega)
  have g229 : c₂.nreg 329 = m := by
    rw [k2 329 (by omega) (by omega) (by omega) (by omega)]; exact f229
  refine spec_seq ?_
  exec_block
  · rw [hN2.r337, e2]; unfold gapAt at hgr; omega
  have ρr : c₂.nmem (c₂.nreg 337 + c₂.nreg 323) =
      Arr c₀.nmem p j 3 (o + 2 ^ j) (gapAt c₀.nmem p j (o + 2 ^ j) m) := by
    rw [hN2.r337, e2, hn2, hn1, hI.nm, cell_add]; rfl
  refine spec_seq ?_
  refine spec_use (rmEv_exec (I := I) hL _ ‹_› (hR2.of fun r h1 h2 => by config_simp; upd_tac)
    (by config_simp; rw [g229]; omega)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨e3, hK3, hR3, hn3, hrm3, ho3⟩
  config_simp at e3; config_simp at hn3; config_simp at hrm3; config_simp at ho3
  rw [ρr, g229, hrm2, hrm1, hI.rm] at e3
  have k3 : ∀ r, (r < 316 ∨ 320 ≤ r) → r ≠ 349 → r ≠ 342 → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => by rw [hK3 r (by omega)]; config_simp; upd_tac
  refine spec_seq ?_
  exec_block
  have hR3' : RCtx p c₃ := hR2.of fun r h1 h2 => k3 r (by omega) (by omega) (by omega)
  refine spec_seq ?_
  refine spec_use (rmEv_exec (I := I) hL _ ‹_›
    (hR3'.of fun r h1 h2 => by config_simp; upd_tac)
    (by config_simp; rw [hK3 317 (by omega)]; config_simp; rw [g229]; omega)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨e4, hK4, hR4, hn4, hrm4, ho4⟩
  config_simp at e4; config_simp at hn4; config_simp at hrm4; config_simp at ho4
  rw [k3 341 (by omega) (by omega) (by omega), g241, hK3 317 (by omega)] at e4
  config_simp at e4
  rw [g229, hrm3, hrm2, hrm1, hI.rm] at e4
  have v203 : c₄.rreg 303 = rmF c₀.rmem p
      (Arr c₀.nmem p j 3 (o + 2 ^ j) (gapAt c₀.nmem p j (o + 2 ^ j) m)) m := by
    rw [hR4 303 (by omega)]; config_simp; exact e3
  have key : ∀ x, x ≤ (hi - lo) / 2 →
      (18 * j + 47) * lg x + (18 * j + 47) ≤ (18 * j + 47) * lg (hi - lo) := fun x hx => by
    have := Nat.mul_le_mul_left (18 * j + 47) (hsz x hx)
    rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have k4 : ∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) → c₄.nreg r = c.nreg r :=
    fun r hr => by
      rw [hK4 r (by omega)]; config_simp; simp only [upd_apply]; split_ifs <;> try omega
      rw [k3 r (by omega) (by omega) (by omega)]; exact k21 r hr
  have v229 : c₄.nreg 329 = m := by
    rw [hK4 329 (by omega)]; config_simp; rw [k3 329 (by omega) (by omega) (by omega), g229]
  have v208 : c₄.nreg 308 = 1 := (k4 308 (by omega)).trans hR.r308
  have v227 : c₄.nreg 327 = lo := by
    rw [hK4 327 (by omega)]; config_simp; rw [k3 327 (by omega) (by omega) (by omega),
      k2 327 (by omega) (by omega) (by omega) (by omega),
      k1 327 (by omega) (by omega) (by omega) (by omega) (by omega), hlo]
  have v228 : c₄.nreg 328 = hi := by
    rw [hK4 328 (by omega)]; config_simp; rw [k3 328 (by omega) (by omega) (by omega),
      k2 328 (by omega) (by omega) (by omega) (by omega),
      k1 328 (by omega) (by omega) (by omega) (by omega) (by omega), hhi]
  have vr : ∀ r, (r < 301 ∨ 304 ≤ r) → c₄.rreg r = c₀.rreg r := fun r hr => by
    rw [hR4 r (by omega)]; config_simp; simp only [upd_apply, show r ≠ 303 by omega, ↓reduceIte]
    rw [hR3 r (by omega)]; config_simp; rw [hrr2, hrr1]; exact hI.rr r hr
  have vn : c₄.nmem = c₀.nmem := by rw [hn4, hn3, hn2, hn1, hI.nm]
  have vm : c₄.rmem = c₀.rmem := by rw [hrm4, hrm3, hrm2, hrm1, hI.rm]
  have vo : c₄.output = c₀.output := by rw [ho4, ho3, ho2, ho1, hI.out]
  have hlo' := hI.lo; have hhi' := hI.hi
  rw [hlo] at hlo'; rw [hhi] at hhi'
  by_cases hb : c₄.rreg 303 < c₄.rreg 301
  · have hP : Pw (rmF c₀.rmem p) c₀.nmem p j o m := by
      rw [v203, e4] at hb; exact hb
    refine spec_ifLtR_true hb ?_
    refine spec_instr (Exec.addN ‹_› 327 329 308 (by rw [v229, v208]; omega)) fun hw' => ?_
    have kk : ∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) →
        upd c₄.nreg 327 (c₄.nreg 329 + c₄.nreg 308) r = c₀.nreg r := fun r hr => by
      simp only [upd_apply, show r ≠ 327 by omega, ↓reduceIte]; rw [k4 r hr]; exact hI.keep r hr
    refine ⟨?_, ?_⟩
    · refine ⟨hw', fun r hr => by config_simp; exact kk r hr, fun r hr => vr r hr, vn, vm, vo,
        by config_simp; rw [v229, v208, v228]; omega, by config_simp; rw [v228]; exact hhin,
        fun σ hσ => ?_, fun σ h1 h2 => ?_⟩
      · config_simp at hσ; rw [v229, v208] at hσ
        rcases Nat.lt_or_ge σ lo with h | h
        · exact hlo' σ h
        · rcases Nat.eq_or_lt_of_le (show σ ≤ m by omega) with e | e
          · rw [e]; exact hP
          · exact hdown σ m e (by omega) hP
      · config_simp at h1; rw [v228] at h1; exact hhi' σ h1 h2
    · config_simp; rw [v229, v208, v228]
      have := key (hi - (m + 1)) (by omega)
      omega
  · have hP : ¬ Pw (rmF c₀.rmem p) c₀.nmem p j o m := by
      rw [v203, e4] at hb; exact hb
    refine spec_ifLtR_false hb ?_
    refine spec_instr (Exec.copyN ‹_› 328 329) fun hw' => ?_
    have kk : ∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) →
        upd c₄.nreg 328 (c₄.nreg 329) r = c₀.nreg r := fun r hr => by
      simp only [upd_apply, show r ≠ 328 by omega, ↓reduceIte]; rw [k4 r hr]; exact hI.keep r hr
    refine ⟨?_, ?_⟩
    · refine ⟨hw', fun r hr => by config_simp; exact kk r hr, fun r hr => vr r hr, vn, vm, vo,
        by config_simp; rw [v229, v227]; omega, by config_simp; rw [v229]; omega,
        fun σ hσ => ?_, fun σ h1 h2 => ?_⟩
      · config_simp at hσ; rw [v227] at hσ; exact hlo' σ hσ
      · config_simp at h1; rw [v229] at h1
        rcases Nat.eq_or_lt_of_le h1 with e | e
        · rw [← e]; exact hP
        · exact fun h => hP (hdown m σ e h2 h)
    · config_simp; rw [v229, v227]
      have := key (m - lo) (by omega)
      omega

/-- **The threshold of a node**: `r327` becomes the end `θ ≤ nc` of the initial segment of the
sources where the right child is strictly better, within `(18 j + 47) lg nc + 4` steps. -/
theorem thrS_exec (hL : RMLay p) {j o : ℕ} (c : Config) (hc : WordsBounded p.W c)
    (hR : RCtx p c) (hN : NCtx p j o c) (hj : j + 1 ≤ p.T) (ho : 2 ^ (j + 1) ∣ o)
    (hos : o < p.s) (hA : AntiM p.s p.nc (rmF c.rmem p))
    (hC : ChildOK (rmF c.rmem p) p c.nmem j o) :
    ∃ c' k, Exec I p.W thrS c c' k ∧ k ≤ (18 * j + 47) * lg p.nc + 4 ∧
      (c'.nreg 327 ≤ p.nc ∧ (∀ σ < c'.nreg 327, Pw (rmF c.rmem p) c.nmem p j o σ) ∧
        (∀ σ, c'.nreg 327 ≤ σ → σ < p.nc → ¬ Pw (rmF c.rmem p) c.nmem p j o σ) ∧
        (∀ r, (r < 316 ∨ (330 ≤ r ∧ r < 340) ∨ 350 ≤ r) → c'.nreg r = c.nreg r) ∧
        KR 301 304 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wnc
  unfold thrS
  refine spec_seq ?_
  exec_block
  · omega
  config_simp
  have hw₁ : WordsBounded p.W { c with nreg := upd (upd c.nreg 327 0) 328 (c.nreg 302) } :=
    ⟨upd_le (upd_le hc.1 (Nat.zero_le _)) (hc.1 302), hc.2⟩
  have hI₀ : ITh p j o c { c with nreg := upd (upd c.nreg 327 0) 328 (c.nreg 302) } :=
    ⟨hw₁, fun r hr => by config_simp; upd_tac, fun r hr => rfl, rfl, rfl, rfl,
      by config_simp; omega, by config_simp; rw [hR.r302], fun σ hσ => by config_simp at hσ; omega,
      fun σ h1 h2 => by config_simp at h1; rw [hR.r302] at h1; omega⟩
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := p.W) (a := 327)
    (b := 328) (body := thrBody) (fun c' => ITh p j o c c')
    (fun c' => (18 * j + 47) * lg (c'.nreg 328 - c'.nreg 327)) (fun _ h => h.wb)
    (fun c' hI' hlt => thrBody_exec hL hR hN hj ho hos hA hC c' hI' hlt) hI₀
  refine ⟨c', k, e, ?_, by have := hI.lohi; have := hI.hin; omega, hI.lo,
    fun σ h1 h2 => hI.hi σ (by omega) h2, hI.keep, hI.rr, hI.nm, hI.rm, hI.out⟩
  config_simp at hk; rw [hR.r302, Nat.sub_zero] at hk; omega

end RM

end Monge

end PlanarFlow
