module

public import PlanarFlow.BKMNW.MsStB2
public import PlanarFlow.BKMNW.StDkRun
public import PlanarFlow.BKMNW.StKInit

/-!
# The MSSP encoder, stage C1–C2: Dijkstra's runs on the cut

**`msDk`** `= dkSetA ; dkSetB ; NegSSSP.stdP` with the base `Ab = r[AR]` of the run and the
address `GA` of the boundary dart whose tail is the root (`r8267`): from Klein's map words of the
cut at `IM` (`NT`, `NH`) and Dijkstra's lengths `LD` (`r8288`), the distances
`DI[ιv x] = dist (pieceGraph N univ ℓD) u x` at `Ab + 5n + 1 + nD` and the tight parents at
`Ab + 9n + 1 + nD` (`NegSSSP.stdP_exec`), `n = 4 nD + 1`, `Inf = cV · 2H + 1`.
**`msDk_exec`** (any map `N` numbered by `σ` with compact vertex nodes `1 + τv`, positive lengths
`ℓD` with `LD[σ d] = ℓD d ≤ 2H`, every vertex reached).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

/-- The registers of Dijkstra's run (all but the base and the root). -/
def dkSetA : Stmt :=
  block [.copyN 7860 7950, .constN 8264 4, .mulN 8265 7950 8264, .addN 7862 8282 8265,
    .addN 7863 7862 7950, .constN 8264 1, .addN 7861 8265 8264, .copyN 7864 8288]

/-- The infinity, the base `r8268` and the root node `NT[M[r8267]]`. -/
def dkSetB : Stmt :=
  block [.copyN 7865 8268, .addN 8265 7335 7335, .mulN 7870 7957 8265, .addN 7870 7870 8264,
    .loadN 8266 8267, .addN 8266 7862 8266, .loadN 7871 8266]

def msDk : Stmt := .seq dkSetA (.seq dkSetB stdP)

theorem dkSetA_exec (c : Config) (hc : WordsBounded W c) {nD IM LD : ℕ}
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (hw : IM + 5 * nD + 4 * nD + 2 ≤ W) (h4 : 4 ≤ W) :
    ∃ c' t, Exec P W dkSetA c c' t ∧ t = 8 ∧ c'.nreg 7860 = nD ∧ c'.nreg 7861 = 4 * nD + 1 ∧
      c'.nreg 7862 = IM + 4 * nD ∧ c'.nreg 7863 = IM + 4 * nD + nD ∧ c'.nreg 7864 = LD ∧
      c'.nreg 8264 = 1 ∧
      (∀ r, (r < 7860 ∨ 7864 < r) → r ≠ 8264 → r ≠ 8265 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dkSetA
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r82, r88]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r82, r88]; omega)
    | (simp only [r50, r82, r88]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem dkSetB_exec (c : Config) (hc : WordsBounded W c) {Ab H cV GA NTb : ℕ}
    (r68 : c.nreg 8268 = Ab) (r35 : c.nreg 7335 = H) (r57 : c.nreg 7957 = cV)
    (r64 : c.nreg 8264 = 1) (r67 : c.nreg 8267 = GA) (r62 : c.nreg 7862 = NTb)
    (hw : cV * (H + H) + 1 ≤ W) (hw' : H + H ≤ W) (hw'' : NTb + c.nmem GA ≤ W) :
    ∃ c' t, Exec P W dkSetB c c' t ∧ t = 7 ∧ c'.nreg 7865 = Ab ∧
      c'.nreg 7870 = cV * (H + H) + 1 ∧ c'.nreg 7871 = c.nmem (NTb + c.nmem GA) ∧
      (∀ r, r ≠ 7865 → r ≠ 7870 → r ≠ 7871 → r ≠ 8265 → r ≠ 8266 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold dkSetB
  exec_block
  all_goals try ((try config_simp); (try simp only [r68, r35, r57, r64, r67, r62]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r68, r35, r57, r64, r67, r62]; omega)
    | (simp only [r68, r35, r57, r64, r67, r62]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

set_option maxHeartbeats 2000000 in
/-- **Dijkstra's run on the cut** (see the module docstring). -/
theorem msDk_exec {N : CombMap D V F} {nD cV : ℕ} (σ : D ≃ Fin nD) (τv : V ≃ Fin cV)
    {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {ℓD : D → ℤ} {IM LD Ab H GA : ℕ} {u : V}
    (c : Config) (hc : WordsBounded W c)
    (hK : StEnc.KInM N σ (fun x => 1 + (τv x : ℕ)) ιg ιf ιe c.nmem IM)
    (hpos : ∀ d, 0 < ℓD d) (hLD : ∀ d, c.nmem (LD + σ d) = (ℓD d).toNat)
    (hL2 : ∀ d, (ℓD d).toNat ≤ H + H)
    (hreach : ∀ x, MSSP.Reach (MSSP.pieceGraph N univ ℓD) u x)
    (hu : c.nmem (IM + 4 * nD + c.nmem GA) = 1 + (τv u : ℕ))
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (r68 : c.nreg 8268 = Ab) (r35 : c.nreg 7335 = H) (r57 : c.nreg 7957 = cV)
    (r67 : c.nreg 8267 = GA) (hcV : cV ≤ nD)
    (l1 : IM + 6 * nD ≤ Ab) (l2 : LD + nD ≤ Ab) (hW : Ab + 10 * (4 * nD + 1) + 1 + nD ≤ W)
    (hWI : cV * (H + H) + 1 + (H + H) ≤ W) (hGA : IM + 4 * nD + c.nmem GA ≤ W) (h4 : 4 ≤ W) :
    ∃ e t, Exec P W msDk c e t ∧ t ≤ 15 + stdCost (4 * nD + 1) nD ∧
      (∀ x, e.nmem (Ab + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u x).toNat) ∧
      (∀ x, x ≠ u → ∃ d, e.nmem (Ab + 9 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) = σ d ∧
        N.head d = x ∧ MSSP.dist (MSSP.pieceGraph N univ ℓD) u (N.tail d) + ℓD d =
          MSSP.dist (MSSP.pieceGraph N univ ℓD) u x) ∧
      (∀ a, a < Ab ∨ Ab + 10 * (4 * nD + 1) + 1 + nD ≤ a → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → r ≠ 8264 → r ≠ 8265 → r ≠ 8266 →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a6x, aR, am, ar, arm, ao⟩ :=
    dkSetA_exec (P := P) c hc r50 r82 r88 (by omega) h4
  obtain ⟨c₂, t₂, e₂, ht₂, b65, b70, b71, bR, bm, br, brm, bo⟩ :=
    dkSetB_exec (P := P) c₁ e₁.wb_right (Ab := Ab) (H := H) (cV := cV) (GA := GA)
      (NTb := IM + 4 * nD) ((aR _ (by omega) (by omega) (by omega)).trans r68)
      ((aR _ (by omega) (by omega) (by omega)).trans r35)
      ((aR _ (by omega) (by omega) (by omega)).trans r57) a6x
      ((aR _ (by omega) (by omega) (by omega)).trans r67) a62 (by omega) (by omega)
      (by rw [am]; exact hGA)
  rw [am, hu] at b71
  have m2 : c₂.nmem = c.nmem := by rw [bm, am]
  have hcard : Fintype.card V * (H + H) < cV * (H + H) + 1 := by
    rw [Fintype.card_congr τv, Fintype.card_fin]; omega
  obtain ⟨c₃, t₃, e₃, ht₃, hD, hPa, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    stdP_exec (P := P) (M := N) σ (ιv := fun x => 1 + (τv x : ℕ))
      (fun x y e => τv.injective (Fin.ext (by simp only at e; omega)))
      (fun x => by have := (τv x).2; omega) (by omega) (by omega) hpos (Lmax := H + H)
      (Inf := cV * (H + H) + 1) hL2 hcard (by omega) (u := u) hreach
      (NTb := IM + 4 * nD) (NHb := IM + 4 * nD + nD) (Lb := LD) (Ab := Ab) (by omega)
      (by omega) l2 hW c₂ e₂.wb_right
      (fun d => by rw [m2]; have := hK.nt d; simp only [Klein.iNT] at this; exact this)
      (fun d => by
        rw [m2]; have := hK.nh d; simp only [Klein.iNH] at this
        rw [show IM + 4 * nD + nD = IM + 5 * nD by ring]; exact this)
      (fun d => by rw [m2]; exact hLD d)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a60)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a61)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a62)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a63)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a64) b65 b70 b71
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, hD, hPa,
    fun a ha => by rw [M₃ a ha, m2], fun r h1 h2 h3 h4 h5 => ?_, by rw [rr₃, br, ar],
    by rw [rm₃, brm, arm], by rw [o₃, bo, ao]⟩
  rw [R₃ r (by omega), bR r (by omega) (by omega) (by omega) h4 h5,
    aR r (by omega) h3 h4]

end MsEnc

end BKMNW

end PlanarFlow
