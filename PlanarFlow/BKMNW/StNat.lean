module

public import PlanarFlow.BKMNW.StFix
public import PlanarFlow.BKMNW.StTree

/-!
# The natural s-t flow program from an explicit start

`STFlow.pstflowW_exec_nat` and `StFix.sNFM_exec` start from an **existential** input and
configuration (those of `pstflowW_exec_exists_cmp`). A call wrapper computing the input from the
frame needs the run from **its own** natural configuration. Here, for every natural configuration
`d` holding (as residues modulo `Mo = 2 H + 1`, `H = pstH n m #F #V kH0`) the real start of
`STFlow.pcore_exec` — the lengths `N c + ε` in `WT` and `PH`, the capacities in `CP`, the
restriction in `RS`, `kTh`, `kH0` — and any input meeting the hypotheses of `pcore_exec`:

* `zres`, `sdec` (the residue of an integer, the signed value of a residue), `res_sdec`,
  `sdec_zres`, `res_eq_zres`;
* `rview`: the real configuration read from `d` (natural registers `< R` and memory `≤ W`, the
  reals decoded from their residues), `rview_sim` (`Sim`), `rview_wb`, `rview_rmem`;
* **`pcore_nat`**: the natural program `constsS 201 Mo H (W + 1); toNat 201 Mo pstProg` runs from
  `d` within `4 · pcoreB + 3` steps (`pcoreB` the bound of `pcore_exec`) and ends with the residue
  of `rs e · pcoreFlowT M c ε s t T₀ e` at `W + 1 + OUT + σ e` (the explicit start: the
  compare-boundedness `pcore_cmpOK` for this configuration);
* `flowT_abs_le`, **`sdec_flow`**: the flow is read back exactly (`|rs · g| ≤ H`);
* **`pcore_sNFM`**: the same for the fixed program `sNFM` (input words in memory at `ib`), from
  the machine's configuration itself, within `3 (4 · pcoreB + 3)` steps; registers `≥ 406` but
  `999` and memory above `pstWN W H` kept.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs WordRAM.Machine.ModNat

/-! ### Residues of integers -/

/-- The residue of an integer modulo `Mo`. -/
def zres (Mo : ℕ) (z : ℤ) : ℕ := (z % (Mo : ℤ)).toNat

/-- The signed value of a residue: `v` if `v ≤ H`, `v - Mo` otherwise. -/
def sdec (Mo H v : ℕ) : ℤ := if v ≤ H then (v : ℤ) else (v : ℤ) - Mo

lemma res_sdec {Mo H v : ℕ} (_hM : 2 * H < Mo) (hv : v < Mo) :
    Res Mo ((sdec Mo H v : ℤ) : ℝ) v := by
  refine ⟨sdec Mo H v, rfl, ?_⟩
  unfold sdec
  split_ifs with h
  · exact (Int.emod_eq_of_lt (by omega) (by omega)).symm
  · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _),
      Int.emod_eq_of_lt (by omega) (by omega)]

lemma zres_lt {Mo : ℕ} (hM : 0 < Mo) (z : ℤ) : zres Mo z < Mo := by
  unfold zres
  have h1 := Int.emod_lt_of_pos z (show (0 : ℤ) < Mo by exact_mod_cast hM)
  have h2 := Int.emod_nonneg z (show (Mo : ℤ) ≠ 0 by exact_mod_cast hM.ne')
  omega

lemma sdec_zres {Mo H : ℕ} {z : ℤ} (hz : |z| ≤ H) (hM : 2 * H < Mo) : sdec Mo H (zres Mo z) = z := by
  rw [abs_le] at hz
  have hM0 : (0 : ℤ) < Mo := by omega
  unfold sdec zres
  rcases le_or_gt 0 z with h0 | h0
  · have e : z % (Mo : ℤ) = z := Int.emod_eq_of_lt h0 (by omega)
    rw [e]
    have : z.toNat ≤ H := by omega
    simp only [this, ↓reduceIte]; omega
  · have e : z % (Mo : ℤ) = z + Mo := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [e]
    have : ¬ (z + Mo).toNat ≤ H := by omega
    simp only [this, ↓reduceIte]; omega

lemma res_eq_zres {Mo : ℕ} {z : ℤ} {v : ℕ} (h : Res Mo ((z : ℤ) : ℝ) v) : v = zres Mo z := by
  obtain ⟨z', hx, hv⟩ := h
  have : z' = z := by exact_mod_cast hx.symm
  subst this
  unfold zres; omega

/-! ### The real view of a natural configuration -/

/-- **The real configuration read from a natural one**: the natural registers `< R` and memory
`≤ W` of `d` (zero elsewhere), the real registers `< R` and memory `≤ W` decoded (`sdec`) from the
residues at `R + r` and `β + a`. -/
def rview (R W Mo H β : ℕ) (d : Config) : Config where
  pc := d.pc
  nreg := fun r => if r < R then d.nreg r else 0
  rreg := fun r => if r < R then ((sdec Mo H (d.nreg (R + r)) : ℤ) : ℝ) else 0
  nmem := fun a => if a ≤ W then d.nmem a else 0
  rmem := fun a => if a ≤ W then ((sdec Mo H (d.nmem (β + a)) : ℤ) : ℝ) else 0
  output := d.output

lemma rview_sim {R W Mo H β : ℕ} {d : Config} (hM : 2 * H < Mo)
    (hr : ∀ r < R, d.nreg (R + r) < Mo) (hm : ∀ a ≤ W, d.nmem (β + a) < Mo) :
    Sim R W Mo β (rview R W Mo H β d) d where
  nreg r h := by simp [rview, h]
  rreg r h := by simp only [rview, h, ↓reduceIte]; exact res_sdec hM (hr r h)
  nmem a h := by simp [rview, h]
  rmem a h := by simp only [rview, h, ↓reduceIte]; exact res_sdec hM (hm a h)
  output := rfl

lemma rview_wb {R W Mo H β : ℕ} {d : Config} (hr : ∀ r < R, d.nreg r ≤ W)
    (hm : ∀ a ≤ W, d.nmem a ≤ W) : WordsBounded W (rview R W Mo H β d) :=
  ⟨fun r => by
      simp only [rview]; split
      · exact hr r ‹_›
      · exact Nat.zero_le _,
    fun a => by
      simp only [rview]; split
      · exact hm a ‹_›
      · exact Nat.zero_le _⟩

lemma rview_rmem {R W Mo H β : ℕ} {d : Config} {a : ℕ} (ha : a ≤ W) {z : ℤ}
    (hv : d.nmem (β + a) = zres Mo z) (hz : |z| ≤ H) (hM : 2 * H < Mo) :
    (rview R W Mo H β d).rmem a = z := by
  simp only [rview, ha, ↓reduceIte, hv, sdec_zres hz hM]

/-! ### The run from an explicit natural start -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {B : ℕ}

variable (V F) in
/-- The step bound of `pcore_exec`. -/
def pcoreB (nD n : ℕ) : ℕ :=
  140 * (n + 1) + 21 + pstOps (Fintype.card V) (Fintype.card F) nD * opCostE n +
    pstExt (Fintype.card V) (Fintype.card F) nD

variable (D V F) in
/-- The bound `H` of the compared differences of the run (`pcore_cmpOK`). -/
def pcoreH (n : ℕ) (N : ℤ) (c ε : D → ℤ) : ℕ :=
  pstH n (Fintype.card D) (Fintype.card F) (Fintype.card V) (kH0 D F N c ε).toNat

lemma kH0_le_pcoreH (n : ℕ) (N : ℤ) (c ε : D → ℤ) :
    kH0 D F N c ε ≤ (pcoreH D V F n N c ε : ℤ) := by
  have h1 : kH0 D F N c ε ≤ ((kH0 D F N c ε).toNat : ℤ) := Int.self_le_toNat _
  have h2 : (kH0 D F N c ε).toNat ≤ pcoreH D V F n N c ε := by
    unfold pcoreH pstH pstVb; omega
  have h3 : (((kH0 D F N c ε).toNat : ℕ) : ℤ) ≤ (pcoreH D V F n N c ε : ℤ) := by exact_mod_cast h2
  linarith

/-- The values of the real start are at most `kH0`: lengths, capacities, `kTh`, `kH0`. -/
lemma start_abs_le {N : ℤ} {c ε : D → ℤ} (hN : 1 ≤ N) (hc : ∀ d, 0 ≤ c d)
    (hε : ∀ d, 0 ≤ ε d) :
    (∀ d, |wlen N c ε d| ≤ kH0 D F N c ε) ∧ (∀ d, |c d| ≤ kH0 D F N c ε) ∧
      |kTh D F N c ε| ≤ kH0 D F N c ε ∧ |kH0 D F N c ε| ≤ kH0 D F N c ε ∧
      1 ≤ kH0 D F N c ε := by
  have hZ0 : 0 ≤ kZ D F N c ε := by
    have : (0 : ℤ) ≤ ∑ d, c d := sum_nonneg fun d _ => hc d
    have : (0 : ℤ) ≤ ∑ d, ε d := sum_nonneg fun d _ => hε d
    unfold kZ lexR; positivity
  have hZH := kZ_le_kH0 hZ0
  have hTH := kTh_le_kH0 hZ0
  have hTh0 : 1 ≤ kTh D F N c ε := by unfold kTh; omega
  refine ⟨fun d => (wlen_abs_le (F := F) (by omega) hc hε d).trans hZH,
    fun d => (cap_le_kZ (F := F) hN hc hε d).trans hZH, ?_, ?_, by omega⟩
  · rw [abs_of_nonneg (by omega)]; exact hTH
  · rw [abs_of_nonneg (by omega)]

/-- **The flow of the run is at most the total capacity**, hence at most `kH0`. -/
lemma flowT_abs_le (hM : M.IsPlane) {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d)
    {N : ℤ} (hN : 1 ≤ N) {s t : V} (hst : s ≠ t) {T : DTree M}
    (hT : LInv c ε s t (tSt M c ε T)) (d : D) :
    |pcoreFlowT M c ε s t T d| ≤ kH0 D F N c ε := by
  obtain ⟨hP, -, -⟩ := pcoreFlowT_spec hM hst hT
  obtain ⟨-, hcap, -, -, -⟩ := start_abs_le (F := F) hN hc hε
  have h1 := hP.le_cap d
  have h2 := hP.le_cap (M.rev d)
  have h3 := hP.antisymm d
  rw [h3] at h2
  have a1 := (abs_le.1 (hcap d)).2
  have a2 := (abs_le.1 (hcap (M.rev d))).2
  rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **The natural s-t flow program from an explicit natural start.** Under the hypotheses of
`pcore_exec` on the input `P`, from every natural configuration `d` bounded by
`pstWN W H` (`W = B + 16 (n + 1)`, `H = pcoreH`, `Mo = 2 H + 1`) whose natural registers `< 201`
and memory `≤ W` are bounded by `W`, whose residue words (registers `201 … 401`, memory
`W + 1 … 2 W + 1`) are below `Mo`, and which holds the residues of the real start of `pcore_exec`
(`WT`, `PH`: `wlen N c ε`; `CP`: `c`; `RS`: `rs`; `kTh`; `kH0`) at `W + 1 + a`, the natural
program runs within `4 · pcoreB + 3` steps, printing nothing, and ends with the residue of
`rs e · pcoreFlowT M c ε s t T₀ e` at `W + 1 + OUT + σ e`; the natural registers `≥ 406` and the
memory outside `[0, 2 W + 1]` are kept. -/
theorem pcore_nat (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t)
    {d₀ d₁ : D} (hd₀ : M.tail d₀ = t) (hd₁ : M.tail d₁ = s) (hPO : PertOK M c ε s t d₀)
    {T₀ : DTree M} (hroot : T₀.root = M.face d₀) (hI₀ : LInv c ε s t (tSt M c ε T₀))
    {N : ℤ} (hN : 2 * lexR F ε < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = s)
    {rs : D → ℤ} (hrs : ∀ e, 0 ≤ rs e ∧ rs e ≤ 1) {d : Config}
    (hd : WordsBounded (pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε)) d)
    (hdr : ∀ r < 201, d.nreg r ≤ B + 16 * (n + 1))
    (hdm : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hrr : ∀ r < 201, d.nreg (201 + r) < pstM (pcoreH D V F n N c ε))
    (hrm : ∀ a ≤ B + 16 * (n + 1),
      d.nmem (B + 16 * (n + 1) + 1 + a) < pstM (pcoreH D V F n N c ε))
    (hwt : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aWT + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (wlen N c ε e))
    (hph : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aPH nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (wlen N c ε e))
    (hcp : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aCP nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (c e))
    (hrsm : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aRS nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (rs e))
    (hth : d.nmem (B + 16 * (n + 1) + 1 + aTH nD) =
      zres (pstM (pcoreH D V F n N c ε)) (kTh D F N c ε))
    (hh0 : d.nmem (B + 16 * (n + 1) + 1 + aH0 nD) =
      zres (pstM (pcoreH D V F n N c ε)) (kH0 D F N c ε)) :
    ∃ d' k', Exec P (pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε))
        (.seq (constsS 201 (pstM (pcoreH D V F n N c ε)) (pcoreH D V F n N c ε)
          (B + 16 * (n + 1) + 1))
          (ModNat.toNat 201 (pstM (pcoreH D V F n N c ε)) (pstProg B nD n))) d d' k' ∧
      k' ≤ 4 * pcoreB V F nD n + 3 ∧
      (∀ e, d'.nmem (B + 16 * (n + 1) + 1 + (aOT nD + σ e)) =
        zres (pstM (pcoreH D V F n N c ε)) (rs e * pcoreFlowT M c ε s t T₀ e)) ∧
      d'.output = d.output ∧
      (∀ r, 406 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, 2 * (B + 16 * (n + 1)) + 1 < a → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  set W := B + 16 * (n + 1) with hWdef
  set H := pcoreH D V F n N c ε with hHdef
  set Mo := pstM H with hMo
  have hMH : 2 * H < Mo := by rw [hMo]; unfold pstM; omega
  have hσ : ∀ e : D, (σ e : ℕ) < nD := fun e => (σ e).2
  have hN1 : 1 ≤ N := by
    have : 0 ≤ lexR F ε := by
      unfold lexR
      have : (0 : ℤ) ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
      positivity
    omega
  obtain ⟨bw, bc, bth, bh0, b1⟩ := start_abs_le (F := F) hN1 hc hPO.nonneg
  have hKH := kH0_le_pcoreH (V := V) (F := F) n N c ε
  rw [← hHdef] at hKH
  set c₀ := rview 201 W Mo H (W + 1) d with hc₀
  have hS := rview_sim (R := 201) (W := W) (β := W + 1) hMH hrr hrm
  have hwb : WordsBounded W c₀ := rview_wb hdr hdm
  have hwt' : ∀ e, c₀.rmem (aWT + σ e) = wlen N c ε e := fun e =>
    rview_rmem (by have := hσ e; unfold aWT; omega) (hwt e) ((bw e).trans hKH) hMH
  have hph' : ∀ e, c₀.rmem (aPH nD + σ e) = wlen N c ε e := fun e =>
    rview_rmem (by have := hσ e; unfold aPH; omega) (hph e) ((bw e).trans hKH) hMH
  have hcp' : ∀ e, c₀.rmem (aCP nD + σ e) = c e := fun e =>
    rview_rmem (by have := hσ e; unfold aCP; omega) (hcp e) ((bc e).trans hKH) hMH
  have hrs' : ∀ e, c₀.rmem (aRS nD + σ e) = ((rs e : ℤ) : ℝ) := fun e =>
    rview_rmem (by have := hσ e; unfold aRS; omega) (hrsm e)
      (by rw [abs_of_nonneg (hrs e).1]; linarith [(hrs e).2]) hMH
  have hth' : c₀.rmem (aTH nD) = kTh D F N c ε :=
    rview_rmem (by unfold aTH; omega) hth (bth.trans hKH) hMH
  have hh0' : c₀.rmem (aH0 nD) = kH0 D F N c ε :=
    rview_rmem (by unfold aH0; omega) hh0 (bh0.trans hKH) hMH
  obtain ⟨c', steps, e, hsteps, hOUT, hout⟩ := pcore_exec hWa hB hB7 hP hM hc hst hd₀ hd₁ hPO
    hroot hI₀ hN hL hK hG hI hoff hCr hwb hwt' hph' hcp' hrs' hth' hh0'
  have hcmp := pcore_cmpOK hWa hB hB7 hP hM hc hst hd₀ hd₁ hPO hroot hI₀ hN hL hK hG hI hoff
    hCr hwb hwt' hph' hcp' hrs' hth' hh0'
  obtain ⟨d', k', e', hk', hS', -, hK', hN', hR', hRm'⟩ := (hcmp.exec e).toNat_consts
    (pstProg_regsOK _ _ _) (pstProg_noDivR _ _ _) hMH (show W < W + 1 by omega)
    (by unfold pstWN; omega) (by unfold pstWN; omega) (by rw [hMo]; unfold pstWN; omega) hS hd
  refine ⟨d', k', e', ?_, fun e => ?_, hS'.output.trans (hout.trans rfl), hK',
    fun a ha => hN' a (by omega) (Or.inr (by omega)), hR', hRm'⟩
  · unfold pcoreB; omega
  · have hres := hS'.rmem (aOT nD + σ e) (by have := hσ e; unfold aOT; omega)
    rw [hOUT e] at hres
    have : ((rs e : ℤ) : ℝ) * ((lrun M c ε s t (fuel F)
        ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩).1.g e : ℝ) =
        (((rs e * pcoreFlowT M c ε s t T₀ e : ℤ)) : ℝ) := by
      push_cast; rfl
    rw [this] at hres
    exact res_eq_zres hres

/-- **The flow read back from its residue**: `sdec` of the final word of `pcore_nat` is
`rs e · pcoreFlowT M c ε s t T₀ e`. -/
theorem sdec_flow (hM : M.IsPlane) {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t)
    {d₀ : D} (hPO : PertOK M c ε s t d₀) {T₀ : DTree M} (hI₀ : LInv c ε s t (tSt M c ε T₀))
    {N : ℤ} (hN : 2 * lexR F ε < N) {rs : D → ℤ} (hrs : ∀ e, 0 ≤ rs e ∧ rs e ≤ 1) (e : D) :
    sdec (pstM (pcoreH D V F n N c ε)) (pcoreH D V F n N c ε)
        (zres (pstM (pcoreH D V F n N c ε)) (rs e * pcoreFlowT M c ε s t T₀ e)) =
      rs e * pcoreFlowT M c ε s t T₀ e := by
  have hN1 : 1 ≤ N := by
    have : 0 ≤ lexR F ε := by
      unfold lexR
      have : (0 : ℤ) ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
      positivity
    omega
  have hKH := kH0_le_pcoreH (V := V) (F := F) n N c ε
  have hb := flowT_abs_le hM hc hPO.nonneg hN1 hst hI₀ e
  refine sdec_zres ?_ (by unfold pstM; omega)
  rw [abs_mul]
  have h1 : |rs e| ≤ 1 := by rw [abs_of_nonneg (hrs e).1]; exact (hrs e).2
  have h2 : 0 ≤ |pcoreFlowT M c ε s t T₀ e| := abs_nonneg _
  calc |rs e| * |pcoreFlowT M c ε s t T₀ e| ≤ 1 * |pcoreFlowT M c ε s t T₀ e| :=
        mul_le_mul_of_nonneg_right h1 h2
    _ ≤ _ := by linarith

set_option maxHeartbeats 1000000 in
/-- **The fixed natural s-t flow program `sNFM` from an explicit machine configuration.** The
hypotheses of `pcore_nat` on the machine configuration `e` itself (registers `< 406` and memory
`≤ pstWN W H` bounded by `pstWN W H`), the parameters `sVM B nD n H (W + 1) ib |P|` at
`1000 … 1044` and the input words of `P` at `ib` (`InData`): `sNFM` runs (on any input `P'`)
within `3 (4 · pcoreB + 3)` steps, printing nothing, and ends with the residue of
`rs e · pcoreFlowT M c ε s t T₀ e` at `W + 1 + OUT + σ e`; the natural registers `≥ 406` but
`999`, the real registers `≥ 406` and the memory above `pstWN W H` are kept. -/
theorem pcore_sNFM (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t)
    {d₀ d₁ : D} (hd₀ : M.tail d₀ = t) (hd₁ : M.tail d₁ = s) (hPO : PertOK M c ε s t d₀)
    {T₀ : DTree M} (hroot : T₀.root = M.face d₀) (hI₀ : LInv c ε s t (tSt M c ε T₀))
    {N : ℤ} (hN : 2 * lexR F ε < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = s)
    {rs : D → ℤ} (hrs : ∀ e, 0 ≤ rs e ∧ rs e ≤ 1) (P' : Input) {W' ib : ℕ} {d : Config}
    (hd : WordsBounded W' d)
    (hWW : pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε) ≤ W')
    (hdr4 : ∀ r < 406, d.nreg r ≤ pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε))
    (hdm4 : ∀ a ≤ pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε),
      d.nmem a ≤ pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε))
    (hdr : ∀ r < 201, d.nreg r ≤ B + 16 * (n + 1))
    (hdm : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hrr : ∀ r < 201, d.nreg (201 + r) < pstM (pcoreH D V F n N c ε))
    (hrm : ∀ a ≤ B + 16 * (n + 1),
      d.nmem (B + 16 * (n + 1) + 1 + a) < pstM (pcoreH D V F n N c ε))
    (hwt : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aWT + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (wlen N c ε e))
    (hph : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aPH nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (wlen N c ε e))
    (hcp : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aCP nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (c e))
    (hrsm : ∀ e, d.nmem (B + 16 * (n + 1) + 1 + (aRS nD + σ e)) =
      zres (pstM (pcoreH D V F n N c ε)) (rs e))
    (hth : d.nmem (B + 16 * (n + 1) + 1 + aTH nD) =
      zres (pstM (pcoreH D V F n N c ε)) (kTh D F N c ε))
    (hh0 : d.nmem (B + 16 * (n + 1) + 1 + aH0 nD) =
      zres (pstM (pcoreH D V F n N c ε)) (kH0 D F N c ε))
    (hIn : InData P (pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε)) ib P.data.length W' d)
    (hv : ∀ j < 45, d.nreg (1000 + j) =
      StFix.sVM B nD n (pcoreH D V F n N c ε) (B + 16 * (n + 1) + 1) ib P.data.length j) :
    ∃ d' k', Exec P' W' StFix.sNFM d d' k' ∧ k' ≤ 3 * (4 * pcoreB V F nD n + 3) ∧
      (∀ e, d'.nmem (B + 16 * (n + 1) + 1 + (aOT nD + σ e)) =
        zres (pstM (pcoreH D V F n N c ε)) (rs e * pcoreFlowT M c ε s t T₀ e)) ∧
      (∀ r, 406 ≤ r → r ≠ 999 → d'.nreg r = d.nreg r) ∧
      (∀ r, 406 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε) < a → d'.nmem a = d.nmem a) ∧
      (∀ a, pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε) < a → d'.rmem a = d.rmem a) ∧
      d'.output = d.output := by
  set Wn := pstWN (B + 16 * (n + 1)) (pcoreH D V F n N c ε) with hWn
  set U : ℕ → Bool := fun r => decide (r < 406) with hU
  set cz := trunc U Wn d with hcdef
  have hA := agree_trunc U Wn d
  have hcw : WordsBounded Wn cz := wordsBounded_trunc (fun r hr => hdr4 r (by simpa [hU] using hr))
    hdm4
  have hW1 : B + 16 * (n + 1) ≤ Wn := by rw [hWn]; unfold pstWN; omega
  have hW2 : 2 * (B + 16 * (n + 1)) + 1 ≤ Wn := by rw [hWn]; unfold pstWN; omega
  have cr : ∀ r < 406, cz.nreg r = d.nreg r := fun r hr => by
    simp [hcdef, trunc, hU, hr]
  have cm : ∀ a ≤ Wn, cz.nmem a = d.nmem a := fun a ha => by simp [hcdef, trunc, ha]
  obtain ⟨c', k', ee, hk', hOUT, hout, -, -, -, -⟩ := pcore_nat hWa hB hB7 hP hM hc hst hd₀ hd₁
    hPO hroot hI₀ hN hL hK hG hI hoff hCr hrs hcw
    (fun r hr => by rw [cr r (by omega)]; exact hdr r hr)
    (fun a ha => by rw [cm a (by omega)]; exact hdm a ha)
    (fun r hr => by rw [cr _ (by omega)]; exact hrr r hr)
    (fun a ha => by rw [cm _ (by omega)]; exact hrm a ha)
    (fun e => by rw [cm _ (by have := (σ e).2; unfold aWT; omega)]; exact hwt e)
    (fun e => by rw [cm _ (by have := (σ e).2; unfold aPH; omega)]; exact hph e)
    (fun e => by rw [cm _ (by have := (σ e).2; unfold aCP; omega)]; exact hcp e)
    (fun e => by rw [cm _ (by have := (σ e).2; unfold aRS; omega)]; exact hrsm e)
    (by rw [cm _ (by unfold aTH; omega)]; exact hth)
    (by rw [cm _ (by unfold aH0; omega)]; exact hh0)
  have hH1 : 1 ≤ pcoreH D V F n N c ε := by unfold pcoreH pstH pstVb; omega
  obtain ⟨d', s', ex, hs3, hA', hK1, hK2, hK3, hK4, L, o1, o2⟩ :=
    StFix.sNFM_exec (P' := P') ee hH1 hWW d (by
      refine ⟨fun r hr => (hA.nreg r hr), fun r hr => hA.rreg r hr, hA.nmem, hA.rmem⟩) hd hIn hv
  have hL0 : L = [] := by
    have : c'.output = cz.output := hout
    rw [o1] at this; simpa using this
  subst hL0
  refine ⟨d', s', ex, by omega, fun e => ?_, hK1, hK2, hK3, hK4, by simpa using o2⟩
  have hσe := (σ e).2
  rw [hA'.nmem _ (by unfold aOT; omega)]
  exact hOUT e

end STFlow

end PlanarFlow
