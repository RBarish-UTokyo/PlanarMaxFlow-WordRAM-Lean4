module

public import PlanarFlow.BKMNW.FrImD

/-!
# The FR image program and its specification

**`frImg`** `= fiPre ; fiNat ; fiRes` (natural words only) writes, from the corners, the
matrix of the dense distance graph, the prices and the explicit arcs in memory (`FrImgIn`, the
integers stored with an offset `K`), the natural image of the FR input
`frPrm b Dm pm r ET EH Lz mE` at `A` and the registers `r7600 … r7613` that
`FrFix.frCall_exec` reads.

**`frImg_spec`**: `FrImgSpec frImg fiScr fiCost fiRoom`, with
`fiCost b mE = 30 b² + 100 b + 100 mE + 300` steps and the scratch `fiRoom b mE = 2 mE + 4 b + 2`
(the counting sort of the arcs by tail); the scratch registers `fiScr`
(`2966 … 2971`, `7600 … 7613`, `8112 … 8149`, `1500 … 1520`, `4910 … 4916`, `5030 … 5035`,
`7861`, `7865`, `7873 … 7875`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-- **The FR image program.** -/
def frImg : Stmt := .seq fiPre (.seq fiNat fiRes)

/-- `frImg` has no real instruction and no real test. -/
theorem frImg_natOnly : Klein.natOnly frImg = true := by decide +kernel

/-- The scratch registers of `frImg`. -/
def fiScr (r : ℕ) : Prop :=
  (2966 ≤ r ∧ r ≤ 2971) ∨ (7600 ≤ r ∧ r ≤ 7613) ∨ (8112 ≤ r ∧ r ≤ 8149) ∨
    (1500 ≤ r ∧ r ≤ 1520) ∨ (4910 ≤ r ∧ r ≤ 4916) ∨ (5030 ≤ r ∧ r ≤ 5035) ∨ r = 7861 ∨
    r = 7865 ∨ (7873 ≤ r ∧ r ≤ 7875)

/-- The step bound of `frImg`. -/
def fiCost (b mE : ℕ) : ℕ := 30 * (b * b) + 100 * b + 100 * mE + 300

/-- The scratch memory of `frImg`. -/
def fiRoom (b mE : ℕ) : ℕ := 2 * mE + 4 * b + 2

/-- The stored offset value of an integer below the bound gives the residue. -/
lemma res_of_in {w K L Mo : ℕ} {z : ℤ} (hMo : 0 < Mo) (hz : (w : ℤ) = z + K) :
    (w + (Mo - K % Mo)) % Mo = (z % (Mo : ℤ)).toNat := res_off hMo z hz

/-- A stored offset value is at most `K + L`. -/
lemma off_le {w K L : ℕ} {z : ℤ} (hz : (w : ℤ) = z + K) (hb : |z| ≤ L) : w ≤ K + L := by
  have := (abs_le.1 hb).2; omega

/-- `decide` on literal goals, `omega` otherwise. -/
local macro "lom" : tactic => `(tactic| first | decide | omega)

/-- The sorted index of the `e`-th arc. -/
noncomputable def fiSI (ET : ℕ → ℕ) (b mE e : ℕ) : ℕ := ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1

set_option maxHeartbeats 1000000 in
/-- **The run of `frImg`, with the image described cell by cell** (no `frPrm` yet). -/
theorem frImg_run {P : Input} {W : ℕ} (c : Config) (hc : WordsBounded W c)
    {b r mE K L DMb PRb ETb EHb ELb A S : ℕ} {ET : ℕ → ℕ}
    (r00 : c.nreg 8100 = b) (r01 : c.nreg 8101 = DMb) (r02 : c.nreg 8102 = PRb)
    (r03 : c.nreg 8103 = r) (r04 : c.nreg 8104 = mE) (r05 : c.nreg 8105 = ETb)
    (r06 : c.nreg 8106 = EHb) (r07 : c.nreg 8107 = ELb) (r08 : c.nreg 8108 = K)
    (r09 : c.nreg 8109 = L) (r10 : c.nreg 8110 = A) (r11 : c.nreg 8111 = S)
    (het : ∀ a < mE, c.nmem (ETb + a) = ET a) (hlt : ∀ a < mE, ET a < b)
    (hDM : DMb + b * b ≤ A) (hPR : PRb + b ≤ A) (hET : ETb + mE ≤ A) (hEH : EHb + mE ≤ A)
    (hEL : ELb + mE ≤ A)
    (hAS : A + 2 * (b * b + b + b + 1 + mE + mE) ≤ S) (hSW : S + (2 * mE + 4 * b + 2) ≤ W)
    (hfW : fW b (b * b + b + b + 1 + mE + mE + b + b) + 1 ≤ W)
    (hKW : K + L + (2 * (6 * ((b + 2) * L)) + 1) ≤ W)
    (hPRv : ∀ x < b, c.nmem (PRb + x) ≤ K + L)
    (hELv : ∀ a < mE, c.nmem (ELb + a) ≤ K + L) :
    ∃ c' t, Exec P W frImg c c' t ∧ t ≤ fiCost b mE ∧
      (∀ a < b * b + b, c'.nmem (A + a) = 0) ∧
      (∀ x < b, c'.nmem (A + (b * b + b) + x) = (pre (fiL ET mE) x).length) ∧
      c'.nmem (A + (b * b + b) + b) = mE ∧
      (∀ e < mE, c'.nmem (A + (b * b + b) + b + 1 + e) = c.nmem (EHb + fiSI ET b mE e)) ∧
      (∀ a, b * b + b + b + 1 + mE ≤ a → a < b * b + b + b + 1 + mE + mE →
        c'.nmem (A + a) = 0) ∧
      (∀ i < b * b, c'.nmem (A + (b * b + b + b + 1 + mE + mE) + i) = c.nmem (DMb + i)) ∧
      (∀ x < b, c'.nmem (A + (b * b + b + b + 1 + mE + mE) + b * b + x) =
        (c.nmem (PRb + x) + (2 * (6 * ((b + 2) * L)) + 1 -
          K % (2 * (6 * ((b + 2) * L)) + 1))) % (2 * (6 * ((b + 2) * L)) + 1)) ∧
      (∀ a, b * b + b ≤ a → a < b * b + b + b + 1 + mE →
        c'.nmem (A + (b * b + b + b + 1 + mE + mE) + a) = 0) ∧
      (∀ e < mE, c'.nmem (A + (b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE) + e) =
        (c.nmem (ELb + fiSI ET b mE e) + (2 * (6 * ((b + 2) * L)) + 1 -
          K % (2 * (6 * ((b + 2) * L)) + 1))) % (2 * (6 * ((b + 2) * L)) + 1)) ∧
      c'.nreg 7600 = b ∧ c'.nreg 7601 = b ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = b * b ∧
      c'.nreg 7604 = b * b + b ∧ c'.nreg 7605 = b * b + b + b + 1 + mE ∧ c'.nreg 7606 = r ∧
      c'.nreg 7607 = b * b + b + b + 1 + mE + mE ∧
      c'.nreg 7608 = b * b + b + b + 1 + mE + mE + b ∧
      c'.nreg 7609 = b * b + b + b + 1 + mE + mE + b + b ∧
      c'.nreg 7610 = 2 * (6 * ((b + 2) * L)) + 1 ∧ c'.nreg 7611 = 6 * ((b + 2) * L) ∧
      c'.nreg 7612 = fW b (b * b + b + b + 1 + mE + mE + b + b) + 1 ∧ c'.nreg 7613 = A ∧
      (∀ a, (a < A ∨ A + 2 * (b * b + b + b + 1 + mE + mE) ≤ a) →
        (a < S ∨ S + (2 * mE + 4 * b + 2) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r', ¬ fiScr r' → c'.nreg r' = c.nreg r') ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hwb : b * b + b + b + 1 + mE + mE + b + b + 1 ≤ W := by
    have : b * b + b + b + 1 + mE + mE + b + b ≤ fW b (b * b + b + b + 1 + mE + mE + b + b) := by
      unfold fW; omega
    omega
  have hMoW : 2 * (6 * ((b + 2) * L)) + 1 ≤ W := by omega
  have hAsW : A + (b * b + b + b + 1 + mE + mE) ≤ W := by omega
  have fN1 : A + ((b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE + mE)) ≤ S := by omega
  have fN2 : S + mE + mE + 4 * b + 2 ≤ W := by omega
  have fR1 : b * b + b ≤ b * b + b + b + 1 + mE := by omega
  have fR2 : DMb + b * b ≤ A + (b * b + b + b + 1 + mE + mE) := by omega
  have fR3 : PRb + b ≤ A + (b * b + b + b + 1 + mE + mE) := by omega
  have fR4 : ELb + mE ≤ A + (b * b + b + b + 1 + mE + mE) := by omega
  have fR5 : A + (b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE) + mE ≤
      S + mE + b + 1 + b + b + b := by omega
  have fR6 : S + mE + b + 1 + b + b + b + mE ≤ W := by omega
  have fR7 : A + (b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE) + mE ≤ W := by omega
  have fR8 : b * b + b + mE + 1 ≤ W := by omega
  -- the parameters
  obtain ⟨c₁, t₁, e₁, ht₁, a12, a13, a14, a15, a16, a24, a25, a26, s00, s01, s02, s03, s04, s05,
      s06, s07, s08, s09, s10, s11, s12, s13, ak, am, ar, arm, ao⟩ :=
    fiPre_exec (P := P) c hc r00 r03 r04 r08 r09 r10 hfW hMoW hAsW
  have hKp : 2 * (6 * ((b + 2) * L)) + 1 - K % (2 * (6 * ((b + 2) * L)) + 1) ≤
      2 * (6 * ((b + 2) * L)) + 1 := Nat.sub_le _ _
  generalize 2 * (6 * ((b + 2) * L)) + 1 - K % (2 * (6 * ((b + 2) * L)) + 1) = Kp at a25 hKp ⊢
  have q1 : ∀ r', 8100 ≤ r' → r' ≤ 8111 → c₁.nreg r' = c.nreg r' := fun r' h1 h2 =>
    ak r' (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
  -- the natural part
  obtain ⟨c₂, t₂, e₂, ht₂, nz1, nOB, nmE, nD, nz2, nzr, nSI, n42, nk, nn, nr, nrm, no⟩ :=
    fiNat_exec (P := P) (ET := ET) c₁ e₁.wb_right (by rw [q1 _ (by decide) (by decide), r00])
      (by rw [q1 _ (by decide) (by decide), r04]) (by rw [q1 _ (by decide) (by decide), r05])
      (by rw [q1 _ (by decide) (by decide), r06]) (by rw [q1 _ (by decide) (by decide), r10])
      (by rw [q1 _ (by decide) (by decide), r11]) a12 a14 a16
      (fun a ha => by rw [am]; exact het a ha) hlt hET hEH fN1 fN2
  have q2 : ∀ r', (8100 ≤ r' ∧ r' ≤ 8139) ∨ (7600 ≤ r' ∧ r' ≤ 7613) →
      c₂.nreg r' = c₁.nreg r' := fun r' h =>
    nn r' (by clear * - h; omega) (by clear * - h; omega) (by clear * - h; omega)
      (by clear * - h; omega) (by clear * - h; omega) (by clear * - h; omega)
      (by clear * - h; omega)
  have hLm := length_pre_fiL_b hlt
  have hSIlt : ∀ e < mE, ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1 < mE := fun e he =>
    fiL_idx_lt (by rw [hLm]; exact he)
  -- the residues
  obtain ⟨c₃, t₃, e₃, ht₃, xM, xP, xL, xk, xn, xr, xrm, xo⟩ :=
    fiRes_exec (P := P) (lb := b * b + b + b + 1 + mE) (SIb := S + mE + b + 1 + b + b + b)
      c₂ e₂.wb_right
      (by rw [q2 _ (by decide), q1 _ (by decide) (by decide), r00])
      (by rw [q2 _ (by decide), q1 _ (by decide) (by decide), r01])
      (by rw [q2 _ (by decide), q1 _ (by decide) (by decide), r02])
      (by rw [q2 _ (by decide), q1 _ (by decide) (by decide), r04])
      (by rw [q2 _ (by decide), q1 _ (by decide) (by decide), r07])
      (by rw [q2 _ (by decide), a12]) (by rw [q2 _ (by decide), a13])
      (by rw [q2 _ (by decide), a15]) (by rw [q2 _ (by decide), a24])
      (by rw [q2 _ (by decide), a25]) (by rw [q2 _ (by decide), a26]) n42
      fR1 fR2 fR3 fR4 fR5 fR6
      (fun e he => by rw [nSI e he]; exact hSIlt e he)
      (fun x hx => by
        rw [nk (PRb + x) (Or.inl (by clear * - hx fR3 hPR; omega))
          (Or.inl (by clear * - hx hPR hAS; omega)), am]
        exact (Nat.add_le_add (hPRv x hx) hKp).trans hKW)
      (fun e he => by
        have hi := hSIlt e he
        rw [nSI e he, nk (ELb + ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1)
          (Or.inl (by clear * - hi hEL; omega)) (Or.inl (by clear * - hi hEL hAS; omega)), am]
        exact (Nat.add_le_add (hELv _ hi) hKp).trans hKW)
      fR7 fR8
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), ?_, fun a ha => ?_, fun x hx => ?_, ?_, fun e he => ?_,
    fun a h1 h2 => ?_, fun i hi => ?_, fun x hx => ?_, fun a h1 h2 => ?_, fun e he => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r' hr' => ?_,
    by rw [xr, nr, ar], by rw [xrm, nrm, arm], by rw [xo, no, ao]⟩
  · unfold fiCost
    clear * - ht₁ ht₂ ht₃
    nlinarith
  · rw [xk (A + a) (Or.inl (by clear * - ha; omega)), nz1 a ha]
  · rw [xk (A + (b * b + b) + x) (Or.inl (by clear * - hx; omega)), nOB x hx]
  · rw [xk (A + (b * b + b) + b) (Or.inl (by omega)), nmE]
  · have hi := hSIlt e he
    rw [xk (A + (b * b + b) + b + 1 + e) (Or.inl (by clear * - he; omega)), nD e he, am]
    rfl
  · rw [xk (A + a) (Or.inl (by clear * - h2; omega)), nz2 a h1 h2]
  · rw [xM i hi, nk (DMb + i) (Or.inl (by clear * - hi hDM; omega))
      (Or.inl (by clear * - hi hDM hAS; omega)), am]
  · rw [xP x hx, nk (PRb + x) (Or.inl (by clear * - hx hPR; omega))
      (Or.inl (by clear * - hx hPR hAS; omega)), am]
  · rw [xk _ (Or.inr (Or.inl ⟨by clear * - h1; omega, by clear * - h2; omega⟩)),
      nzr _ (by clear * - h2; omega)]
  · have hi := hSIlt e he
    rw [xL e he, nSI e he, nk (ELb + ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1)
      (Or.inl (by clear * - hi hEL; omega)) (Or.inl (by clear * - hi hEL hAS; omega)), am]
    rfl
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s00]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s01]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s02]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s03]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s04]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s05]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s06]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s07]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s08]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s09]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s10]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s11]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s12]
  · rw [xn _ (by decide) (by decide), q2 _ (by decide), s13]
  · rw [xk a (by clear * - h1; omega), nk a (by clear * - h1; omega)
      (by clear * - h2; omega), am]
  · unfold fiScr at hr'
    rw [xn r' (by clear * - hr'; omega) (by clear * - hr'; omega),
      nn r' (by clear * - hr'; omega) (by clear * - hr'; omega) (by clear * - hr'; omega)
        (by clear * - hr'; omega) (by clear * - hr'; omega) (by clear * - hr'; omega)
        (by clear * - hr'; omega),
      ak r' (by clear * - hr'; omega) (by clear * - hr'; omega) (by clear * - hr'; omega)]

/-- The cells of the natural image from the run's description. -/
theorem fiNM_cells {b mE A EHb : ℕ} {ET EH : ℕ → ℕ} {Dm : ℕ → ℕ → ℕ} {pm : ℕ → ℤ} {r : ℕ}
    {Lz : ℕ → ℤ} (hlt : ∀ a < mE, ET a < b) (mem cm : ℕ → ℕ)
    (heh : ∀ a < mE, cm (EHb + a) = EH a)
    (R1 : ∀ a < b * b + b, mem (A + a) = 0)
    (R2 : ∀ x < b, mem (A + (b * b + b) + x) = (pre (fiL ET mE) x).length)
    (R3 : mem (A + (b * b + b) + b) = mE)
    (R4 : ∀ e < mE, mem (A + (b * b + b) + b + 1 + e) = cm (EHb + fiSI ET b mE e))
    (R5 : ∀ a, b * b + b + b + 1 + mE ≤ a → a < b * b + b + b + 1 + mE + mE → mem (A + a) = 0)
    {a : ℕ} (ha : a < b * b + b + b + 1 + mE + mE) :
    mem (A + a) = FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) a := by
  have hLm := length_pre_fiL_b hlt
  rcases Nat.lt_or_ge a (b * b + b) with h1 | h1
  · rw [R1 a h1, frNM_lo hlt h1]
  obtain ⟨x, rfl⟩ : ∃ x, a = b * b + b + x := ⟨a - (b * b + b), by omega⟩
  rcases Nat.lt_or_ge x (b + 1) with h2 | h2
  · rw [frNM_off hlt (by omega)]
    rcases Nat.lt_or_ge x b with h3 | h3
    · rw [← Nat.add_assoc, R2 x h3]
    · obtain rfl : x = b := by omega
      rw [← Nat.add_assoc, R3, hLm]
  obtain ⟨e, rfl⟩ : ∃ e, x = b + 1 + e := ⟨x - (b + 1), by omega⟩
  rcases Nat.lt_or_ge e mE with h3 | h3
  · have hi : fiSI ET b mE e < mE := fiL_idx_lt (by rw [hLm]; exact h3)
    rw [show b * b + b + (b + 1 + e) = b * b + b + b + 1 + e by ring, frNM_dst hlt h3,
      show A + (b * b + b + b + 1 + e) = A + (b * b + b) + b + 1 + e by ring, R4 e h3,
      heh _ hi]
    rfl
  · rw [R5 _ (by omega) (by omega), frNM_hi hlt (by omega)]

/-- The cells of the residues from the run's description. -/
theorem fiRS_cells {b mE A K L DMb PRb ELb : ℕ} {ET EH : ℕ → ℕ} {Dm : ℕ → ℕ → ℕ}
    {pm : ℕ → ℤ} {r : ℕ} {Lz : ℕ → ℤ} (hB : FrImgB b Dm pm r mE ET EH Lz L) (mem cm : ℕ → ℕ)
    (hdm : ∀ i < b, ∀ j < b, cm (DMb + i * b + j) = Dm i j)
    (hpr : ∀ x < b, (cm (PRb + x) : ℤ) = pm x + K)
    (hel : ∀ a < mE, (cm (ELb + a) : ℤ) = Lz a + K)
    (R6 : ∀ i < b * b, mem (A + (b * b + b + b + 1 + mE + mE) + i) = cm (DMb + i))
    (R7 : ∀ x < b, mem (A + (b * b + b + b + 1 + mE + mE) + b * b + x) =
      (cm (PRb + x) + (2 * (6 * ((b + 2) * L)) + 1 -
        K % (2 * (6 * ((b + 2) * L)) + 1))) % (2 * (6 * ((b + 2) * L)) + 1))
    (R8 : ∀ a, b * b + b ≤ a → a < b * b + b + b + 1 + mE →
      mem (A + (b * b + b + b + 1 + mE + mE) + a) = 0)
    (R9 : ∀ e < mE, mem (A + (b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE) + e) =
      (cm (ELb + fiSI ET b mE e) + (2 * (6 * ((b + 2) * L)) + 1 -
        K % (2 * (6 * ((b + 2) * L)) + 1))) % (2 * (6 * ((b + 2) * L)) + 1))
    {a : ℕ} (ha : a < b * b + b + b + 1 + mE + mE) :
    mem (A + (b * b + b + b + 1 + mE + mE) + a) =
      FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L a := by
  have hb1 := hB.b_pos
  have hLm := length_pre_fiL_b hB.et
  have hMo0 : 0 < 2 * (6 * ((b + 2) * L)) + 1 := by omega
  rcases Nat.lt_or_ge a (b * b) with h1 | h1
  · rw [R6 a h1, frRS_D hB h1]
    have hi : a / b < b := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h1
    have hj : a % b < b := Nat.mod_lt _ (by omega)
    have := hdm _ hi _ hj
    rwa [Nat.add_assoc, Nat.div_add_mod' a b] at this
  obtain ⟨x, rfl⟩ : ∃ x, a = b * b + x := ⟨a - b * b, by omega⟩
  rcases Nat.lt_or_ge x b with h2 | h2
  · rw [← Nat.add_assoc, R7 x h2, frRS_p hB h2, frM_frPrm]
    exact res_off hMo0 _ (hpr x h2)
  obtain ⟨y, rfl⟩ : ∃ y, x = b + y := ⟨x - b, by omega⟩
  rcases Nat.lt_or_ge y (b + 1 + mE) with h3 | h3
  · rw [R8 _ (by omega) (by omega), frRS_mid hB (by omega) (by omega)]
  obtain ⟨e, rfl⟩ : ∃ e, y = b + 1 + mE + e := ⟨y - (b + 1 + mE), by omega⟩
  have he : e < mE := by omega
  have hi : fiSI ET b mE e < mE := fiL_idx_lt (by rw [hLm]; exact he)
  rw [show A + (b * b + b + b + 1 + mE + mE) + (b * b + (b + (b + 1 + mE + e))) =
      A + (b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE) + e by ring, R9 e he,
    show b * b + (b + (b + 1 + mE + e)) = b * b + b + b + 1 + mE + e by ring,
    frRS_len hB he, frM_frPrm]
  exact res_off hMo0 _ (hel _ hi)

/-- **The FR image program meets its specification** (`FrImgSpec`): within
`30 b² + 100 b + 100 mE + 300` steps, scratch `2 mE + 4 b + 2` cells. -/
theorem frImg_spec : FrImgSpec frImg fiScr fiCost fiRoom := by
  intro b Dm pm r mE ET EH Lz K L DMb PRb ETb EHb ELb A S W I c hB hI hc hDM hPR hET hEH hEL
    hAS hSW hKW hWW
  have hlt := hB.et
  have hsb : (frPrm b Dm pm r ET EH Lz mE).sb = b * b + b + b + 1 + mE + mE := frPrm_sb hlt
  have hWp : (frPrm b Dm pm r ET EH Lz mE).W = fW b (b * b + b + b + 1 + mE + mE + b + b) :=
    frPrm_W hlt
  have hMo : frM (frPrm b Dm pm r ET EH Lz mE) L = 2 * (6 * ((b + 2) * L)) + 1 := frM_frPrm L
  rw [hsb] at hAS ⊢
  rw [hWp] at hWW
  rw [hMo] at hKW
  have hPRv : ∀ x < b, c.nmem (PRb + x) ≤ K + L := fun x hx =>
    off_le (hI.pr x hx) (hB.pm x hx)
  have hELv : ∀ a < mE, c.nmem (ELb + a) ≤ K + L := fun a ha => off_le (hI.el a ha) (hB.lz a ha)
  obtain ⟨c', t, ex, ht, R1, R2, R3, R4, R5, R6, R7, R8, R9, s00, s01, s02, s03, s04, s05, s06,
      s07, s08, s09, s10, s11, s12, s13, hk, hn, hr, hrm, ho⟩ :=
    frImg_run (P := I) (ET := ET) c hc hI.r00 hI.r01 hI.r02 hI.r03 hI.r04 hI.r05 hI.r06 hI.r07
      hI.r08 hI.r09 hI.r10 hI.r11 hI.et hlt hDM hPR hET hEH hEL hAS hSW hWW hKW hPRv hELv
  refine ⟨c', t, ex, ht, fun a ha => ?_, fun a ha => ?_, s00, s01, s02, s03, by rw [s04]; rfl,
    by rw [s05, frPrm_lb hlt], s06, by rw [s07], by rw [s08, frPrm_db hlt],
    by rw [s09, frPrm_wb hlt], by rw [s10, hMo], s11, by rw [s12, hWp], s13, hk, hn, hr, hrm,
    ho⟩
  · exact fiNM_cells hlt c'.nmem c.nmem hI.eh R1 R2 R3 R4 R5 ha
  · exact fiRS_cells hB c'.nmem c.nmem hI.dm hI.pr hI.el R6 R7 R8 R9 ha

end MsCall

end BKMNW

end PlanarFlow
