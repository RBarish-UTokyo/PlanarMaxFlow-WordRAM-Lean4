module

public import PlanarFlow.BKMNW.MsStD

/-!
# The MSSP encoder, stages D2 and E: the real words of the start, the image, the registers

* **`msD2 = twS ; twW ; wrLoop vTW ; trSt`**: the residues of Klein's real start in the low
  memory at `β = B + 16 (n + 1) + 1`: `WT[j] = [IS[j] = 1 ∧ D1[NT[j]] < H] ? LN[j] : L` at
  `β + j`, `PH[j] = IS[j] · LN[j]` at `β + nD + j`, `L, Th, H0` at `β + 3 nD`, `+ 1`, `+ 2`
  (**`msD2_exec`**);
* **`msE = cpS ; cpArr ; mbZeroRegs (range 1000) ; kpS ; kPrm ; fnA ; fnB`**: the image
  `[IM, IM + len)` copied to `β' = kleinWN B n Hc + 1`, the registers `< 1000` zeroed, the
  parameters `knVM` of `kNFM` at `1000 … 1047`, the registers `8010 … 8019`, `8033`, `8034` of
  the call (**`msE_exec`**).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

/-- The base `β` of the residues of the real words. -/
abbrev dBeta (w nD k t : ℕ) : ℕ := dB w nD k t + 16 * (4 * nD + 1 + 1) + 1

/-- The three trip words. -/
def trSt : Stmt := block [.storeN 8260 8234, .constN 7360 1, .addN 7361 8260 7360,
  .storeN 7361 8235, .addN 7361 7361 7360, .storeN 7361 8240]

theorem trSt_exec (c : Config) (hc : WordsBounded W c) {a L Th H0 : ℕ} (r60 : c.nreg 8260 = a)
    (r34 : c.nreg 8234 = L) (r35 : c.nreg 8235 = Th) (r40 : c.nreg 8240 = H0)
    (hw : a + 2 ≤ W) :
    ∃ c' u, Exec P W trSt c c' u ∧ u = 6 ∧ c'.nmem a = L ∧ c'.nmem (a + 1) = Th ∧
      c'.nmem (a + 2) = H0 ∧ (∀ b, b ≠ a → b ≠ a + 1 → b ≠ a + 2 → c'.nmem b = c.nmem b) ∧
      (∀ r, r ≠ 7360 → r ≠ 7361 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold trSt
  exec_block
  all_goals try ((try config_simp); (try simp only [r60, r34, r35, r40]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun b h1 h2 h3 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r60, r34, r35, r40])
  all_goals (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- **Stage D2.** -/
def msD2 : Stmt := .seq twS (.seq twW (.seq (wrLoop vTW) trSt))

set_option maxHeartbeats 4000000 in
/-- **Stage D2: the real words of the start in the low memory.** -/
theorem msD2_exec (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ} (hD : DReg c w cV cF k t nD IM A1 H N1 SL TI Lg)
    (his : ∀ j < nD, c.nmem (IM + 6 * nD + j) ≤ 1)
    (hnt : ∀ j < nD, c.nmem (IM + 4 * nD + j) < 4 * nD + 1)
    (l1 : dBeta w nD k t + 3 * nD + 3 ≤ IM) (l2 : IM + 8 * nD ≤ A1)
    (hW : A1 + 40 * nD + 10 + 3 * IM + H + MsEnc.msL w cV + 40 ≤ W) :
    ∃ e u, Exec P W msD2 c e u ∧ u ≤ hpCost twSL + hpCost twWL + (19 + 8) * nD + 5 + 6 ∧
      DReg e w cV cF k t nD IM A1 H N1 SL TI Lg ∧
      (∀ j < nD, e.nmem (dBeta w nD k t + j) =
          (if c.nmem (IM + 6 * nD + j) = 1 ∧
              c.nmem (A1 + 21 * nD + 6 + c.nmem (IM + 4 * nD + j)) < H then
            c.nmem (IM + 7 * nD + j) else MsEnc.msL w cV) ∧
        e.nmem (dBeta w nD k t + nD + j) =
          if c.nmem (IM + 6 * nD + j) = 1 then c.nmem (IM + 7 * nD + j) else 0) ∧
      e.nmem (dBeta w nD k t + 3 * nD) = MsEnc.msL w cV ∧
      e.nmem (dBeta w nD k t + 3 * nD + 1) = MsEnc.msTh w cV ∧
      e.nmem (dBeta w nD k t + 3 * nD + 2) = MsEnc.msH0 w cV k ∧
      (∀ a, (a < dBeta w nD k t ∨ dBeta w nD k t + 2 * nD ≤ a) →
        (a < dBeta w nD k t + 3 * nD ∨ dBeta w nD k t + 3 * nD + 3 ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7360 → r ≠ 7361 → r ≠ 7370 → r ≠ 7371 → (r < 8200 ∨ 8220 ≤ r) →
        (r < 8273 ∨ 8279 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hβ : dBeta w nD k t = dB w nD k t + 16 * (4 * nD + 1 + 1) + 1 := rfl
  obtain ⟨c₁, x₁, a73, a74, a75, a76, a77, a78, aR, am, ar, arm, ao⟩ :=
    twS_exec (P := P) c hc hD.a.d28 hD.a.d34 hD.d54 hD.d55 hD.d56 hD.d57 (by omega)
  have hD1 := hD.congr (e' := c₁) (fun r h1 h2 => aR r (by omega) (by omega) (by omega))
  obtain ⟨c₂, x₂, b00, b01, b02, bR, bm, br, brm, bo⟩ :=
    twW_exec (P := P) c₁ x₁.wb_right hD1.a.d25 hD1.d49 (by omega)
  have m2 : c₂.nmem = c.nmem := by rw [bm, am]
  have q2 : ∀ r, 8273 ≤ r → r < 8279 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    bR r (by omega) (by omega) (by omega)
  obtain ⟨c₃, t₃, x₃, ht₃, w5, wm5, -, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₂
    x₂.wb_right (VAL := vTW) (B := 19) (m := nD) (RVo := dBeta w nD k t)
    (RTo := dBeta w nD k t + nD) (N := nD) b00 b01 b02
    (vTW_spec (P := P) c₂ (nD := nD) (ISb := IM + 6 * nD) (LNb := IM + 7 * nD)
      (NTb := IM + 4 * nD) (D1b := A1 + 21 * nD + 6) (H := H) (L := MsEnc.msL w cV)
      (by rw [q2 8273 (by omega) (by omega)]; exact a73)
      (by rw [q2 8274 (by omega) (by omega)]; exact a74)
      (by rw [q2 8275 (by omega) (by omega)]; exact a75)
      (by rw [q2 8276 (by omega) (by omega)]; exact a76)
      (by rw [q2 8277 (by omega) (by omega)]; exact a77)
      (by rw [q2 8278 (by omega) (by omega)]; exact a78)
      (fun j hj => by
        have := hnt j hj
        rw [m2]
        exact ⟨⟨Or.inr (by omega), Or.inr (by omega)⟩, ⟨Or.inr (by omega), Or.inr (by omega)⟩,
          ⟨Or.inr (by omega), Or.inr (by omega)⟩, ⟨Or.inr (by omega), Or.inr (by omega)⟩⟩)
      (fun j hj => by rw [m2]; exact his j hj)
      (fun j hj => by
        have := hnt j hj
        rw [m2]
        exact ⟨by omega, by omega, by omega, by omega, hc.2 _⟩) (by omega) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl le_rfl) (by omega) (by omega)
    (by omega)
  have hD3 := hD1.congr (e' := c₃) (fun r h1 h2 => by
    rw [wR5 r (by omega), bR r (by omega) (by omega) (by omega)])
  obtain ⟨c₄, t₄, x₄, ht₄, s0, s1, s2, sm, sR, sr, srm, so⟩ :=
    trSt_exec (P := P) c₃ x₃.wb_right hD3.d60 hD3.a.d34 hD3.a.d35 hD3.a.d40 (by omega)
  refine ⟨c₄, _, .seq x₁ (.seq x₂ (.seq x₃ x₄)), by omega,
    hD3.congr (fun r h1 h2 => sR r (by omega) (by omega)), fun j hj => ?_,
    by rw [hβ]; exact s0, by rw [hβ]; exact s1, by rw [hβ]; exact s2, fun a h1 h2 => ?_,
    fun r h1 h2 h3 h4 h5 h6 => ?_, by rw [sr, wr5, br, ar], by rw [srm, wrm5, brm, arm],
    by rw [so, wo5, bo, ao]⟩
  · obtain ⟨g1, g2⟩ := w5 j hj rfl
    rw [m2] at g1 g2
    rw [sm _ (by omega) (by omega) (by omega), sm _ (by omega) (by omega) (by omega)]
    exact ⟨g1, g2⟩
  · rw [sm a (by omega) (by omega) (by omega), wm5 a (by omega) (by omega), m2]
  · rw [sR r h1 h2, wR5 r (by omega), bR r (by omega) h3 h4, aR r (by omega) h3 h4]

/-- The base `β' = kleinWN B n Hc + 1` of Klein's input words. -/
abbrev dBeta' (w cV cF k t nD : ℕ) : ℕ :=
  Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) + 1

/-- **Stage E.** -/
def msE : Stmt := .seq cpS (.seq cpArr (.seq (mbZeroRegs (List.range 1000))
  (.seq kpS (.seq kPrm (.seq fnA fnB)))))

/-- The step bound of stage E. -/
def costE (len : ℕ) : ℕ := hpCost cpSL + (7 * len + 4) + 1000 + hpCost kpSL + hpCost kPrmL +
  hpCost fnAL + hpCost fnBL

set_option maxHeartbeats 4000000 in
/-- **Stage E: the image, the zero registers, `knVM`, the registers of the call.** -/
theorem msE_exec (c : Config) (hc : WordsBounded W c)
    {w cV cF k t nD IM A1 H N1 SL TI Lg : ℕ} (hD : DReg c w cV cF k t nD IM A1 H N1 SL TI Lg)
    (l1 : dBeta' w cV cF k t nD + dLen nD k t ≤ IM)
    (hW : 4 * dBeta' w cV cF k t nD + 4 * IM + N1 + SL + TI + Lg + 200 * nD + 4 * k + 8 * t +
      200 ≤ W) :
    ∃ e u, Exec P W msE c e u ∧ u ≤ costE (dLen nD k t) ∧
      (∀ i < dLen nD k t, e.nmem (dBeta' w cV cF k t nD + i) = c.nmem (IM + i)) ∧
      (∀ a, (a < dBeta' w cV cF k t nD ∨ dBeta' w cV cF k t nD + dLen nD k t ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r < 1000, e.nreg r = 0) ∧
      (∀ j < 48, e.nreg (1000 + j) = KleinFix.knVM (dB w nD k t) nD (4 * nD + 1) k t
        (MsEnc.msHI w cV cF k) (dBeta' w cV cF k t nD) (dLen nD k t) j) ∧
      e.nreg 8010 = t ∧ e.nreg 8011 = 4 * nD + 1 + k ∧ e.nreg 8012 = dBeta w nD k t + 3 * nD + 3 ∧
      e.nreg 8013 = N1 ∧ e.nreg 8014 = SL ∧ e.nreg 8015 = TI ∧ e.nreg 8016 = 4 * nD + 1 + k ∧
      e.nreg 8017 = dBeta' w cV cF k t nD ∧ e.nreg 8018 = dLen nD k t ∧ e.nreg 8019 = Lg ∧
      e.nreg 8033 = dBeta w nD k t ∧ e.nreg 8034 = 3 * nD + 3 ∧
      (∀ r, 1048 ≤ r → (r < 4910 ∨ 4916 < r) → (r < 7300 ∨ 7311 < r) → r ≠ 7370 → r ≠ 7371 →
        (r < 8010 ∨ 8019 < r) → r ≠ 8033 → r ≠ 8034 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hMo := Nat.le_mul_self (2 * MsEnc.msHI w cV cF k + 1)
  have eKW : Klein.kleinWN (dB w nD k t) (4 * nD + 1) (MsEnc.msHI w cV cF k) =
      2 * (dB w nD k t + 16 * (4 * nD + 1 + 1)) + 1 +
      (2 * MsEnc.msHI w cV cF k + 1) * (2 * MsEnc.msHI w cV cF k + 1) +
      (2 * MsEnc.msHI w cV cF k + 1) := rfl
  have eB : dB w nD k t = w + 40 * nD + 2 * k + 2 * t + t * t + 20 := rfl
  have eL : dLen nD k t = 37 * nD + k + 2 * t + 11 := rfl
  have hβ' : dBeta' w cV cF k t nD = Klein.kleinWN (dB w nD k t) (4 * nD + 1)
    (MsEnc.msHI w cV cF k) + 1 := rfl
  obtain ⟨c₁, x₁, a10, a11, a12, aR, am, ar, arm, ao⟩ :=
    cpS_exec (P := P) c hc hD.a.d26 hD.d51 hD.d59 (by omega)
  obtain ⟨c₂, t₂, x₂, ht₂, g1, g2, gR, gr, grm, go⟩ :=
    cpArr_exec (P := P) c₁ x₁.wb_right a10 a11 a12 ⟨Or.inr (by omega), by omega, by omega,
      by omega⟩
  obtain ⟨c₃, x₃, z1, z2, zm, zr, zrm, zo⟩ :=
    mbZeroRegs_exec' (P := P) (List.range 1000) c₂ x₂.wb_right
  have q3 : ∀ r, 8220 ≤ r → r < 8262 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [z2 r (by simp; omega), gR r (by omega), aR r (by omega) (by omega) (by omega)]
  have hD3 := hD.congr q3
  obtain ⟨c₄, x₄, k0, k1, k2, k3, k4, k5, k6, k7, kR, km, kr, krm, ko⟩ :=
    kpS_exec (P := P) c₃ x₃.wb_right hD3.a.d23 hD3.a.d24 hD3.a.d25 hD3.d45 hD3.d47 hD3.d50
      hD3.d51 hD3.d59 (by omega)
  obtain ⟨c₅, x₅, v5, vR, vm, vr, vrm, vo⟩ :=
    MsEnc.kPrm_exec (I := P) c₄ x₄.wb_right ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ (by omega)
  have hD5 := hD3.congr (fun r h1 h2 => by
    rw [vR r (by omega) (by omega) (by omega), kR r (by omega) (by omega) (by omega)])
  obtain ⟨c₆, x₆, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, fR, fm, fr, frm, fo⟩ :=
    fnA_exec (P := P) c₅ x₅.wb_right hD5.a.d24 hD5.a.d29 hD5.a.d30 hD5.a.d31 hD5.a.d32 hD5.d51
      hD5.d53 hD5.d59 hD5.d61 (by omega)
  have hD6 := hD5.congr (fun r h1 h2 => fR r (by omega) (by omega) (by omega))
  obtain ⟨c₇, x₇, h33, h34, hR, hm, hr, hrm, ho⟩ :=
    fnB_exec (P := P) c₆ x₆.wb_right hD6.d49 hD6.d52 (by omega)
  have m7 : c₇.nmem = c₂.nmem := by rw [hm, fm, vm, km, zm]
  refine ⟨c₇, _, .seq x₁ (.seq x₂ (.seq x₃ (.seq x₄ (.seq x₅ (.seq x₆ x₇))))), ?_,
    fun i hi => ?_, fun a ha => ?_, fun r hr => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h33, h34, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_,
    by rw [hr, fr, vr, kr, zr, gr, ar], by rw [hrm, frm, vrm, krm, zrm, grm, arm],
    by rw [ho, fo, vo, ko, zo, go, ao]⟩
  · unfold costE; simp only [List.length_range] at *; omega
  · rw [m7, g1 i hi, am]
  · rw [m7, g2 a ha, am]
  · rw [hR r (by omega) (by omega) (by omega), fR r (by omega) (by omega) (by omega),
      vR r (by omega) (by omega) (by omega), kR r (by omega) (by omega) (by omega)]
    exact z1 r (by simp; omega)
  · rw [hR _ (by omega) (by omega) (by omega), fR _ (by omega) (by omega) (by omega)]; exact v5 j hj
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f10
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f11
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f12
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f13
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f14
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f15
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f16
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f17
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f18
  · rw [hR _ (by omega) (by omega) (by omega)]; exact f19
  · rw [hR r (by omega) h4 h5, fR r (by omega) h4 h5,
      vR r (by omega) (by omega) (by omega), kR r (by omega) h4 h5, z2 r (by simp; omega),
      gR r (by omega), aR r (by omega) h4 h5]

end MsEnc

end BKMNW

end PlanarFlow
