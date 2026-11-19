module

public import PlanarFlow.NegSSSP.NdFullC1

/-!
# The full branch: the split's area cleared, the node's primary values, the residues

**`fbC2`** `= wsClr ; cpRegs fbPI ; fbPn ; pcProg 2296 fbRL ; (cpRegs ; ldProg) ×3`: the
split's work area `[0, Frame.spWs k]` zeroed (the node asks zeros below `Z`); the sizes in the
renamed `PnIn` registers `1080 … 1093`; the node's parameter program (`W' = r1022`,
`M = r1023`, `H = r1024`); the residues modulo `M` of the lengths and of the two extended
potentials at `W' + 1 + (Z + j M₀ + ·)`, `j = 3, 4, 5`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The sizes into the renamed `PnIn` registers. -/
def fbPI : List (ℕ × ℕ) :=
  [(1080, 2240), (1081, 2243), (1082, 2241), (1083, 2300), (1084, 2244), (1085, 2247),
    (1086, 2245), (1087, 2301), (1088, 2474), (1089, 2464), (1090, 2496), (1091, 2205),
    (1092, 2315), (1093, 2316)]

/-- The bases of the residues (scratch `2296`, `2297`). -/
def fbRL : List PcStep :=
  [(2330, [(1, .v 1022), (1, .v 2313), (3, .v 2314), (1, .one)], 0),
    (2331, [(1, .v 1022), (1, .v 2313), (4, .v 2314), (1, .one)], 0),
    (2332, [(1, .v 1022), (1, .v 2313), (5, .v 2314), (1, .one)], 0),
    (2333, [(1, .v 3004), (5, .v 2475), (4, .one)], 0),
    (2334, [(1, .v 3003), (4, .v 2475)], 0), (2335, [(1, .v 3003), (6, .v 2475)], 0)]

set_option maxRecDepth 100000 in
theorem fbRL_wf : pcWF 2296 9600 fbRL = true := by kernel_rfl

theorem fbRL_cost : pcCost fbRL = 94 := by kernel_rfl

theorem fbRL_eqs {g : ℕ → ℕ} (h : PcSol fbRL g) :
    g 2330 = g 1022 + 1 + (g 2313 + 3 * g 2314) ∧ g 2331 = g 1022 + 1 + (g 2313 + 4 * g 2314) ∧
    g 2332 = g 1022 + 1 + (g 2313 + 5 * g 2314) ∧ g 2333 = g 3004 + 4 + 5 * g 2475 ∧
    g 2334 = g 3003 + 4 * g 2475 ∧ g 2335 = g 3003 + 6 * g 2475 := by
  simp only [PcSol, fbRL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero, mul_one] at h
  omega

theorem fbRL_notDst {r : ℕ} (h : r < 2330 ∨ 2335 < r) : r ∉ pcDsts fbRL := by
  simp only [pcDsts, fbRL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

/-- The registers of the three residue loads. -/
def fbQ1 : List (ℕ × ℕ) :=
  [(2840, 2474), (2841, 2333), (2842, 2203), (2843, 2330), (2844, 1023), (2845, 2204)]
/-- … -/
def fbQ2 : List (ℕ × ℕ) :=
  [(2840, 2464), (2841, 2334), (2842, 2203), (2843, 2331), (2844, 1023), (2845, 2205)]
/-- … -/
def fbQ3 : List (ℕ × ℕ) :=
  [(2840, 2464), (2841, 2335), (2842, 2203), (2843, 2332), (2844, 1023), (2845, 2205)]

theorem fbQ_ok : cpOK fbPI = true ∧ cpSrc fbPI = true ∧ cpOK fbQ1 = true ∧ cpSrc fbQ1 = true ∧
    cpOK fbQ2 = true ∧ cpSrc fbQ2 = true ∧ cpOK fbQ3 = true ∧ cpSrc fbQ3 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem fbQ_frame {r : ℕ} (h : r < 2840 ∨ 2845 < r) :
    r ∉ fbQ1.map (·.1) ∧ r ∉ fbQ2.map (·.1) ∧ r ∉ fbQ3.map (·.1) := by
  simp only [fbQ1, fbQ2, fbQ3, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

theorem fbPI_frame {r : ℕ} (h : r < 1080 ∨ 1093 < r) : r ∉ fbPI.map (·.1) := by
  simp only [fbPI, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem pwS_congr {m m' : ℕ → ℕ} {a b n : ℕ} (h : ∀ j < n, m' (a + j) = m (a + j) ∧
    m' (b + j) = m (b + j)) : pwS m' a b n = pwS m a b n := by
  unfold pwS
  exact Finset.sum_congr rfl fun j hj => by
    rw [(h j (Finset.mem_range.1 hj)).1, (h j (Finset.mem_range.1 hj)).2]

/-- **The full branch, part C2.** -/
def fbC2 : Stmt :=
  .seq Frame.wsClr <| .seq (cpRegs fbPI) <| .seq fbPn <| .seq (pcProg 2296 fbRL) <|
  .seq (cpRegs fbQ1) <| .seq ldProg <| .seq (cpRegs fbQ2) <| .seq ldProg <|
  .seq (cpRegs fbQ3) ldProg

theorem pnπ_in (j : ℕ) (hj : j < 14) : pnπ (10610 + j) = 1080 + j := by
  have := pnπ_hi (80 + j) (by omega)
  rwa [show 10530 + (80 + j) = 10610 + j by omega, show 1000 + (80 + j) = 1080 + j by omega]
    at this

theorem HnPrim.congr {f g : ℕ → ℕ} {p₀ p₁ : FeP} {Pb₀ Pb₁ W' M Hh N1₀ N1₁ Wc₀ Wc₁ : ℕ}
    (hH : HnPrim f p₀ p₁ Pb₀ Pb₁ W' M Hh N1₀ N1₁ Wc₀ Wc₁)
    (h : ∀ j < 30, g (10530 + j) = f (10530 + j)) :
    HnPrim g p₀ p₁ Pb₀ Pb₁ W' M Hh N1₀ N1₁ Wc₀ Wc₁ :=
  ⟨(h 0 (by decide)).trans hH.a0, (h 1 (by decide)).trans hH.a1, (h 2 (by decide)).trans hH.a2,
    (h 3 (by decide)).trans hH.a3, (h 4 (by decide)).trans hH.a4, (h 5 (by decide)).trans hH.a5,
    (h 10 (by decide)).trans hH.b0, (h 11 (by decide)).trans hH.b1,
    (h 12 (by decide)).trans hH.b2, (h 13 (by decide)).trans hH.b3,
    (h 14 (by decide)).trans hH.b4, (h 15 (by decide)).trans hH.b5,
    (h 20 (by decide)).trans hH.c0, (h 21 (by decide)).trans hH.c1,
    (h 22 (by decide)).trans hH.c2, (h 23 (by decide)).trans hH.c3,
    (h 24 (by decide)).trans hH.c4, (h 25 (by decide)).trans hH.c5,
    (h 26 (by decide)).trans hH.c6, (h 27 (by decide)).trans hH.c7,
    (h 28 (by decide)).trans hH.c8⟩

/-- The cost of `fbC2` (without the clearing and the parameter program). -/
def fbC2Cost (k : ℕ) (p₀ p₁ : FeP) : ℕ :=
  Frame.wsCost k + 14 + pnCost p₀.nD p₁.nD + 94 + 3 * (6 + (11 * (2 * k) + 6))

section C2

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

set_option maxHeartbeats 8000000 in
/-- **The full branch, part C2** (see the module docstring). -/
theorem fbC2_exec {en : ℕ → D} {ι : ℕ → V} {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} {p₀ p₁ : FeP}
    {m k w b L h d Z M₀ Y S : ℕ} (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d) (r74 : c.nreg 2474 = m)
    (r75 : c.nreg 2475 = k) (r64 : c.nreg 2464 = w) (r96 : c.nreg 2496 = b)
    (r2203 : c.nreg 2203 = h + 10 * k) (r2204 : c.nreg 2204 = L) (r2205 : c.nreg 2205 = L + 1)
    (e40 : c.nreg 2240 = p₀.nD) (e41 : c.nreg 2241 = p₀.nV) (e00 : c.nreg 2300 = p₀.nF)
    (e43 : c.nreg 2243 = p₀.k) (f44 : c.nreg 2244 = p₁.nD) (f45 : c.nreg 2245 = p₁.nV)
    (f01 : c.nreg 2301 = p₁.nF) (f47 : c.nreg 2247 = p₁.k)
    (r13 : c.nreg 2313 = Z) (r14 : c.nreg 2314 = M₀) (r15 : c.nreg 2315 = Y)
    (r16 : c.nreg 2316 = S)
    (hm1 : c.nmem (d + 1) = m) (hk2 : c.nmem (d + 2) = k)
    (hid : ∀ i < 2 * k, c.nmem (h + 10 * k + i) = i)
    (hln : ∀ i < m, c.nmem (d + 4 + 5 * k + i) = (ℓ (en i) + L).toNat)
    (hℓ : ∀ i < m, |ℓ (en i)| ≤ L)
    (hG₀ : ∀ v < w, (c.nmem (h + 4 * k + v) : ℤ) = δ₀ (ι v) + (L + 1) ∧ |δ₀ (ι v)| ≤ L + 1)
    (hG₁ : ∀ v < w, (c.nmem (h + 6 * k + v) : ℤ) = δ₁ (ι v) + (L + 1) ∧ |δ₁ (ι v)| ≤ L + 1)
    (hM₀ : M₀ = m + w + 1) (hY : Z + 22 * M₀ ≤ Y) (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END) (hZs : Frame.spWs k < Z)
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (1 + pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD))
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (1 + pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD))
    (hb1 : 1 ≤ b) (hW1 : pnW p₀ p₁ ≤ W) (hW2 : 2 * nodeHN m b w (L + 1) + 1 ≤ W)
    (hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ W) (hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ W)
    (h9600 : 9600 ≤ W) (hWs : Frame.spWs k + 205 ≤ W) (hdW : 2 * pnW p₀ p₁ + 2 ≤ d)
    (hdh : d + 4 + 5 * k + m ≤ h) (hmk : m ≤ k) (hw : w ≤ 2 * k) (hR : h + 160 * k ≤ W)
    (hMW : 2 * nodeHN m b w (L + 1) + 1 + 2 * L + 2 ≤ W) :
    ∃ c' t, Exec P W fbC2 c c' t ∧ t ≤ fbC2Cost k p₀ p₁ ∧
      (∀ a ≤ Frame.spWs k, c'.nmem a = 0) ∧
      HnPrim (fun r => c'.nreg (pnπ r)) p₀ p₁ (Y + 16 * S) (Y + 16 * S + w) (pnW p₀ p₁)
        (2 * nodeHN m b w (L + 1) + 1) (nodeHN m b w (L + 1)) (MSSP.isoN1 p₀.A p₀.N p₀.FN)
        (MSSP.isoN1 p₁.A p₁.N p₁.FN)
        (1 + pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD)
        (1 + pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD) ∧
      (∀ i < m, (c'.nmem (pnW p₀ p₁ + 1 + (Z + 3 * M₀ + i)) : ℤ) =
        ℓ (en i) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (pnW p₀ p₁ + 1 + (Z + 4 * M₀ + v)) : ℤ) =
        δ₀ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (pnW p₀ p₁ + 1 + (Z + 5 * M₀ + v)) : ℤ) =
        δ₁ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ a, Frame.spWs k < a → (a < pnW p₀ p₁ + 1 + (Z + 3 * M₀) ∨
        pnW p₀ p₁ + 1 + (Z + 6 * M₀) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 1000 ∨ (1170 ≤ r ∧ r < 2296) ∨ (2297 < r ∧ r < 2330) ∨
        (2335 < r ∧ r < 2840) ∨ (2850 < r ∧ r < 2966) ∨ 2978 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hE0 := pn_end p₀
  have hE1 := pn_end p₁
  have hEW : p₁.END ≤ pnW p₀ p₁ := by unfold pnW; omega
  have hZW : Z + 6 * M₀ ≤ pnW p₀ p₁ := by clear * - hEW hE0 hE1 hY hI0₀ hI0₁; omega
  obtain ⟨ok0, sr0, ok1, sr1, ok2, sr2, ok3, sr3⟩ := fbQ_ok
  -- the split's area
  obtain ⟨c₁, t₁, e₁, ht₁, z₁, m₁, f₁, rr₁, rm₁, o₁⟩ := Frame.wsClr_exec (I := P) c hc r04 hm1
    hk2 (by clear * - hdh hR; omega) hWs
  have F₁ : ∀ r, (r < 2966 ∨ 2978 < r) → c₁.nreg r = c.nreg r := f₁
  -- the sizes
  obtain ⟨c₂, e₂, g₂, f₂, m₂, rr₂, rm₂, o₂⟩ := cpRegs_exec (P := P) (W := W) _ ok0 sr0 c₁
    e₁.wb_right
  simp only [fbPI, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₂
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13⟩ := g₂
  have hπ : ∀ j < 14, c₂.nreg (pnπ (10610 + j)) = c₂.nreg (1080 + j) := fun j hj => by
    rw [pnπ_in j hj]
  have hin : PnIn (fun r => c₂.nreg (pnπ r)) p₀ p₁ m w b (L + 1) Y S :=
    ⟨by rw [hπ 0 (by decide), u0, F₁ _ (by decide), e40],
      by rw [hπ 1 (by decide), u1, F₁ _ (by decide), e43],
      by rw [hπ 2 (by decide), u2, F₁ _ (by decide), e41],
      by rw [hπ 3 (by decide), u3, F₁ _ (by decide), e00],
      by rw [hπ 4 (by decide), u4, F₁ _ (by decide), f44],
      by rw [hπ 5 (by decide), u5, F₁ _ (by decide), f47],
      by rw [hπ 6 (by decide), u6, F₁ _ (by decide), f45],
      by rw [hπ 7 (by decide), u7, F₁ _ (by decide), f01],
      by rw [hπ 8 (by decide), u8, F₁ _ (by decide), r74],
      by rw [hπ 9 (by decide), u9, F₁ _ (by decide), r64],
      by rw [hπ 10 (by decide), u10, F₁ _ (by decide), r96],
      by rw [hπ 11 (by decide), u11, F₁ _ (by decide), r2205],
      by rw [hπ 12 (by decide), u12, F₁ _ (by decide), r15],
      by rw [hπ 13 (by decide), u13, F₁ _ (by decide), r16]⟩
  have M₂ : ∀ a, Frame.spWs k < a → c₂.nmem a = c.nmem a := fun a ha => by rw [m₂, m₁ a ha]
  have hpw₀ : pwS c₂.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD =
      pwS c.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD :=
    pwS_congr fun j _ => ⟨M₂ _ (by clear * - hZs hY hI0₀; omega),
      M₂ _ (by clear * - hZs hY hI0₀; omega)⟩
  have hpw₁ : pwS c₂.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD =
      pwS c.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD :=
    pwS_congr fun j _ => ⟨M₂ _ (by clear * - hZs hY hI0₀ hI0₁ hE0; omega),
      M₂ _ (by clear * - hZs hY hI0₀ hI0₁ hE0; omega)⟩
  -- the primary values
  obtain ⟨c₃, t₃, e₃, ht₃, hP₃, f₃, m₃, rr₃, rm₃, o₃⟩ := fbPn_exec (P := P) c₂ e₂.wb_right hin
    hI0₀ hI0₁ (by rw [hpw₀]; exact hL₀) (by rw [hpw₁]; exact hL₁) hb1 hW1 hW2 hW3 hW4 h9600
  rw [hpw₀, hpw₁] at hP₃
  have hWr : c₃.nreg 1022 = pnW p₀ p₁ := by
    have := hP₃.c2; rwa [show (10550 + 2 = 10552) from rfl, pnπ_hi 22 (by decide)] at this
  have hMr : c₃.nreg 1023 = 2 * nodeHN m b w (L + 1) + 1 := by
    have := hP₃.c3; rwa [show (10550 + 3 = 10553) from rfl, pnπ_hi 23 (by decide)] at this
  have F₃ : ∀ r, (r < 1000 ∨ 1170 ≤ r) → (r < 2966 ∨ 2978 < r) → c₃.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [f₃ r h1, f₂ r (fbPI_frame (by clear * - h1; omega)), F₁ r h2]
  -- the bases
  obtain ⟨c₄, e₄, s₄, f₄, m₄, rr₄, rm₄, o₄⟩ := pcProg_exec (I := P) (W := W) fbRL fbRL_wf h9600
    c₃ e₃.wb_right (fun g hg hs => by
      have k' : ∀ r, (r < 2296 ∨ (2297 < r ∧ r < 2330) ∨ 2335 < r) → g r = c₃.nreg r :=
        fun r hr => hg r (fbRL_notDst (by clear * - hr; omega)) (by clear * - hr; omega)
          (by clear * - hr; omega)
      obtain ⟨E0, E1, E2, E3, E4, E5⟩ := fbRL_eqs hs
      have a1 := k' 1022 (by decide); have a2 := k' 2313 (by decide)
      have a3 := k' 2314 (by decide); have a4 := k' 3004 (by decide)
      have a5 := k' 2475 (by decide); have a6 := k' 3003 (by decide)
      rw [hWr] at a1
      rw [F₃ 2313 (by decide) (by decide), r13] at a2
      rw [F₃ 2314 (by decide) (by decide), r14] at a3
      rw [F₃ 3004 (by decide) (by decide), r04] at a4
      rw [F₃ 2475 (by decide) (by decide), r75] at a5
      rw [F₃ 3003 (by decide) (by decide), r03] at a6
      intro x hx
      simp only [fbRL, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          one_mul, add_zero, mul_one]
        clear * - a1 a2 a3 a4 a5 a6 hZW hW1 hdW hdh hR hmk
        omega)
  have F₄ : ∀ r, (r < 2296 ∨ (2297 < r ∧ r < 2330) ∨ 2335 < r) → c₄.nreg r = c₃.nreg r :=
    fun r hr => f₄ r (fbRL_notDst (by clear * - hr; omega)) (by clear * - hr; omega)
      (by clear * - hr; omega)
  obtain ⟨E0, E1, E2, E3, E4, E5⟩ := fbRL_eqs s₄
  have v1022 : c₄.nreg 1022 = pnW p₀ p₁ := by rw [F₄ 1022 (by decide), hWr]
  have v1023 : c₄.nreg 1023 = 2 * nodeHN m b w (L + 1) + 1 := by rw [F₄ 1023 (by decide), hMr]
  have v13 : c₄.nreg 2313 = Z := by rw [F₄ 2313 (by decide), F₃ 2313 (by decide) (by decide), r13]
  have v14 : c₄.nreg 2314 = M₀ := by
    rw [F₄ 2314 (by decide), F₃ 2314 (by decide) (by decide), r14]
  have v04 : c₄.nreg 3004 = d := by rw [F₄ 3004 (by decide), F₃ 3004 (by decide) (by decide), r04]
  have v75 : c₄.nreg 2475 = k := by rw [F₄ 2475 (by decide), F₃ 2475 (by decide) (by decide), r75]
  have v03 : c₄.nreg 3003 = h := by rw [F₄ 3003 (by decide), F₃ 3003 (by decide) (by decide), r03]
  rw [v1022, v13, v14] at E0 E1 E2
  rw [v04, v75] at E3
  rw [v03, v75] at E4 E5
  have G₄ : ∀ r, (r < 1000 ∨ (1170 ≤ r ∧ r < 2296) ∨ (2297 < r ∧ r < 2330) ∨ 2335 < r) →
      (r < 2966 ∨ 2978 < r) → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [F₄ r (by clear * - h1; omega), F₃ r (by clear * - h1; omega) h2]
  have hm₄ : c₄.nmem = c₂.nmem := by rw [m₄, m₃]
  have hMpos : 0 < 2 * nodeHN m b w (L + 1) + 1 := by omega
  have L₄ : ∀ a, Frame.spWs k < a → c₄.nmem a = c.nmem a := fun a ha => by rw [hm₄, M₂ a ha]
  have hsk : Frame.spWs k < pnW p₀ p₁ + 1 := by clear * - hZs hZW; omega
  have hk10 : ∀ i < 2 * k, c₄.nmem (h + 10 * k + i) = i := fun i hi => by
    rw [L₄ _ (by clear * - hsk hdW hdh; omega)]; exact hid i hi
  -- the lengths
  obtain ⟨c₅, e₅, g₅, f₅, m₅, rr₅, rm₅, o₅⟩ := cpRegs_exec (P := P) (W := W) _ ok1 sr1 c₄
    e₄.wb_right
  simp only [fbQ1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₅
  obtain ⟨u40, u41, u42, u43, u44, u45⟩ := g₅
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, m₆, f₆, rr₆, rm₆, o₆⟩ := ldProg_exec (P := P) (n := m)
    (INb := d + 4 + 5 * k) (Jb := h + 10 * k) (Ob := pnW p₀ p₁ + 1 + (Z + 3 * M₀))
    (M := 2 * nodeHN m b w (L + 1) + 1) (L := L) c₅ e₅.wb_right
    (by rw [u40, G₄ 2474 (by decide) (by decide), r74]) (by rw [u41, E3])
    (by rw [u42, G₄ 2203 (by decide) (by decide), r2203]) (by rw [u43, E0])
    (by rw [u44, v1023]) (by rw [u45, G₄ 2204 (by decide) (by decide), r2204]) hMpos
    (by clear * - h9600; omega) (by clear * - hR hmk; omega)
    (by clear * - hZW hW1 hM₀ hmk hdW hdh hR; omega)
    (Or.inl (by clear * - hZW hM₀ hdW hdh; omega))
    (fun i hi => by
      rw [m₅, hk10 i (by clear * - hi hmk; omega), L₄ _ (by clear * - hsk hdW; omega),
        hln i hi]
      have := abs_le.1 (hℓ i hi)
      refine ⟨by clear * - hi hdh hR hmk; omega, Or.inr (by clear * - hZW hM₀ hdW; omega),
        by clear * - this hMW; omega⟩)
  have R₆ : ∀ i < m, (c₆.nmem (pnW p₀ p₁ + 1 + (Z + 3 * M₀ + i)) : ℤ) =
      ℓ (en i) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ) := fun i hi => by
    rw [show pnW p₀ p₁ + 1 + (Z + 3 * M₀ + i) = pnW p₀ p₁ + 1 + (Z + 3 * M₀) + i by ring,
      v₆ i hi]
    exact fb_ldv hMpos (by rw [m₅]; exact hk10 i (by clear * - hi hmk; omega))
      (by rw [m₅, L₄ _ (by clear * - hsk hdW; omega), hln i hi]; exact fb_off (hℓ i hi))
  have M₆ : ∀ a, (a < pnW p₀ p₁ + 1 + (Z + 3 * M₀) ∨ pnW p₀ p₁ + 1 + (Z + 3 * M₀) + m ≤ a) →
      c₆.nmem a = c₄.nmem a := fun a ha => by rw [m₆ a ha, m₅]
  have G₆ : ∀ r, (r < 2840 ∨ 2850 < r) → c₆.nreg r = c₄.nreg r := fun r hr => by
    rw [f₆ r hr, f₅ r (fbQ_frame (by clear * - hr; omega)).1]
  -- the first child's potential
  obtain ⟨c₇, e₇, g₇, f₇, m₇, rr₇, rm₇, o₇⟩ := cpRegs_exec (P := P) (W := W) _ ok2 sr2 c₆
    e₆.wb_right
  simp only [fbQ2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₇
  obtain ⟨w40, w41, w42, w43, w44, w45⟩ := g₇
  have hk10' : ∀ i < 2 * k, c₇.nmem (h + 10 * k + i) = i := fun i hi => by
    rw [m₇, M₆ _ (Or.inr (by clear * - hZW hM₀ hdW hdh; omega))]; exact hk10 i hi
  have L₇ : ∀ a, h ≤ a → c₇.nmem a = c.nmem a := fun a ha => by
    rw [m₇, M₆ _ (Or.inr (by clear * - ha hZW hM₀ hdW hdh; omega)),
      L₄ _ (by clear * - ha hsk hdW hdh; omega)]
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, m₈, f₈, rr₈, rm₈, o₈⟩ := ldProg_exec (P := P) (n := w)
    (INb := h + 4 * k) (Jb := h + 10 * k) (Ob := pnW p₀ p₁ + 1 + (Z + 4 * M₀))
    (M := 2 * nodeHN m b w (L + 1) + 1) (L := L + 1) c₇ e₇.wb_right
    (by rw [w40, G₆ 2464 (by decide), G₄ 2464 (by decide) (by decide), r64])
    (by rw [w41, G₆ 2334 (by decide), E4])
    (by rw [w42, G₆ 2203 (by decide), G₄ 2203 (by decide) (by decide), r2203])
    (by rw [w43, G₆ 2331 (by decide), E1]) (by rw [w44, G₆ 1023 (by decide), v1023])
    (by rw [w45, G₆ 2205 (by decide), G₄ 2205 (by decide) (by decide), r2205]) hMpos
    (by clear * - h9600; omega) (by clear * - hR hw; omega)
    (by clear * - hZW hW1 hM₀ hw hdW hdh hR; omega)
    (Or.inl (by clear * - hZW hM₀ hdW hdh; omega))
    (fun v hv => by
      rw [hk10' v (by clear * - hv hw; omega), L₇ _ (by clear * -; omega)]
      obtain ⟨h1, h2⟩ := hG₀ v hv
      have := abs_le.1 h2
      refine ⟨by clear * - hv hR hw; omega, Or.inr (by clear * - hZW hM₀ hdW hdh; omega),
        by clear * - this h1 hMW; omega⟩)
  have R₈ : ∀ v < w, (c₈.nmem (pnW p₀ p₁ + 1 + (Z + 4 * M₀ + v)) : ℤ) =
      δ₀ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ) := fun v hv => by
    rw [show pnW p₀ p₁ + 1 + (Z + 4 * M₀ + v) = pnW p₀ p₁ + 1 + (Z + 4 * M₀) + v by ring,
      v₈ v hv]
    exact fb_ldv hMpos (hk10' v (by clear * - hv hw; omega))
      (by rw [L₇ _ (by clear * -; omega), (hG₀ v hv).1]; push_cast; ring)
  have G₈ : ∀ r, (r < 2840 ∨ 2850 < r) → c₈.nreg r = c₄.nreg r := fun r hr => by
    rw [f₈ r hr, f₇ r (fbQ_frame (by clear * - hr; omega)).2.1, G₆ r hr]
  -- the second child's potential
  obtain ⟨c₉, e₉, g₉, f₉, m₉, rr₉, rm₉, o₉⟩ := cpRegs_exec (P := P) (W := W) _ ok3 sr3 c₈
    e₈.wb_right
  simp only [fbQ3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₉
  obtain ⟨x40, x41, x42, x43, x44, x45⟩ := g₉
  have L₉ : ∀ a, h ≤ a → c₉.nmem a = c.nmem a := fun a ha => by
    rw [m₉, m₈ _ (Or.inr (by clear * - ha hZW hM₀ hdW hdh; omega)), L₇ a ha]
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v₁₀, m₁₀, f₁₀, rr₁₀, rm₁₀, o₁₀⟩ := ldProg_exec (P := P) (n := w)
    (INb := h + 6 * k) (Jb := h + 10 * k) (Ob := pnW p₀ p₁ + 1 + (Z + 5 * M₀))
    (M := 2 * nodeHN m b w (L + 1) + 1) (L := L + 1) c₉ e₉.wb_right
    (by rw [x40, G₈ 2464 (by decide), G₄ 2464 (by decide) (by decide), r64])
    (by rw [x41, G₈ 2335 (by decide), E5])
    (by rw [x42, G₈ 2203 (by decide), G₄ 2203 (by decide) (by decide), r2203])
    (by rw [x43, G₈ 2332 (by decide), E2]) (by rw [x44, G₈ 1023 (by decide), v1023])
    (by rw [x45, G₈ 2205 (by decide), G₄ 2205 (by decide) (by decide), r2205]) hMpos
    (by clear * - h9600; omega) (by clear * - hR hw; omega)
    (by clear * - hZW hW1 hM₀ hw hdW hdh hR; omega)
    (Or.inl (by clear * - hZW hM₀ hdW hdh; omega))
    (fun v hv => by
      rw [L₉ (h + 10 * k + v) (by clear * -; omega), hid v (by clear * - hv hw; omega),
        L₉ _ (by clear * -; omega)]
      obtain ⟨h1, h2⟩ := hG₁ v hv
      have := abs_le.1 h2
      refine ⟨by clear * - hv hR hw; omega, Or.inr (by clear * - hZW hM₀ hdW hdh; omega),
        by clear * - this h1 hMW; omega⟩)
  have R₁₀ : ∀ v < w, (c₁₀.nmem (pnW p₀ p₁ + 1 + (Z + 5 * M₀ + v)) : ℤ) =
      δ₁ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ) := fun v hv => by
    rw [show pnW p₀ p₁ + 1 + (Z + 5 * M₀ + v) = pnW p₀ p₁ + 1 + (Z + 5 * M₀) + v by ring,
      v₁₀ v hv]
    exact fb_ldv hMpos (by rw [L₉ _ (by clear * -; omega)]; exact hid v (by clear * - hv hw; omega))
      (by rw [L₉ _ (by clear * -; omega), (hG₁ v hv).1]; push_cast; ring)
  refine ⟨c₁₀, t₁ + (fbPI.length + (t₃ + (pcCost fbRL + (fbQ1.length + (t₆ + (fbQ2.length +
    (t₈ + (fbQ3.length + t₁₀)))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉ e₁₀)))))))),
    ?_, fun a ha => ?_, hP₃.congr ?_, fun i hi => ?_, fun v hv => ?_, R₁₀, fun a h1 h2 => ?_,
    fun r hr => ?_, by rw [rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [fbRL_cost]; unfold fbC2Cost
    simp only [fbPI, fbQ1, fbQ2, fbQ3, List.length_cons, List.length_nil]
    clear * - ht₁ ht₃ ht₆ ht₈ ht₁₀ hmk hw; omega
  · rw [m₁₀ a (Or.inl (by clear * - ha hsk; omega)), m₉,
      m₈ a (Or.inl (by clear * - ha hsk; omega)), m₇,
      M₆ a (Or.inl (by clear * - ha hsk; omega)), hm₄, m₂]
    exact z₁ a ha
  · intro j hj
    rw [pnπ_hi j (by clear * - hj; omega), f₁₀ _ (Or.inl (by clear * - hj; omega)),
      f₉ _ (fbQ_frame (Or.inl (by clear * - hj; omega))).2.2,
      G₈ _ (Or.inl (by clear * - hj; omega)), F₄ _ (Or.inl (by clear * - hj; omega))]
  · rw [m₁₀ _ (Or.inl (by clear * - hi hM₀; omega)), m₉,
      m₈ _ (Or.inl (by clear * - hi hM₀; omega)), m₇]
    exact R₆ i hi
  · rw [m₁₀ _ (Or.inl (by clear * - hv hM₀; omega)), m₉]
    exact R₈ v hv
  · rw [m₁₀ a (by clear * - h2 hM₀; omega), m₉, m₈ a (by clear * - h2 hM₀; omega), m₇,
      M₆ a (by clear * - h2 hM₀; omega), hm₄, M₂ a h1]
  · rw [f₁₀ r (by clear * - hr; omega), f₉ r (fbQ_frame (by clear * - hr; omega)).2.2,
      G₈ r (by clear * - hr; omega), G₄ r (by clear * - hr; omega) (by clear * - hr; omega)]

end C2

end NegSSSP

end PlanarFlow
