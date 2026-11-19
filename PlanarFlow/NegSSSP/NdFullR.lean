module

public import PlanarFlow.NegSSSP.NdFullC2

/-!
# The full branch: the registers before the node

**`fbR`** `= cpRegs fbRC1 ; pcProg 2960 fbRD ; block [subN 2954 2935 2931] ;
spZeroRegs (List.range 2920) ; cpRegs fbRC2 ; pcProg 2960 fbRN`:
* the values needed after the node saved in registers `≥ 2920` (which the node keeps):
  `2930 = W'`, `2931 = Z`, `2932 = M₀`, `2933 = H`, `2934 = M`, `2935 = END₁`, `2936 = w`,
  `2937 = m`, `2938 = k`, `2939 = b`, `2940 = B`, `2941 = Y`, `2942 = S`, `2943 … 2950` the
  eight sizes of the two instances; the log `2924 = 2925 = h + 200 k`, `2926 = 1`; the base of
  the node's outcome `2951 = W' + 1 + Z + 20 M₀`, of the residues `2952 = W' + 1 + Z + 3 M₀`,
  their length `2953 = 3 M₀`, `2954 = END₁ − Z`, `2956 = 0`;
* every register below `2920` zeroed, then the node's context: `NCtx` (`800 … 825`), `XCtx`
  (`930 … 945`), `PnInR` (`2657 … 2670`).

**`fbR_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The values saved before the node. -/
def fbRC1 : List (ℕ × ℕ) :=
  [(2930, 1022), (2931, 2313), (2932, 2314), (2933, 1024), (2934, 1023), (2935, 2321),
    (2936, 2464), (2937, 2474), (2938, 2475), (2939, 2496), (2940, 2205), (2941, 2315),
    (2942, 2316), (2943, 2240), (2944, 2243), (2945, 2241), (2946, 2300), (2947, 2244),
    (2948, 2247), (2949, 2245), (2950, 2301)]

/-- The derived values (scratch `2960`, `2961`). -/
def fbRD : List PcStep :=
  [(2924, [(1, .v 3003), (200, .v 2475)], 0), (2925, [(1, .v 3003), (200, .v 2475)], 0),
    (2926, [(1, .one)], 0), (2951, [(1, .v 1022), (1, .v 2313), (20, .v 2314), (1, .one)], 0),
    (2952, [(1, .v 1022), (1, .v 2313), (3, .v 2314), (1, .one)], 0),
    (2953, [(3, .v 2314)], 0), (2956, [], 0), (2957, [(1, .v 3003), (8, .v 2475)], 0)]

/-- The copies into the node's context. -/
def fbRC2 : List (ℕ × ℕ) :=
  [(800, 2937), (801, 2936), (802, 2939), (2657, 2943), (2658, 2944), (2659, 2945),
    (2660, 2946), (2661, 2947), (2662, 2948), (2663, 2949), (2664, 2950), (2665, 2937),
    (2666, 2936), (2667, 2939), (2668, 2940), (2669, 2941), (2670, 2942)]

/-- The slots of `NCtx` and `XCtx` (scratch `2960`, `2961`). -/
def fbRNs (j : ℕ) : PcStep :=
  (803 + j, (1, .v 2931) :: (if j = 0 then [] else [(j, .v 2932)]), 0)

/-- … -/
def fbRXs (j : ℕ) : PcStep :=
  (930 + j, (1, .v 2941) :: (if j = 0 then [] else [(j, .v 2942)]), 0)

/-- … -/
def fbRN : List PcStep :=
  (List.range 22).map fbRNs ++ [(825, [(4, .v 2937), (18, .v 2936), (175, .one)], 0)] ++
    (List.range 16).map fbRXs

/-- **The registers before the node.** -/
def fbR : Stmt :=
  .seq (cpRegs fbRC1) <| .seq (pcProg 2960 fbRD) <| .seq (block [.subN 2954 2935 2931]) <|
  .seq (Frame.spZeroRegs (List.range 2920)) <| .seq (cpRegs fbRC2) (pcProg 2960 fbRN)

set_option maxRecDepth 100000 in
theorem fbRD_wf : pcWF 2960 9600 fbRD = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem fbRN_wf : pcWF 2960 9600 fbRN = true := by kernel_rfl

theorem fbRD_cost : pcCost fbRD = 88 := by kernel_rfl

theorem fbRN_cost : pcCost fbRN = 425 := by kernel_rfl

theorem fbRC_ok : cpOK fbRC1 = true ∧ cpSrc fbRC1 = true ∧ cpOK fbRC2 = true ∧
    cpSrc fbRC2 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The cost of `fbR`. -/
def fbRCost : ℕ := 21 + 88 + 1 + 2920 + 17 + 425

theorem fbRD_eqs {g : ℕ → ℕ} (h : PcSol fbRD g) :
    g 2924 = g 3003 + 200 * g 2475 ∧ g 2925 = g 3003 + 200 * g 2475 ∧ g 2926 = 1 ∧
    g 2951 = g 1022 + g 2313 + 20 * g 2314 + 1 ∧ g 2952 = g 1022 + g 2313 + 3 * g 2314 + 1 ∧
    g 2953 = 3 * g 2314 ∧ g 2956 = 0 ∧ g 2957 = g 3003 + 8 * g 2475 := by
  simp only [PcSol, fbRD, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero, mul_one] at h
  omega

theorem fbRN_eqs {g : ℕ → ℕ} (h : PcSol fbRN g) :
    (∀ j < 22, g (803 + j) = g 2931 + j * g 2932) ∧
    g 825 = 4 * g 2937 + 18 * g 2936 + 175 ∧
    (∀ j < 16, g (930 + j) = g 2941 + j * g 2942) := by
  refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
  · have := h (fbRNs j) (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))
    rw [show 803 + j = (fbRNs j).1 from rfl, this]; unfold fbRNs
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hpSum, hpM.ev]
    · simp [hpSum, hpM.ev, Nat.pos_iff_ne_zero.1 hj0]
  · have := h (825, [(4, .v 2937), (18, .v 2936), (175, .one)], 0)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    rw [this]; simp [hpSum, hpM.ev]; ring
  · have := h (fbRXs j) (List.mem_append_right _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
    rw [show 930 + j = (fbRXs j).1 from rfl, this]; unfold fbRXs
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hpSum, hpM.ev]
    · simp [hpSum, hpM.ev, Nat.pos_iff_ne_zero.1 hj0]

theorem fbRD_notDst {r : ℕ}
    (h : r < 2924 ∨ (2926 < r ∧ r < 2951) ∨ (2953 < r ∧ r ≠ 2956 ∧ r ≠ 2957)) :
    r ∉ pcDsts fbRD := by
  simp only [pcDsts, fbRD, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

theorem fbRN_notDst {r : ℕ} (h : r < 803 ∨ (825 < r ∧ r < 930) ∨ 945 < r) :
    r ∉ pcDsts fbRN := by
  simp only [pcDsts, fbRN, List.map_append, List.map_map, List.mem_append, List.mem_map,
    List.mem_range, Function.comp_apply, fbRNs, fbRXs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and]
  refine ⟨⟨fun j _ => by omega, by omega⟩, fun j _ => by omega⟩

theorem fbRC1_frame {r : ℕ} (h : r < 2930 ∨ 2950 < r) : r ∉ fbRC1.map (·.1) := by
  simp only [fbRC1, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem fbRC2_frame {r : ℕ} (h : r < 800 ∨ (802 < r ∧ r < 2657) ∨ 2670 < r) :
    r ∉ fbRC2.map (·.1) := by
  simp only [fbRC2, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem fbRN_bound {g : ℕ → ℕ} {Z M₀ m w Y S : ℕ} (a1 : g 2931 = Z) (a2 : g 2932 = M₀)
    (a3 : g 2937 = m) (a4 : g 2936 = w) (a5 : g 2941 = Y) (a6 : g 2942 = S)
    (hb3 : Z + 21 * M₀ ≤ W) (hb4 : 4 * m + 18 * w + 175 ≤ W) (hb5 : Y + 15 * S ≤ W) :
    ∀ s ∈ fbRN, hpSum g s.2.1 ≤ W := by
  intro s hs
  simp only [fbRN, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with (⟨j, hj, rfl⟩ | rfl) | ⟨j, hj, rfl⟩
  · unfold fbRNs
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [hpSum, hpM.ev, a1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        ite_true]; omega
    · simp only [hpSum, hpM.ev, a1, a2, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.pos_iff_ne_zero.1 hj0, ite_false]
      have : j * M₀ ≤ 21 * M₀ := Nat.mul_le_mul_right _ (by omega)
      omega
  · simp only [hpSum, hpM.ev, a3, a4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · unfold fbRXs
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [hpSum, hpM.ev, a5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        ite_true]; omega
    · simp only [hpSum, hpM.ev, a5, a6, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.pos_iff_ne_zero.1 hj0, ite_false]
      have : j * S ≤ 15 * S := Nat.mul_le_mul_right _ (by omega)
      omega

set_option maxHeartbeats 8000000 in
/-- **The registers before the node** (see the module docstring). -/
theorem fbR_exec {p₀ p₁ : FeP} {W' Z M₀ H M E₁ w m k b B Y S h : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (r1022 : c.nreg 1022 = W') (r2313 : c.nreg 2313 = Z) (r2314 : c.nreg 2314 = M₀)
    (r1024 : c.nreg 1024 = H) (r1023 : c.nreg 1023 = M) (r2321 : c.nreg 2321 = E₁)
    (r2464 : c.nreg 2464 = w) (r2474 : c.nreg 2474 = m) (r2475 : c.nreg 2475 = k)
    (r2496 : c.nreg 2496 = b) (r2205 : c.nreg 2205 = B) (r2315 : c.nreg 2315 = Y)
    (r2316 : c.nreg 2316 = S)
    (e40 : c.nreg 2240 = p₀.nD) (e43 : c.nreg 2243 = p₀.k) (e41 : c.nreg 2241 = p₀.nV)
    (e00 : c.nreg 2300 = p₀.nF) (f44 : c.nreg 2244 = p₁.nD) (f47 : c.nreg 2247 = p₁.k)
    (f45 : c.nreg 2245 = p₁.nV) (f01 : c.nreg 2301 = p₁.nF) (r3003 : c.nreg 3003 = h)
    (h9600 : 9600 ≤ W) (hb1 : h + 200 * k ≤ W) (hb2 : W' + Z + 20 * M₀ + 1 ≤ W)
    (hb3 : Z + 21 * M₀ ≤ W) (hb4 : 4 * m + 18 * w + 175 ≤ W) (hb5 : Y + 15 * S ≤ W) :
    ∃ c' t, Exec P W fbR c c' t ∧ t ≤ fbRCost ∧
      c'.nreg 2930 = W' ∧ c'.nreg 2931 = Z ∧ c'.nreg 2932 = M₀ ∧ c'.nreg 2933 = H ∧
      c'.nreg 2934 = M ∧ c'.nreg 2935 = E₁ ∧ c'.nreg 2936 = w ∧ c'.nreg 2937 = m ∧
      c'.nreg 2938 = k ∧ c'.nreg 2924 = h + 200 * k ∧ c'.nreg 2925 = h + 200 * k ∧
      c'.nreg 2926 = 1 ∧ c'.nreg 2951 = W' + Z + 20 * M₀ + 1 ∧
      c'.nreg 2952 = W' + Z + 3 * M₀ + 1 ∧ c'.nreg 2953 = 3 * M₀ ∧ c'.nreg 2954 = E₁ - Z ∧
      c'.nreg 2956 = 0 ∧ c'.nreg 2957 = h + 8 * k ∧
      NCtx m w b Z M₀ c' ∧ XCtx Y S c' ∧ PnInR c'.nreg p₀ p₁ m w b B Y S ∧
      (∀ r < 2920, (r < 800 ∨ (825 < r ∧ r < 930) ∨ (945 < r ∧ r < 2657) ∨ 2670 < r) →
        c'.nreg r = 0) ∧
      (∀ r, 2961 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ok1, sr1, ok2, sr2⟩ := fbRC_ok
  -- the saves
  obtain ⟨c₁, e₁, g₁, f₁, m₁, rr₁, rm₁, o₁⟩ := cpRegs_exec (P := P) (W := W) _ ok1 sr1 c hc
  simp only [fbRC1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₁
  obtain ⟨s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46,
    s47, s48, s49, s50⟩ := g₁
  have F₁ : ∀ r, (r < 2930 ∨ 2950 < r) → c₁.nreg r = c.nreg r := fun r hr => f₁ r (fbRC1_frame hr)
  -- the derived values
  obtain ⟨c₂, e₂, q₂, f₂, m₂, rr₂, rm₂, o₂⟩ := pcProg_exec (I := P) (W := W) fbRD fbRD_wf h9600
    c₁ e₁.wb_right (fun g hg hs => by
      have k' : ∀ r, (r < 2924 ∨ (2926 < r ∧ r < 2951) ∨ (2953 < r ∧ r ≠ 2956 ∧ r ≠ 2957)) →
          r ≠ 2960 →
          r ≠ 2961 → g r = c₁.nreg r := fun r hr h1 h2 => hg r (fbRD_notDst hr) h1 h2
      have a1 : g 3003 = h := by rw [k' 3003 (by omega) (by omega) (by omega), F₁ _ (by omega), r3003]
      have a2 : g 2475 = k := by rw [k' 2475 (by omega) (by omega) (by omega), F₁ _ (by omega), r2475]
      have a3 : g 1022 = W' := by rw [k' 1022 (by omega) (by omega) (by omega), F₁ _ (by omega), r1022]
      have a4 : g 2313 = Z := by rw [k' 2313 (by omega) (by omega) (by omega), F₁ _ (by omega), r2313]
      have a5 : g 2314 = M₀ := by rw [k' 2314 (by omega) (by omega) (by omega), F₁ _ (by omega), r2314]
      intro s hs
      simp only [fbRD, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          one_mul, add_zero, mul_one, a1, a2, a3, a4, a5]
        clear * - hb1 hb2 hb3 h9600
        omega)
  have F₂ : ∀ r, (r < 2924 ∨ (2926 < r ∧ r < 2951) ∨ (2953 < r ∧ r ≠ 2956 ∧ r ≠ 2957)) →
          r ≠ 2960 →
      r ≠ 2961 → c₂.nreg r = c₁.nreg r := fun r hr h1 h2 => f₂ r (fbRD_notDst hr) h1 h2
  obtain ⟨D24, D25, D26, D51, D52, D53, D56, D57⟩ := fbRD_eqs q₂
  rw [F₂ 3003 (by omega) (by omega) (by omega), F₁ _ (by omega), r3003,
    F₂ 2475 (by omega) (by omega) (by omega), F₁ _ (by omega), r2475] at D24 D25 D57
  rw [F₂ 1022 (by omega) (by omega) (by omega), F₁ _ (by omega), r1022,
    F₂ 2313 (by omega) (by omega) (by omega), F₁ _ (by omega), r2313,
    F₂ 2314 (by omega) (by omega) (by omega), F₁ _ (by omega), r2314] at D51 D52
  rw [F₂ 2314 (by omega) (by omega) (by omega), F₁ _ (by omega), r2314] at D53
  have hw₂ := e₂.wb_right
  have t35 : c₂.nreg 2935 = E₁ := by
    rw [F₂ _ (by omega) (by omega) (by omega), s35, r2321]
  have t31 : c₂.nreg 2931 = Z := by
    rw [F₂ _ (by omega) (by omega) (by omega), s31, r2313]
  -- `END₁ − Z`
  obtain ⟨c₃, k₃, e₃, hk₃, h54, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.subN 2954 2935 2931]) c₂ c₃ k₃ ∧ k₃ = 1 ∧
      c₃.nreg 2954 = E₁ - Z ∧ (∀ r, r ≠ 2954 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [t35, t31]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [t35, t31]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  -- the zeroing
  obtain ⟨c₄, e₄, z₄, f₄, m₄, rr₄, rm₄, o₄⟩ := Frame.spZeroRegs_exec (P := P)
    (List.range 2920) c₃ hw₃
  rw [List.length_range] at e₄
  have F₄ : ∀ r, 2920 ≤ r → c₄.nreg r = c₃.nreg r := fun r hr =>
    f₄ r (by simp only [List.mem_range]; omega)
  have Z₄ : ∀ r < 2920, c₄.nreg r = 0 := fun r hr => z₄ r (List.mem_range.2 hr)
  -- `G r`: the value at `r ≥ 2920` after the saves and the derived values
  have G : ∀ r, 2920 ≤ r → c₄.nreg r = c₃.nreg r := F₄
  have v : ∀ r, 2929 < r → r < 2951 → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [G r (by omega), hn₃ r (by omega), F₂ r (by omega) (by omega) (by omega)]
  -- the copies
  obtain ⟨c₅, e₅, g₅, f₅, m₅, rr₅, rm₅, o₅⟩ := cpRegs_exec (P := P) (W := W) _ ok2 sr2 c₄
    e₄.wb_right
  simp only [fbRC2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₅
  obtain ⟨u800, u801, u802, u57, u58, u59, u60, u61, u62, u63, u64, u65, u66, u67, u68, u69,
    u70⟩ := g₅
  have F₅ : ∀ r, (r < 800 ∨ (802 < r ∧ r < 2657) ∨ 2670 < r) → c₅.nreg r = c₄.nreg r :=
    fun r hr => f₅ r (fbRC2_frame hr)
  have w31 : c₅.nreg 2931 = Z := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s31, r2313]
  have w32 : c₅.nreg 2932 = M₀ := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s32, r2314]
  have w36 : c₅.nreg 2936 = w := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s36, r2464]
  have w37 : c₅.nreg 2937 = m := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s37, r2474]
  have w41 : c₅.nreg 2941 = Y := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s41, r2315]
  have w42 : c₅.nreg 2942 = S := by rw [F₅ _ (by omega), v _ (by omega) (by omega), s42, r2316]
  -- the slots
  obtain ⟨c₆, e₆, q₆, f₆, m₆, rr₆, rm₆, o₆⟩ := pcProg_exec (I := P) (W := W) fbRN fbRN_wf h9600
    c₅ e₅.wb_right (fun g hg hs => by
      have k' : ∀ r, 2930 < r → r < 2943 → g r = c₅.nreg r := fun r h1 h2 =>
        hg r (fbRN_notDst (by omega)) (by omega) (by omega)
      exact fbRN_bound ((k' 2931 (by omega) (by omega)).trans w31)
        ((k' 2932 (by omega) (by omega)).trans w32) ((k' 2937 (by omega) (by omega)).trans w37)
        ((k' 2936 (by omega) (by omega)).trans w36) ((k' 2941 (by omega) (by omega)).trans w41)
        ((k' 2942 (by omega) (by omega)).trans w42) hb3 hb4 hb5)
  have F₆ : ∀ r, (r < 803 ∨ (825 < r ∧ r < 930) ∨ 945 < r) → r ≠ 2960 → r ≠ 2961 →
      c₆.nreg r = c₅.nreg r := fun r hr h1 h2 => f₆ r (fbRN_notDst hr) h1 h2
  obtain ⟨N1, N2, N3⟩ := fbRN_eqs q₆
  have x31 : c₆.nreg 2931 = Z := by rw [F₆ _ (by omega) (by omega) (by omega), w31]
  have x32 : c₆.nreg 2932 = M₀ := by rw [F₆ _ (by omega) (by omega) (by omega), w32]
  have x36 : c₆.nreg 2936 = w := by rw [F₆ _ (by omega) (by omega) (by omega), w36]
  have x37 : c₆.nreg 2937 = m := by rw [F₆ _ (by omega) (by omega) (by omega), w37]
  have x41 : c₆.nreg 2941 = Y := by rw [F₆ _ (by omega) (by omega) (by omega), w41]
  have x42 : c₆.nreg 2942 = S := by rw [F₆ _ (by omega) (by omega) (by omega), w42]
  -- `H r`: a register `≥ 2920` other than the scratch, back to `c₃`
  have Hk : ∀ r, 2920 ≤ r → r ≠ 2960 → r ≠ 2961 → c₆.nreg r = c₃.nreg r := fun r h1 h2 h3 => by
    rw [F₆ r (by omega) h2 h3, F₅ r (by omega), G r h1]
  have hx : ∀ r, 2929 < r → r < 2951 → c₆.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [Hk r (by omega) (by omega) (by omega), hn₃ r (by omega),
      F₂ r (by omega) (by omega) (by omega)]
  have hy : ∀ r, 2920 ≤ r → r ≠ 2954 → r ≠ 2960 → r ≠ 2961 → c₆.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => by rw [Hk r h1 h3 h4, hn₃ r h2]
  have cp : ∀ r, 802 < r → r < 2657 → (r < 803 ∨ (825 < r ∧ r < 930) ∨ 945 < r) →
      r < 2920 → c₆.nreg r = 0 := fun r h1 h2 h3 h4 => by
    rw [F₆ r h3 (by omega) (by omega), F₅ r (by omega), Z₄ r h4]
  have cq : ∀ r, (r < 800 ∨ 2670 < r) → r < 2920 → c₆.nreg r = 0 := fun r h1 h2 => by
    rw [F₆ r (by omega) (by omega) (by omega), F₅ r (by omega), Z₄ r h2]
  have cc : ∀ r, (800 ≤ r ∧ r < 803) ∨ (2657 ≤ r ∧ r ≤ 2670) → c₆.nreg r = c₅.nreg r :=
    fun r hr => F₆ r (by omega) (by omega) (by omega)
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_,
    by rw [hx _ (by omega) (by omega), s30, r1022], by rw [x31],
    by rw [x32], by rw [hx _ (by omega) (by omega), s33, r1024],
    by rw [hx _ (by omega) (by omega), s34, r1023], by rw [hx _ (by omega) (by omega), s35, r2321],
    by rw [x36], by rw [x37], by rw [hx _ (by omega) (by omega), s38, r2475],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D24],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D25],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D26],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D51],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D52],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D53],
    by rw [Hk _ (by omega) (by omega) (by omega), h54],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D56],
    by rw [hy _ (by omega) (by omega) (by omega) (by omega), D57], ?_, ?_, ?_,
    fun r h1 h2 => ?_, fun r hr => ?_, by rw [m₆, m₅, m₄, hm₃, m₂, m₁],
    by rw [rr₆, rr₅, rr₄, hr₃, rr₂, rr₁], by rw [rm₆, rm₅, rm₄, hrm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, ho₃, o₂, o₁]⟩
  · simp only [fbRCost, List.length_cons, List.length_nil, fbRC1, fbRC2, fbRD_cost, fbRN_cost,
      hk₃]
    omega
  · refine ⟨by rw [cc _ (by omega), u800, v _ (by omega) (by omega), s37, r2474],
      by rw [cc _ (by omega), u801, v _ (by omega) (by omega), s36, r2464],
      by rw [cc _ (by omega), u802, v _ (by omega) (by omega), s39, r2496],
      fun j hj => by rw [N1 j hj, x31, x32, Nat.mul_comm], by rw [N2, x37, x36]; rfl⟩
  · exact ⟨fun j hj => by rw [N3 j hj, x41, x42, Nat.mul_comm]⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cc _ (by omega), u57, v _ (by omega) (by omega), s43, e40]
    · rw [cc _ (by omega), u58, v _ (by omega) (by omega), s44, e43]
    · rw [cc _ (by omega), u59, v _ (by omega) (by omega), s45, e41]
    · rw [cc _ (by omega), u60, v _ (by omega) (by omega), s46, e00]
    · rw [cc _ (by omega), u61, v _ (by omega) (by omega), s47, f44]
    · rw [cc _ (by omega), u62, v _ (by omega) (by omega), s48, f47]
    · rw [cc _ (by omega), u63, v _ (by omega) (by omega), s49, f45]
    · rw [cc _ (by omega), u64, v _ (by omega) (by omega), s50, f01]
    · rw [cc _ (by omega), u65, v _ (by omega) (by omega), s37, r2474]
    · rw [cc _ (by omega), u66, v _ (by omega) (by omega), s36, r2464]
    · rw [cc _ (by omega), u67, v _ (by omega) (by omega), s39, r2496]
    · rw [cc _ (by omega), u68, v _ (by omega) (by omega), s40, r2205]
    · rw [cc _ (by omega), u69, v _ (by omega) (by omega), s41, r2315]
    · rw [cc _ (by omega), u70, v _ (by omega) (by omega), s42, r2316]
  · rcases h2 with h2 | h2 | h2 | h2
    · exact cq r (Or.inl h2) h1
    · exact cp r (by omega) (by omega) (Or.inr (Or.inl h2)) h1
    · exact cp r (by omega) h2.2 (Or.inr (Or.inr h2.1)) h1
    · exact cq r (Or.inr h2) h1
  · rw [Hk r (by omega) (by omega) (by omega), hn₃ r (by omega),
      F₂ r (by omega) (by omega) (by omega), F₁ r (by omega)]

end NegSSSP

end PlanarFlow
