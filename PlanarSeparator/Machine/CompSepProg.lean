module

public import PlanarSeparator.Machine.CompLight

/-!
# The separator of the components on the machine

**`PlanarSeparator.Piece.compSepProg`** computes the separation
`compSep G (ltComp R (ord N)) (ord N) U w` (the separator routine
`PlanarSeparator.ltRoutine` of a plane rotation system, `ltRoutine … |>.sep U w`) of a vertex set
`U` given as the sorted list of its vertices (`CPre`): the labels `1` on `U` (`initA`), the
components by breadth-first search (`compsB`), the heavy component (`heavyP`); if there is one,
its sorted list, the program of a piece on it (`PlanarSeparator.Piece.pieceCall`), the weights of
its two parts and the mark of the rest of `U`; otherwise the scan of the light components, the
mode and the marks; finally the cleanup of the labels, the component weights and the seen flags.

* `cleanP`, `cleanP_exec`: the cleanup.
* **`compSepProg_exec`**: the run, within
  `2400 #U + (6 Δ + 3415) ∑_{v ∈ U} deg v + 12 ∑_{v ∈ U} w v + 5400` steps; the marks
  `0`, `1`, `2` at `aMk + v`, `v ∈ U`, are exactly the three parts of `compSep`; the rest of the
  memory is kept except the list area `[aL, aL + N)` and the queue `[aQ, aQ + N)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-! ### The cleanup -/

/-- The body of the cleanup: the label of `U[i]`, its component weight and seen flag zeroed. -/
def eBody : Stmt :=
  .seq (block pfx) (block [.storeN 1118 0, .subN 1119 1119 1001, .addN 1118 1104 1119,
    .storeN 1118 0, .addN 1118 1105 1119, .storeN 1118 0, .addN 1110 1110 1001])

/-- **The cleanup.** -/
def cleanP : Stmt := .seq (.instr (.constN 1110 0)) (.whileLtN 1110 1101 eBody)

theorem cleanP_exec {d : Config} (hw : WordsBounded W d) {aU aC aW aS : ℕ}
    (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h00 : d.nreg 1100 = aU)
    (h02 : d.nreg 1102 = aC) (h04 : d.nreg 1104 = aW) (h05 : d.nreg 1105 = aS)
    (h1101 : d.nreg 1101 = #U) (hU : ∀ l < #U, d.nmem (aU + l) = lv U l)
    (l1 : aU + N ≤ aC) (l2 : aC + N ≤ aW) (l3 : aW + N + 1 ≤ aS) (l4 : aS + N + 1 ≤ W)
    (hlab : ∀ x ∈ UN U, 1 ≤ d.nmem (aC + x) ∧ d.nmem (aC + x) ≤ N + 1)
    (hout : ∀ x < N, x ∉ UN U → d.nmem (aC + x) = 0)
    (hcs : ∀ j ≤ N, (d.nmem (aW + j) ≠ 0 ∨ d.nmem (aS + j) ≠ 0) →
      ∃ x ∈ UN U, d.nmem (aC + x) = j + 1) :
    ∃ d' k, Exec P W cleanP d d' k ∧ WordsBounded W d' ∧
      (∀ x < N, d'.nmem (aC + x) = 0) ∧ (∀ j ≤ N, d'.nmem (aW + j) = 0) ∧
      (∀ j ≤ N, d'.nmem (aS + j) = 0) ∧
      (∀ a, (∀ x < N, a ≠ aC + x) → (∀ j ≤ N, a ≠ aW + j) → (∀ j ≤ N, a ≠ aS + j) →
        d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d'.nreg r = d.nreg r) ∧
      k ≤ 13 * #U + 3 := by
  have hUN := card_le_N U
  set lab := fun x => d.nmem (aC + x)
  have e0 := Exec.constN (P := P) hw 1110 0 (Nat.zero_le _)
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧
    (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aC + x) = if ∃ l < i, lv U l = x then 0 else lab x) ∧
    (∀ j ≤ N, d'.nmem (aW + j) = if ∃ l < i, lab (lv U l) - 1 = j then 0 else d.nmem (aW + j)) ∧
    (∀ j ≤ N, d'.nmem (aS + j) = if ∃ l < i, lab (lv U l) - 1 = j then 0 else d.nmem (aS + j)) ∧
    (∀ a, (∀ x < N, a ≠ aC + x) → (∀ j ≤ N, a ≠ aW + j) → (∀ j ≤ N, a ≠ aS + j) →
      d'.nmem a = d.nmem a)
  have hI₀ : I 0 _ := ⟨e0.wb_right, by simp, by simp [h1101],
    fun r hr _ _ _ => by simp [hr], fun x hx => by simp [lab], fun j hj => by simp,
    fun j hj => by simp, fun a _ _ _ => rfl⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 11) (body := eBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hC, hW, hS, hfr⟩ := h
      obtain ⟨x, hxdef⟩ : ∃ x, x = lv U i := ⟨_, rfl⟩
      have hxU : x ∈ UN U := hxdef ▸ lv_mem_UN U hi
      have hx := lt_of_mem_UN hxU
      have hl1 : 1 ≤ lab x := (hlab x hxU).1
      have hlN : lab x ≤ N + 1 := (hlab x hxU).2
      have mU : d'.nmem (aU + i) = x := by
        rw [hfr _ (fun y hy => by omega) (fun j hj => by omega) (fun j hj => by omega), hxdef]
        exact hU i hi
      have hnot : ¬ ∃ l < i, lv U l = x := by
        rintro ⟨l, hl, e⟩
        rw [hxdef] at e
        have := lv_inj' U (by omega) hi e; omega
      have mC : d'.nmem (aC + x) = lab x := by rw [hC x hx, iteF hnot]
      obtain ⟨d₂, e₂, hw₂, b14, b18, b19, q₂, m₂⟩ := pfx_exec (P := P) hw'
        (by rw [hq 1100 (by omega) (by omega) (by omega) (by omega), h00])
        (by rw [hq 1102 (by omega) (by omega) (by omega) (by omega), h02]) h10 mU
        (by omega) (by omega)
      rw [mC] at b19
      have q2 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → d₂.nreg r = d.nreg r :=
        fun r a b c' e => by rw [q₂ r c' b e, hq r a b c' e]
      have r01 := q2 1001 (by omega) (by omega) (by omega) (by omega)
      have r00 := q2 0 (by omega) (by omega) (by omega) (by omega)
      have r04 := q2 1104 (by omega) (by omega) (by omega) (by omega)
      have r05 := q2 1105 (by omega) (by omega) (by omega) (by omega)
      have r10 : d₂.nreg 1110 = i := by rw [q₂ 1110 (by omega) (by omega) (by omega), h10]
      obtain ⟨d₃, k₃, e₃, hw₃, c10, q₃, m₃, hk₃⟩ : ∃ d₃ k₃, Exec P W
          (block [.storeN 1118 0, .subN 1119 1119 1001, .addN 1118 1104 1119,
            .storeN 1118 0, .addN 1118 1105 1119, .storeN 1118 0, .addN 1110 1110 1001])
          d₂ d₃ k₃ ∧ WordsBounded W d₃ ∧ d₃.nreg 1110 = i + 1 ∧
          (∀ r, r ≠ 1110 → r ≠ 1118 → r ≠ 1119 → d₃.nreg r = d₂.nreg r) ∧
          d₃.nmem = upd (upd (upd d₂.nmem (aC + x) 0) (aW + (lab x - 1)) 0)
            (aS + (lab x - 1)) 0 ∧ k₃ = 7 := by
        exec_block
        · config_simp; rw [r04, h04, b19, r01, h01]; omega
        · config_simp; rw [r05, h05, b19, r01, h01]; omega
        · config_simp; rw [r10, r01, h01]; omega
        · refine ⟨‹WordsBounded _ _›, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], ?_, rfl⟩
          · simp only [upd_apply, ↓reduceIte]; rw [r10, r01, h01]
          · rw [b18, r00, h0, r04, h04, b19, r01, h01, r05, h05]
      refine ⟨d₃, _, .seq e₂ e₃, ⟨hw₃, c10, ?_, fun r a b c' e => ?_, fun y hy => ?_,
        fun j hj => ?_, fun j hj => ?_, fun a ha hb hc => ?_⟩, by omega⟩
      · rw [q₃ 1101 (by omega) (by omega) (by omega), q2 1101 (by omega) (by omega) (by omega)
          (by omega), h1101]
      · rw [q₃ r a c' e, q2 r a b c' e]
      · rw [m₃, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), m₂]
        by_cases hyx : y = x
        · subst hyx; rw [upd_same, iteT ⟨i, Nat.lt_succ_self _, hxdef.symm⟩]
        · rw [upd_other _ _ _ (by omega), hC y hy]
          congr 1
          apply propext
          constructor
          · rintro ⟨l, hl, e⟩; exact ⟨l, by omega, e⟩
          · rintro ⟨l, hl, e⟩
            refine ⟨l, ?_, e⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact hl
            · exact absurd (e.symm.trans hxdef.symm) hyx
      · rw [m₃, upd_other _ _ _ (by omega)]
        by_cases hjx : j = lab x - 1
        · subst hjx; rw [upd_same, iteT ⟨i, Nat.lt_succ_self _, by rw [← hxdef]⟩]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), m₂, hW j hj]
          congr 1
          apply propext
          constructor
          · rintro ⟨l, hl, e⟩; exact ⟨l, by omega, e⟩
          · rintro ⟨l, hl, e⟩
            refine ⟨l, ?_, e⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact hl
            · rw [← hxdef] at e; exact absurd e.symm hjx
      · rw [m₃]
        by_cases hjx : j = lab x - 1
        · subst hjx; rw [upd_same, iteT ⟨i, Nat.lt_succ_self _, by rw [← hxdef]⟩]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            m₂, hS j hj]
          congr 1
          apply propext
          constructor
          · rintro ⟨l, hl, e⟩; exact ⟨l, by omega, e⟩
          · rintro ⟨l, hl, e⟩
            refine ⟨l, ?_, e⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact hl
            · rw [← hxdef] at e; exact absurd e.symm hjx
      · rw [m₃, upd_other _ _ _ (hc _ (by omega)), upd_other _ _ _ (hb _ (by omega)),
          upd_other _ _ _ (ha _ hx), m₂]
        exact hfr a ha hb hc)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, hq₁, hC₁, hW₁, hS₁, hfr₁⟩ := hI₁
  have hz : ∀ j ≤ N, (∃ l < #U, lab (lv U l) - 1 = j) ∨ (d.nmem (aW + j) = 0 ∧
      d.nmem (aS + j) = 0) := fun j hj => by
    by_cases h : d.nmem (aW + j) ≠ 0 ∨ d.nmem (aS + j) ≠ 0
    · obtain ⟨x, hx, e⟩ := hcs j hj h
      obtain ⟨l, hl, rfl⟩ := (lv_mem_iff U).2 hx
      exact Or.inl ⟨l, hl, by simp only [lab]; omega⟩
    · right; omega
  refine ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, hfr₁,
    hq₁, by omega⟩
  · rw [hC₁ x hx]
    by_cases h : x ∈ UN U
    · rw [iteT ((lv_mem_iff U).2 h)]
    · rw [iteF (fun h' => h ((lv_mem_iff U).1 h'))]; exact hout x hx h
  · rw [hW₁ j hj]
    rcases hz j hj with h | h
    · rw [iteT h]
    · split_ifs <;> omega
  · rw [hS₁ j hj]
    rcases hz j hj with h | h
    · rw [iteT h]
    · split_ifs <;> omega

/-! ### The front: labels, components, heavy component -/

/-- The labels `1`, the components, the heavy component. -/
def front : Stmt := .seq initA (.seq compsB heavyP)

theorem front_exec {c : Config} (hl : CLay G U w W c) :
    ∃ d k, Exec P W front c d k ∧ Env N W c d ∧
      (∃ nc, BInv G U w #U nc (labF c d) (cwF c d) ∧
        HidOK G U w (labF c d) #U (d.nreg 1123)) ∧
      d.nreg 1120 = ∑ v ∈ U, w v ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output ∧
      k ≤ 74 * #U + 15 * ∑ x ∈ UN U, dg G x + 14 := by
  obtain ⟨d₁, k₁, e₁, hk₁, hw₁, hfix₁, h30₁, h20₁, hlab₁, hfr₁⟩ := initA_exec (P := P) hl
  have env₁ : Env N W c d₁ := ⟨hw₁, hfix₁, h30₁, fun a ha => hfr₁ a (by
    unfold Wz at ha; omega)⟩
  obtain ⟨d₂, k₂, e₂, env₂, ⟨nc, hB₂⟩, hk₂⟩ := compsB_exec (P := P) hl env₁ hlab₁
    (fun j hj => by unfold cwF; rw [hfr₁ _ (by have := hl.lC; have := hl.lQ; omega)]; exact hl.cw j hj)
  have h20₂ : d₂.nreg 1120 = ∑ v ∈ U, w v := by rw [Exec.nreg_of_wr e₂ compsB_wr, h20₁]
  obtain ⟨d₃, k₃, e₃, env₃, hm₃, h20₃, hok₃, hk₃⟩ := heavyP_exec (P := P) hl env₂ hB₂ h20₂
  have hlab₃ : labF c d₃ = labF c d₂ := by funext x; unfold labF; rw [hm₃]
  have hcw₃ : cwF c d₃ = cwF c d₂ := by funext x; unfold cwF; rw [hm₃]
  have e := (Exec.seq e₁ (Exec.seq e₂ e₃) : Exec P W front c d₃ _)
  obtain ⟨rr, rm⟩ := Exec.real_of_noReal e (by decide)
  refine ⟨d₃, _, e, env₃, ⟨nc, by rw [hlab₃, hcw₃]; exact hB₂, by rw [hlab₃]; exact hok₃⟩,
    h20₃, rr, rm, Exec.output_of_ou e (by decide), by omega⟩

/-! ### The marks -/

variable (G) in
/-- **The marks of the separation of the components**: `0`, `1`, `2` at `aM + v` exactly on the
three parts of `compSep G (ltComp R (ord N)) (ord N) U w`. -/
def MarkOK (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (U : Finset (Fin N)) (aM : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  ∀ v ∈ U, (mem (aM + v) = 0 ↔ v ∈ (compSep G (ltComp R (ord N)) (ord N) U w).1) ∧
    (mem (aM + v) = 1 ↔ v ∈ (compSep G (ltComp R (ord N)) (ord N) U w).2.1) ∧
    (mem (aM + v) = 2 ↔ v ∈ (compSep G (ltComp R (ord N)) (ord N) U w).2.2)

/-- The registers kept by the separator of the components. -/
def KeptC (r : ℕ) : Prop :=
  r < 1000 ∨ r = 1001 ∨ (1010 ≤ r ∧ r ≤ 1015) ∨ (1017 ≤ r ∧ r ≤ 1019) ∨ (1100 ≤ r ∧ r ≤ 1105)

theorem wMk_eq {C X : Finset (Fin N)} (hX : X ⊆ C) (mk : ℕ → ℕ) (b : ℕ)
    (h : ∀ v ∈ C, mk v = b ↔ v ∈ X) : wMk C w mk b #C = ∑ v ∈ X, w v := by
  unfold wMk
  rw [sum_lv_eq C (fun x => if mk x = b then SepProg.wI w x else 0)]
  unfold UN
  rw [sum_map, ← sum_filter_of_ne (p := fun v => v ∈ X) ?_]
  · rw [show C.filter (· ∈ X) = X from filter_mem_eq_inter.trans (inter_eq_right.2 hX)]
    refine sum_congr rfl fun v hv => ?_
    simp only [Fin.valEmbedding_apply, iteT ((h v (hX hv)).2 hv)]
    simp [SepProg.wI]
  · intro v hv hne
    by_contra hvX
    simp only [Fin.valEmbedding_apply] at hne
    rw [iteF (fun e => hvX ((h v hv).1 e))] at hne
    exact hne rfl

theorem pieceCall_wmax : pieceCall.wmax < 1100 := by decide +kernel

/-! ### The heavy case -/

/-- **The heavy case**: the list of the heavy component, the program of a piece on it, the
weights of its parts and the marks of the rest of `U`. -/
def dHeavy : Stmt :=
  .seq (.instr (.addN 1121 1123 1001)) (.seq lPass (.seq (.instr (.copyN 1016 1127))
    (.seq pieceCall (.seq wPass (.seq selPass rPass)))))

theorem heavy_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {Z nc : ℕ} {c d : Config} (hp : CPre G R w U Z W c)
    (env : Env N W c d) (hB : BInv G U w #U nc (labF c d) (cwF c d)) {l : ℕ} (hlU : l < #U)
    (hhv : hv G U w l) (hmin : ∀ l' < l, ¬ hv G U w l')
    (h23 : d.nreg 1123 = labF c d (lv U l) - 1) (hrr : d.rreg = c.rreg)
    (hrm : d.rmem = c.rmem) :
    ∃ d' k, Exec P W dHeavy d d' k ∧ WordsBounded W d' ∧
      MarkOK G R w U (c.nreg 1019) d'.nmem ∧
      (∀ a, (∀ v ∈ U, a ≠ c.nreg 1019 + v) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
        d'.nmem a = d.nmem a) ∧
      (∀ r, KeptC r → d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      d'.output = d.output ∧
      k ≤ 2200 * #U + (6 * Δ + 3400) * ∑ v ∈ U, G.degree v + 12 * ∑ v ∈ U, w v +
        39 * #U + 5330 := by
  have hl := hp.lay
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hUN := card_le_N U
  have hsw := hl.sw
  have f := env.fix
  have hl' : l < (ul U).length := by rw [ul_length]; exact hlU
  obtain ⟨vF, hvF⟩ : ∃ vF, vF = (ul U)[l] := ⟨_, rfl⟩
  have hvU : vF ∈ U := hvF ▸ ul_mem U hl'
  have hlv : lv U l = (vF : ℕ) := by rw [hvF]; exact lv_ul U hl'
  obtain ⟨C, hCdef⟩ : ∃ C, C = comp G U vF := ⟨_, rfl⟩
  have hCU : C ⊆ U := hCdef ▸ comp_subset _ _
  have hCN := card_le_N C
  have hvC : vF ∈ C := hCdef ▸ mem_comp_self hvU
  obtain ⟨hb, hbdef⟩ : ∃ hb, hb = labF c d (lv U l) := ⟨_, rfl⟩
  have hb2 : 2 ≤ hb := hbdef ▸ hB.final (lv_mem_UN U hlU)
  have hC : ∀ x (hx : x ∈ UN U), (⟨x, lt_of_mem_UN hx⟩ : Fin N) ∈ C ↔ labF c d x = hb := by
    intro x hx
    rw [hbdef, hB.same _ (lv_mem_UN U hlU) x hx (hbdef ▸ hb2), hlv, hCdef]
    exact cN_val.symm
  have hsC : ∑ v ∈ C, w v ≤ ∑ v ∈ U, w v :=
    sum_le_sum_of_subset_of_nonneg hCU fun _ _ _ => Nat.zero_le _
  -- the label of the heavy component
  obtain ⟨d₀, e₀, hw₀, a21, q₀, m₀⟩ : ∃ d₀, Exec P W (.instr (.addN 1121 1123 1001)) d d₀ 1 ∧
      WordsBounded W d₀ ∧ d₀.nreg 1121 = hb ∧ (∀ r, r ≠ 1121 → d₀.nreg r = d.nreg r) ∧
      d₀.nmem = d.nmem := by
    have e := Exec.addN (P := P) env.wb 1121 1123 1001
      (by rw [h23, f 1001 (by omega), hl.one, ← hbdef]; have := hB.lab_le (lv_mem_UN U hlU); omega)
    refine ⟨_, e, e.wb_right, ?_, fun r hr => by simp [hr], rfl⟩
    simp only [upd_same]; rw [h23, f 1001 (by omega), hl.one, ← hbdef]; omega
  have env₀ : Env N W c d₀ := ⟨hw₀, fun r hr => by rw [q₀ r (by omega)]; exact f r hr,
    by rw [q₀ 1130 (by omega)]; exact env.two, fun a ha => by rw [m₀]; exact env.fr a ha⟩
  have hlab₀ : labF c d₀ = labF c d := by funext x; unfold labF; rw [m₀]
  -- the list of the component
  obtain ⟨d₁, k₁, e₁, hw₁, hr₁, h27, hL₁, hfr₁, hk₁⟩ := lPass_exec (P := P) hl env₀ hCU a21
    (by rw [hlab₀]; exact hC)
  have e2 := Exec.copyN (P := P) hw₁ 1016 1127
  obtain ⟨d₂, he₂⟩ : ∃ d₂, d₂ = { d₁ with nreg := upd d₁.nreg 1016 (d₁.nreg 1127) } := ⟨_, rfl⟩
  rw [← he₂] at e2
  have hw₂ : WordsBounded W d₂ := e2.wb_right
  have b16 : d₂.nreg 1016 = #C := by rw [he₂]; simp [h27]
  have q₂ : ∀ r, r ≠ 1016 → d₂.nreg r = d₁.nreg r := fun r hr => by rw [he₂]; simp [hr]
  have m₂ : d₂.nmem = d₁.nmem := by rw [he₂]
  have R2 : ∀ r < 1110, r ≠ 1016 → d₂.nreg r = c.nreg r := fun r hr h16 => by
    rw [q₂ r h16, hr₁ r (Or.inl hr), q₀ r (by omega), f r hr]
  have eL := (Exec.seq e₀ e₁ : Exec P W (.seq (.instr (.addN 1121 1123 1001)) lPass) d d₁ _)
  obtain ⟨rr₁, rm₁⟩ := Exec.real_of_noReal eL (by decide)
  have ou₁ := Exec.output_of_ou eL (by decide)
  have hPre : Pre G R w C Z W d₂ := pre_of hp hCU hw₂ R2 b16
    (fun a ha hL => by rw [m₂, hfr₁ a hL, m₀]; exact env.fr a ha)
    (fun j hj => by rw [m₂]; exact hL₁ j hj)
    (by rw [he₂]; simp only; rw [rr₁, hrr]) (by rw [he₂]; simp only; rw [rm₁, hrm])
  -- the program of the piece
  obtain ⟨d₃, k₃, e₃, hk₃, hD⟩ := pieceCall_exec (P := P) hPre hR
    (hCdef ▸ inConn_comp) hΔ
  have K3 : ∀ r, 1100 ≤ r → d₃.nreg r = d₂.nreg r := fun r hr =>
    Exec.nreg_of_wr e₃ (Stmt.wr_of_wmax (by have := pieceCall_wmax; omega))
  have KK3 : ∀ r, Kept r → d₃.nreg r = d₂.nreg r := hD.regs
  have hmarkC := fun (v : Fin N) (hv : v ∈ C) => pieceCall_ltComp (R := R) (w := w) hD hv
  have R19 : d₂.nreg 1019 = c.nreg 1019 := R2 1019 (by omega) (by omega)
  have F3 : ∀ a, (∀ v ∈ C, a ≠ c.nreg 1019 + v) → d₃.nmem a = d₂.nmem a := fun a ha =>
    hD.frame a fun j hj => by
      rw [R19]
      have hj' : j < (clist (ord N) C).length := by rw [length_clist_ord]; exact hj
      rw [lv_eq C hj']
      exact ha _ (by rw [← mem_clist mem_ord]; exact List.get_mem _ _)
  have F3' : ∀ a, (∀ v ∈ C, a ≠ c.nreg 1019 + v) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
      d₃.nmem a = d.nmem a := fun a h1 h2 => by rw [F3 a h1, m₂, hfr₁ a h2, m₀]
  have notmk : ∀ a, a < c.nreg 1019 → ∀ v ∈ C, a ≠ c.nreg 1019 + v := fun a ha v _ => by omega
  -- the registers after the piece
  have T : ∀ r, r < 1110 → r ≠ 1016 → Kept r → d₃.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [KK3 r h3, R2 r h1 h2]
  have g01 : d₃.nreg 1001 = 1 := by rw [T 1001 (by omega) (by omega) (Or.inl rfl)]; exact hl.one
  have g00 : d₃.nreg 0 = 0 := hD.zreg 0 (by omega)
  have g16 : d₃.nreg 1016 = #C := by rw [KK3 1016 (by unfold Kept; omega), b16]
  have g15 : d₃.nreg 1015 = c.nreg 1015 := T 1015 (by omega) (by omega) (by unfold Kept; omega)
  have g19 : d₃.nreg 1019 = c.nreg 1019 := T 1019 (by omega) (by omega) (by unfold Kept; omega)
  have g14 : d₃.nreg 1014 = c.nreg 1014 := T 1014 (by omega) (by omega) (by unfold Kept; omega)
  have g30 : d₃.nreg 1130 = 2 := by
    rw [K3 1130 (by omega), q₂ 1130 (by omega), hr₁ 1130 (by omega), q₀ 1130 (by omega)]
    exact env.two
  have big : ∀ r, 1100 ≤ r → r < 1110 → d₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [K3 r h1, R2 r h2 (by omega)]
  have g21 : d₃.nreg 1121 = hb := by
    rw [K3 1121 (by omega), q₂ 1121 (by omega), hr₁ 1121 (by omega), a21]
  -- the weights of the parts
  have hNW3 : N + 3 ≤ W := by omega
  obtain ⟨d₄, k₄, e₄, hw₄, a28, a29, q₄, m₄, hk₄⟩ := wPass_exec (P := P) (C := C) (w := w) hD.wb
    g01 g00 g16 g15 g19 g14 g30
    (fun j hj => by
      rw [F3 _ (notmk _ (by omega)), m₂]; exact hL₁ j hj)
    (fun v hv => by
      rw [F3 _ (notmk _ (by omega)), m₂, hfr₁ _ (Or.inl (by omega)), m₀,
        env.fr _ (by unfold Wz; omega)]; exact hl.wt v hv)
    (by omega) (by omega) (by omega) (by omega) hNW3
  have q4 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1117 → r ≠ 1118 → r ≠ 1119 → r ≠ 1128 →
      r ≠ 1129 → r ≠ 1131 → d₄.nreg r = d₃.nreg r := q₄
  obtain ⟨d₅, k₅, e₅, hw₅, a26, q₅, m₅, hk₅⟩ := selPass_exec (P := P) hw₄
    (by rw [q4 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), g01]) (by omega)
  have R5 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1117 → r ≠ 1118 → r ≠ 1119 → r ≠ 1128 →
      r ≠ 1129 → r ≠ 1131 → r ≠ 1126 → d₅.nreg r = d₃.nreg r := fun r a b c' e g h k l m =>
    by rw [q₅ r m, q4 r a b c' e g h k l]
  set sel := if d₄.nreg 1128 ≤ d₄.nreg 1129 then 1 else 2 with hsel
  obtain ⟨d₆, k₆, e₆, hw₆, hmk₆, hfr₆, q₆, hk₆⟩ := rPass_exec (P := P) (U := U) hw₅
    (aU := c.nreg 1100) (aC := c.nreg 1102) (aM := c.nreg 1019) (hb := hb) (sel := sel)
    (by rw [R5 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), g01])
    (by rw [R5 1100 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), big 1100 (by omega) (by omega)])
    (by rw [R5 1102 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), big 1102 (by omega) (by omega)])
    (by rw [R5 1019 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), g19])
    (by rw [R5 1101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), big 1101 (by omega) (by omega)]; exact hl.uu)
    (by rw [R5 1121 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), g21]) a26
    (fun j hj => by
      rw [m₅, m₄, F3' _ (notmk _ (by omega)) (Or.inl (by omega)),
        env.fr _ (by unfold Wz; omega)]; exact hl.ul j hj)
    (by omega) (by omega) (by omega)
  -- the separation of the piece
  obtain ⟨hsep, -, -, -⟩ := ltComp_spec R hR mem_ord C w (hCdef ▸ inConn_comp) ⟨vF, hvC⟩
  set S := (ltComp R (ord N) C w).1
  set A := (ltComp R (ord N) C w).2.1
  set B := (ltComp R (ord N) C w).2.2
  have hSC : S ⊆ C := fun v hv => hsep.union_eq ▸ mem_union_left _ (mem_union_left _ hv)
  have hAC : A ⊆ C := fun v hv => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hv)
  have hBC : B ⊆ C := fun v hv => hsep.union_eq ▸ mem_union_right _ hv
  have hmk : ∀ v ∈ C, (d₃.nmem (c.nreg 1019 + v) = 0 ↔ v ∈ S) ∧
      (d₃.nmem (c.nreg 1019 + v) = 1 ↔ v ∈ A) ∧ (d₃.nmem (c.nreg 1019 + v) = 2 ↔ v ∈ B) :=
    fun v hv => by rw [← R19]; exact hmarkC v hv
  have hwA : d₄.nreg 1128 = ∑ v ∈ A, w v := by
    rw [a28]; exact wMk_eq hAC _ 1 fun v hv => (hmk v hv).2.1
  have hwB : d₄.nreg 1129 = ∑ v ∈ B, w v := by
    rw [a29]; exact wMk_eq hBC _ 2 fun v hv => (hmk v hv).2.2
  have hcs : compSep G (ltComp R (ord N)) (ord N) U w =
      if ∑ u ∈ A, w u ≤ ∑ u ∈ B, w u then (S, A ∪ (U \ C), B) else (S, A, B ∪ (U \ C)) := by
    unfold compSep
    rw [heavyC_some hlU hhv hmin, ← hvF]
    subst hCdef
    rfl
  have hlabv : ∀ v : Fin N, d₅.nmem (c.nreg 1102 + v) = labF c d v := fun v => by
    rw [m₅, m₄, F3' _ (notmk _ (by omega)) (Or.inl (by omega))]; rfl
  have hmark6 : ∀ v ∈ U, d₆.nmem (c.nreg 1019 + v) =
      if v ∈ C then d₃.nmem (c.nreg 1019 + v) else sel := fun v hv => by
    rw [hmk₆ v v.2, hlabv]
    by_cases hvC' : v ∈ C
    · rw [iteT hvC', iteF (fun h => h.2 ((hC v (val_mem_UN.2 hv)).1 hvC')), m₅, m₄]
    · rw [iteF hvC', iteT ⟨val_mem_UN.2 hv, fun h => hvC' ((hC v (val_mem_UN.2 hv)).2 h)⟩]
  have hsel : sel = if ∑ u ∈ A, w u ≤ ∑ u ∈ B, w u then 1 else 2 := by rw [hsel, hwA, hwB]
  refine ⟨d₆, _, .seq e₀ (.seq e₁ (.seq e2 (.seq e₃ (.seq e₄ (.seq e₅ e₆))))), hw₆, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- the marks
    intro v hv
    rw [hcs, hmark6 v hv]
    by_cases hvC' : v ∈ C
    · rw [iteT hvC']
      split_ifs <;> simp only [mem_union, mem_sdiff, hvC', not_true_eq_false, and_false,
        or_false] <;> exact hmk v hvC'
    · rw [iteF hvC', hsel]
      have h1 : v ∉ S := fun h => hvC' (hSC h)
      have h2 : v ∉ A := fun h => hvC' (hAC h)
      have h3 : v ∉ B := fun h => hvC' (hBC h)
      split_ifs <;> simp [h1, h2, h3, hv, hvC']
  · -- the frame
    intro a ha hL
    by_cases hM : c.nreg 1019 ≤ a ∧ a < c.nreg 1019 + N
    · obtain ⟨x, rfl⟩ : ∃ x, a = c.nreg 1019 + x := ⟨a - c.nreg 1019, by omega⟩
      have hxN : x < N := by omega
      have hxU : x ∉ UN U := fun h => by
        obtain ⟨_, hxU⟩ := mem_UN.1 h
        exact ha ⟨x, hxN⟩ hxU rfl
      rw [hmk₆ x hxN, iteF (fun h => hxU h.1), m₅, m₄]
      refine F3' _ (fun v hv e => ?_) hL
      have : (v : ℕ) = x := by omega
      exact hxU (this ▸ val_mem_UN.2 (hCU hv))
    · rw [hfr₆ a (by omega), m₅, m₄]
      exact F3' _ (fun v _ e => hM (by have := v.2; omega)) hL
  · -- the registers
    intro r hr
    unfold KeptC at hr
    rw [q₆ r (by omega) (by omega) (by omega) (by omega), R5 r (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hr with hr | hr | hr | hr | hr
    · rw [hD.zreg r hr, f r (by omega), hp.zreg r hr]
    · rw [T r (by omega) (by omega) (Or.inl hr), f r (by omega)]
    · rw [T r (by omega) (by omega) (by unfold Kept; omega), f r (by omega)]
    · rw [T r (by omega) (by omega) (by unfold Kept; omega), f r (by omega)]
    · rw [big r (by omega) (by omega), f r (by omega)]
  · have e' := (Exec.seq e₄ (Exec.seq e₅ e₆) : Exec P W (.seq wPass (.seq selPass rPass)) d₃ d₆ _)
    rw [(Exec.real_of_noReal e' (by decide)).1, hD.rr, he₂]; simp only; rw [rr₁]
  · have e' := (Exec.seq e₄ (Exec.seq e₅ e₆) : Exec P W (.seq wPass (.seq selPass rPass)) d₃ d₆ _)
    rw [(Exec.real_of_noReal e' (by decide)).2, hD.rm, he₂]; simp only; rw [rm₁]
  · have e' := (Exec.seq e₄ (Exec.seq e₅ e₆) : Exec P W (.seq wPass (.seq selPass rPass)) d₃ d₆ _)
    rw [Exec.output_of_ou e' (by decide), hD.out, he₂]; simp only; rw [ou₁]
  · have hdeg : ∑ v ∈ C, G.degree v ≤ ∑ v ∈ U, G.degree v :=
      sum_le_sum_of_subset_of_nonneg hCU fun _ _ _ => Nat.zero_le _
    have h1 := Nat.mul_le_mul_left (6 * Δ + 3400) hdeg
    have h2 := card_le_card hCU
    omega


/-! ### The light case -/

theorem mkL_one_iff (lab sn : ℕ → ℕ) (M kj x : ℕ) : mkL lab sn M kj x = 1 ↔
    (0 < M ∧ lab x - 1 = kj) ∨ (¬ 0 < M ∧ 0 < sn (lab x - 1)) := by
  unfold mkL; split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by omega) h

theorem mkL_cases (lab sn : ℕ → ℕ) (M kj x : ℕ) : mkL lab sn M kj x = 1 ∨ mkL lab sn M kj x = 2 := by
  unfold mkL; split_ifs <;> simp

/-- **The light case**: the scan, the mode, the marks. -/
def dLight : Stmt := .seq scanP (.seq modeP mPass)

theorem light_exec {R : Kasteleyn.RotationSystem G} {nc : ℕ} {c d : Config}
    (hl : CLay G U w W c) (env : Env N W c d) (hB : BInv G U w #U nc (labF c d) (cwF c d))
    (hnone : ∀ l < #U, ¬ hv G U w l) (h20 : d.nreg 1120 = ∑ v ∈ U, w v) :
    ∃ d' k, Exec P W dLight d d' k ∧ WordsBounded W d' ∧
      MarkOK G R w U (c.nreg 1019) d'.nmem ∧
      (∀ a, (∀ v ∈ U, a ≠ c.nreg 1019 + v) → (∀ j ≤ N, a ≠ c.nreg 1105 + j) →
        d'.nmem a = d.nmem a) ∧
      (∀ j ≤ N, d'.nmem (c.nreg 1105 + j) ≠ 0 → ∃ x ∈ UN U, labF c d x = j + 1) ∧
      (∀ r, KeptC r → d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      d'.output = d.output ∧ k ≤ 41 * #U + 21 := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hUN := card_le_N U
  have hsw := hl.sw
  have f := env.fix
  obtain ⟨d₁, k₁, e₁, hw₁, hr₁, hok, hfr₁, hk₁⟩ := scanP_exec (P := P) hl env hB h20
  set sn := fun j => d₁.nmem (c.nreg 1105 + j)
  have hlab₁ : ∀ x < N, d₁.nmem (c.nreg 1102 + x) = labF c d x := fun x hx =>
    hfr₁ _ (Or.inl (by omega))
  -- the result of the scan
  obtain ⟨hkj, hres⟩ : d₁.nreg 1134 ≤ N ∧
      ((0 < (∑ v ∈ U, w v) ∧ ∃ l < #U, (∀ l' < l, 3 * wt w (pU G U (l' + 1)) < (∑ v ∈ U, w v)) ∧
        (∑ v ∈ U, w v) ≤ 3 * wt w (pU G U (l + 1)) ∧ d₁.nreg 1134 = labF c d (lv U l) - 1 ∧
        SeenAt (labF c d) sn (pU G U (l + 1))) ∨
      ((∑ v ∈ U, w v) = 0 ∧ d₁.nreg 1134 = 0 ∧ SeenAt (labF c d) sn (∅ : Finset (Fin N)))) := by
    rcases hok with ⟨hpos, -, -, hbelow, -, -⟩ | ⟨hpos, -, l, -, hl, hmin, hcross, hkj, hS⟩ |
      ⟨h0, -, hkj, hS⟩
    · exfalso
      have hU0 : 0 < #U := by
        rcases Nat.eq_zero_or_pos #U with h | h
        · rw [card_eq_zero] at h; simp [h, wt] at hpos
        · exact h
      have := hbelow (#U - 1) (by omega)
      rw [show #U - 1 + 1 = #U by omega, pU_all] at this
      omega
    · refine ⟨?_, Or.inl ⟨hpos, l, hl, hmin, hcross, hkj, hS⟩⟩
      rw [hkj]; have := hB.lab_le (lv_mem_UN U hl); omega
    · exact ⟨by omega, Or.inr ⟨h0, hkj, hS⟩⟩
  -- the mode
  have g01 : d₁.nreg 1001 = 1 := by rw [hr₁ 1001 (by omega), f 1001 (by omega)]; exact hl.one
  have g00 : d₁.nreg 0 = 0 := by rw [hr₁ 0 (by omega), f 0 (by omega)]; exact hl.r0
  have g04 : d₁.nreg 1104 = c.nreg 1104 := by rw [hr₁ 1104 (by omega), f 1104 (by omega)]
  have g20 : d₁.nreg 1120 = (∑ v ∈ U, w v) := by rw [hr₁ 1120 (by omega)]; exact h20
  have hcwk : d₁.nmem (c.nreg 1104 + d₁.nreg 1134) = cwF c d (d₁.nreg 1134) :=
    hfr₁ _ (Or.inl (by omega))
  have hcwle : cwF c d (d₁.nreg 1134) ≤ (∑ v ∈ U, w v) := by
    rcases hres with ⟨-, l, hl, -, -, hkj', -⟩ | ⟨-, hkj', -⟩
    · rw [hkj', hB.wt _ (lv_mem_UN U hl) (hB.final (lv_mem_UN U hl)), ← sum_UN]
      exact sum_le_sum_of_subset_of_nonneg cN_subset fun _ _ _ => Nat.zero_le _
    · rw [hkj', hB.cz 0 (Nat.zero_le _) (Or.inl rfl)]; exact Nat.zero_le _
  obtain ⟨d₂, k₂, e₂, hw₂, a35, q₂, m₂, hk₂⟩ := modeP_exec (P := P) hw₁ rfl g04 g20 g01 g00
    (by omega) (by rw [hcwk]; omega)
  rw [hcwk] at a35
  -- the marks
  have q2 : ∀ r, r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1135 → d₂.nreg r = d₁.nreg r := q₂
  have R2 : ∀ r < 1110, d₂.nreg r = c.nreg r := fun r hr => by
    rw [q2 r (by omega) (by omega) (by omega) (by omega), hr₁ r (Or.inl hr), f r hr]
  obtain ⟨d₃, k₃, e₃, hw₃, hmk₃, hfr₃, q₃, hk₃⟩ := mPass_exec (P := P) (U := U) hw₂
    (aU := c.nreg 1100) (aC := c.nreg 1102) (aS := c.nreg 1105) (aM := c.nreg 1019)
    (R2 1001 (by omega) ▸ hl.one) (R2 0 (by omega) ▸ hl.r0) (R2 1100 (by omega))
    (R2 1102 (by omega)) (R2 1105 (by omega)) (R2 1019 (by omega))
    (R2 1101 (by omega) ▸ hl.uu) a35
    (by rw [q2 1134 (by omega) (by omega) (by omega) (by omega)])
    (by rw [q2 1130 (by omega) (by omega) (by omega) (by omega), hr₁ 1130 (by omega)];
        exact env.two)
    (fun j hj => by rw [m₂, hfr₁ _ (Or.inl (by omega)), env.fr _ (by unfold Wz; omega)];
                    exact hl.ul j hj)
    (by omega) (by omega) (by omega) (by omega)
    (fun x hx => by rw [m₂, hlab₁ x (lt_of_mem_UN hx)]; exact hB.lab_le hx)
  have hlab₂ : ∀ x < N, d₂.nmem (c.nreg 1102 + x) = labF c d x := fun x hx => by
    rw [m₂, hlab₁ x hx]
  have hsn₂ : ∀ j, d₂.nmem (c.nreg 1105 + j) = sn j := fun j => by rw [m₂]
  -- the first part
  have key : ∀ v ∈ U, (mkL (fun y => d₂.nmem (c.nreg 1102 + y)) (fun j => d₂.nmem (c.nreg 1105 + j))
      (d₂.nreg 1135) (d₁.nreg 1134) v = 1 ↔ v ∈ lightA G (ord N) U w) := by
    intro v hv
    rw [mkL_one_iff]
    simp only [hlab₂ v v.2, hsn₂]
    have h2v := hB.final (val_mem_UN.2 hv)
    rcases hres with ⟨hpos, l, hl, hmin, hcross, hkj', hS⟩ | ⟨h0, hkj', hS⟩
    · have hl' : l < (ul U).length := by rw [ul_length]; exact hl
      have hla := lightA_eq U w (G := G) hl' hpos hcross hmin
      have hlv : lv U l = ((ul U)[l] : ℕ) := lv_ul U hl'
      have hxU := ul_mem U hl'
      have h2l := hB.final (lv_mem_UN U hl)
      have hk1 : 1 ≤ d₁.nreg 1134 := by rw [hkj']; omega
      have hcwv : cwF c d (d₁.nreg 1134) = ∑ u ∈ comp G U (ul U)[l], w u := by
        rw [hkj', hB.wt _ (lv_mem_UN U hl) h2l, hlv, sum_cN]
      rw [hla]
      by_cases hth : ∑ u ∈ U, w u ≤ 3 * ∑ u ∈ comp G U (ul U)[l], w u
      · have hM : d₂.nreg 1135 = 1 := by rw [a35, hcwv, iteT ⟨by omega, hth⟩]
        rw [iteT hth, hM, ← hB.lab_eq_iff hxU hv, ← hlv, hkj']
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
        · intro h; exact Or.inl ⟨by omega, by omega⟩
      · have hM : d₂.nreg 1135 = 0 := by rw [a35, hcwv, iteF (fun h => hth h.2)]
        have hsv := hS.seen_iff hB hv
        rw [iteF hth, hM, hsv]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · omega
          · by_contra h'; rw [iteF h'] at h; omega
        · intro h; exact Or.inr ⟨by omega, by rw [iteT h]; omega⟩
    · rw [lightA_zero U w h0]
      have hM : d₂.nreg 1135 = 0 := by rw [a35, hkj', iteF (by omega)]
      have hsv : sn (labF c d v - 1) = 0 := by
        rw [hS _ (by have := hB.lab_le (val_mem_UN.2 hv); omega)]; simp
      rw [hM, hsv]
      simp
  have hcs : compSep G (ltComp R (ord N)) (ord N) U w =
      (∅, lightA G (ord N) U w, U \ lightA G (ord N) U w) := by
    unfold compSep
    rw [heavyC_none hnone]
  have e := (Exec.seq e₁ (Exec.seq e₂ e₃) : Exec P W dLight d d₃ _)
  refine ⟨d₃, _, e, hw₃, fun v hv => ?_, fun a ha hb => ?_, fun j hj hne => ?_, fun r hr => ?_,
    (Exec.real_of_noReal e (by decide)).1, (Exec.real_of_noReal e (by decide)).2,
    Exec.output_of_ou e (by decide), by omega⟩
  · rw [hcs, hmk₃ v v.2, iteT (val_mem_UN.2 hv), ← a35]
    have hk := key v hv
    have hc := mkL_cases (fun y => d₂.nmem (c.nreg 1102 + y)) (fun j => d₂.nmem (c.nreg 1105 + j))
      (d₂.nreg 1135) (d₁.nreg 1134) v
    simp only [notMem_empty, iff_false, mem_sdiff, hv, true_and]
    refine ⟨by omega, hk, ?_⟩
    rw [← hk]
    omega
  · by_cases hM : c.nreg 1019 ≤ a ∧ a < c.nreg 1019 + N
    · obtain ⟨x, rfl⟩ : ∃ x, a = c.nreg 1019 + x := ⟨a - c.nreg 1019, by omega⟩
      have hxN : x < N := by omega
      have hxU : x ∉ UN U := fun h => by
        obtain ⟨_, hxU⟩ := mem_UN.1 h
        exact ha ⟨x, hxN⟩ hxU rfl
      rw [hmk₃ x hxN, iteF hxU, m₂, hfr₁ _ (Or.inr (by omega))]
    · rw [hfr₃ a (by omega), m₂, hfr₁ a (by
        by_contra h'; exact hb (a - c.nreg 1105) (by omega) (by omega))]
  · rw [hfr₃ _ (Or.inl (by omega)), hsn₂] at hne
    rcases hres with ⟨-, l, -, -, -, -, hS⟩ | ⟨-, -, hS⟩
    · rw [hS j hj] at hne
      split_ifs at hne with h
      · obtain ⟨y, hy, e⟩ := h; exact ⟨y, val_mem_UN.2 (pU_subset U _ hy), e⟩
      · exact absurd rfl hne
    · rw [hS j hj] at hne; simp at hne
  · unfold KeptC at hr
    rw [q₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q2 r (by omega) (by omega) (by omega) (by omega), hr₁ r (by omega)]

/-! ### The program -/

/-- **The separator of the components on the machine.** -/
def compSepProg : Stmt := .seq front (.seq (.ifLtN 0 1123 dHeavy dLight) cleanP)

theorem sum_dg (U : Finset (Fin N)) : ∑ x ∈ UN U, dg G x = ∑ v ∈ U, G.degree v := by
  unfold UN dg
  rw [sum_map]
  refine sum_congr rfl fun v _ => ?_
  simp only [Fin.valEmbedding_apply, gofs_succ]
  omega

variable (G) in
/-- **The state after the separator of the components**: the kept registers, the marks
`MarkOK`, the memory as at the start except the marks of `U`, the list area and the queue. -/
structure CDone (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (U : Finset (Fin N)) (W : ℕ)
    (c d : Config) : Prop where
  wb : WordsBounded W d
  regs : ∀ r, KeptC r → d.nreg r = c.nreg r
  mark : MarkOK G R w U (c.nreg 1019) d.nmem
  frame : ∀ a, (∀ v ∈ U, a ≠ c.nreg 1019 + v) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
    (a < c.nreg 1103 ∨ c.nreg 1103 + N ≤ a) → d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

/-- **The separator of the components on the machine**: from `CPre` (a plane rotation system
`R` of `G` of maximum degree at most `Δ`, the sorted list of `U`), `compSepProg` runs to the
state `CDone` (the marks `0`, `1`, `2` of the three parts of
`compSep G (ltComp R (ord N)) (ord N) U w`) within
`2400 #U + (6 Δ + 3415) ∑_{v ∈ U} deg v + 12 ∑_{v ∈ U} w v + 5400` steps. -/
theorem compSepProg_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {Z : ℕ} {c : Config} (hp : CPre G R w U Z W c) :
    ∃ d k, Exec P W compSepProg c d k ∧
      k ≤ 2400 * #U + (6 * Δ + 3415) * ∑ v ∈ U, G.degree v + 12 * ∑ v ∈ U, w v + 5400 ∧
      CDone G R w U W c d := by
  have hl := hp.lay
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hUN := card_le_N U
  obtain ⟨d₁, k₁, e₁, env₁, ⟨nc, hB, hok⟩, h20, rr₁, rm₁, ou₁, hk₁⟩ := front_exec (P := P) hl
  have f := env₁.fix
  have hsn₁ : ∀ j ≤ N, d₁.nmem (c.nreg 1105 + j) = 0 := fun j hj => by
    rw [env₁.fr _ (by unfold Wz; omega)]; exact hl.sn j hj
  -- the middle
  obtain ⟨d₂, k₂, e₂, hw₂, hmark₂, hfr₂, hsn₂, hreg₂, rr₂, rm₂, ou₂, hk₂⟩ : ∃ d₂ k₂,
      Exec P W (.ifLtN 0 1123 dHeavy dLight) d₁ d₂ k₂ ∧ WordsBounded W d₂ ∧
      MarkOK G R w U (c.nreg 1019) d₂.nmem ∧
      (∀ a, (∀ v ∈ U, a ≠ c.nreg 1019 + v) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
        (∀ j ≤ N, a ≠ c.nreg 1105 + j) → d₂.nmem a = d₁.nmem a) ∧
      (∀ j ≤ N, d₂.nmem (c.nreg 1105 + j) ≠ 0 → ∃ x ∈ UN U, labF c d₁ x = j + 1) ∧
      (∀ r, KeptC r → d₂.nreg r = d₁.nreg r) ∧ d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧
      d₂.output = d₁.output ∧
      k₂ ≤ 2200 * #U + (6 * Δ + 3400) * ∑ v ∈ U, G.degree v + 12 * ∑ v ∈ U, w v +
        41 * #U + 5332 := by
    have g00 : d₁.nreg 0 = 0 := by rw [f 0 (by omega)]; exact hl.r0
    rcases hok with ⟨h0, hnone⟩ | ⟨l, hlU, hhv, hmin, hid, h1⟩
    · obtain ⟨d₂, k₂, e₂, hw₂, hm₂, hfr₂, hsn₂, hreg₂, rr₂, rm₂, ou₂, hk₂⟩ :=
        light_exec (P := P) (R := R) hl env₁ hB hnone h20
      exact ⟨d₂, _, .ifLtN_false (by rw [g00, h0]; omega) e₂, hw₂, hm₂,
        fun a h1 _ h3 => hfr₂ a h1 h3, hsn₂, hreg₂, rr₂, rm₂, ou₂, by omega⟩
    · obtain ⟨d₂, k₂, e₂, hw₂, hm₂, hfr₂, hreg₂, rr₂, rm₂, ou₂, hk₂⟩ :=
        heavy_exec (P := P) hR hΔ hp env₁ hB hlU hhv hmin hid (rr₁.trans rfl) rm₁
      refine ⟨d₂, _, .ifLtN_true (by rw [g00]; omega) e₂, hw₂, hm₂,
        fun a h1 h2 _ => hfr₂ a h1 h2, fun j hj hne => ?_, hreg₂, rr₂, rm₂, ou₂, by omega⟩
      rw [hfr₂ _ (fun v _ => by omega) (Or.inl (by omega)), hsn₁ j hj] at hne
      exact absurd rfl hne
  -- the cleanup
  have K : ∀ r, KeptC r → d₂.nreg r = c.nreg r := fun r hr => by
    rw [hreg₂ r hr, f r (by unfold KeptC at hr; omega)]
  have hm2 : ∀ a, (∀ v ∈ U, a ≠ c.nreg 1019 + v) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
      (∀ j ≤ N, a ≠ c.nreg 1105 + j) → ¬ Wz (N := N) c a → d₂.nmem a = c.nmem a :=
    fun a h1 h2 h3 h4 => by rw [hfr₂ a h1 h2 h3, env₁.fr a h4]
  have hlab₂ : ∀ x < N, d₂.nmem (c.nreg 1102 + x) = labF c d₁ x := fun x hx =>
    hfr₂ _ (fun v _ => by omega) (Or.inl (by omega)) (fun j _ => by omega)
  obtain ⟨d₃, k₃, e₃, hw₃, hC₃, hW₃, hS₃, hfr₃, hr₃, hk₃⟩ := cleanP_exec (P := P) (U := U) hw₂
    (aU := c.nreg 1100) (aC := c.nreg 1102) (aW := c.nreg 1104) (aS := c.nreg 1105)
    (by rw [K 1001 (by unfold KeptC; omega)]; exact hl.one)
    (by rw [K 0 (by unfold KeptC; omega)]; exact hl.r0)
    (K 1100 (by unfold KeptC; omega)) (K 1102 (by unfold KeptC; omega))
    (K 1104 (by unfold KeptC; omega)) (K 1105 (by unfold KeptC; omega))
    (by rw [K 1101 (by unfold KeptC; omega)]; exact hl.uu)
    (fun j hj => by
      rw [hm2 _ (fun v _ => by omega) (Or.inl (by omega)) (fun i _ => by omega)
        (by unfold Wz; omega)]; exact hl.ul j hj)
    (by omega) (by omega) (by omega) (by omega)
    (fun x hx => by
      rw [hlab₂ x (lt_of_mem_UN hx)]
      exact ⟨by have := hB.final hx; omega, hB.lab_le hx⟩)
    (fun x hx hxU => by rw [hlab₂ x hx]; exact hB.out x hx hxU)
    (fun j hj h => by
      rcases h with h | h
      · rw [hfr₂ _ (fun v _ => by omega) (Or.inl (by omega)) (fun i _ => by omega)] at h
        have h' : ¬ (j = 0 ∨ nc < j) := fun h'' => h (hB.cz j hj h'')
        obtain ⟨x, hx, e⟩ := hB.surj j (by omega) (by omega)
        exact ⟨x, hx, by rw [hlab₂ x (lt_of_mem_UN hx)]; exact e⟩
      · obtain ⟨x, hx, e⟩ := hsn₂ j hj h
        exact ⟨x, hx, by rw [hlab₂ x (lt_of_mem_UN hx)]; exact e⟩)
  have e := (Exec.seq e₁ (Exec.seq e₂ e₃) : Exec P W compSepProg c d₃ _)
  refine ⟨d₃, _, e, ?_, ⟨hw₃, fun r hr => ?_, fun v hv => ?_, fun a h1 h2 h3 => ?_, ?_, ?_, ?_⟩⟩
  · have hdg := sum_dg (G := G) U
    have hring : (6 * Δ + 3415) * ∑ v ∈ U, G.degree v =
        (6 * Δ + 3400) * ∑ v ∈ U, G.degree v + 15 * ∑ v ∈ U, G.degree v := by ring
    omega
  · rw [hr₃ r (by unfold KeptC at hr; omega) (by unfold KeptC at hr; omega)
      (by unfold KeptC at hr; omega) (by unfold KeptC at hr; omega), K r hr]
  · have hm : ∀ x < N, d₃.nmem (c.nreg 1019 + x) = d₂.nmem (c.nreg 1019 + x) := fun x hx =>
      hfr₃ _ (fun y _ => by omega) (fun j _ => by omega) (fun j _ => by omega)
    rw [hm v v.2]; exact hmark₂ v hv
  · by_cases hcid : c.nreg 1102 ≤ a ∧ a < c.nreg 1102 + N
    · obtain ⟨x, rfl⟩ : ∃ x, a = c.nreg 1102 + x := ⟨a - c.nreg 1102, by omega⟩
      rw [hC₃ x (by omega), hl.cid x (by omega)]
    by_cases hcw : c.nreg 1104 ≤ a ∧ a < c.nreg 1104 + N + 1
    · obtain ⟨x, rfl⟩ : ∃ x, a = c.nreg 1104 + x := ⟨a - c.nreg 1104, by omega⟩
      rw [hW₃ x (by omega), hl.cw x (by omega)]
    by_cases hsn : c.nreg 1105 ≤ a ∧ a < c.nreg 1105 + N + 1
    · obtain ⟨x, rfl⟩ : ∃ x, a = c.nreg 1105 + x := ⟨a - c.nreg 1105, by omega⟩
      rw [hS₃ x (by omega), hl.sn x (by omega)]
    rw [hfr₃ a (fun x hx => by omega) (fun j hj => by omega) (fun j hj => by omega)]
    exact hm2 a h1 h2 (fun j hj => by omega) (by unfold Wz; omega)
  · rw [Exec.output_of_ou e₃ (by decide), ou₂, ou₁]
  · rw [(Exec.real_of_noReal e₃ (by decide)).1, rr₂, rr₁]
  · rw [(Exec.real_of_noReal e₃ (by decide)).2, rm₂, rm₁]


end Piece

end PlanarSeparator
