module

public import PlanarFlow.BKMNW.Nf7aP1

/-!
# The prologue of `fixP`, part 2: the marks and the corner walk

**`proP2`** `= fmkProg ; cwProg ; pinD`: from the state after part 1 (`RegP1`, the face walk
`NX`, the face labels `FL`, zero marks): the marks `ON = p.ON`, the corner walk
`MK[a] = p.cw.mks a`, `BT[x] = p.cw.bt x`, `r9419 = p.cw.cnt` (**`proP2_exec`**,
`≤ 19 k + 26 m + 16` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

/-- `fmk2` depends only on the marked places below `n` and on the start at the point. -/
lemma fmk2_congr {base base' x x' y y' : ℕ → ℕ} {n i : ℕ} (hx : ∀ l < n, x l = x' l)
    (hy : ∀ l < n, y l = y' l) (hb : base i = base' i) :
    fmk2 base x y n i = fmk2 base' x' y' n i := by
  rw [fmk2_eq, fmk2_eq, hb]
  have : (∃ l' < n, i = x l' ∨ i = y l') ↔ (∃ l' < n, i = x' l' ∨ i = y' l') :=
    ⟨fun ⟨l, hl, e⟩ => ⟨l, hl, by rw [← hx l hl, ← hy l hl]; exact e⟩,
      fun ⟨l, hl, e⟩ => ⟨l, hl, by rw [hx l hl, hy l hl]; exact e⟩⟩
  simp only [this]

lemma fmk2_le_one {x y : ℕ → ℕ} {n i : ℕ} : fmk2 (fun _ => 0) x y n i ≤ 1 := by
  rw [fmk2_eq]; split_ifs <;> omega

/-- `cwProg_exec` with the model functions given by equations. -/
theorem cwProg_exec' (c : Config) (hc : WordsBounded W c)
    {N m NXb SGb ONb FLb MKb BTb t₀b : ℕ}
    (r00 : c.nreg 9400 = N) (r02 : c.nreg 9402 = t₀b) (r04 : c.nreg 9404 = NXb)
    (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb)
    (r10 : c.nreg 9410 = BTb) (r31 : c.nreg 9431 = SGb) (hNm : N ≤ m)
    (ht₀ : c.nmem t₀b < m) (hMK : ∀ a ≤ m, c.nmem (MKb + a) ≤ 1)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m) (hNX : ∀ i < m, c.nmem (NXb + i) < m)
    (hSG : ∀ i < m, c.nmem (SGb + i) < m)
    (dMK : ∀ a, MKb ≤ a → a ≤ MKb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ a ≠ t₀b)
    (dBT : ∀ a, BTb ≤ a → a < BTb + m → (a < FLb ∨ FLb + m ≤ a) ∧ (a < ONb ∨ ONb + m ≤ a) ∧
      (a < NXb ∨ NXb + m ≤ a) ∧ (a < SGb ∨ SGb + m ≤ a) ∧ (a < MKb ∨ MKb + m < a))
    (hW : FLb + m + MKb + ONb + NXb + SGb + BTb + m + 3 ≤ W)
    {tt g mk0 : ℕ → ℕ} (htt : ∀ n, tt n = (twF NXb SGb ONb c.nmem)^[n] (c.nmem t₀b))
    (hg : ∀ n, g n = c.nmem (FLb + tt n))
    (hmk : ∀ a, mk0 a = if a ≤ m then c.nmem (MKb + a) else 0) :
    ∃ c' k, Exec P W cwProg c c' k ∧ k ≤ 26 * N + 10 ∧
      c'.nreg 9441 = tt N ∧ c'.nreg 9442 = (cwRun g tt mk0 N).cnt ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = (cwRun g tt mk0 N).mks a) ∧
      (∀ x < (cwRun g tt mk0 N).cnt, c'.nmem (BTb + x) = (cwRun g tt mk0 N).bt x) ∧
      (∀ a, ¬ (MKb ≤ a ∧ a ≤ MKb + m) → ¬ (BTb ≤ a ∧ a < BTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain rfl : tt = _ := funext htt
  obtain rfl : g = _ := funext hg
  obtain rfl : mk0 = _ := funext hmk
  exact cwProg_exec (P := P) c hc r00 r02 r04 r05 r06 r07 r10 r31 hNm ht₀ hMK hFL hNX hSG dMK dBT
    hW

/-- The iterates of the walk stay below `m`. -/
lemma FpIn.tt_lt (p : FpIn) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (h0 : p.PD 0 < p.m) : ∀ n, p.tt n < p.m
  | 0 => h0
  | n + 1 => by
    show p.tw^[n + 1] (p.PD 0) < p.m
    rw [Function.iterate_succ_apply']
    have := FpIn.tt_lt p hSG hNX h0 n
    unfold FpIn.tw
    split_ifs
    · exact hNX.lt _ this
    · exact hSG.lt _ this

/-- The marks, the corner walk and the number of corners. -/
def proP2 : Stmt := .seq fmkProg (.seq cwProg pinD)

set_option maxHeartbeats 1600000 in
/-- **The prologue, part 2, on the machine.** -/
theorem proP2_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (hR : RegP1 p A0 c) (hlo : ∀ a < A0, c.nmem a = p.mem a)
    (hNXm : ∀ i < p.m, c.nmem (A0 + i) = nxF p.d p.m p.mem i)
    (hFLm : ∀ i < p.m, c.nmem (A0 + p.m + i) = p.lab i)
    (hONm : ∀ i < p.m, c.nmem (A0 + p.m + p.m + i) = 0)
    (hMKm : ∀ a ≤ p.m, c.nmem (A0 + p.m + p.m + p.m + a) = 0)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hPD : ∀ l < p.k, p.PD l < p.m) (hk0 : 0 < p.k)
    (hfr : p.d + 4 + 7 * p.m ≤ A0) (hsg : p.PDb + p.k ≤ A0)
    (hW : 8 * (A0 + 9 * p.m + 2) + p.k ≤ W) :
    ∃ c' t, Exec P W proP2 c c' t ∧ t ≤ 19 * p.k + 26 * p.m + 16 ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + i) = p.ON i) ∧
      (∀ a ≤ p.m, c'.nmem (A0 + p.m + p.m + p.m + a) = p.cw.mks a) ∧
      (∀ x < p.cw.cnt, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + x) =
        p.cw.bt x) ∧
      c'.nreg 9419 = p.cw.cnt ∧
      (∀ a, ¬ (A0 + p.m + p.m ≤ a ∧ a < A0 + p.m + p.m + p.m) →
        ¬ (A0 + p.m + p.m + p.m ≤ a ∧ a ≤ A0 + p.m + p.m + p.m + p.m) →
        ¬ (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m ≤ a ∧
          a < A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m + p.m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9439 ∨ 9449 < r) → (r < 9450 ∨ 9455 < r) → r ≠ 9419 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, -⟩ := hR
  have hPDm : ∀ l < p.k, c.nmem (p.PDb + l) = p.PD l := fun l hl => hlo _ (by omega)
  have hRVm : ∀ i < p.m, c.nmem (p.d + 4 + p.m + i) = p.RV i := fun i hi => hlo _ (by omega)
  have hlab : ∀ i < p.m, p.lab i ≤ p.m := fun i hi => by
    have := olab_lt hNX hi; simp only [FpIn.lab]; omega
  -- marks
  obtain ⟨c₁, t₁, e₁, ht₁, mON, mMK, mk, mn, mr, mrm, mo⟩ :=
    fmkProg_exec (P := P) c hc (k := p.k) (m := p.m) (PDb := p.PDb) (RVb := p.d + 4 + p.m)
      (FLb := A0 + p.m) (ONb := A0 + p.m + p.m) (MKb := A0 + p.m + p.m + p.m) g01 g02 g05 g06
      g07 g30 g36 (fun l hl => by rw [hPDm l hl]; exact hPD l hl)
      (fun i hi => by rw [hRVm i hi]; exact hRV i hi)
      (fun i hi => by rw [hFLm i hi]; exact hlab i hi)
      (fun a ha => ⟨by omega, by omega, by omega⟩) (by omega) (by omega)
  have eON : ∀ i < p.m, c₁.nmem (A0 + p.m + p.m + i) = p.ON i := fun i hi => by
    rw [mON i hi]
    exact fmk2_congr (fun l hl => hPDm l hl)
      (fun l hl => by rw [hPDm l hl, hRVm _ (hPD l hl)]) (hONm i hi)
  have eMK : ∀ a ≤ p.m, c₁.nmem (A0 + p.m + p.m + p.m + a) = p.MK0 a := fun a ha => by
    rw [mMK a ha]
    simp only [FpIn.MK0, ha, ↓reduceIte]
    exact fmk2_congr (fun l hl => by rw [hPDm l hl, hFLm _ (hPD l hl)])
      (fun l hl => by rw [hPDm l hl, hRVm _ (hPD l hl), hFLm _ (hRV _ (hPD l hl))]) (hMKm a ha)
  have k1 : ∀ a, (a < A0 + p.m + p.m ∨ A0 + p.m + p.m + p.m + p.m < a) → c₁.nmem a = c.nmem a :=
    fun a ha => mk a (by omega) (by omega)
  -- the walk
  have hsg1 : ∀ i < p.m, c₁.nmem (p.d + 4 + p.m + p.m + i) = sgF p.d p.m p.mem i := fun i hi => by
    rw [k1 _ (Or.inl (by omega)), hlo _ (by omega)]; simp only [sgF]; congr 1; ring
  have hnx1 : ∀ i < p.m, c₁.nmem (A0 + i) = nxF p.d p.m p.mem i := fun i hi => by
    rw [k1 _ (Or.inl (by omega)), hNXm i hi]
  have htw : ∀ i < p.m, twF A0 (p.d + 4 + p.m + p.m) (A0 + p.m + p.m) c₁.nmem i = p.tw i :=
    fun i hi => by
      simp only [twF, FpIn.tw, eON i hi, hnx1 i hi, hsg1 i hi]
  have h0 : p.PD 0 < p.m := hPD 0 hk0
  have htt := FpIn.tt_lt p hSG hNX h0
  have e0 : c₁.nmem p.PDb = p.PD 0 := by rw [k1 _ (Or.inl (by omega)), ← hPDm 0 hk0]; rfl
  have hit : ∀ n, p.tt n = (twF A0 (p.d + 4 + p.m + p.m) (A0 + p.m + p.m) c₁.nmem)^[n]
      (c₁.nmem p.PDb) := fun n => by
    rw [e0]
    exact (iter_congr_on (fun i hi => (htw i hi).symm)
      (fun i hi => by unfold FpIn.tw; split_ifs
                      · exact hNX.lt _ hi
                      · exact hSG.lt _ hi) n _ h0)
  have n1 : ∀ r, (r < 9450 ∨ 9455 < r) → c₁.nreg r = c.nreg r := mn
  obtain ⟨c₂, t₂, e₂, ht₂, w41, w42, wMK, wBT, wk, wn, wr, wrm, wo⟩ :=
    cwProg_exec' (P := P) c₁ e₁.wb_right (N := p.m) (m := p.m) (NXb := A0)
      (SGb := p.d + 4 + p.m + p.m) (ONb := A0 + p.m + p.m) (FLb := A0 + p.m)
      (MKb := A0 + p.m + p.m + p.m) (BTb := A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m)
      (t₀b := p.PDb) (by rw [n1 _ (by omega), g00]) (by rw [n1 _ (by omega), g02])
      (by rw [n1 _ (by omega), g04]) (by rw [n1 _ (by omega), g05])
      (by rw [n1 _ (by omega), g06]) (by rw [n1 _ (by omega), g07])
      (by rw [n1 _ (by omega), g10]) (by rw [n1 _ (by omega), g31]) le_rfl (by rw [e0]; exact h0)
      (fun a ha => by rw [eMK a ha]; simp only [FpIn.MK0, ha, ↓reduceIte]; exact fmk2_le_one)
      (fun i hi => by rw [k1 _ (Or.inl (by omega)), hFLm i hi]; exact hlab i hi)
      (fun i hi => by rw [hnx1 i hi]; exact hNX.lt _ hi)
      (fun i hi => by rw [hsg1 i hi]; exact hSG.lt _ hi)
      (fun a h1 h2 => ⟨by omega, by omega, by omega, by omega, by omega⟩)
      (fun a h1 h2 => ⟨by omega, by omega, by omega, by omega, by omega⟩) (by omega)
      (tt := p.tt) (g := fun n => p.lab (p.tt n)) (mk0 := p.MK0) hit
      (fun n => by rw [k1 _ (Or.inl (by have := htt n; omega)), hFLm _ (htt n)])
      (fun a => by
        by_cases ha : a ≤ p.m
        · simp only [ha, ↓reduceIte]; exact (eMK a ha).symm
        · simp only [FpIn.MK0, ha, ↓reduceIte])
  have n2 : ∀ r, (r < 9439 ∨ 9449 < r) → c₂.nreg r = c₁.nreg r := wn
  obtain ⟨c₃, t₃, e₃, ht₃, d19, dk, dm, dr, drm, do'⟩ := pinD_exec (P := P) c₂ e₂.wb_right
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [d19, w42]; rfl, fun a h1 h2 h3 => ?_, fun r h1 h2 h3 => ?_, by rw [dr, wr, mr],
    by rw [drm, wrm, mrm], by rw [do', wo, mo]⟩
  · rw [dm, wk _ (by omega) (by omega)]; exact eON i hi
  · rw [dm, wMK a ha]; rfl
  · rw [dm, wBT x hx]; rfl
  · rw [dm, wk _ (by omega) h3, mk a h1 (by omega)]
  · rw [dk r h3, n2 r h1, n1 r h2]

end BKMNW

end PlanarFlow
