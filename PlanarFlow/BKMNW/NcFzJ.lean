module

public import PlanarFlow.BKMNW.NcFzI
public import PlanarFlow.BKMNW.NcPbHyp

/-!
# The frame-level fix specification, the copy-back and `fzP`

**`FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf`**: given the MSSP call program's
specification on every map, for **any** plane map `M₀` (rotations and faces transitive) with a
*base frame* at `d` (`r9998`; `m` darts numbered by `en` with `EnumOK`, `RV`, `SG`) and a frame of
**`M₀.pendant e he`** at `d'` (`r3004`; `MFr`, `m'` darts, the first `m` being `inl (en i)`,
offset `Z'`, capacities `cap ≥ 0`, a pseudoflow `f₀`), the parts of a separator of `M₀` given in
the layout on the base numbering (**`SegsL`**, from `Gb = r6807`, part `j = r6800`), the heap
top `A0 = r3006`, the zero area `≤ Wz` of at least `wzf m' Z'` words and the room
`A0 + fxR m' Z' ≤ W`: the program `fixC` writes in the flow array of the pendant frame

  `Z' + fixPath (M₀.pendant e he) cap f₀ (πj.lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
     (negP (negMach (nsIds M₀ henum (en 0)) M₀ I))`

(the MSSP and the negative-length shortest paths **of the base map**, as `fixFrozen` uses them),
within `fxT m #faces(πj) k(πj)` steps, keeping the memory and the reals below `A0` off the flow
array, the zero area, the registers `PKeep` and the output.

**Why two frames**: `fixPos_exec`/`fixZero_exec` (frame-level in the call `x`)
leave `fixPath (pmap hP) … (negLay gid I x hP)`, the negative-length shortest paths *of the map of
the frame*. Run on a frame of the map with pendant edges, that is `negMach` on that map, which is
not `negP (negLay … of the piece map)`; the flows `s + cob χ` differ with the potentials `χ`
(they are not unique), so the value is not the `fixFrozen` that `FzPSpec'` pins. Moreover
`posT … m'` charges `mssp m' k` and `negsssp m'` for `m' ≤ 3m` darts, above `fixRun m …`.
Hence `fixC` must run the part of `fixP` with the MSSP call (`st2`) and the final negSSSP call
(`finP`'s `negStep_lay_exec`) on the base frame (`r9998`, indices `< m` = the `inl` darts of the
pendant frame) and the rest on the pendant frame; this is what `FixFrameSpec` states.

**The copy-back**: `cbA` (restores `r3004`, `r3006` and the layout registers from the
saved values at `S = r9804`), `cbP = cbA ; FF := FL' + Z ∸ Z' ; FF := Q·F1 + FF ∸ Q·FF`.
**`fzP fixC = pfP ; fxG ; fixC ; cbP`**, `fxG` sets `r3004 := d'`, `r9998 := d`,
`r3006 := d' + 4 + 7m'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv CombMap

/-- **The parts of a separator of `M₀` in the layout**, on the numbering `en` (`SegsOut'` with a
list of paths of `M₀`). -/
def SegsL {D V F : Type*} (M₀ : CombMap D V F) (en : ℕ → D) (m : ℕ) (segs : List (SPath M₀))
    (lo hi Gb : ℕ) (mem : ℕ → ℕ) : Prop :=
  lo ≤ Gb ∧ mem Gb = segs.length ∧ Gb + 1 + 3 * segs.length + (segs.map SPath.k).sum ≤ hi ∧
    ∀ (j : ℕ) (hj : j < segs.length),
      mem (Gb + 1 + j) = ((segs.take j).map SPath.k).sum ∧
      mem (Gb + 1 + segs.length + j) = (segs[j]).k ∧
      (∀ l < (segs[j]).k,
        mem (Gb + 1 + 2 * segs.length + ((segs.take j).map SPath.k).sum + l) < m ∧
        en (mem (Gb + 1 + 2 * segs.length + ((segs.take j).map SPath.k).sum + l)) =
          (segs[j]).d l) ∧
      mem (Gb + 1 + 2 * segs.length + (segs.map SPath.k).sum + j) < m ∧
      M₀.tail (en (mem (Gb + 1 + 2 * segs.length + (segs.map SPath.k).sum + j))) = (segs[j]).p 0

/-- **The frame-level specification of the frozen-fix program** (see the module docstring). -/
def FixFrameSpec (fixC msP : Stmt) (Scr : ℕ → Prop) (Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ)
    (C C₀ : ℕ) (fxT : ℕ → ℕ → ℕ → ℕ) (fxR wzf : ℕ → ℕ → ℕ) : Prop :=
    (∀ {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F']
      [DecidableEq F'] (M' : CombMap D' V' F'),
      MsCall.MsspCallSpec M' msP Scr (MsEnc.msCostS C C₀) Rm wzm) →
  ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M₀ : CombMap D V F), M₀.IsPlane → M₀.RotTrans → M₀.FaceTrans →
  ∀ (e : V → D) (he : ∀ v, M₀.tail (e v) = v) (I : Input) (W Wz m m' Z' d d' A0 lo hi Gb j : ℕ)
    (en : ℕ → D) (henum : NsStep.EnumOK M₀ en m) (en' : ℕ → D ⊕ (V × Bool))
    (segs : List (SPath M₀)) (hj : j < segs.length) (cap f₀ : D ⊕ (V × Bool) → ℤ) (c : Config),
    c.nmem d = m →
    (∀ i < m, c.nmem (d + 4 + m + i) < m ∧ en (c.nmem (d + 4 + m + i)) = M₀.rev (en i)) →
    (∀ i < m, c.nmem (d + 4 + 2 * m + i) < m ∧
      en (c.nmem (d + 4 + 2 * m + i)) = M₀.next (M₀.rev (en i))) →
    MFr (M₀.pendant e he) en' m' Z' cap f₀ d' c.nmem → (∀ i < m, en' i = .inl (en i)) →
    m ≤ m' → m' ≤ 3 * m → 0 < m →
    SegsL M₀ en m segs lo hi Gb c.nmem →
    IsPseudo (M₀.pendant e he) cap f₀ → (∀ y, 0 ≤ cap y) →
    c.nreg 3004 = d' → c.nreg 9998 = d → c.nreg 3006 = A0 → c.nreg 6807 = Gb →
    c.nreg 6800 = j →
    d + 4 + 3 * m ≤ A0 → d' + 4 + 7 * m' ≤ A0 → hi ≤ A0 → Wz < d → Wz < lo → Wz < d' →
    A0 + fxR m' Z' ≤ W → wzf m' Z' ≤ Wz → MemZ Wz c → WordsBounded W c →
    ∃ c' t, Exec I W fixC c c' t ∧ t ≤ fxT m (segs[j]).faces.card (segs[j]).k ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (NsStep.nsIds M₀ henum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a < A0, (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      MemZ Wz c' ∧ (∀ r, NcStep.PKeep r → c'.nreg r = c.nreg r) ∧ c'.output = c.output

/-! ### The programs -/

/-- The registers of the frozen-fix program: the pendant frame, the base frame, the heap top. -/
def fxG : Stmt := block [.copyN 3004 9971, .copyN 9998 9950, .copyN 3006 9979]

/-- The registers of the copy-back from the saved values (`S = r9804`), and `r3004`, `r3006`
restored. -/
def cbA : Stmt :=
  block [.copyN 9958 9804, .loadN 3004 9958, .constN 9940 1, .addN 9941 9958 9940,
    .loadN 3006 9941, .addN 9941 9941 9940, .loadN 9930 9941, .addN 9941 9941 9940,
    .loadN 9951 9941, .addN 9941 9941 9940, .loadN 9952 9941, .addN 9941 9941 9940,
    .loadN 9968 9941, .addN 9941 9941 9940, .loadN 9977 9941, .copyN 9956 9800,
    .copyN 9989 9803, .constN 9972 0]

/-- **The copy-back**: `FF := FL' + Z ∸ Z'`, then `FF := Q·F1 + FF ∸ Q·FF`. -/
def cbP : Stmt :=
  .seq cbA (.seq (lp 9977 9972 9989 9951 9952 9972 9930 bAk)
    (lp 9956 9968 9989 9972 9972 9989 9930 bMx))

/-- **The program of `fixFrozen`** with the frozen-fix program `fixC`. -/
def fzP (fixC : Stmt) : Stmt := .seq pfP (.seq fxG (.seq fixC cbP))

variable {P : Input} {W : ℕ}

theorem fxG_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W fxG c c' k ∧ k = 3 ∧ c'.nreg 3004 = c.nreg 9971 ∧
      c'.nreg 9998 = c.nreg 9950 ∧ c'.nreg 3006 = c.nreg 9979 ∧
      (∀ r, r ≠ 3004 → r ≠ 9998 → r ≠ 3006 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fxG
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try (simp (disch := omega) only [upd_other]))

set_option maxHeartbeats 1600000 in
theorem cbA_exec (c : Config) (hc : WordsBounded W c) {S : ℕ} (r04 : c.nreg 9804 = S)
    (w : S + 6 ≤ W) :
    ∃ c' k, Exec P W cbA c c' k ∧ k = 18 ∧ c'.nreg 9958 = S ∧ c'.nreg 3004 = c.nmem S ∧
      c'.nreg 3006 = c.nmem (S + 1) ∧ c'.nreg 9930 = c.nmem (S + 2) ∧
      c'.nreg 9951 = c.nmem (S + 3) ∧ c'.nreg 9952 = c.nmem (S + 4) ∧
      c'.nreg 9968 = c.nmem (S + 5) ∧ c'.nreg 9977 = c.nmem (S + 6) ∧
      c'.nreg 9956 = c.nreg 9800 ∧ c'.nreg 9989 = c.nreg 9803 ∧ c'.nreg 9972 = 0 ∧
      (∀ r, r ≠ 3004 → r ≠ 3006 → r ≠ 9930 → ¬ (9940 ≤ r ∧ r ≤ 9989) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cbA
  exec_block
  all_goals try ((try config_simp); (try simp only [r04]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals (try simp only [r04])
  all_goals (try (simp (disch := omega) only [upd_other]))
  all_goals (try (congr 1; omega))

set_option maxHeartbeats 1600000 in
/-- **The copy-back**: `FF[t] = Q·F1 + FF₁ ∸ Q·FF₁` with `FF₁ = FL'[t] + Z ∸ Z'`, i.e.
`F1` on the darts touching `Del` and the pendant run's value elsewhere; `r3004`, `r3006`
restored from the saved values. -/
theorem cbP_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W)
    {S d A0 m Z Qb FLb F1b FFb : ℕ} (r04 : c.nreg 9804 = S) (r00 : c.nreg 9800 = F1b)
    (r03 : c.nreg 9803 = FFb) (s0 : c.nmem S = d) (s1 : c.nmem (S + 1) = A0)
    (s2 : c.nmem (S + 2) = m) (s3 : c.nmem (S + 3) = Z) (s4 : c.nmem (S + 4) = m * Z)
    (s5 : c.nmem (S + 5) = Qb) (s6 : c.nmem (S + 6) = FLb)
    (lF : F1b + m ≤ S) (lFF : FFb + m ≤ S) (lFF' : F1b + m ≤ FFb ∨ FFb + m ≤ F1b)
    (lQ : S + 7 ≤ Qb) (lFL : S + 7 ≤ FLb) (wQ : Qb + m ≤ W) (wFL : FLb + m ≤ W)
    (hq : ∀ t < m, c.nmem (Qb + t) ≤ 1) (hf : ∀ t < m, c.nmem (F1b + t) ≤ 2 * Z)
    (hfl : ∀ t < m, c.nmem (FLb + t) + 3 * Z ≤ W) :
    ∃ c' k, Exec P W cbP c c' k ∧ k ≤ 24 * m + 40 ∧
      (∀ t < m, c'.nmem (FFb + t) = c.nmem (Qb + t) * c.nmem (F1b + t) +
        (c.nmem (FLb + t) + Z - m * Z) - c.nmem (Qb + t) * (c.nmem (FLb + t) + Z - m * Z)) ∧
      (∀ a, (a < FFb ∨ FFb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 3004 = d ∧ c'.nreg 3006 = A0 ∧
      (∀ r, r ≠ 3004 → r ≠ 3006 → ¬ (9920 ≤ r ∧ r ≤ 9999) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have wS : S + 6 ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, a58, a04, a06, a30, a51, a52, a68, a77, a56, a89, a72, g₁, m₁, rr₁,
    rm₁, o₁⟩ := cbA_exec (P := P) c hc r04 wS
  rw [s0] at a04; rw [s1] at a06; rw [s2] at a30; rw [s3] at a51; rw [s4] at a52
  rw [s5] at a68; rw [s6] at a77; rw [r00] at a56; rw [r03] at a89
  obtain ⟨c₂, k₂, e₂, hk₂, L₂⟩ := lp_exec (P := P) (xr := 9977) (yr := 9972) (or := 9989)
    (kr := 9951) (k2r := 9952) (rr := 9972) (bnd := 9930) (body := bAk) (O := FFb) (n := m)
    (B := 9 * m + 4) (val := fun t => c₁.nmem (FLb + t) + Z - m * Z) c₁ e₁.wb_right
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lAk_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := FLb) (O := FFb) (K := Z) (K₂ := m * Z)
        (by rw [g _ (by omega), a30]) (by unfold PfScr; omega) (by rw [a23, a77])
        (by rw [a25, a89]) (by rw [a26, a51]) (by rw [a27, a52]) (by omega) (by omega)
        (by omega) (fun t ht => by rw [hm', m₁]; have := hfl t ht; omega)
        (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)
  have q2 : ∀ r, ¬ LpScr r → c₂.nreg r = c₁.nreg r := L₂.reg
  obtain ⟨c₃, k₃, e₃, hk₃, L₃⟩ := lp_exec (P := P) (xr := 9956) (yr := 9968) (or := 9989)
    (kr := 9972) (k2r := 9972) (rr := 9989) (bnd := 9930) (body := bMx) (O := FFb) (n := m)
    (B := 15 * m + 4)
    (val := fun t => c₂.nmem (Qb + t) * c₂.nmem (F1b + t) + c₂.nmem (FFb + t) -
      c₂.nmem (Qb + t) * c₂.nmem (FFb + t)) c₂ e₂.wb_right
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      have hq' : ∀ t < m, c'.nmem (Qb + t) ≤ 1 := fun t ht => by
        rw [hm', L₂.mem _ (by omega), m₁]; exact hq t ht
      have hf' : ∀ t < m, c'.nmem (F1b + t) ≤ 2 * Z := fun t ht => by
        rw [hm', L₂.mem _ (by omega), m₁]; exact hf t ht
      have hff : ∀ t < m, c'.nmem (FFb + t) ≤ c.nmem (FLb + t) + Z := fun t ht => by
        rw [hm', L₂.val t ht, m₁]; omega
      obtain ⟨c'', k, ex, hk, hP⟩ := lMx_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := F1b) (Y := Qb) (O := FFb) (R := FFb)
        (by rw [g _ (by omega), q2 _ (by unfold LpScr; omega), a30]) (by unfold PfScr; omega)
        (by rw [a23, q2 _ (by unfold LpScr; omega), a56])
        (by rw [a24, q2 _ (by unfold LpScr; omega), a68])
        (by rw [a25, q2 _ (by unfold LpScr; omega), a89])
        (by rw [a29, q2 _ (by unfold LpScr; omega), a89]) (by omega) (by omega)
        (by omega) (by omega) (by omega)
        (fun t ht => by
          have := mul_le_of_le_one'' (a := c'.nmem (F1b + t)) (hq' t ht)
          have := hf' t ht; have := hff t ht; have := hfl t ht; omega)
        (fun t ht => by
          have := mul_le_of_le_one'' (a := c'.nmem (FFb + t)) (hq' t ht)
          have := hff t ht; have := hfl t ht; omega)
        (fun t ht j hj => by omega) (fun t ht j hj => by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)
  have q3 : ∀ r, ¬ LpScr r → c₃.nreg r = c₂.nreg r := L₃.reg
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, fun t ht => ?_, fun a ha => ?_,
    ?_, ?_, fun r h1 h2 h3 => ?_, by rw [L₃.rr, L₂.rr, rr₁], by rw [L₃.rm, L₂.rm, rm₁],
    by rw [L₃.out, L₂.out, o₁]⟩
  · rw [L₃.val t ht, L₂.val t ht, L₂.mem (Qb + t) (by omega), L₂.mem (F1b + t) (by omega), m₁]
  · rw [L₃.mem a ha, L₂.mem a ha, m₁]
  · rw [q3 _ (by unfold LpScr; omega), q2 _ (by unfold LpScr; omega), a04]
  · rw [q3 _ (by unfold LpScr; omega), q2 _ (by unfold LpScr; omega), a06]
  · rw [q3 _ (by unfold LpScr; omega), q2 _ (by unfold LpScr; omega), g₁ r h1 h2 (by omega)
      (by omega)]

end NcFz

end BKMNW

end PlanarFlow
