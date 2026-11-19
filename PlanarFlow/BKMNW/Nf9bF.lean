module

public import PlanarFlow.BKMNW.Nf9bE
public import PlanarFlow.BKMNW.Nf9bD

/-!
# Step 2 of the frozen fix — the MSSP call on the base map

After the prologue on the frame of the map with pendant edges (`ProOut` of `cIn d' m' Gb segs j
Z' mem`), `swB ; qbP ; st2 msP ; p7dG` runs step 2 (`st2_exec`, generic in the map) **on the
base map `M₀`**: `m` darts numbered by `en`, the reverse from the first `m` cells of the pendant
`RV` (`PCtx.rvE`), the rotation `SG` of the base frame, the path `segs[j]`, the lengths
`ℓ0 cap f₀ = (cap − f₀) ∘ inl` from the first `m` cells of the pendant `CL`, the query darts `QB`
of `qbP`. The answers are `DmY` (MSSP of the base map at the corners of the pendant walk), the data
of the stage loop on the pendant map is **`mkP`**.

* `pq_pd` (the path indices), **`st9_in`** (the inputs of step 2 in memory), **`st9_qb`** (the query
  darts: base indices on the corner faces), **`st9_fix`** (the fixed arrays and the first state),
  `st9_run` (`st2_exec` instantiated), **`st9_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep NcFz SPath
  WordRAM WordRAM.Machine WordRAM.Programs

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

section Ctx

variable (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
include H

/-- **The path indices** of the part: base indices of the darts of `segs[j]`. -/
lemma pq_pd {l : ℕ} (hl : l < (segs[j]'H.hj).k) :
    (cIn d' m' Gb segs j Z' mem).PD l < m ∧
      en ((cIn d' m' Gb segs j Z' mem).PD l) = (segs[j]'H.hj).d l ∧
      en' ((cIn d' m' Gb segs j Z' mem).PD l) = ((segs[j]'H.hj).lift e he).d l := by
  have h : (cIn d' m' Gb segs j Z' mem).PD l < m ∧
      en ((cIn d' m' Gb segs j Z' mem).PD l) = (segs[j]'H.hj).d l :=
    cIn_pd (d := d') (Z := Z') H.sl H.hj (l := l) (by rw [cIn_k H.hj]; exact hl)
  refine ⟨h.1, h.2, ?_⟩
  rw [H.hen _ h.1, h.2]; rfl

lemma pq_k : (cIn d' m' Gb segs j Z' mem).k = (segs[j]'H.hj).k := cIn_k H.hj

set_option maxHeartbeats 4000000 in
/-- **The inputs of step 2 in memory** after the prologue. -/
theorem st9_in (hk0 : 0 < (segs[j]'H.hj).k) {A0 W : ℕ}
    (hG : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (cIn d' m' Gb segs j Z' mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    q.cw.cnt ≤ 2 * q.k ∧
    (∀ i < m, c.nmem (d' + 4 + m' + i) < m ∧ en (c.nmem (d' + 4 + m' + i)) = M₀.rev (en i)) ∧
    (∀ i < m, c.nmem (d + 4 + m + m + i) < m ∧ en (c.nmem (d + 4 + m + m + i)) = M₀.rot (en i)) ∧
    (∀ l < (segs[j]'H.hj).k, c.nmem (q.PDb + l) < m ∧
      en (c.nmem (q.PDb + l)) = (segs[j]'H.hj).d l) ∧
    (∀ i < m, (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) : ℤ) =
      ℓ0 cap f₀ (en i) ∧ c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) ≤ 2 * Z') ∧
    (∀ a < 2 * (segs[j]'H.hj).k, c.nmem (X.ETb + a) = X.ET a) ∧
    (∀ a < 2 * (segs[j]'H.hj).k, c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.k + q.k + a) = X.EH a) := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  have hmm := H.mm
  have hb2k : q.cw.cnt ≤ 2 * q.k := by
    rw [mkP_card H hk0, ← hkq]; exact (segs[j]'H.hj).card_faces_le
  have hPDb : q.PDb + q.k ≤ hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).1
  have hrv : ∀ i < m, c.nmem (d' + 4 + m' + i) < m ∧
      en (c.nmem (d' + 4 + m' + i)) = M₀.rev (en i) := fun i hi' => by
    rw [alo' _ (by omega), H.rvE hi']; exact H.brv i hi'
  have hrt : ∀ i < m, c.nmem (d + 4 + m + m + i) < m ∧
      en (c.nmem (d + 4 + m + m + i)) = M₀.rot (en i) := fun i hi' => by
    rw [alo' _ (by omega), show d + 4 + m + m + i = d + 4 + 2 * m + i by omega]
    exact H.bsg i hi'
  have hpd : ∀ l < (segs[j]'H.hj).k, c.nmem (q.PDb + l) < m ∧
      en (c.nmem (q.PDb + l)) = (segs[j]'H.hj).d l := fun l hl => by
    have h := pq_pd H hl
    rw [alo' _ (by omega)]
    exact ⟨h.1, h.2.1⟩
  have hln : ∀ i < m, (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) : ℤ) =
      ℓ0 cap f₀ (en i) ∧
      c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) ≤ 2 * Z' := fun i hi' => by
    have hi'' : i < m' := by omega
    rw [aCL i hi'']
    have hcp := H.fr.cp i hi''
    have hr := H.fr.rv i hi''
    have hcpr := H.fr.cp _ hr.1
    have hfl := H.fr.fl i hi''
    have h1 := H.pseudo.le_cap (en' i)
    have h2 := H.pseudo.le_cap ((M₀.pendant e he).rev (en' i))
    rw [H.pseudo.antisymm (en' i), ← hr.2] at h2
    have := cl_word (CP := q.CP i) (FLW := q.FLW i) (Z := q.Z) (U := cap (en' i))
      (f := f₀ (en' i)) (r := cap (en' (mem (d' + 4 + m' + i))))
      (by show (mem (d' + 4 + m' + m' + m' + i) : ℤ) = _
          rw [show d' + 4 + m' + m' + m' + i = d' + 4 + 3 * m' + i by omega]; exact hcp.1)
      (by show mem (d' + 4 + m' + m' + m' + i) ≤ Z'
          rw [show d' + 4 + m' + m' + m' + i = d' + 4 + 3 * m' + i by omega]; exact hcp.2)
      (by show (mem (d' + 4 + m' + m' + m' + m' + m' + m' + i) : ℤ) = Z' + _
          rw [show d' + 4 + m' + m' + m' + m' + m' + m' + i = d' + 4 + 6 * m' + i by omega]
          exact hfl)
      h1 h2 (by rw [← hcpr.1]; exact_mod_cast hcpr.2)
    rw [H.hen i hi'] at this
    exact this
  have het := mkP_et H hk0 (q.Qb A0)
  have hET : ∀ a < 2 * (segs[j]'H.hj).k, c.nmem (X.ETb + a) = X.ET a := fun a ha => by
    obtain ⟨l, rfl | rfl⟩ : ∃ l, a = 2 * l ∨ a = 2 * l + 1 := ⟨a / 2, by omega⟩
    · rw [(het l (by omega)).1, ← (aET l (by omega)).1]; try rfl
    · rw [(het l (by omega)).2.1, ← (aET l (by omega)).2.1]; try rfl
  have hEH : ∀ a < 2 * (segs[j]'H.hj).k, c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k +
      q.k + q.k + q.k + a) = X.EH a := fun a ha => by
    obtain ⟨l, rfl | rfl⟩ : ∃ l, a = 2 * l ∨ a = 2 * l + 1 := ⟨a / 2, by omega⟩
    · rw [(het l (by omega)).2.2.1, ← (aET l (by omega)).2.2.1]; try rfl
    · rw [(het l (by omega)).2.2.2, ← (aET l (by omega)).2.2.2]; try rfl
  exact ⟨hb2k, hrv, hrt, hpd, hln, hET, hEH⟩

set_option maxHeartbeats 4000000 in
/-- **The query darts written by `qbP`**: base indices whose faces are the corners. -/
theorem st9_qb (hk0 : 0 < (segs[j]'H.hj).k) {A0 W : ℕ}
    (hG : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (cIn d' m' Gb segs j Z' mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    ∀ x < q.cw.cnt,
      qbM c.nmem q.PDb (d' + 4 + m') X.ETb (q.Qb A0 + 15 * q.k) q.k
        (q.Qb A0 + 15 * q.k + x) < m ∧
      M₀.face (en (qbM c.nmem q.PDb (d' + 4 + m') X.ETb (q.Qb A0 + 15 * q.k) q.k
        (q.Qb A0 + 15 * q.k + x))) = X.β x := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  intro x hx
  have IN := st9_in H hk0 hG c hO hhi hfr hfb
  obtain ⟨hb2k, hrv, -, hpd, -, hET, -⟩ := IN
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  obtain ⟨c1, c2, c3, -⟩ := mkP_corners H hk0 (q.Qb A0)
  -- the corner `x` is the corner of some arc
  have hxa : ∃ a < 2 * q.k, c.nmem (X.ETb + a) = x := by
    have hm := c1 x hx
    simp only [SPath.faces, List.mem_toFinset, List.mem_map, darts_eq, List.mem_range] at hm
    obtain ⟨y, ⟨a, ha, rfl⟩, hy⟩ := hm
    refine ⟨a, by rw [← hkq]; exact ha, ?_⟩
    rw [hET a ha]
    show X.idx ((M₀.pendant e he).face (dartAt ((segs[j]'H.hj).lift e he) a)) = x
    have hb := c3 _ (c1 x hx)
    rw [hy]
    exact c2 _ hb.1 _ hx hb.2
  obtain ⟨a, ha, hea, hv⟩ := qbM_val c.nmem q.PDb (d' + 4 + m') X.ETb (q.Qb A0 + 15 * q.k) q.k x
    hxa
  rw [hv]
  -- the dart of the arc `a`
  have ha' : a < 2 * (segs[j]'H.hj).k := by rw [hkq]; exact ha
  have hl : a / 2 < (segs[j]'H.hj).k := by omega
  obtain ⟨p1, p2⟩ := hpd _ hl
  have hqv : qv c.nmem q.PDb (d' + 4 + m') a < m ∧
      en (qv c.nmem q.PDb (d' + 4 + m') a) = dartAt (segs[j]'H.hj) a := by
    unfold qv dartAt
    split_ifs with h2
    · exact ⟨p1, p2⟩
    · obtain ⟨r1, r2⟩ := hrv _ p1
      exact ⟨r1, by rw [r2, p2]⟩
  refine ⟨hqv.1, ?_⟩
  have hmem : (M₀.pendant e he).face (dartAt ((segs[j]'H.hj).lift e he) a) ∈
      ((segs[j]'H.hj).lift e he).faces :=
    SPath.face_mem _ (SLx.dartAt_mem (X := X) ha')
  have hidx := (c3 _ hmem).2
  have hET' : X.ET a = x := by rw [← hET a ha']; exact hea
  have e1 : X.β x = (M₀.pendant e he).face (dartAt ((segs[j]'H.hj).lift e he) a) := by
    rw [← hET']; exact hidx
  rw [e1, dartAt_lift, hqv.2]
  rfl

set_option maxHeartbeats 4000000 in
/-- **The fixed arrays and the first state after step 2.** -/
theorem st9_fix (hk0 : 0 < (segs[j]'H.hj).k) {A0 W : ℕ}
    (hG : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (cIn d' m' Gb segs j Z' mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0)
    {Wz : ℕ} (hWA : Wz < A0) (c₃ : Config)
    (mS : ∀ a, Wz < a → a < (cIn d' m' Gb segs j Z' mem).Qb A0 +
      15 * (cIn d' m' Gb segs j Z' mem).k → c₃.nmem a = c.nmem a)
    (hSI : ∀ e' < 2 * (segs[j]'H.hj).k, c₃.nmem (lySI ((cIn d' m' Gb segs j Z' mem).Qb A0 +
      15 * (cIn d' m' Gb segs j Z' mem).k) (cIn d' m' Gb segs j Z' mem).cw.cnt
      (segs[j]'H.hj).k + e') =
      MsCall.sIdx (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
        ((cIn d' m' Gb segs j Z' mem).Qb A0)).ET (2 * (segs[j]'H.hj).k)
        (cIn d' m' Gb segs j Z' mem).cw.cnt e') :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    X.Fix c₃.nmem ∧ X.Stt (X.st 0) c₃.nmem := by
  have IN := st9_in H hk0 hG c hO hhi hfr hfb
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  obtain ⟨hb2k, -, -, -, -, hET, -⟩ := IN
  have hmm := H.mm
  have hrot' := pendant_rotTrans he H.rot
  -- the bounds of the flow and its net outflows
  have hKB : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hG.hK
  have hB0 : (0 : ℤ) ≤ X.B := by positivity
  have hf0K : ∀ y, |f₀ y| ≤ (X.K : ℤ) := fun y => by
    have h1 : |f₀ y| ≤ (X.B : ℤ) := hG.bf0 y
    push_cast at hKB; linarith
  have hdvK : ∀ v, |(M₀.pendant e he).div f₀ v| ≤ (X.K : ℤ) := fun v => by
    have h1 : |(M₀.pendant e he).div f₀ v| ≤ (X.B : ℤ) := hG.bdv v
    push_cast at hKB; linarith
  have mS' : ∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c₃.nmem a = c.nmem a := mS
  have aW5' : ∀ l < q.k, c.nmem (q.Qb A0 + l) = q.CP (q.PD l) ∧
      c.nmem (q.Qb A0 + q.k + l) = q.CP (q.RV (q.PD l)) ∧
      c.nmem (q.Qb A0 + q.k + q.k + l) = q.FLW (q.PD l) + q.K - q.Z ∧
      c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + l) = q.FLW (q.PD l) + q.K - q.Z ∧
      c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + l) = q.DVw l := aW5
  have hQ : A0 ≤ q.Qb A0 := by simp only [FpIn.Qb]; omega
  have hPDq : ∀ l < (segs[j]'H.hj).k, q.PD l < m ∧
      en' (q.PD l) = ((segs[j]'H.hj).lift e he).d l := fun l hl =>
    ⟨(pq_pd H hl).1, (pq_pd H hl).2.2⟩
  have hfwq : ∀ l < (segs[j]'H.hj).k, (((q.FLW (q.PD l) + q.K - q.Z : ℕ)) : ℤ) =
      f₀ (((segs[j]'H.hj).lift e he).d l) + q.K := fun l hl => by
    have h1 : (((q.FLW (q.PD l) + q.K - Z' : ℕ)) : ℤ) = f₀ (en' (q.PD l)) + q.K :=
      cIn_fw (Gb := Gb) (sg := segs) (j := j) (K := q.K) (i := q.PD l) H.fr
        (by have := (hPDq l hl).1; omega) (hf0K _)
    rw [(hPDq l hl).2] at h1
    exact h1
  refine ⟨?_, ?_⟩
  · -- the fixed arrays
    have eSI : lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k =
        lySI (q.Qb A0 + 15 * q.k) q.cw.cnt (segs[j]'H.hj).k := by rw [hkq]
    refine ⟨fun l hl' => ?_, fun l hl' => ?_, fun l hl' => ?_, fun l hl' => ?_, fun a ha => ?_,
      fun e' he' => ?_⟩
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := hPDq l hl'
      have hcw : (q.CP (q.PD l) : ℤ) = cap (en' (q.PD l)) :=
        cIn_cw (Gb := Gb) (sg := segs) (j := j) H.fr (by omega)
      show (c₃.nmem (q.Qb A0 + l) : ℤ) = cap (((segs[j]'H.hj).lift e he).d l)
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).1, hcw, hv]
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := hPDq l hl'
      show (c₃.nmem (q.Qb A0 + q.k + l) : ℤ) =
        cap ((M₀.pendant e he).rev (((segs[j]'H.hj).lift e he).d l))
      have hr : q.RV (q.PD l) < m' ∧ en' (q.RV (q.PD l)) = (M₀.pendant e he).rev (en' (q.PD l)) :=
        cIn_rv (Gb := Gb) (sg := segs) (j := j) H.fr (i := q.PD l) (by omega)
      have hcw : (q.CP (q.RV (q.PD l)) : ℤ) = cap (en' (q.RV (q.PD l))) :=
        cIn_cw (Gb := Gb) (sg := segs) (j := j) H.fr hr.1
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.1, hcw, hr.2, hv]
    · have hl2 : l < q.k := hkq ▸ hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + l) : ℤ) =
        f₀ (((segs[j]'H.hj).lift e he).d l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.2.1, hfwq l hl']
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := hPDq l hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + l) : ℤ) =
        (M₀.pendant e he).div f₀ (((segs[j]'H.hj).lift e he).p l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.2.2]
      have hPD' : q.PD l < m' := by omega
      have hdv : (q.DVw l : ℤ) = (M₀.pendant e he).div f₀ ((M₀.pendant e he).tail (en' (q.PD l))) +
          q.K :=
        cIn_dv (Gb := Gb) (sg := segs) (j := j) H.fr hrot' hPD' (by rw [hv]; exact hdvK _)
      rw [hdv, hv, ((segs[j]'H.hj).lift e he).tail_d l hl']
    · have hXk : X.P.k = q.k := by rw [← hkq]; rfl
      have ha2 : a < 2 * q.k := by
        have : a < 2 * X.P.k := ha
        omega
      show c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + a) = X.ET a
      rw [mS' _ (by omega) (by omega)]; exact hET a (by omega)
    · show c₃.nmem (lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k + e') = _
      rw [eSI]; exact hSI e' he'
  · -- the state before the first stage
    refine SLx.stt_zero _ (fun l hl' => ?_) (fun y hy => ?_)
    · have hl2 : l < q.k := hkq ▸ hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + l) : ℤ) = f₀ (((segs[j]'H.hj).lift e he).d l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.1, hfwq l hl']
    · have hy' : y < q.cw.cnt := hy
      show c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
        y) = 0
      rw [mS' _ (by omega) (by omega)]; exact (aPW y (by omega)).1

end Ctx

end F9b

end BKMNW

end PlanarFlow
