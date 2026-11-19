module

public import PlanarFlow.BKMNW.Nf7dF

/-!
# `fixP` on a part with `k = 0` from the frame

For an empty part (`πj.k = 0`, a single vertex) `fixPath` has no stage: it is the final
negative-length call alone, `f₀ + cob χ` with `χ = negLay (U − f₀)`. **`fixZero_exec`**: the program
`fixZero = proP1a ; proP1b ; proP3a ; z0Blk ; finP` (the face labels and offset `K = 16 fpB`,
then the final step at `T = Q`) writes `fixPath (pmap hP) U f₀ πj (msspPlaneK) (frRef)
(negLay gid I x hP)` into `FL` within `zT C C₀ m = 63 + (120 m + 60) + (12 m + 22) + 1 +
finT C C₀ m 0` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Programs

/-- The steps of `fixZero`. -/
def zT (C C₀ m : ℕ) : ℕ := 63 + (120 * m + 60) + (12 * m + 22) + 1 + finT C C₀ m 0

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

set_option maxHeartbeats 4000000 in
/-- The semantic side of an empty part: the final call alone, its outcome, the bounds. -/
theorem fz7d_sem (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) (hl : Lay M gid u S T Z x m en d mem) {πj : SPath (pmap hP)} (hk00 : πj.k = 0)
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) {AS K : ℕ}
    (hAS : ((AS : ℕ) : ℤ) = SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1))
    (hK : 16 * fpB AS m 0 ≤ K) :
    ∃ χ, negLay gid I x hP ((fun y => u y.1) - f₀) = some χ ∧
      NegPre (pmap hP) ((fun y => u y.1) - f₀) ∧
      fixPath (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _)
        (negLay gid I x hP) = f₀ + (pmap hP).cob χ ∧
      IsPseudo (pmap hP) (fun y => u y.1) (f₀ + (pmap hP).cob χ) ∧
      (∀ e, |f₀ e| ≤ (K : ℤ)) ∧ (∀ e, |u e.1 - f₀ e| ≤ (K : ℤ)) := by
  have hmssp : MSSPSpecAt (pmap hP) (Klein.msspPlaneK (pmap hP)) πj :=
    fun ℓ' hnn' y hy => Klein.msspPlaneK_spec hpl hrot hface πj ℓ' hnn' y hy
  have hc0 : ∀ e : SDart (pdarts M x.1.piece x.2.1), 0 ≤ u e.1 := fun e => by
    obtain ⟨i, hi, he⟩ := hl.en_surj e.1 e.2
    rw [← he, ← (hl.cp i hi).1]; positivity
  have hinv := fixPath_invB hpl hc0 hf₀ hmssp (frRef_spec _) πj.k le_rfl
  have e0 : fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k =
      (f₀, 0) := by rw [hk00]; rfl
  rw [e0] at hinv
  have hNP := fixPath_negPre hpl hrot hface hc0 hf₀ hmssp (frRef_spec (SFace x.2.2
    (pdarts M x.1.piece x.2.1) (revPerm M)))
  rw [e0] at hNP
  obtain ⟨χ, hχ⟩ := neg_some (negLay_spec gid I x hP) hinv.final
  have hfx : fixPath (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _)
      (negLay gid I x hP) = f₀ + (pmap hP).cob χ := by
    rw [fixPath_eq_fpState, e0]
    simp only
    rw [hχ]
  have hps := (fixPath_spec hpl hc0 hf₀ πj hmssp (frRef_spec _) (negLay_spec gid I x hP)).pseudo
  rw [hfx] at hps
  have hKe : (16 * (4 * (AS + m * (4 * AS + 1)) + 12 * AS + 4) : ℤ) ≤ K := by
    have e : 16 * fpB AS m 0 = 16 * (4 * (AS + m * (4 * AS + 1)) + 12 * AS + 4) := by
      unfold fpB; ring
    rw [e] at hK
    exact_mod_cast hK
  have hAS0 : (0 : ℤ) ≤ AS := by positivity
  have hY : (0 : ℤ) ≤ (m : ℤ) * (4 * AS + 1) := by positivity
  refine ⟨χ, hχ, hNP, hfx, hps, fun e => ?_, fun e => ?_⟩
  · have h1 := abs_le_of_pseudo hf₀ e
    have h2 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) e
    have h3 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) ((pmap hP).rev e)
    rw [← hAS] at h2 h3
    push_cast at hKe; nlinarith
  · have h1 := abs_le_of_pseudo hf₀ e
    have h2 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) e
    have h3 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) ((pmap hP).rev e)
    rw [← hAS] at h2 h3
    have h4 : |u e.1 - f₀ e| ≤ |u e.1| + |f₀ e| := abs_sub _ _
    push_cast at hKe; nlinarith

set_option maxHeartbeats 4000000 in
/-- The face labels and the offset of an empty part (`proP1a ; proP1b ; proP3a ; z0Blk`). -/
theorem fz7d_pre (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length)
    (hq0 : (callIn d m Gb π j Z c.nmem).k = 0)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hfr : d + 4 + 7 * m ≤ A0)
    (hZ1 : A0 + 9 * m + 1 + d + Gb + j + π.segs.length + π.segs.length +
      (callIn d m Gb π j Z c.nmem).off + 8 ≤ W)
    (hZ2 : ∑ i ∈ range m, (callIn d m Gb π j Z c.nmem).FLW i + 6 ≤ W)
    (hZ3 : (callIn d m Gb π j Z c.nmem).AS + 16 * fpB (callIn d m Gb π j Z c.nmem).AS m 0 + Z +
      16 ≤ W) :
    let q := callIn d m Gb π j Z c.nmem
    ∃ c' t, Exec I W (.seq proP1a (.seq proP1b (.seq proP3a z0Blk))) c c' t ∧
      t ≤ 63 + (120 * m + 60) + (12 * m + 22) + 1 ∧
      c'.nreg 9469 = A0 + 9 * m + 1 ∧ c'.nreg 9400 = m ∧ c'.nreg 9436 = 1 ∧
      c'.nreg 9434 = d + 4 + 3 * m ∧ c'.nreg 9435 = d + 4 + 6 * m ∧ c'.nreg 9421 = Z ∧
      c'.nreg 9310 = q.K ∧ c'.nreg 9401 = 0 ∧ c'.nreg 9402 = q.PDb ∧
      c'.nreg 9430 = d + 4 + m ∧ c'.nreg 9431 = d + 4 + 2 * m ∧
      c'.nreg 9374 = A0 + 9 * m + 1 ∧ c'.nreg 9375 = A0 + 9 * m + 1 ∧
      c'.nreg 9376 = A0 + 9 * m + 1 ∧ c'.nreg 9405 = A0 + m ∧
      (∀ a < A0, c'.nmem a = c.nmem a) ∧
      (∀ i < m, c'.nmem (A0 + m + i) = olab (nxF d m c.nmem) i + 1) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro q
  have hpre := callIn_pre (d := d) (Z := Z) hl hS hj
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpre
  have hQe : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  obtain ⟨c₁, t₁, e₁, ht₁, R1, a5030, a5031, a4470, a4471, a4472, a4473, a7350, a7351, a7352,
      a8430, k1, n1, rr1, rm1, o1⟩ :=
    proP1a_exec (P := I) q c hc (j := j) (A0 := A0) r04 r06 r07 r00 p1 p2 p3 p4 p5
      (by rw [hq0]; show A0 + 9 * m + 15 * 0 + 1 + d + Gb + j + π.segs.length +
        π.segs.length + q.off + 8 ≤ W; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bNX, bLAB, -, -, -, -, bk, bR, rr2, rm2, o2⟩ :=
    proP1b_exec (P := I) q c₁ e₁.wb_right (A0 := A0)
      (by rw [k1 _ (by unfold scr1; norm_num)]; exact r04)
      a5030 a5031 a4470 a4471 a4472 a4473 a7350 a7351 a7352 a8430
      (fun a _ => by rw [n1]; rfl) p1 p6 p7 p8 hfr
      (show A0 + 9 * q.m + 2 ≤ W from by show A0 + 9 * m + 2 ≤ W; omega) hZ2
  have R2 : RegP1 q A0 c₂ := R1.congr fun r hr _ _ _ => bR r (by clear * - hr; omega)
    (by clear * - hr; omega) (by clear * - hr; omega) (by clear * - hr; omega)
    (by clear * - hr; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, d20, d73, d22, d10, -, dm, dR, rr3, rm3, o3⟩ :=
    proP3a_exec (P := I) q c₂ e₂.wb_right R2 b1 hfr
      (show A0 + 9 * q.m + 2 ≤ W from by show A0 + 9 * m + 2 ≤ W; omega)
      (show q.AS + 16 * fpB q.AS q.m q.k + q.Z + q.k + 16 ≤ W from by
        rw [hq0]; show q.AS + 16 * fpB q.AS m 0 + Z + 0 + 16 ≤ W; omega)
  obtain ⟨c₄, t₄, e₄, ht₄, z69, zk, zm, rr4, rm4, o4⟩ := z0Blk_exec (P := I) c₃ e₃.wb_right
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R2
  have K4 : ∀ r, 9400 ≤ r → r ≤ 9438 → r ≠ 9420 → r ≠ 9422 → c₄.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => (zk r (by clear * - h2; omega)).trans
      (dR r h3 (by clear * - h1; omega) h4 (by clear * - h1; omega) (by clear * - h2; omega))
  have K4' : ∀ r, 9374 ≤ r → r ≤ 9377 → c₄.nreg r = c₂.nreg r :=
    fun r h1 h2 => (zk r (by clear * - h2; omega)).trans
      (dR r (by clear * - h2; omega) (by clear * - h1; omega) (by clear * - h2; omega)
        (by clear * - h1; omega) (by clear * - h2; omega))
  have m4 : ∀ a, a < A0 → c₄.nmem a = c.nmem a := fun a ha => by
    rw [zm, dm a (by clear * - ha hfr; omega)]; exact b1 a ha
  have ht2' : t₂ ≤ 120 * m + 60 := ht₂
  have ht3' : t₃ ≤ 12 * m + 22 := ht₃
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by clear * - ht₁ ht2' ht3' ht₄; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, m4, fun i hi => ?_, fun r hr => ?_, by rw [rr4, rr3, rr2, rr1],
    by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  · rw [z69, dR _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g18, hq0]; simp only [Nat.add_zero]; exact hQe
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g00]; rfl
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g36]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g34]; show d + 4 + m + m + m = _; ring
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g35]
    show d + 4 + m + m + m + m + m + m = _; ring
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g21]; rfl
  · rw [zk _ (by norm_num)]; exact d10
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g01, hq0]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g30]; rfl
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g31]; show d + 4 + m + m = _; ring
  · rw [K4' _ (by norm_num) (by norm_num), g74, hQe]
  · rw [K4' _ (by norm_num) (by norm_num), g75, hQe, hq0]
  · rw [K4' _ (by norm_num) (by norm_num), g76, hQe, hq0]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g05]; rfl
  · rw [zm, dm _ (by
      show ¬ (A0 + m + m + m + m + 1 + m + m + m ≤ A0 + m + i ∧
        A0 + m + m + m + m + 1 + m + m + m + m > A0 + m + i)
      clear * - hi; omega)]; exact bLAB i hi
  · rw [zk r (by clear * - hr; omega),
      dR r (by clear * - hr; omega) (by clear * - hr; omega) (by clear * - hr; omega)
        (by clear * - hr; omega) (by clear * - hr; omega),
      bR r (by clear * - hr; omega) (by clear * - hr; omega) (by clear * - hr; omega)
        (by clear * - hr; omega) (by clear * - hr; omega), k1 r (by unfold scr1; clear * - hr; omega)]

set_option maxHeartbeats 4000000 in
/-- **`fixP` on a part with `k = 0`** (see the module docstring). -/
theorem fixZero_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hk00 : πj.k = 0)
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hZ1 : A0 + 9 * m + 1 + d + Gb + j + π.segs.length + π.segs.length +
      (callIn d m Gb π j Z c.nmem).off + 8 ≤ W)
    (hZ2 : ∑ i ∈ range m, (callIn d m Gb π j Z c.nmem).FLW i + 6 ≤ W)
    (hZ3 : (callIn d m Gb π j Z c.nmem).AS + 16 * fpB (callIn d m Gb π j Z c.nmem).AS m 0 + Z +
      16 ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) m ≤ Wz)
    (hW : 5 * (A0 + 9 * m + 1) + (A0 + m) + 3 * d + 60 * m + 60 +
      (callIn d m Gb π j Z c.nmem).PDb + 3 * (A0 + 9 * m + 1) + negT C C₀ m ≤ W)
    (wL : 2 * (callIn d m Gb π j Z c.nmem).K + rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W)
    (hw2' : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) ≤ W)
    (hv : Z + Z + 2 * (callIn d m Gb π j Z c.nmem).K +
      2 * rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W) :
    ∃ c' t, Exec I W fixZero c c' t ∧ t ≤ zT C C₀ m ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP)) := by
  have hq0 : (callIn d m Gb π j Z c.nmem).k = 0 := hk ▸ hk00
  have htop := (callIn_top (d := d) (Z := Z) hS hj).1
  have hPDb : lo ≤ (callIn d m Gb π j Z c.nmem).PDb := by
    obtain ⟨h1, -⟩ := hS
    show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
    omega
  obtain ⟨c₄, t₄, e₄, ht₄, z69, z00, z36, z34, z35, z21, z10, z01, z02, z30, z31, z74, z75, z76,
      z05, m4, L4, K4, rr4, rm4, o4⟩ :=
    fz7d_pre (Wz := Wz) I c hc hl hS hj hq0 r04 r06 r07 r00 hfr hZ1 hZ2 hZ3
  obtain ⟨χ, hχ, hNP, hfx, hps, hgK, hℓK⟩ := fz7d_sem hP hpl hrot hface I hl hk00 hf₀
    (callIn_as hl) (K := (callIn d m Gb π j Z c.nmem).K)
    (by show 16 * fpB _ m 0 ≤ 16 * fpB _ m (callIn d m Gb π j Z c.nmem).k; rw [hq0])
  have hl4 : Lay M gid u S T Z x m en d c₄.nmem := hl.congr fun a h1 h2 =>
    m4 a (by clear * - h2 hfr; omega)
  have hNX : ∀ i < m, nxF d m c₄.nmem i = nxF d m c.nmem i := fun i hi => by
    unfold nxF
    have h1 := (hl.rv i hi).1
    rw [m4 (d + 4 + m + i) (by clear * - hi hfr; omega), m4 _ (by clear * - h1 hfr; omega)]
  set E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm with hE
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => layEn_val hi
  have eL4 : layEn (pdarts M x.1.piece x.2.1) en m hl4.en_mem hm = E := rfl
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, k5, r5, rr5, rm5, o5⟩ :=
    finP_exec C C₀ hC hP f₀ hNP I I c₄ e₄.wb_right hl4 hm (Tb := A0 + 9 * m + 1) (k := 0)
      (PDb := (callIn d m Gb π j Z c.nmem).PDb) (CWb := A0 + 9 * m + 1)
      (CRb := A0 + 9 * m + 1) (FWb := A0 + 9 * m + 1)
      (K := (callIn d m Gb π j Z c.nmem).K) (Wz := Wz) (LABb := A0 + m) hχ
      z69 z00 z36 z34 z35 z21 z10 z01 z02 z30 z31 z74 z75 z76 z05
      (fun i hi => by
        rw [L4 i hi, olab_congr (f := nxF d m c₄.nmem) (g := nxF d m c.nmem) hNX hl4.permOn_nx hi])
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun i hi _ => by
        rw [eL4, m4 _ (by clear * - hi hfr; omega)]
        have hfl := hFL i hi
        rw [fext_mem _ (hl.en_mem i hi)] at hfl
        have eEi : (⟨en i, hl.en_mem i hi⟩ : SDart (pdarts M x.1.piece x.2.1)) = E i :=
          (Subtype.ext (eEv i hi)).symm
        rw [eEi] at hfl
        exact hfl)
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun i hi => by rw [eL4]; exact hgK _)
      (fun i hi => by
        rw [eL4]
        have := hℓK (E i)
        rw [eEv i hi] at this
        exact this)
      (fun i hi => by
        rw [eL4]
        have h1 := hps.le_cap ((pmap hP).rev (E i))
        rw [hps.antisymm (E i)] at h1
        have h2 := hl.cp _ (hl.rv i hi).1
        have h3 : ((pmap hP).rev (E i)).1 = en (c.nmem (d + 4 + m + i)) := by
          rw [pmap_rev, eEv i hi, (hl.rv i hi).2]
        change -(f₀ + (pmap hP).cob χ) (E i) ≤ u ((pmap hP).rev (E i)).1 at h1
        rw [h3] at h1
        have : (c.nmem (d + 4 + 3 * m + c.nmem (d + 4 + m + i)) : ℤ) ≤ Z := by
          exact_mod_cast h2.2
        linarith [h2.1])
      (fun a ha => by rw [m4 a (by clear * - ha hWzd hfr; omega)]; exact hz a ha) hSz hWzd
      ⟨by clear * - hfr; omega, by clear * -; omega,
        by clear * - htop hhi hq0; omega, by clear * -; omega, by clear * -; omega,
        by clear * -; omega⟩
      hWz (by clear * - hW; omega) wL hw2' hw3
      (fun i hi => by have := (hl4.cp i hi).2; clear * - this hv; omega)
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
  obtain ⟨ca, ka, kb, ea, eb, hkab⟩ := e₄.seq_inv
  obtain ⟨cb, kc, kd, ec, ed, hkcd⟩ := eb.seq_inv
  obtain ⟨cc, ke, kf, ee, ef, hkef⟩ := ed.seq_inv
  refine ⟨c₅, _, ea.seq (ec.seq (ee.seq (ef.seq e₅))), ?_, fun r hr => ?_, fun a ha hn => ?_,
    by rw [o5, o4], z5, by rw [← hfx] at F5; exact F5⟩
  · unfold zT; clear * - ht₄ ht₅ hkab hkcd hkef; omega
  · rw [r5 r (by unfold KeepR; clear * - hr; omega) (by clear * - hr; omega), K4 r hr]
  · refine ⟨?_, by rw [rm5, rm4]⟩
    by_cases hw : a ≤ Wz
    · rw [z5 a hw, hz a hw]
    · rw [k5 a (by clear * - hw; omega) (by clear * - ha; omega) hn, m4 a ha]

end Call

end BKMNW

end PlanarFlow
