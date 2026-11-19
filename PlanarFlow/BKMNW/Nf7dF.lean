module

public import PlanarFlow.BKMNW.Nf7dE

/-!
# `fixP` on a part with `0 < k` from the frame

**`fixPos_exec`**: at a call `x` with a plane piece map (transitive rotations and faces), from the
frame (`Lay`), the parts of the separator (`SegsOut` from `r6807`, the part `j = r6800` with
`0 < k`), an input flow `f₀` in `FL` that is a pseudoflow for `U`, the memory `≤ Wz` zero, and an
MSSP call program meeting `MsspCallSpec` on the piece map (scratch below `9300`), the program
`fixPos msP = fpPro ; st2 msP ; p7dG ; loopP ; clrP ; finP` writes
`fixPath (pmap hP) U f₀ πj (msspPlaneK) (frRef) (negLay gid I x hP)` into `FL`, within
`posT = (162 m + 103 k + 180) + (cost m k b + st2T b k + 4) +
  (loopT b k + (20 (lb + 2k) + 32 + finT C C₀ m k))` steps, keeping the driver's registers, the
memory below `A0 = r3006` off `FL` and the zero area. The word/zero-area bounds are hypotheses
(stated with `X = mkX …`).
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

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ}

/-- The steps of `fixPos` (`b` corners, `k` darts on the path, `lb = b² + 2b + 1 + 2k`). -/
def posT (C C₀ : ℕ) (cost : ℕ → ℕ → ℕ → ℕ) (m k b : ℕ) : ℕ :=
  (162 * m + 103 * k + 180) + (cost m k b + st2T b k + 4) +
    (loopT b k + (20 * (b * b + b + b + 1 + 2 * k + 2 * k) + 32 + finT C C₀ m k))

set_option maxHeartbeats 8000000 in
/-- **`fixP` on a part with `0 < k`** (see the module docstring). -/
theorem fixPos_exec (C C₀ : ℕ) (hC : 200000 ≤ C) {msP : Stmt} {Scr : ℕ → Prop}
    {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hMS : MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    -- the bounds
    (hW1 : 16 * ((callIn d m Gb π j Z c.nmem).Qb A0 + 15 * (callIn d m Gb π j Z c.nmem).k + 2) ≤ W)
    (hW2 : ∑ i ∈ range m, (callIn d m Gb π j Z c.nmem).FLW i + (callIn d m Gb π j Z c.nmem).AS +
      16 * fpB (callIn d m Gb π j Z c.nmem).AS m (callIn d m Gb π j Z c.nmem).k + m * Z + Z +
      (callIn d m Gb π j Z c.nmem).k + 16 ≤ W)
    (hl14 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).p + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).LG ≤ W)
    (hw1 : 16 * (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).K + 1 ≤ W)
    (hw2 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).Mo + 3 * (mkX hP hl hm πj f₀
      (callIn d m Gb π j Z c.nmem) ((callIn d m Gb π j Z c.nmem).Qb A0)).K ≤ W)
    (hwz : wzm m (2 * Z) ≤ Wz)
    (hSHz : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).SH + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((callIn d m Gb π j Z c.nmem).Qb A0 + 15 * (callIn d m Gb π j Z c.nmem).k)
      (callIn d m Gb π j Z c.nmem).cw.cnt (callIn d m Gb π j Z c.nmem).k +
      Rm m (callIn d m Gb π j Z c.nmem).k (callIn d m Gb π j Z c.nmem).cw.cnt ≤ W)
    (hKL : (callIn d m Gb π j Z c.nmem).K + 8 * fpB (callIn d m Gb π j Z c.nmem).AS m
      (callIn d m Gb π j Z c.nmem).k + moOf (callIn d m Gb π j Z c.nmem).cw.cnt
      (8 * fpB (callIn d m Gb π j Z c.nmem).AS m (callIn d m Gb π j Z c.nmem).k) ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) m ≤ Wz)
    (hW : 5 * (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).p + (A0 + m) + 3 * d + 60 * m + 60 +
      (callIn d m Gb π j Z c.nmem).PDb + (callIn d m Gb π j Z c.nmem).Qb A0 +
      ((callIn d m Gb π j Z c.nmem).Qb A0 + πj.k) +
      ((callIn d m Gb π j Z c.nmem).Qb A0 + πj.k + πj.k) + πj.k + negT C C₀ m ≤ W)
    (wL : 2 * (callIn d m Gb π j Z c.nmem).K + rtL (pmap hP) (fun y => u y.1 -
      (fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)
      ≤ W)
    (hw2' : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) ≤ W)
    (hv : Z + Z + 2 * (callIn d m Gb π j Z c.nmem).K + 2 * rtL (pmap hP) (fun y => u y.1 -
      (fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)
      ≤ W) :
    ∃ c' t, Exec I W (fixPos msP) c c' t ∧
      t ≤ posT C C₀ cost m πj.k (callIn d m Gb π j Z c.nmem).cw.cnt ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP)) := by
  have hpre := callIn_pre (d := d) (Z := Z) hl hS hj
  have htop := callIn_top (d := d) (Z := Z) hS hj
  set q := callIn d m Gb π j Z c.nmem with hq
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpre
  have hk0' : 0 < q.k := hk ▸ hk0
  have hQe : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  -- the prologue
  obtain ⟨c₁, t₁, e₁, ht₁, hO, k1, rr1, rm1, o1⟩ :=
    fpPro_exec (P := I) q c hc (j := j) r04 r06 r07 r00 (fun a _ => rfl) p1 p2 p3 p4 p5
      (show q.Gb + 1 + j + q.ns < A0 from by
        have := htop.2; show Gb + 1 + j + π.segs.length < A0; omega)
      p6 p7 p8 p9 hk0' hfr (show q.PDb + q.k ≤ A0 from by have := htop.1; omega) hW1 hW2
  have hO' := hO
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO'
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c₁.nmem a = c.nmem a := alo
  have hz1 : ∀ a ≤ Wz, c₁.nmem a = 0 := fun a ha => by rw [alo' a (by omega)]; exact hz a ha
  -- the data of the stage loop
  set X := mkX hP hl hm πj f₀ q (q.Qb A0) with hX
  have hG : X.Good W := mkX_good hP hl hm hpl hrot hface hS hj hk hd hk0 hf₀
    (lt_of_le_of_lt hSHz (by rw [hQe]; omega)) hl14 hw1 hw2
  -- step 2
  obtain ⟨c₃, t₃, e₃, ht₃, hR, hFx, hS0, hImg, r69, r71, r74, r75, K3, hz3, m3, rr3, rm3, o3⟩ :=
    st7d_exec hP hMS hScr hpl hrot hface hl hm hS hj hk hd hk0 hf₀ hFL (I := I) hG c₁ e₁.wb_right
      hO hz1 hWzd hWlo hhi hfr hwz hSHz hpw hKL
  have nK : ∀ r, 9400 ≤ r → r ≤ 9438 → r ≠ 9419 → r ≠ 9420 → r ≠ 9422 →
      c₃.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 =>
    K3 r (keepR_ge (by omega)) (by simp only [st2W]; omega) (by omega) (by omega) (by omega) (by omega)
  have m31 : ∀ a, Wz < a → a < A0 → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m3 a h1 (by rw [hQe]; omega), alo' a h2]
  have hl3 : Lay M gid u S T Z x m en d c₃.nmem := hl.congr fun a h1 h2 => m31 a (by omega)
    (by omega)
  have hFL3 : FLHas Z m d en c₃.nmem f₀ := fun i hi => by
    rw [m31 _ (by omega) (by omega)]; exact hFL i hi
  have hPDm3 : ∀ l < X.P.k, c₃.nmem (c₃.nreg 9402 + l) < m ∧
      en (c₃.nmem (c₃.nreg 9402 + l)) = (X.P.d l).1 := fun l hl' => by
    have hl2 : l < q.k := hk ▸ hl'
    rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02]
    have hPDb : lo ≤ q.PDb := by
      obtain ⟨h1, -⟩ := hS
      show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
      omega
    rw [m31 _ (by omega) (by omega)]
    obtain ⟨h1, h2⟩ := callIn_pd (d := d) (Z := Z) hS hj hl2
    exact ⟨h1, h2.trans (hd l hl').symm⟩
  have hNX : ∀ i < m, nxF d m c₃.nmem i = nxF d m c.nmem i := fun i hi => by
    unfold nxF
    have h1 := (hl.rv i hi).1
    rw [m31 (d + 4 + m + i) (by omega) (by omega), m31 _ (by omega) (by omega)]
  have hLAB3 : ∀ i < m, c₃.nmem (A0 + m + i) = olab (nxF d m c₃.nmem) i + 1 := fun i hi => by
    rw [m3 _ (by omega) (by rw [hQe]; omega), show A0 + m + i = A0 + q.m + i from rfl, aLAB i hi,
      olab_congr (f := nxF d m c₃.nmem) (g := nxF d m c.nmem) hNX hl3.permOn_nx hi]
    rfl
  have hPDz : Wz < c₃.nreg 9402 := by
    rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02]
    obtain ⟨h1, -⟩ := hS
    show Wz < Gb + 1 + π.segs.length + π.segs.length + _
    omega
  have hPD9 : c₃.nreg 9402 = q.PDb := by
    rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02]
  have hW' : 5 * X.p + (A0 + m) + 3 * d + 60 * m + 60 + c₃.nreg 9402 + X.CWb + X.CRb + X.FWb +
      X.P.k + negT C C₀ m ≤ W := by
    rw [hPD9]
    have e1 : X.CWb = q.Qb A0 := rfl
    have e2 : X.CRb = q.Qb A0 + q.k := rfl
    have e3 : X.FWb = q.Qb A0 + q.k + q.k := rfl
    have e4 : X.P.k = πj.k := rfl
    rw [e1, e2, e3, e4, ← hk]; exact hW
  have hv' : Z + Z + 2 * X.K + 2 * rtL (pmap hP) (fun y => u y.1 - (X.st X.P.k).1 y) ≤ W := hv
  -- the stage loop and the final step
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, m5, k5, rr5, rm5, o5⟩ :=
    fin7d_exec C C₀ hC hP X hG hrot hface rfl I I c₃ e₃.wb_right hl3 hm hFL3 (LABb := A0 + m)
      (Wz := Wz) hPDm3 hR hFx hS0 hImg r69
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g00]; rfl)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g36])
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g34]
          show d + 4 + m + m + m = _; ring)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g35]
          show d + 4 + m + m + m + m + m + m = _; ring)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g21]; rfl)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g01]
          exact hk.symm)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g30]; rfl)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g31]
          show d + 4 + m + m = _; ring)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g05]; rfl)
      r75 r71 r74 hLAB3
      (fun a ha h1 h2 => hz3 a ha h1 h2) hSHz hPDz hSz hWzd
      ⟨by omega, by show A0 + m + m ≤ q.Qb A0; rw [hQe]; omega,
        by rw [hPD9]; show q.PDb + πj.k ≤ q.Qb A0; rw [hk, hQe]; omega⟩
      hWz hW' wL hw2' hw3
      (fun i hi => by have := (hl3.cp i hi).2; omega)
  obtain ⟨cm, ka, kb, ea, eb, hkab⟩ := e₃.seq_inv
  refine ⟨c₅, _, e₁.seq (ea.seq (eb.seq e₅)), ?_, fun r hr => ?_, fun a ha hn => ?_, by rw [o5, o3, o1],
    z5, F5⟩
  · have ht5' : t₅ ≤ loopT q.cw.cnt πj.k + (20 * (q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 +
        2 * πj.k + 2 * πj.k) + 32 + finT C C₀ m πj.k) := ht₅
    unfold posT
    rw [hk] at ht5' ⊢
    rw [hkab] at ht₃
    have ht1' : t₁ ≤ 162 * m + 103 * q.k + 180 := ht₁
    have ht3' : ka + kb ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k + 4 := ht₃
    clear * - ht1' ht3' ht5'
    omega
  · rw [k5 r (by unfold KeepR; omega) (by omega) (by unfold SLx.scr swScr FrFix.frScr; omega),
      K3 r (by unfold KeepR; omega) (by simp only [st2W]; omega) (by omega) (by omega) (by omega)
        (by omega),
      k1 r (by unfold proScr scr1; omega) (by omega) (by omega) (by omega)]
  · refine ⟨?_, by rw [rm5, rm3, rm1]⟩
    by_cases hw : a ≤ Wz
    · rw [z5 a hw, hz a hw]
    · rw [m5 a (by omega) (by show a < q.Qb A0; rw [hQe]; omega) hn, m31 a (by omega) ha]

end Call

end BKMNW

end PlanarFlow
