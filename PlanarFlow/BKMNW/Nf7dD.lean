module

public import PlanarFlow.BKMNW.Nf7dC

/-!
# `fixP` on a part with `0 < k`: step 2 and the glue at a node call

**`st7d_exec`**: from the state the prologue leaves at a node call (`ProOut` of `callIn`), the
memory `≤ Wz` zero, and the MSSP call program meeting `MsspCallSpec` on the piece map,
`st2 msP ; p7dG` runs within `cost m k b + st2T b k + 4` steps to a configuration where the data
`X = mkX …` of the stage loop meets `SLx.Regs`, `SLx.Fix`, `SLx.Stt (X.st 0)`, `SLx.Img`, the
registers of the final step hold `T = X.p`, `SH`, `SH + Wf + 1`, `0`, the rest of the zero area is
zero, and the memory in `(Wz, S1)` and the registers of `KeepR` outside step 2's are kept.
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

/-- The word of a length `c − f₀` from the frame (`CL = CP + Z − FLW`). -/
lemma cl_word {CP FLW Z : ℕ} {U f r : ℤ} (hCP : (CP : ℤ) = U) (hCPZ : CP ≤ Z)
    (hFL : (FLW : ℤ) = Z + f) (hle : f ≤ U) (hr : -f ≤ r) (hrZ : r ≤ Z) :
    ((CP + Z - FLW : ℕ) : ℤ) = U - f ∧ CP + Z - FLW ≤ 2 * Z := by
  omega

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

set_option maxHeartbeats 4000000 in
/-- The inputs of step 2 at a node call (from the frame, the parts and the prologue). -/
theorem st7d_in
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hrot : (pmap hP).RotTrans)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    {A0 W : ℕ}
    (hG : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (callIn d m Gb π j Z mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0) :
    let q := callIn d m Gb π j Z mem
    let X := mkX hP hl hm πj f₀ q (q.Qb A0)
    let E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm
    q.cw.cnt ≤ 2 * q.k ∧
    (∀ i < q.cw.cnt, (pmap hP).face (E (q.cw.bt i)) ∈ πj.faces) ∧
    (∀ i < m, c.nmem (d + 4 + m + i) < m ∧ E (c.nmem (d + 4 + m + i)) = (pmap hP).rev (E i)) ∧
    (∀ i < m, c.nmem (d + 4 + m + m + i) < m ∧
      E (c.nmem (d + 4 + m + m + i)) = (pmap hP).rot (E i)) ∧
    (∀ l < πj.k, c.nmem (q.PDb + l) < m ∧ E (c.nmem (q.PDb + l)) = πj.d l) ∧
    (∀ i < m, (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) : ℤ) =
      ((fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) - f₀) (E i) ∧
      c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) ≤ 2 * Z) ∧
    (∀ i < q.cw.cnt, c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + q.m + i) < m ∧
      E (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + q.m + i)) = E (q.cw.bt i)) ∧
    (∀ a < 2 * πj.k, c.nmem (X.ETb + a) = X.ET a) ∧
    (∀ a < 2 * πj.k, c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.k + a) = X.EH a) := by
  intro q X
  have hkq : πj.k = q.k := hk
  have hk0' : 0 < q.k := hk ▸ hk0
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  intro E
  have hE : E = layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm := rfl
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => layEn_val hi
  have hbt : ∀ y < q.cw.cnt, q.cw.bt y < m := fun y hy => callIn_bt_lt hl hS hj hk0' hy
  have hb2k : q.cw.cnt ≤ 2 * q.k := by
    have := hG.l10
    change q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.cw.cnt ≤
      q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k at this
    omega
  have hmd : mem d = m := hl.hm
  have hPDb : lo ≤ q.PDb := by
    obtain ⟨h1, -⟩ := hS
    show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
    omega
  have hPDk : q.PDb + q.k ≤ hi := (callIn_top (d := d) (Z := Z) hS hj).1
  have hQ : q.Qb A0 = A0 + m + m + m + m + 1 + m + m + m + m + m := rfl
  -- the inputs of step 2
  have hts : ∀ i < q.cw.cnt, (pmap hP).face (E (q.cw.bt i)) ∈ πj.faces := fun i hi => by
    have h := hG.β_mem i hi
    change (if h : q.cw.bt i < m then (pmap hP).face (vDart hl h)
      else (pmap hP).face (πj.d 0)) ∈ πj.faces at h
    rw [dif_pos (hbt i hi)] at h
    have e : vDart hl (hbt i hi) = E (q.cw.bt i) := Subtype.ext (eEv _ (hbt i hi)).symm
    rwa [e] at h
  have hℓ : ∀ e, 0 ≤ ((fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) - f₀) e := fun e => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]
  have hrv : ∀ i < m, c.nmem (d + 4 + m + i) < m ∧
      E (c.nmem (d + 4 + m + i)) = (pmap hP).rev (E i) := fun i hi => by
    rw [alo' _ (by show d + 4 + m + i < A0; omega)]
    obtain ⟨h1, h2⟩ := hl.rv i hi
    exact ⟨h1, Subtype.ext (by rw [eEv _ h1, h2, pmap_rev, eEv i hi])⟩
  have hrt : ∀ i < m, c.nmem (d + 4 + m + m + i) < m ∧
      E (c.nmem (d + 4 + m + m + i)) = (pmap hP).rot (E i) := fun i hi => by
    rw [alo' _ (by show d + 4 + m + m + i < A0; omega)]
    obtain ⟨h1, h2⟩ := hl.sg i hi
    rw [show d + 4 + m + m + i = d + 4 + 2 * m + i by omega]
    refine ⟨h1, Subtype.ext ?_⟩
    rw [eEv _ h1, h2]
    show _ = ((subMap _ _ _ _).rot (E i)).1
    rw [subMap_rot, eEv i hi]
  have hpd : ∀ l < πj.k, c.nmem (q.PDb + l) < m ∧ E (c.nmem (q.PDb + l)) = πj.d l :=
    fun l hl' => by
      obtain ⟨h1, h2⟩ := callIn_pdv hl hP hS hj hk hd hl'
      have hl2 : l < q.k := hkq ▸ hl'
      rw [alo' _ (by omega)]
      exact ⟨h1, by rw [← h2]; exact Subtype.ext (eEv _ h1)⟩
  have hln : ∀ i < m, (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) : ℤ) =
      ((fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) - f₀) (E i) ∧
      c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + i) ≤ 2 * Z := fun i hi => by
    rw [aCL i hi]
    have hcp := hl.cp i hi
    have hcpr := hl.cp _ (hl.rv i hi).1
    have hfl := hFL i hi
    rw [fext_mem _ (hl.en_mem i hi)] at hfl
    have eEi : (⟨en i, hl.en_mem i hi⟩ : SDart (pdarts M x.1.piece x.2.1)) = E i :=
      (Subtype.ext (eEv i hi)).symm
    rw [eEi] at hfl
    have h1 := hf₀.le_cap (E i)
    have h2 := hf₀.le_cap ((pmap hP).rev (E i))
    rw [hf₀.antisymm (E i)] at h2
    have eR : ((pmap hP).rev (E i)).1 = en (mem (d + 4 + m + i)) := by
      rw [pmap_rev, eEv i hi, (hl.rv i hi).2]
    change -f₀ (E i) ≤ u ((pmap hP).rev (E i)).1 at h2
    rw [eR] at h2
    have := cl_word (CP := q.CP i) (FLW := q.FLW i) (Z := q.Z) (U := u (E i).1) (f := f₀ (E i))
      (r := u (en (mem (d + 4 + m + i))))
      (by show (mem (d + 4 + m + m + m + i) : ℤ) = _
          rw [show d + 4 + m + m + m + i = d + 4 + 3 * m + i by omega, hcp.1, eEv i hi])
      (by show mem (d + 4 + m + m + m + i) ≤ Z
          rw [show d + 4 + m + m + m + i = d + 4 + 3 * m + i by omega]; exact hcp.2)
      (by show (mem (d + 4 + m + m + m + m + m + m + i) : ℤ) = Z + _
          rw [show d + 4 + m + m + m + m + m + m + i = d + 4 + 6 * m + i by omega]; exact hfl)
      h1 h2 (by rw [← hcpr.1]; exact_mod_cast hcpr.2)
    exact this
  have hqd : ∀ i < q.cw.cnt, c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + q.m + i) < m ∧
      E (c.nmem (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m + q.m + i)) = E (q.cw.bt i) :=
    fun i hi => by rw [aBT i hi]; exact ⟨hbt i hi, rfl⟩
  have het := mkX_et hP hl hm hrot hS hj hk hd hk0 f₀ (q.Qb A0)
  have hET : ∀ a < 2 * πj.k, c.nmem (X.ETb + a) = X.ET a := fun a ha => by
    obtain ⟨l, rfl | rfl⟩ : ∃ l, a = 2 * l ∨ a = 2 * l + 1 := ⟨a / 2, by omega⟩
    · rw [(het l (by omega)).1, ← (aET l (by omega)).1]; try rfl
    · rw [(het l (by omega)).2.1, ← (aET l (by omega)).2.1]; try rfl
  have hEH : ∀ a < 2 * πj.k, c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.k + a) = X.EH a := fun a ha => by
    obtain ⟨l, rfl | rfl⟩ : ∃ l, a = 2 * l ∨ a = 2 * l + 1 := ⟨a / 2, by omega⟩
    · rw [(het l (by omega)).2.2.1, ← (aET l (by omega)).2.2.1]; try rfl
    · rw [(het l (by omega)).2.2.2, ← (aET l (by omega)).2.2.2]; try rfl
  exact ⟨hb2k, hts, hrv, hrt, hpd, hln, hqd, hET, hEH⟩

set_option maxHeartbeats 4000000 in
/-- The fixed arrays and the first state after step 2 (from the prologue). -/
theorem st7d_fix
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hrot : (pmap hP).RotTrans)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    {A0 W : ℕ}
    (hG : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (callIn d m Gb π j Z mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    {Wz : ℕ} (hWA : Wz < A0) (c₃ : Config)
    (mS : ∀ a, Wz < a → a < (callIn d m Gb π j Z mem).Qb A0 + 15 * (callIn d m Gb π j Z mem).k → c₃.nmem a = c.nmem a)
    (hSI : ∀ e < 2 * πj.k, c₃.nmem (lySI ((callIn d m Gb π j Z mem).Qb A0 + 15 * (callIn d m Gb π j Z mem).k) (callIn d m Gb π j Z mem).cw.cnt πj.k + e) =
      MsCall.sIdx (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) ((callIn d m Gb π j Z mem).Qb A0)).ET (2 * πj.k) (callIn d m Gb π j Z mem).cw.cnt e) :
    let q := (callIn d m Gb π j Z mem)
    let X := mkX hP hl hm πj f₀ q (q.Qb A0)
    X.Fix c₃.nmem ∧ X.Stt (X.st 0) c₃.nmem := by
  have IN := st7d_in hP hrot hl hm hS hj hk hd hk0 hf₀ hFL hG c hO hhi hfr
  intro q X
  have hkq : πj.k = q.k := hk
  have hk0' : 0 < q.k := hk ▸ hk0
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  set E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm with hE
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => layEn_val hi
  have hbt : ∀ y < q.cw.cnt, q.cw.bt y < m := fun y hy => callIn_bt_lt hl hS hj hk0' hy
  have hb2k : q.cw.cnt ≤ 2 * q.k := by
    have := hG.l10
    change q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.cw.cnt ≤
      q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k at this
    omega
  have hmd : mem d = m := hl.hm
  have hPDb : lo ≤ q.PDb := by
    obtain ⟨h1, -⟩ := hS
    show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
    omega
  have hPDk : q.PDb + q.k ≤ hi := (callIn_top (d := d) (Z := Z) hS hj).1
  have hQ : q.Qb A0 = A0 + m + m + m + m + 1 + m + m + m + m + m := rfl
  obtain ⟨hb2k, -, -, -, -, -, -, hET, -⟩ := IN
  -- the bounds of the flow and its net outflows
  have hKB : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hG.hK
  have hB0 : (0 : ℤ) ≤ X.B := by positivity
  have hf0K : ∀ e, |f₀ e| ≤ (X.K : ℤ) := fun e => by
    have h1 : |f₀ e| ≤ (X.B : ℤ) := hG.bf0 e
    push_cast at hKB; linarith
  have hdvK : ∀ v, |(pmap hP).div f₀ v| ≤ (X.K : ℤ) := fun v => by
    have h1 : |(pmap hP).div f₀ v| ≤ (X.B : ℤ) := hG.bdv v
    push_cast at hKB; linarith
  have hAS : ((q.AS : ℕ) : ℤ) = SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) :=
    callIn_as hl
  have mS' : ∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c₃.nmem a = c.nmem a := mS
  have aW5' : ∀ l < q.k, c.nmem (q.Qb A0 + l) = q.CP (q.PD l) ∧
      c.nmem (q.Qb A0 + q.k + l) = q.CP (q.RV (q.PD l)) ∧
      c.nmem (q.Qb A0 + q.k + q.k + l) = q.FLW (q.PD l) + q.K - q.Z ∧
      c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + l) = q.FLW (q.PD l) + q.K - q.Z ∧
      c.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + l) = q.DVw l := aW5
  refine ⟨?_, ?_⟩
  · -- the fixed arrays
    have eSI : lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k = lySI (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k := by
      rw [hkq]
    refine ⟨fun l hl' => ?_, fun l hl' => ?_, fun l hl' => ?_, fun l hl' => ?_, fun a ha => ?_,
      fun e he => ?_⟩
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hl'
      show (c₃.nmem (q.Qb A0 + l) : ℤ) = u (πj.d l).1
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).1]
      exact (callIn_cw hl hPD).trans (congrArg u (by rw [← hv]; rfl))
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hl'
      show (c₃.nmem (q.Qb A0 + q.k + l) : ℤ) = u ((pmap hP).rev (πj.d l)).1
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.1]
      exact (callIn_cw hl (i := q.RV (q.PD l)) (hl.rv _ hPD).1).trans
        (congrArg u (by
          show en (mem (d + 4 + m + (callIn d m Gb π j Z mem).PD l)) = _
          rw [(hl.rv _ hPD).2, pmap_rev, ← hv]; rfl))
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + l) : ℤ) = f₀ (πj.d l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.2.1,
]
      exact (callIn_fw (Gb := Gb) (π := π) (j := j) (K := q.K) hl hFL hPD (hf0K _)).trans
        (by rw [← hv]; rfl)
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + l) : ℤ) =
        (pmap hP).div f₀ (πj.p l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.2.2]
      exact (callIn_dv hl hP hFL hPD (hdvK _)).trans (by rw [hv, πj.tail_d l hl'])
    · have ha2 : a < 2 * q.k := hkq ▸ ha
      show c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + a) = X.ET a
      rw [mS' _ (by omega) (by omega)]; exact hET a ha
    · show c₃.nmem (lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k + e) = _
      rw [eSI]; exact hSI e he
  · -- the state before the first stage
    refine SLx.stt_zero _ (fun l hl' => ?_) (fun y hy => ?_)
    · have hl2 : l < q.k := hkq ▸ hl'
      obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hl'
      show (c₃.nmem (q.Qb A0 + q.k + q.k + l) : ℤ) = f₀ (πj.d l) + q.K
      rw [mS' _ (by omega) (by omega), (aW5' l hl2).2.2.1,
]
      exact (callIn_fw (Gb := Gb) (π := π) (j := j) (K := q.K) hl hFL hPD (hf0K _)).trans
        (by rw [← hv]; rfl)
    · have hy' : y < q.cw.cnt := hy
      show c₃.nmem (q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + y) = 0
      rw [mS' _ (by omega) (by omega)]; exact (aPW y (by omega)).1

set_option maxHeartbeats 8000000 in
/-- The run of step 2 at a node call (`st2_exec` instantiated). -/
theorem st7d_run {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hMS : MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    {A0 W Wz : ℕ} {I : Input}
    (hG : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).Good W)
    (c : Config) (hc : WordsBounded W c) (hO : ProOut (callIn d m Gb π j Z mem) A0 c)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo) (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hwz : wzm m (2 * Z) ≤ Wz)
    (hSHz : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).SH + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((callIn d m Gb π j Z mem).Qb A0 + 15 * (callIn d m Gb π j Z mem).k)
      (callIn d m Gb π j Z mem).cw.cnt (callIn d m Gb π j Z mem).k +
      Rm m (callIn d m Gb π j Z mem).k (callIn d m Gb π j Z mem).cw.cnt ≤ W)
    (hKL : (callIn d m Gb π j Z mem).K + 8 * fpB (callIn d m Gb π j Z mem).AS m
      (callIn d m Gb π j Z mem).k + moOf (callIn d m Gb π j Z mem).cw.cnt
      (8 * fpB (callIn d m Gb π j Z mem).AS m (callIn d m Gb π j Z mem).k) ≤ W) :
    let q := callIn d m Gb π j Z mem
    let X := mkX hP hl hm πj f₀ q (q.Qb A0)
    ∃ c' t, Exec I W (st2 msP) c c' t ∧ t ≤ cost m πj.k q.cw.cnt + st2T q.cw.cnt πj.k ∧
      -- the registers of the stage loop
      c'.nreg 9501 = c.nreg 9416 ∧ c'.nreg 9502 = c.nreg 9412 ∧ c'.nreg 9503 = c.nreg 9413 ∧
      c'.nreg 9504 = X.ETb ∧ c'.nreg 8100 = q.cw.cnt ∧ c'.nreg 9360 = wfOf q.cw.cnt πj.k + 1 ∧
      c'.nreg 9361 = shOf q.cw.cnt πj.k X.L + (wfOf q.cw.cnt πj.k + 1) ∧ c'.nreg 8113 = q.cw.cnt * q.cw.cnt ∧
      c'.nreg 8102 = X.PRb ∧ c'.nreg 8125 = moOf q.cw.cnt X.L - X.K % moOf q.cw.cnt X.L ∧ c'.nreg 8124 = moOf q.cw.cnt X.L ∧
      c'.nreg 8112 = 1 ∧ c'.nreg 8104 = 2 * πj.k ∧
      c'.nreg 8115 = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * πj.k ∧ c'.nreg 9362 = lySI (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k ∧
      c'.nreg 8107 = X.ELb ∧
      c'.nreg 7600 = q.cw.cnt ∧ c'.nreg 7601 = q.cw.cnt ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = q.cw.cnt * q.cw.cnt ∧
      c'.nreg 7604 = q.cw.cnt * q.cw.cnt + q.cw.cnt ∧ c'.nreg 7605 = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * πj.k ∧
      c'.nreg 7607 = lySb q.cw.cnt πj.k ∧ c'.nreg 7608 = lySb q.cw.cnt πj.k + q.cw.cnt ∧
      c'.nreg 7609 = lySb q.cw.cnt πj.k + q.cw.cnt + q.cw.cnt ∧ c'.nreg 7610 = moOf q.cw.cnt X.L ∧
      c'.nreg 7611 = 6 * ((q.cw.cnt + 2) * X.L) ∧ c'.nreg 7612 = wfOf q.cw.cnt πj.k + 1 ∧
      c'.nreg 7614 = lyOb (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k ∧ c'.nreg 7615 = lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k ∧
      c'.nreg 7616 = shOf q.cw.cnt πj.k X.L ∧
      (∀ r, KeepR r → ¬ st2W r → c'.nreg r = c.nreg r) ∧
      -- the resident image and its shadow, the rest of the zero area
      ImgAt c'.nmem (img0 q.cw.cnt X.Dm X.ET X.EH πj.k) X.L (lySb q.cw.cnt πj.k) (wfOf q.cw.cnt πj.k) (shOf q.cw.cnt πj.k X.L) ∧
      ZeroAt c'.nmem Wz (lySb q.cw.cnt πj.k) (wfOf q.cw.cnt πj.k) (shOf q.cw.cnt πj.k X.L) ∧
      -- the sorted indices, the memory kept
      (∀ e < 2 * πj.k, c'.nmem (lySI (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k + e) = MsCall.sIdx X.ET (2 * πj.k) q.cw.cnt e) ∧
      (∀ a, Wz < a → a < (q.Qb A0 + 15 * q.k) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro q X
  have IN := st7d_in hP hrot hl hm hS hj hk hd hk0 hf₀ hFL hG c hO hhi hfr
  have hkq : πj.k = q.k := hk
  have hk0' : 0 < q.k := hk ▸ hk0
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  set E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm with hE
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => layEn_val hi
  have hbt : ∀ y < q.cw.cnt, q.cw.bt y < m := fun y hy => callIn_bt_lt hl hS hj hk0' hy
  have hb2k : q.cw.cnt ≤ 2 * q.k := by
    have := hG.l10
    change q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.cw.cnt ≤
      q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k at this
    omega
  have hmd : mem d = m := hl.hm
  have hPDb : lo ≤ q.PDb := by
    obtain ⟨h1, -⟩ := hS
    show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
    omega
  have hPDk : q.PDb + q.k ≤ hi := (callIn_top (d := d) (Z := Z) hS hj).1
  have hQ : q.Qb A0 = A0 + m + m + m + m + 1 + m + m + m + m + m := rfl
  obtain ⟨hb2k, hts, hrv, hrt, hpd, hln, hqd, hET, hEH⟩ := IN
  have hℓ : ∀ e, 0 ≤ ((fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) - f₀) e := fun e => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]
  -- sizes
  have hSHz' : X.SH + X.WN ≤ Wz := hSHz
  have hWfe : X.Wf = wfOf q.cw.cnt πj.k := rfl
  have hMo : X.Mo = moOf q.cw.cnt X.L := rfl
  have hSHe : X.SH = shOf q.cw.cnt πj.k X.L := by
    show shOf q.cw.cnt q.k _ = _; rw [hk]; rfl
  have hSHWN : X.SH = X.WN + 1 := by
    rw [hSHe]; show _ = 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo + 1; rw [hMo, hWfe]; unfold shOf; ring
  have hlwf := lySb_le_wfOf q.cw.cnt πj.k
  have hWN1 : 2 * wfOf q.cw.cnt πj.k + 1 ≤ X.WN := by
    show _ ≤ 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo; rw [hWfe]; omega
  have hlow : shOf q.cw.cnt πj.k X.L + (wfOf q.cw.cnt πj.k + 1) + lySb q.cw.cnt πj.k ≤ Wz + 1 := by
    rw [← hSHe]; omega
  have hpw' : lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k + Rm m πj.k q.cw.cnt ≤ W := by
    rw [hk]; exact hpw
  have hQe : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  have hOm : q.Qb A0 + 15 * q.k ≤ lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k := by
    unfold lyOm; omega
  have hOmP : lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k + q.cw.cnt * q.cw.cnt ≤
      lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k := by
    unfold lyP lyOb lyS lyA; omega
  have hWA : Wz < A0 := by omega
  have hPRS : X.PRb + q.cw.cnt ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.cw.cnt ≤ _; omega
  have hETS : X.ETb + 2 * πj.k ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * πj.k ≤ _; omega
  have hEHS : q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * πj.k ≤
      q.Qb A0 + 15 * q.k := by omega
  have hELS : X.ELb + 2 * πj.k ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + 2 * πj.k ≤ _; omega
  have hzA : Wz < X.PRb ∧ Wz < X.ETb ∧
      Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k ∧ Wz < X.ELb := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
        q.k; omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k; omega
    · omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k; omega
  have hpla : MsCall.MsPlace m πj.k q.cw.cnt Wz W (d + 4 + m) (d + 4 + m + m) q.PDb
      (A0 + m + m + m + m + 1 + m + m + m) (A0 + m + m + m + m + 1 + m + m + m + m)
      (lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k) (lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k)
      (Rm m πj.k q.cw.cnt) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, ⟨by omega, hOmP⟩, hpw'⟩
  -- step 2
  obtain ⟨c₂, t₂, e₂, ht₂, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b14, b15, b16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩ :=
    st2_exec (pmap hP) hMS hScr hpl hrot (en := E) (m := m) (P := πj)
      (ℓ := (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) - f₀) (Lmax := 2 * Z)
      (b := q.cw.cnt) (ts := fun i => E (q.cw.bt i)) (RVb := d + 4 + m) (RTb := d + 4 + m + m)
      (Pb := q.PDb) (Lb := A0 + m + m + m + m + 1 + m + m + m)
      (Qb := A0 + m + m + m + m + 1 + m + m + m + m) (S1 := q.Qb A0 + 15 * q.k) (PRb := X.PRb)
      (ETb := X.ETb) (EHb := q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k)
      (ELb := X.ELb) (K := X.K) (L := X.L) (Wz := Wz) (W := W) (ET := X.ET) (EH := X.EH)
      (Dm := X.Dm) (I := I) c hc (lay_enumOK hP hl hm hface) hk0 hℓ hts (fun _ _ _ _ => rfl)
      (by rw [g18]; ring) a19 (by rw [g01, hk]) g36 g00 g30 g31 g02 g09 g10 g17 g14 g15 g77 a10 a22
      hrv hrt hpd hln hqd (fun x hx => (aPW x (by omega)).2.1) hET hEH
      (fun a ha => (aPW a (by omega)).2.2) hpla (by omega) hPRS hETS hEHS hELS hzA
      (SLx.frImgB0 hG) hz hwz hlow hKL
  exact ⟨c₂, t₂, e₂, ht₂, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b14, b15, b16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩

set_option maxHeartbeats 8000000 in
/-- **Step 2 and the glue at a node call** (see the module docstring). -/
theorem st7d_exec {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hMS : MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    {A0 W Wz : ℕ} {I : Input}
    (hG : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).Good W)
    (c : Config) (hc : WordsBounded W c) (hO : ProOut (callIn d m Gb π j Z mem) A0 c)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo) (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hwz : wzm m (2 * Z) ≤ Wz)
    (hSHz : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).SH + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem)
      ((callIn d m Gb π j Z mem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((callIn d m Gb π j Z mem).Qb A0 + 15 * (callIn d m Gb π j Z mem).k)
      (callIn d m Gb π j Z mem).cw.cnt (callIn d m Gb π j Z mem).k +
      Rm m (callIn d m Gb π j Z mem).k (callIn d m Gb π j Z mem).cw.cnt ≤ W)
    (hKL : (callIn d m Gb π j Z mem).K + 8 * fpB (callIn d m Gb π j Z mem).AS m
      (callIn d m Gb π j Z mem).k + moOf (callIn d m Gb π j Z mem).cw.cnt
      (8 * fpB (callIn d m Gb π j Z mem).AS m (callIn d m Gb π j Z mem).k) ≤ W) :
    let q := callIn d m Gb π j Z mem
    let X := mkX hP hl hm πj f₀ q (q.Qb A0)
    ∃ c' t, Exec I W (.seq (st2 msP) p7dG) c c' t ∧ t ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k + 4 ∧
      X.Regs c' ∧ X.Fix c'.nmem ∧ X.Stt (X.st 0) c'.nmem ∧ X.Img c'.nmem ∧
      c'.nreg 9469 = X.p ∧ c'.nreg 9471 = X.SH ∧ c'.nreg 9474 = X.SH + (X.Wf + 1) ∧
      c'.nreg 9475 = 0 ∧
      (∀ r, KeepR r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 →
        c'.nreg r = c.nreg r) ∧
      (∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro q X
  have IN := st7d_in hP hrot hl hm hS hj hk hd hk0 hf₀ hFL hG c hO hhi hfr
  have hkq : πj.k = q.k := hk
  have hk0' : 0 < q.k := hk ▸ hk0
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  set E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm with hE
  have eEv : ∀ i < m, (E i).1 = en i := fun i hi => layEn_val hi
  have hbt : ∀ y < q.cw.cnt, q.cw.bt y < m := fun y hy => callIn_bt_lt hl hS hj hk0' hy
  have hb2k : q.cw.cnt ≤ 2 * q.k := by
    have := hG.l10
    change q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.cw.cnt ≤
      q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k at this
    omega
  have hmd : mem d = m := hl.hm
  have hPDb : lo ≤ q.PDb := by
    obtain ⟨h1, -⟩ := hS
    show lo ≤ Gb + 1 + π.segs.length + π.segs.length + _
    omega
  have hPDk : q.PDb + q.k ≤ hi := (callIn_top (d := d) (Z := Z) hS hj).1
  have hQ : q.Qb A0 = A0 + m + m + m + m + 1 + m + m + m + m + m := rfl
  obtain ⟨hb2k, hts, hrv, hrt, hpd, hln, hqd, hET, hEH⟩ := IN
  -- sizes
  have hSHz' : X.SH + X.WN ≤ Wz := hSHz
  have hWfe : X.Wf = wfOf q.cw.cnt πj.k := rfl
  have hMo : X.Mo = moOf q.cw.cnt X.L := rfl
  have hSHe : X.SH = shOf q.cw.cnt πj.k X.L := by
    show shOf q.cw.cnt q.k _ = _; rw [hk]; rfl
  have hSHWN : X.SH = X.WN + 1 := by
    rw [hSHe]; show _ = 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo + 1; rw [hMo, hWfe]; unfold shOf; ring
  have hlwf := lySb_le_wfOf q.cw.cnt πj.k
  have hWN1 : 2 * wfOf q.cw.cnt πj.k + 1 ≤ X.WN := by
    show _ ≤ 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo; rw [hWfe]; omega
  have hlow : shOf q.cw.cnt πj.k X.L + (wfOf q.cw.cnt πj.k + 1) + lySb q.cw.cnt πj.k ≤ Wz + 1 := by
    rw [← hSHe]; omega
  have hpw' : lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k + Rm m πj.k q.cw.cnt ≤ W := by
    rw [hk]; exact hpw
  have hQe : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  have hOm : q.Qb A0 + 15 * q.k ≤ lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k := by
    unfold lyOm; omega
  have hOmP : lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k + q.cw.cnt * q.cw.cnt ≤
      lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k := by
    unfold lyP lyOb lyS lyA; omega
  have hWA : Wz < A0 := by omega
  have hPRS : X.PRb + q.cw.cnt ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.cw.cnt ≤ _; omega
  have hETS : X.ETb + 2 * πj.k ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * πj.k ≤ _; omega
  have hEHS : q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * πj.k ≤
      q.Qb A0 + 15 * q.k := by omega
  have hELS : X.ELb + 2 * πj.k ≤ q.Qb A0 + 15 * q.k := by
    show q.Qb A0 + q.k + q.k + q.k + 2 * πj.k ≤ _; omega
  have hzA : Wz < X.PRb ∧ Wz < X.ETb ∧
      Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k ∧ Wz < X.ELb := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
        q.k; omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k; omega
    · omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k; omega
  have hpla : MsCall.MsPlace m πj.k q.cw.cnt Wz W (d + 4 + m) (d + 4 + m + m) q.PDb
      (A0 + m + m + m + m + 1 + m + m + m) (A0 + m + m + m + m + 1 + m + m + m + m)
      (lyOm (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k) (lyP (q.Qb A0 + 15 * q.k) q.cw.cnt πj.k)
      (Rm m πj.k q.cw.cnt) :=
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, ⟨by omega, hOmP⟩, hpw'⟩
  clear hpla
  -- step 2
  obtain ⟨c₂, t₂, e₂, ht₂, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b14, b15, b16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩ :=
    st7d_run hP hMS hScr hpl hrot hface hl hm hS hj hk hd hk0 hf₀ hFL (I := I) hG c hc
      ⟨⟨g00, g03, g36, g21, g01, g71, g02,
      g30, g31, g34, g35, g04, g05, g06, g07, g08, g09, g10, g11, g74, g75, g76, g77, g12, g13, g14,
      g15, g16, g17, g18⟩, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩
      hz hWzd hWlo hhi hfr hwz hSHz hpw hKL
  obtain ⟨c₃, t₃, e₃, ht₃, p69, p71, p74, p75, pk, pm, pr, prm, po⟩ :=
    p7dG_exec (P := I) c₂ e₂.wb_right
  rw [hkq] at ht₂ s62 b14 b15 b16
  have K2 : ∀ r, KeepR r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 h6 => by rw [pk r h3 h4 h5 h6, sk r h1 h2]
  have K3 : ∀ r, r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → c₃.nreg r = c₂.nreg r := pk
  have nS : ∀ r, 9300 ≤ r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 →
      c₃.nreg r = c.nreg r := fun r h1 => K2 r (keepR_ge h1)
  have mS : ∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [pm]; exact sm a h1 h2
  -- the bounds of the flow and its net outflows
  have hKB : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hG.hK
  have hB0 : (0 : ℤ) ≤ X.B := by positivity
  have hf0K : ∀ e, |f₀ e| ≤ (X.K : ℤ) := fun e => by
    have h1 : |f₀ e| ≤ (X.B : ℤ) := hG.bf0 e
    push_cast at hKB; linarith
  have hdvK : ∀ v, |(pmap hP).div f₀ v| ≤ (X.K : ℤ) := fun v => by
    have h1 : |(pmap hP).div f₀ v| ≤ (X.B : ℤ) := hG.bdv v
    push_cast at hKB; linarith
  have hAS : ((q.AS : ℕ) : ℤ) = SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) :=
    callIn_as hl
  have ht₂' : t₂ ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k := by
    change t₂ ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k at ht₂; exact ht₂
  have sZ' : ZeroAt c₂.nmem Wz (lySb q.cw.cnt πj.k) (wfOf q.cw.cnt πj.k) (shOf q.cw.cnt πj.k X.L) :=
    sZ
  refine ⟨c₃, _, e₂.seq e₃, by omega, ?_, ?_, ?_, ?_, by rw [p69, b15]; rfl, by rw [p71, b16]; rfl,
    by rw [p74, s61, ← hSHe]; rfl, p75, K2, ?_, mS, by rw [pr, sr], by rw [prm, srm], by rw [po, so]⟩
  · -- the registers
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), a10]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), g71]; exact hk.symm
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), a73]
      have e : (4 * SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) + 1).toNat =
          4 * q.AS + 1 := by rw [← hAS]; omega
      exact e.symm
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), g74]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), g75]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), g76]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), g77]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s01, g16]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s02, g12]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s03, g13]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s04]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s00
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s60
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; rw [s61, ← hSHe]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s13
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s8102
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s25
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s24
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s12
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s8104
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s15
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s62
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s8107
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b00
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b01
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b02
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b03
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b04
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b05
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b07
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b08
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b09
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b10
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b11
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b12
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b14
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b15
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact b16
  · exact (st7d_fix hP hrot hl hm hS hj hk hd hk0 hf₀ hFL hG c ⟨⟨g00, g03, g36, g21, g01, g71, g02,
      g30, g31, g34, g35, g04, g05, g06, g07, g08, g09, g10, g11, g74, g75, g76, g77, g12, g13, g14,
      g15, g16, g17, g18⟩, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ hhi hfr hWA
      c₃ mS (fun e he => by rw [pm]; exact sSI e he)).1
  · exact (st7d_fix hP hrot hl hm hS hj hk hd hk0 hf₀ hFL hG c ⟨⟨g00, g03, g36, g21, g01, g71, g02,
      g30, g31, g34, g35, g04, g05, g06, g07, g08, g09, g10, g11, g74, g75, g76, g77, g12, g13, g14,
      g15, g16, g17, g18⟩, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ hhi hfr hWA
      c₃ mS (fun e he => by rw [pm]; exact sSI e he)).2
  · -- the image
    have hI : ImgAt c₃.nmem (img0 X.b X.Dm X.ET X.EH X.P.k) X.L (lySb X.b X.P.k)
        (wfOf X.b X.P.k) X.SH := by rw [pm, hSHe]; exact sI
    have hZ : ZeroAt c₃.nmem Wz (lySb X.b X.P.k) (wfOf X.b X.P.k) X.SH := by
      rw [pm, hSHe]; exact sZ
    exact SLx.img_of_st2 hG hI hZ hSHz' hWfe
  · -- the rest of the zero area
    intro a ha h1 h2
    have e1 := hSHWN
    rw [hSHe] at e1 h2
    rw [pm]
    refine sZ' a ha (by omega) (by omega) (by omega) (by omega)


end Call

end BKMNW

end PlanarFlow
