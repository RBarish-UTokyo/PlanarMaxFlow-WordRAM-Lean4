module

public import PlanarFlow.BKMNW.Nf7bC

/-!
# The stage loop of `fixP`, part D: the layout, the invariant, the image of a stage

* **`SLx M`** (the data of the stage loop: the path, `c`, `f₀`, the MSSP and FR functions, the
  corners `β`/`idx`, the natural matrix `Dm`, the offset `K`, the bounds `B`, `L`, the bases of
  the arrays), its derived numbers (`Wf = W + 1 − 1` of the FR inputs, `Mo = frM`, `H = frH`,
  `WN = frWN`, `lb`, `LG` the room of the log), `SLx.prm pm r Lz` (the FR input of a stage);
* **`SLx.Regs`** (the registers of the layout), **`SLx.Good`** (the hypotheses: the problem, the
  corners, the matrix, the bounds, the layout chain), `SLx.Fix` (the fixed arrays), `SLx.Stt`
  (the arrays `FW`, `PW` hold the state), `SLx.Img` (the resident image and its shadow are the image
  of some FR input of the stage family), `SLx.scr` (the scratch registers), **`SLx.J`** (the loop
  invariant);
* **`SLx.img_upd`**: rewriting the residues of the prices and of the sorted lengths turns the image
  of one stage input into that of another (live and shadow).

## The layout (registers)
`9310 = K`, `9371 = k`, `9373 = Mbw = 4 absSum c + 1`, `9374 = CWb`, `9375 = CRb`, `9376 = FWb`,
`9377 = ELb`, `9501 = PWb`, `9502 = F0b`, `9503 = DVb`, `9504 = ETb`; `imU`: `8100 = b`,
`9360 = Wf + 1`, `9361 = SH + Wf + 1`, `8113 = b²`, `8102 = PRb`, `8125 = Mo − K mod Mo`,
`8124 = Mo`, `8112 = 1`, `8104 = 2k`, `8115 = lb`, `9362 = SIb`, `8107 = ELb`; `frRun`:
`7600 = 7601 = b`, `7602 = 0`, `7603 = b²`, `7604 = b² + b`, `7605 = lb`, `7607 = lb + 2k`,
`7608 = lb + 2k + b`, `7609 = lb + 2k + 2b`, `7610 = Mo`, `7611 = H`, `7612 = Wf + 1`,
`7614 = Ob`, `7615 = p`, `7616 = SH`.
## The layout (memory)
image `[0, WN]`, shadow `[SH, SH + WN]`, then (in this order, gaps allowed; the order of the
prologue: `CW = Q`, `CR = Q + k`, `FW = Q + 2k`, `EL = Q + 3k`, `F0 = Q + 5k`, `DV = Q + 6k`,
`ET = Q + 7k`, `PW = Q + 11k`, `PR = Q + 13k`) `CW[k]`, `CR[k]`, `FW[k]`, `EL[2k]`, `F0[k]`,
`DV[k]`, `ET[2k]`, `PW[b]`, `PR[b]`, `SI[2k]`, the FR answers `[Ob, Ob + 2b)`, the log
`[p, p + LG)`, `p + LG ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine Monge.FR

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **The data of the stage loop.** -/
structure SLx (M : CombMap D V F) where
  P : SPath M
  c : D → ℤ
  f₀ : D → ℤ
  mssp : List D → (D → ℤ) → F → F → Option ℤ
  fr : FRFun F
  b : ℕ
  β : ℕ → F
  idx : F → ℕ
  Dm : ℕ → ℕ → ℕ
  K : ℕ
  B : ℕ
  L : ℕ
  CWb : ℕ
  CRb : ℕ
  F0b : ℕ
  DVb : ℕ
  FWb : ℕ
  ETb : ℕ
  SIb : ℕ
  PWb : ℕ
  PRb : ℕ
  ELb : ℕ
  SH : ℕ
  Ob : ℕ
  p : ℕ

namespace SLx

variable {M : CombMap D V F} (X : SLx M)

/-- The tails of the explicit arcs (corner numbers). -/
noncomputable def ET (a : ℕ) : ℕ := X.idx (M.face (dartAt X.P a))

/-- The heads of the explicit arcs (corner numbers). -/
noncomputable def EH (a : ℕ) : ℕ := X.idx (M.face (M.rev (dartAt X.P a)))

/-- The FR input of a stage. -/
noncomputable def prm (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) : Prm :=
  MsCall.frPrm X.b X.Dm pm r X.ET X.EH Lz (2 * X.P.k)

/-- The base of the lengths of the explicit arcs in an FR input. -/
def lb : ℕ := X.b * X.b + X.b + X.b + 1 + 2 * X.P.k

/-- The word bound `W` of the FR inputs. -/
def Wf : ℕ := MsCall.fW X.b (X.lb + 2 * X.P.k + X.b + X.b)

/-- The modulus `frM`. -/
def Mo : ℕ := 2 * (6 * ((X.b + 2) * X.L)) + 1

/-- The half modulus `frH`. -/
def H : ℕ := 6 * ((X.b + 2) * X.L)

/-- The top of the resident image (`frWN`). -/
def WN : ℕ := 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo

/-- The room of the log of a run. -/
def LG : ℕ := 4 * (6300 * (X.b * lg X.b ^ 2 + 2 * X.P.k * lg X.b)) + 3

/-- `4 absSum c + 1` as a word. -/
def Mbw : ℕ := (4 * absSum X.c + 1).toNat

/-- The dense distance graph of the stages. -/
noncomputable def Dst : DDG F := ⟨X.P.faces, X.mssp X.P.darts (X.c - X.f₀)⟩

/-- The state after `i` stages. -/
noncomputable def st (i : ℕ) : (D → ℤ) × (F → ℤ) := fpState M X.c X.f₀ X.P X.mssp X.fr i

/-- **The registers of the layout.** -/
def Regs (c : Config) : Prop :=
  (c.nreg 9310 = X.K ∧ c.nreg 9371 = X.P.k ∧ c.nreg 9373 = X.Mbw ∧ c.nreg 9374 = X.CWb ∧
    c.nreg 9375 = X.CRb ∧ c.nreg 9376 = X.FWb ∧ c.nreg 9377 = X.ELb ∧ c.nreg 9501 = X.PWb ∧
    c.nreg 9502 = X.F0b ∧ c.nreg 9503 = X.DVb ∧ c.nreg 9504 = X.ETb) ∧
  (c.nreg 8100 = X.b ∧ c.nreg 9360 = X.Wf + 1 ∧ c.nreg 9361 = X.SH + (X.Wf + 1) ∧
    c.nreg 8113 = X.b * X.b ∧ c.nreg 8102 = X.PRb ∧ c.nreg 8125 = X.Mo - X.K % X.Mo ∧
    c.nreg 8124 = X.Mo ∧ c.nreg 8112 = 1 ∧ c.nreg 8104 = 2 * X.P.k ∧ c.nreg 8115 = X.lb ∧
    c.nreg 9362 = X.SIb ∧ c.nreg 8107 = X.ELb) ∧
  (c.nreg 7600 = X.b ∧ c.nreg 7601 = X.b ∧ c.nreg 7602 = 0 ∧ c.nreg 7603 = X.b * X.b ∧
    c.nreg 7604 = X.b * X.b + X.b ∧ c.nreg 7605 = X.lb ∧ c.nreg 7607 = X.lb + 2 * X.P.k ∧
    c.nreg 7608 = X.lb + 2 * X.P.k + X.b ∧ c.nreg 7609 = X.lb + 2 * X.P.k + X.b + X.b ∧
    c.nreg 7610 = X.Mo ∧ c.nreg 7611 = X.H ∧ c.nreg 7612 = X.Wf + 1 ∧ c.nreg 7614 = X.Ob ∧
    c.nreg 7615 = X.p ∧ c.nreg 7616 = X.SH)

/-- **The hypotheses of the stage loop.** -/
structure Good (W : ℕ) : Prop where
  plane : M.IsPlane
  c_nn : ∀ e, 0 ≤ X.c e
  pseudo : IsPseudo M X.c X.f₀
  mssp_spec : MSSPSpecAt M X.mssp X.P
  fr_spec : FRSpec X.fr
  k_pos : 0 < X.P.k
  β_mem : ∀ x < X.b, X.β x ∈ X.P.faces
  idx_lt : ∀ y ∈ X.P.faces, X.idx y < X.b
  β_idx : ∀ y ∈ X.P.faces, X.β (X.idx y) = y
  inj : ∀ i < X.b, ∀ j < X.b, X.β i = X.β j → i = j
  dsome : ∀ i < X.b, ∀ j < X.b, ∃ a, X.Dst.len (X.β i) (X.β j) = some a
  dm : ∀ i < X.b, ∀ j < X.b, (X.Dm i j : ℤ) = (X.Dst.len (X.β i) (X.β j)).getD 0
  cross : Monge.Crossing X.b fun i j => (X.Dm i j : ℤ)
  dmL : ∀ i < X.b, ∀ j < X.b, X.Dm i j ≤ X.L
  bf0 : ∀ e, |X.f₀ e| ≤ (X.B : ℤ)
  bdv : ∀ v, |M.div X.f₀ v| ≤ (X.B : ℤ)
  bc : 4 * absSum X.c + 1 ≤ (X.B : ℤ)
  bst : 2 * (absSum X.c + (4 * absSum X.c + 1)) + X.P.k * Bst D X.c ≤ (X.B : ℤ)
  hK : 16 * X.B ≤ X.K
  hL : 8 * X.B ≤ X.L
  l1 : X.WN < X.SH
  l2 : X.SH + X.WN < X.CWb
  l3 : X.CWb + X.P.k ≤ X.CRb
  l4 : X.CRb + X.P.k ≤ X.FWb
  l5 : X.FWb + X.P.k ≤ X.ELb
  l6 : X.ELb + 2 * X.P.k ≤ X.F0b
  l7 : X.F0b + X.P.k ≤ X.DVb
  l8 : X.DVb + X.P.k ≤ X.ETb
  l9 : X.ETb + 2 * X.P.k ≤ X.PWb
  l10 : X.PWb + X.b ≤ X.PRb
  l11 : X.PRb + X.b ≤ X.SIb
  l12 : X.SIb + 2 * X.P.k ≤ X.Ob
  l13 : X.Ob + X.b + X.b ≤ X.p
  l14 : X.p + X.LG ≤ W
  w1 : 16 * X.K + 1 ≤ W
  w2 : X.Mo + 3 * X.K ≤ W

/-- **The fixed arrays.** -/
def Fix (nm : ℕ → ℕ) : Prop :=
  (∀ l < X.P.k, (nm (X.CWb + l) : ℤ) = X.c (X.P.d l)) ∧
  (∀ l < X.P.k, (nm (X.CRb + l) : ℤ) = X.c (M.rev (X.P.d l))) ∧
  (∀ l < X.P.k, (nm (X.F0b + l) : ℤ) = X.f₀ (X.P.d l) + X.K) ∧
  (∀ l < X.P.k, (nm (X.DVb + l) : ℤ) = M.div X.f₀ (X.P.p l) + X.K) ∧
  (∀ a < 2 * X.P.k, nm (X.ETb + a) = X.ET a) ∧
  (∀ e < 2 * X.P.k, nm (X.SIb + e) = MsCall.sIdx X.ET (2 * X.P.k) X.b e)

/-- **The arrays `FW`, `PW` hold the state `s`.** -/
def Stt (s : (D → ℤ) × (F → ℤ)) (nm : ℕ → ℕ) : Prop :=
  (∀ l < X.P.k, (nm (X.FWb + l) : ℤ) = s.1 (X.P.d l) + X.K) ∧
  (∀ x < X.b, (nm (X.PWb + x) : ℤ) = s.2 (X.β x))

/-- **The resident image and its shadow** are the image of an FR input of the stages. -/
def Img (nm : ℕ → ℕ) : Prop :=
  ∃ (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ),
    MsCall.FrImgB X.b X.Dm pm r (2 * X.P.k) X.ET X.EH Lz X.L ∧
    ∀ a ≤ X.WN, nm a = (FrFix.frCfgN (X.prm pm r Lz) X.L).nmem a ∧
      nm (X.SH + a) = (FrFix.frCfgN (X.prm pm r Lz) X.L).nmem a

/-- The memory cells written by the loop above the shadow. -/
def Wr (a : ℕ) : Prop :=
  (X.FWb ≤ a ∧ a < X.FWb + X.P.k) ∨ (X.PWb ≤ a ∧ a < X.PRb + X.b) ∨
    (X.ELb ≤ a ∧ a < X.ELb + 2 * X.P.k) ∨ (X.Ob ≤ a ∧ a < X.Ob + X.b + X.b) ∨
    (X.p ≤ a ∧ a < X.p + X.LG)

/-- The scratch registers of a stage. -/
def scr (r : ℕ) : Prop :=
  swScr r ∨ (9311 ≤ r ∧ r ≤ 9320) ∨ r = 9370 ∨ r = 9372 ∨ (9378 ≤ r ∧ r ≤ 9387) ∨ r = 8126 ∨
    (8140 ≤ r ∧ r ≤ 8149) ∨ FrFix.frScr r ∨ r = 7606 ∨ r = 9500 ∨ (9505 ≤ r ∧ r ≤ 9511) ∨
    (9520 ≤ r ∧ r ≤ 9531)

/-- **The invariant of the stage loop** before stage `i` (relative to the start `c₀`). -/
def J (c₀ : Config) (i : ℕ) (c : Config) : Prop :=
  c.nreg 9500 = i ∧ (∀ r, ¬ scr r → c.nreg r = c₀.nreg r) ∧ X.Stt (X.st i) c.nmem ∧
    X.Img c.nmem ∧
    (∀ a, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → ¬ X.Wr a → c.nmem a = c₀.nmem a) ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The cost of a stage. -/
def T : ℕ := 108 * (6300 * (X.b * lg X.b ^ 2 + 2 * X.P.k * lg X.b)) + 56 * X.b + 68 * X.P.k + 1200

/-! ### Basic facts -/

variable {X}

lemma dartAt_mem {a : ℕ} (ha : a < 2 * X.P.k) : dartAt X.P a ∈ X.P.darts := by
  rw [darts_eq, List.mem_map]; exact ⟨a, List.mem_range.2 ha, rfl⟩

lemma ET_lt {W : ℕ} (hG : X.Good W) {a : ℕ} (ha : a < 2 * X.P.k) : X.ET a < X.b :=
  hG.idx_lt _ (X.P.face_mem (dartAt_mem ha))

lemma EH_lt {W : ℕ} (hG : X.Good W) {a : ℕ} (ha : a < 2 * X.P.k) : X.EH a < X.b :=
  hG.idx_lt _ (X.P.face_mem (X.P.rev_mem_darts (dartAt_mem ha)))

lemma b_pos {W : ℕ} (hG : X.Good W) : 1 ≤ X.b := by
  have := ET_lt hG (a := 0) (by have := hG.k_pos; omega); omega

lemma lb_le_Wf : X.lb + 2 * X.P.k + X.b + X.b ≤ X.Wf := by
  unfold Wf MsCall.fW; omega

lemma prm_W {W : ℕ} (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    (X.prm pm r Lz).W = X.Wf := by
  rw [prm, MsCall.frPrm_W (fun a ha => ET_lt hG ha)]; rfl

lemma prm_WN {W : ℕ} (hG : X.Good W) (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) :
    frWN (X.prm pm r Lz) X.L = X.WN := by
  unfold frWN WN; rw [prm_W hG]; rfl

lemma prm_M (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) : frM (X.prm pm r Lz) X.L = X.Mo := rfl

lemma prm_H (pm : ℕ → ℤ) (r : ℕ) (Lz : ℕ → ℤ) : frH (X.prm pm r Lz) X.L = X.H := rfl

/-- **Rewriting the residues of the prices and of the sorted lengths** (live and shadow) turns
the image of one stage input into that of another. -/
theorem img_upd {W : ℕ} (hG : X.Good W) {pm pm' : ℕ → ℤ} {r r' : ℕ} {Lz Lz' : ℕ → ℤ}
    (hb : MsCall.FrImgB X.b X.Dm pm r (2 * X.P.k) X.ET X.EH Lz X.L)
    (hb' : MsCall.FrImgB X.b X.Dm pm' r' (2 * X.P.k) X.ET X.EH Lz' X.L) {nm nm' : ℕ → ℕ}
    (himg : ∀ a ≤ X.WN, nm a = (FrFix.frCfgN (X.prm pm r Lz) X.L).nmem a ∧
      nm (X.SH + a) = (FrFix.frCfgN (X.prm pm r Lz) X.L).nmem a)
    (hp : ∀ x < X.b, nm' (X.Wf + 1 + X.b * X.b + x) = (pm' x % (X.Mo : ℤ)).toNat ∧
      nm' (X.SH + (X.Wf + 1) + X.b * X.b + x) = (pm' x % (X.Mo : ℤ)).toNat)
    (hl : ∀ e < 2 * X.P.k,
      nm' (X.Wf + 1 + X.lb + e) = (Lz' (MsCall.sIdx X.ET (2 * X.P.k) X.b e) % (X.Mo : ℤ)).toNat ∧
      nm' (X.SH + (X.Wf + 1) + X.lb + e) =
        (Lz' (MsCall.sIdx X.ET (2 * X.P.k) X.b e) % (X.Mo : ℤ)).toNat)
    (hk : ∀ a, a ≤ X.SH + X.WN → ¬ (X.Wf + 1 + X.b * X.b ≤ a ∧ a < X.Wf + 1 + X.b * X.b + X.b) →
      ¬ (X.Wf + 1 + X.lb ≤ a ∧ a < X.Wf + 1 + X.lb + 2 * X.P.k) →
      ¬ (X.SH + (X.Wf + 1) + X.b * X.b ≤ a ∧ a < X.SH + (X.Wf + 1) + X.b * X.b + X.b) →
      ¬ (X.SH + (X.Wf + 1) + X.lb ≤ a ∧ a < X.SH + (X.Wf + 1) + X.lb + 2 * X.P.k) →
      nm' a = nm a) :
    ∀ a ≤ X.WN, nm' a = (FrFix.frCfgN (X.prm pm' r' Lz') X.L).nmem a ∧
      nm' (X.SH + a) = (FrFix.frCfgN (X.prm pm' r' Lz') X.L).nmem a := by
  have hWf := X.lb_le_Wf
  have hSH := hG.l1
  have hWN : 2 * X.Wf + 1 ≤ X.WN := by unfold WN; omega
  intro a ha
  have key := MsCall.frCfgN_frPrm_upd hb hb' a
  have eW : (MsCall.frPrm X.b X.Dm pm r X.ET X.EH Lz (2 * X.P.k)).W = X.Wf := prm_W hG pm r Lz
  rw [eW] at key
  have eM : (frM (MsCall.frPrm X.b X.Dm pm r X.ET X.EH Lz (2 * X.P.k)) X.L : ℤ) = (X.Mo : ℤ) := rfl
  rw [eM] at key
  have elb : X.b * X.b + X.b + X.b + 1 + 2 * X.P.k = X.lb := rfl
  rw [elb] at key
  show nm' a = (FrFix.frCfgN (MsCall.frPrm X.b X.Dm pm' r' X.ET X.EH Lz' (2 * X.P.k)) X.L).nmem a ∧
    nm' (X.SH + a) = (FrFix.frCfgN (MsCall.frPrm X.b X.Dm pm' r' X.ET X.EH Lz' (2 * X.P.k)) X.L).nmem a
  rw [key]
  have ho := himg a ha
  by_cases h1 : X.Wf + 1 + X.b * X.b ≤ a ∧ a < X.Wf + 1 + X.b * X.b + X.b
  · simp only [h1, and_self, ↓reduceIte]
    obtain ⟨x, rfl⟩ : ∃ x, a = X.Wf + 1 + X.b * X.b + x := ⟨a - (X.Wf + 1 + X.b * X.b), by omega⟩
    rw [show X.Wf + 1 + X.b * X.b + x - (X.Wf + 1 + X.b * X.b) = x by omega]
    obtain ⟨q1, q2⟩ := hp x (by omega)
    refine ⟨q1, ?_⟩
    rw [show X.SH + (X.Wf + 1 + X.b * X.b + x) = X.SH + (X.Wf + 1) + X.b * X.b + x by ring, q2]
  simp only [h1, ↓reduceIte]
  by_cases h2 : X.Wf + 1 + X.lb ≤ a ∧ a < X.Wf + 1 + X.lb + 2 * X.P.k
  · simp only [h2, and_self, ↓reduceIte]
    obtain ⟨e, rfl⟩ : ∃ e, a = X.Wf + 1 + X.lb + e := ⟨a - (X.Wf + 1 + X.lb), by omega⟩
    rw [show X.Wf + 1 + X.lb + e - (X.Wf + 1 + X.lb) = e by omega]
    obtain ⟨q1, q2⟩ := hl e (by omega)
    refine ⟨q1, ?_⟩
    rw [show X.SH + (X.Wf + 1 + X.lb + e) = X.SH + (X.Wf + 1) + X.lb + e by ring, q2]
  simp only [h2, ↓reduceIte]
  refine ⟨(hk a (by omega) h1 h2 (by omega) (by omega)).trans ho.1, ?_⟩
  rw [hk _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact ho.2

end SLx

end BKMNW

end PlanarFlow
