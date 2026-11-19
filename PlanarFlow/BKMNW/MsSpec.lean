module

public import PlanarFlow.BKMNW.StTree
public import PlanarFlow.BKMNW.FrCall
public import PlanarFlow.BKMNW.FRFixPath
public import PlanarFlow.BKMNW.NsMath
public import PlanarFlow.NegSSSP.ArcSort

/-!
# The specifications of the MSSP call and of the FR image

The node step of the maximum-flow algorithm calls, inside FixConservationOnPath along a path `P`
of a piece map `M` (`fixPath`), multiple-source shortest paths once (the dense distance graph
`⟨P.faces, mssp P.darts (c - f₀)⟩`) and FR-Dijkstra at every stage. This file states, as
hypotheses another program may assume, what a machine program for these two calls computes,
and proves the facts that make the statements usable:

* **`MsIn`**: the input of an MSSP call in memory: the map by index arrays (the reverse `RV`
  and the rotation `RT` of a dart order `en` of `m` darts, as in the frame of a call and in
  `StEnc.smP_kin`), the path (`k` dart indices), the lengths (natural words, the lengths are
  `≥ 0`: they are residual capacities `c - f₀` of a pseudoflow), and `q` query darts.
* **`MsspCallSpec M msP Scr cost room wz`**: the program `msP` run from a configuration with
  the memory `≤ Wz` zero (`wz m Lmax ≤ Wz`, `Lmax` a bound of the lengths) and the input `MsIn`
  above `Wz` writes the `q × q` matrix of the answers
  **`msspPlaneK M P.darts ℓ (face tᵢ) (face tⱼ)`** (read with `getD 0`, as natural words) at
  `Ob`, within `cost m k q` steps, leaves the memory `≤ Wz` zero, keeps the memory above `Wz`
  outside `[Ob, Ob + q²)` and the scratch `[p, p + room m k q)`, and the registers outside
  `Scr`, reals and output.
* `msOut_eq`: the words of the matrix are the answers of **any** subroutine meeting
  `MSSPSpecAt` at the faces along the path (`msspPlaneK_eq_of_isDist`), and they are values,
  not `none` (`msOut_some`), at the corners (`fixCorner`) of the path.
* **`FrImgIn`** / **`FrImgSpec frImP Scr cost room`**: from the corners `b`, a `b × b` natural
  matrix `Dm`, prices `pm` and `mE` explicit arcs (tails, heads, lengths; the integers stored
  with an offset `K`, `z ↦ z + K`), the program `frImP` writes the natural image of the FR input
  `frPrm b Dm pm r ET EH Lz mE = mkPrm b b Dm pm r (csList ET EH 1 Lz mE)` at `A`
  (`frNM` at `[A, A + sb)`, `frRS … L` at `[A + sb, A + 2 sb)`) and the registers
  `r7600 … r7613` that `FrFix.frCall_exec` reads.

Registers of these specifications: `8000 … 8299` (MSSP call inputs `8000 … 8009`, FR image inputs
`8100 … 8111`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt Monge Monge.FR NegSSSP NsStep Klein

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-! ### The MSSP call -/

/-- **The input of an MSSP call in memory**: the registers `r8000 … r8009` (`m`, `RVb`, `RTb`,
`k`, `Pb`, `Lb`, `q`, `Qb`, `Ob`, `p`), the reverse and the rotation of the darts as indices in
the order `en` (`RV`, `RT`), the darts of the path (`Pb + j ↦` the index of `P.d j`), the lengths
(`Lb + i ↦ ℓ (en i)`, natural words, bounded by `Lmax`) and the query darts
(`Qb + i ↦` the index of `ts i`). -/
structure MsIn (M : CombMap D V F) (en : ℕ → D) (m : ℕ) (P : SPath M) (ℓ : D → ℤ) (Lmax : ℕ)
    (q : ℕ) (ts : ℕ → D) (RVb RTb Pb Lb Qb Ob p : ℕ) (c : Config) : Prop where
  r00 : c.nreg 8000 = m
  r01 : c.nreg 8001 = RVb
  r02 : c.nreg 8002 = RTb
  r03 : c.nreg 8003 = P.k
  r04 : c.nreg 8004 = Pb
  r05 : c.nreg 8005 = Lb
  r06 : c.nreg 8006 = q
  r07 : c.nreg 8007 = Qb
  r08 : c.nreg 8008 = Ob
  r09 : c.nreg 8009 = p
  rv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i)
  rt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i)
  pd : ∀ j < P.k, c.nmem (Pb + j) < m ∧ en (c.nmem (Pb + j)) = P.d j
  ln : ∀ i < m, (c.nmem (Lb + i) : ℤ) = ℓ (en i) ∧ c.nmem (Lb + i) ≤ Lmax
  qd : ∀ i < q, c.nmem (Qb + i) < m ∧ en (c.nmem (Qb + i)) = ts i

/-- **The placement of an MSSP call**: the memory `≤ Wz` is free (zero), the input arrays lie
in `(Wz, Ob)`, the output `[Ob, Ob + q²)` and the scratch `[p, p + R)` above them, all below the
word bound. -/
structure MsPlace (m k q Wz W RVb RTb Pb Lb Qb Ob p R : ℕ) : Prop where
  rv : Wz < RVb ∧ RVb + m ≤ Ob
  rt : Wz < RTb ∧ RTb + m ≤ Ob
  pb : Wz < Pb ∧ Pb + k ≤ Ob
  lb : Wz < Lb ∧ Lb + m ≤ Ob
  qb : Wz < Qb ∧ Qb + q ≤ Ob
  ob : Wz < Ob ∧ Ob + q * q ≤ p
  pw : p + R ≤ W

/-- The word of the answer from the face of `t` to the face of `t'`. -/
noncomputable def msW (M : CombMap D V F) (P : SPath M) (ℓ : D → ℤ) (t t' : D) : ℕ :=
  ((msspPlaneK M P.darts ℓ (M.face t) (M.face t')).getD 0).toNat

variable (M) in
/-- **The specification of an MSSP call program** `msP` on the map `M` (a plane map with
transitive rotations and faces, whose faces are the orbits of `next`): from a configuration
with the memory `≤ Wz` zero, `wz m Lmax ≤ Wz`, and the input `MsIn` placed by `MsPlace`, with
nonnegative lengths and query darts on faces along the path, `msP` runs within `cost m k q`
steps to a configuration with the memory `≤ Wz` zero again, the answers
`msW M P ℓ (ts i) (ts j)` at `Ob + i q + j`, the memory above `Wz` outside the output and the
scratch kept, the registers outside `Scr` kept, reals and output kept. -/
def MsspCallSpec (msP : Stmt) (Scr : ℕ → Prop) (cost room : ℕ → ℕ → ℕ → ℕ)
    (wz : ℕ → ℕ → ℕ) : Prop :=
  M.IsPlane → M.RotTrans →
  ∀ (en : ℕ → D) (m : ℕ) (P : SPath M) (ℓ : D → ℤ) (Lmax q : ℕ) (ts : ℕ → D)
    (RVb RTb Pb Lb Qb Ob p Wz W : ℕ) (I : Input) (c : Config),
    EnumOK M en m → 0 < P.k → (∀ e, 0 ≤ ℓ e) → (∀ i < q, M.face (ts i) ∈ P.faces) →
    WordsBounded W c → MsIn M en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c →
    MsPlace m P.k q Wz W RVb RTb Pb Lb Qb Ob p (room m P.k q) →
    (∀ a ≤ Wz, c.nmem a = 0) → wz m Lmax ≤ Wz →
    ∃ c' t, Exec I W msP c c' t ∧ t ≤ cost m P.k q ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ i < q, ∀ j < q, c'.nmem (Ob + i * q + j) = msW M P ℓ (ts i) (ts j)) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + q * q ≤ a) → (a < p ∨ p + room m P.k q ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ Scr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- **The words of the answers are those of any MSSP subroutine** meeting the specification
along the path, at the faces along the path: `msspPlaneK` is determined there
(`Klein.msspPlaneK_eq_of_isDist`). -/
theorem msOut_eq (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {t t' : D} (ht : M.face t ∈ P.faces) :
    msspPlaneK M P.darts ℓ (M.face t) (M.face t') = mssp P.darts ℓ (M.face t) (M.face t') := by
  rw [Klein.msspPlaneK_eq_of_isDist hM hrot hface P ℓ hnn ht (hmssp ℓ hnn _ ht)]

/-- **At the corners of the path, the answers are values** (the dual graph minus the path is
reached along the face of the path), nonnegative for nonnegative lengths. -/
theorem msOut_some (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, 0 ≤ ℓ e) {i : ℕ}
    (hi : fixCorner M P i ∈ P.faces) (j : ℕ) :
    ∃ a, 0 ≤ a ∧ msspPlaneK M P.darts ℓ (fixCorner M P i) (fixCorner M P j) = some a := by
  have hspec : MSSPSpecAt M (msspPlaneK M) P := fun ℓ' hnn' x hx =>
    Klein.msspPlaneK_spec hM hrot hface P ℓ' hnn' x hx
  obtain ⟨a, ha⟩ := fixDDG_some P hspec (fun e _ => hnn e) hi j
  refine ⟨a, ?_, ha⟩
  have hD := Klein.msspPlaneK_spec hM hrot hface P ℓ (fun e _ => hnn e) _ hi
  have hnn' : ∀ x, 0 ≤ ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts).len x := fun x =>
    hnn x.1
  obtain ⟨L, -, hlen⟩ := hD.some_walk _ a ha
  rw [← hlen]
  refine List.sum_nonneg fun z hz => ?_
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
  exact hnn' x

/-- The word of an answer that is a value is that value. -/
theorem msW_of_some {P : SPath M} {ℓ : D → ℤ} {t t' : D} {a : ℤ}
    (ha0 : 0 ≤ a) (ha : msspPlaneK M P.darts ℓ (M.face t) (M.face t') = some a) :
    (msW M P ℓ t t' : ℤ) = a := by
  simp only [msW, ha, Option.getD_some, Int.toNat_of_nonneg ha0]

/-! ### The FR image -/

/-- **The FR input of the image**: `b` corners (all the vertices), the matrix `Dm` (natural
words), the prices `pm`, the root `r`, the `mE` explicit arcs `(ET a, EH a, Lz a)` in their
order, laid out by `mkPrm` (tail by tail). -/
noncomputable def frPrm (b : ℕ) (Dm : ℕ → ℕ → ℕ) (pm : ℕ → ℤ) (r : ℕ) (ET EH : ℕ → ℕ)
    (Lz : ℕ → ℤ) (mE : ℕ) : Prm :=
  mkPrm b b (fun i j => (Dm i j : ℤ)) pm r (csList ET EH (fun _ => 1) Lz mE)

/-- With every keep flag `1`, `csList` lists all the arcs in order. -/
theorem csList_ones (ET EH : ℕ → ℕ) (Lz : ℕ → ℤ) (n : ℕ) :
    csList ET EH (fun _ => 1) Lz n = (List.range n).map fun a => (ET a, EH a, Lz a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csList, ih, one_ne_zero, ↓reduceIte, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]

/-- **The input of the FR image in memory**: the registers `r8100 … r8111` (`b`, `DMb`, `PRb`,
`r`, `mE`, `ETb`, `EHb`, `ELb`, `K`, `L`, `A`, `S`), the matrix `DM[i b + j] = Dm i j`, the prices
`PR[x] = pm x + K`, the arcs `ET[a] = ET a`, `EH[a] = EH a`, `EL[a] = Lz a + K`. -/
structure FrImgIn (b : ℕ) (Dm : ℕ → ℕ → ℕ) (pm : ℕ → ℤ) (r mE : ℕ) (ET EH : ℕ → ℕ)
    (Lz : ℕ → ℤ) (K L DMb PRb ETb EHb ELb A S : ℕ) (c : Config) : Prop where
  r00 : c.nreg 8100 = b
  r01 : c.nreg 8101 = DMb
  r02 : c.nreg 8102 = PRb
  r03 : c.nreg 8103 = r
  r04 : c.nreg 8104 = mE
  r05 : c.nreg 8105 = ETb
  r06 : c.nreg 8106 = EHb
  r07 : c.nreg 8107 = ELb
  r08 : c.nreg 8108 = K
  r09 : c.nreg 8109 = L
  r10 : c.nreg 8110 = A
  r11 : c.nreg 8111 = S
  dm : ∀ i < b, ∀ j < b, c.nmem (DMb + i * b + j) = Dm i j
  pr : ∀ x < b, (c.nmem (PRb + x) : ℤ) = pm x + K
  et : ∀ a < mE, c.nmem (ETb + a) = ET a
  eh : ∀ a < mE, c.nmem (EHb + a) = EH a
  el : ∀ a < mE, (c.nmem (ELb + a) : ℤ) = Lz a + K

/-- **The bounds of the FR image**: `1 ≤ b`, `r < b`, the arcs between corners, every value
bounded by `L` (so `XB`). -/
structure FrImgB (b : ℕ) (Dm : ℕ → ℕ → ℕ) (pm : ℕ → ℤ) (r mE : ℕ) (ET EH : ℕ → ℕ)
    (Lz : ℕ → ℤ) (L : ℕ) : Prop where
  b_pos : 1 ≤ b
  r_lt : r < b
  et : ∀ a < mE, ET a < b
  eh : ∀ a < mE, EH a < b
  dm : ∀ i < b, ∀ j < b, Dm i j ≤ L
  pm : ∀ x < b, |pm x| ≤ L
  lz : ∀ a < mE, |Lz a| ≤ L

/-- **The specification of an FR image program** `frImP`: from `FrImgIn` with `FrImgB`, the
input arrays below `A`, the image `[A, A + 2 sb)` and the scratch `[S, S + room b mE)` apart,
within `cost b mE` steps, the natural image of `frPrm …` at `A` and the registers `r7600 … r7613`
that `FrFix.frCall_exec` reads; memory outside the image and the scratch kept, registers outside
`Scr` kept, reals and output kept. -/
def FrImgSpec (frImP : Stmt) (Scr : ℕ → Prop) (cost room : ℕ → ℕ → ℕ) : Prop :=
  ∀ (b : ℕ) (Dm : ℕ → ℕ → ℕ) (pm : ℕ → ℤ) (r mE : ℕ) (ET EH : ℕ → ℕ) (Lz : ℕ → ℤ)
    (K L DMb PRb ETb EHb ELb A S W : ℕ) (I : Input) (c : Config),
    FrImgB b Dm pm r mE ET EH Lz L →
    FrImgIn b Dm pm r mE ET EH Lz K L DMb PRb ETb EHb ELb A S c → WordsBounded W c →
    DMb + b * b ≤ A → PRb + b ≤ A → ETb + mE ≤ A → EHb + mE ≤ A → ELb + mE ≤ A →
    A + 2 * (frPrm b Dm pm r ET EH Lz mE).sb ≤ S → S + room b mE ≤ W →
    K + L + frM (frPrm b Dm pm r ET EH Lz mE) L ≤ W → (frPrm b Dm pm r ET EH Lz mE).W + 1 ≤ W →
    ∃ c' t, Exec I W frImP c c' t ∧ t ≤ cost b mE ∧
      (∀ a < (frPrm b Dm pm r ET EH Lz mE).sb,
        c'.nmem (A + a) = FrFix.frNM (frPrm b Dm pm r ET EH Lz mE) a) ∧
      (∀ a < (frPrm b Dm pm r ET EH Lz mE).sb,
        c'.nmem (A + (frPrm b Dm pm r ET EH Lz mE).sb + a) =
          FrFix.frRS (frPrm b Dm pm r ET EH Lz mE) L a) ∧
      c'.nreg 7600 = (frPrm b Dm pm r ET EH Lz mE).N ∧
      c'.nreg 7601 = (frPrm b Dm pm r ET EH Lz mE).b ∧
      c'.nreg 7602 = (frPrm b Dm pm r ET EH Lz mE).Db ∧
      c'.nreg 7603 = (frPrm b Dm pm r ET EH Lz mE).pb ∧
      c'.nreg 7604 = (frPrm b Dm pm r ET EH Lz mE).ob ∧
      c'.nreg 7605 = (frPrm b Dm pm r ET EH Lz mE).lb ∧
      c'.nreg 7606 = (frPrm b Dm pm r ET EH Lz mE).r ∧
      c'.nreg 7607 = (frPrm b Dm pm r ET EH Lz mE).sb ∧
      c'.nreg 7608 = (frPrm b Dm pm r ET EH Lz mE).db ∧
      c'.nreg 7609 = (frPrm b Dm pm r ET EH Lz mE).wb ∧
      c'.nreg 7610 = frM (frPrm b Dm pm r ET EH Lz mE) L ∧
      c'.nreg 7611 = frH (frPrm b Dm pm r ET EH Lz mE) L ∧
      c'.nreg 7612 = (frPrm b Dm pm r ET EH Lz mE).W + 1 ∧
      c'.nreg 7613 = A ∧
      (∀ a, (a < A ∨ A + 2 * (frPrm b Dm pm r ET EH Lz mE).sb ≤ a) →
        (a < S ∨ S + room b mE ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r', ¬ Scr r' → c'.nreg r' = c.nreg r') ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- The image's input meets the layout of FR-Dijkstra. -/
theorem frPrm_lay {b : ℕ} {Dm : ℕ → ℕ → ℕ} {pm : ℕ → ℤ} {r mE : ℕ} {ET EH : ℕ → ℕ}
    {Lz : ℕ → ℤ} {L : ℕ} (h : FrImgB b Dm pm r mE ET EH Lz L) :
    Lay (frPrm b Dm pm r ET EH Lz mE) := by
  refine mkPrm_lay h.b_pos le_rfl h.r_lt fun a ha => ?_
  rw [csList_ones, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact h.eh i (List.mem_range.1 hi)

end MsCall

end BKMNW

end PlanarFlow
