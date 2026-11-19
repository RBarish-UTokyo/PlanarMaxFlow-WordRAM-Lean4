module

public import PlanarFlow.NegSSSP.Enc.FeMem

/-!
# The memory layout of the composed encoder and its first phase

`FeP`: the constants of the encoder of a one-face instance (the sizes `nD`, `k`, `nV`, `nF` of
the map, the base `I0` of its plain arrays, a bound `Lmax` on the isolating lengths). The
regions (all derived from these, in this order):

| region | words | content |
| --- | --- | --- |
| `I0` | `5 nD + k` | the plain arrays `RV`, `NT`, `NF`, `IS`, `LN` of the map (by `σ₀`), `G` |
| `β` | `Kw + 1` | **Klein's input words** (the slot copied by the node) |
| `SL` | `N` | the lengths with the sources copied |
| `ONE` | `N` | ones (the keep flags of all the darts) |
| `ZV` | `7 A + N + 1` | the search of the vertices (`PA` its parent array) |
| `O1`, `ZC` | `2 FN + 2`, `4 N + 15 FN + 2` | a cotree `C₁` of the search tree: orders, scratch |
| `WW` | `N` | the isolating weights `FN + treeW C₁` |
| `ZI` | `AE` | scratch of the weights |
| `RD` | `N` | the reach bits of the tails of the darts from the second root |
| `MK` | `2 A + 1` | marks and queue of the searches of the piece |
| `ISO` | `N` | the isolating lengths |
| `RK` | `3 N + 3` | the residues of Klein's real constants |
| `DB` | `A` | the distances (Bellman–Ford) |
| `ZS`, `ZT`, `OS` | | scratch of the orders, of the cotree, of the out-lists |

(`N = nD + 8 k`, `A = nV + 2 k`, `FN = nF + 2 k` the numbers of darts, vertices and faces of the
map with the sources copied, `AE = A + N + FN`, `NN = 2 AE` nodes, `Kw = kBL N NN k k 0 +
16 (NN + 1)`.)

* `feAProg`: `srcArrProg` (the dart arrays of the map with the sources copied), then the ones;
  `feA_exec`: **phase A** (`43 nD + 284 k + 45 + 5 N + 19` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **The constants of the encoder of a one-face instance.** -/
structure FeP where
  nD : ℕ
  k : ℕ
  nV : ℕ
  nF : ℕ
  I0 : ℕ
  Lmax : ℕ

namespace FeP

variable (p : FeP)

def N : ℕ := p.nD + 8 * p.k
def A : ℕ := p.nV + 2 * p.k
def FN : ℕ := p.nF + 2 * p.k
def AE : ℕ := p.A + p.N + p.FN
def NN : ℕ := 2 * p.AE
def β : ℕ := p.I0 + 5 * p.nD + p.k
def Bw : ℕ := kBL p.N p.NN p.k p.k 0
def Kw : ℕ := p.Bw + 16 * (p.NN + 1)
def SL : ℕ := p.β + p.Kw + 1
def ONE : ℕ := p.SL + p.N
def ZV : ℕ := p.ONE + p.N
def PA : ℕ := p.ZV + 6 * p.A + 1 + p.N
def O1 : ℕ := p.ZV + 7 * p.A + p.N + 1
def ZC : ℕ := p.O1 + 2 * p.FN + 2
def WW : ℕ := p.ZC + 4 * p.N + 15 * p.FN + 2
def ZI : ℕ := p.WW + p.N
def RD : ℕ := p.ZI + p.AE
def MK : ℕ := p.RD + p.N
def ISO : ℕ := p.MK + 2 * p.A + 1
def RK : ℕ := p.ISO + p.N
def DB : ℕ := p.RK + 3 * p.N + 3
def ZS : ℕ := p.DB + p.A
def ZT : ℕ := p.ZS + 8 * p.A + 1
def OS : ℕ := p.ZT + 4 * p.N + 15 * p.FN + 2
def END : ℕ := p.OS + 2 * p.A + 1
def Inf : ℕ := p.A * p.Lmax + 1

/-- The defining equations of the layout (for `omega`). -/
lemma eqs : p.N = p.nD + 8 * p.k ∧ p.A = p.nV + 2 * p.k ∧ p.FN = p.nF + 2 * p.k ∧
    p.AE = p.A + p.N + p.FN ∧ p.NN = 2 * p.AE ∧ p.β = p.I0 + 5 * p.nD + p.k ∧
    p.SL = p.β + p.Kw + 1 ∧ p.ONE = p.SL + p.N ∧
    p.ZV = p.ONE + p.N ∧ p.PA = p.ZV + 6 * p.A + 1 + p.N ∧ p.O1 = p.ZV + 7 * p.A + p.N + 1 ∧
    p.ZC = p.O1 + 2 * p.FN + 2 ∧ p.WW = p.ZC + 4 * p.N + 15 * p.FN + 2 ∧ p.ZI = p.WW + p.N ∧
    p.RD = p.ZI + p.AE ∧ p.MK = p.RD + p.N ∧ p.ISO = p.MK + 2 * p.A + 1 ∧
    p.RK = p.ISO + p.N ∧ p.DB = p.RK + 3 * p.N + 3 ∧ p.ZS = p.DB + p.A ∧
    p.ZT = p.ZS + 8 * p.A + 1 ∧ p.OS = p.ZT + 4 * p.N + 15 * p.FN + 2 ∧
    p.END = p.OS + 2 * p.A + 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The work space of Klein's input. -/
lemma kw_eq : p.Bw = 9 * p.N + 7 * p.NN + p.k + 4 + 2 * p.k + (3 * p.N + 3) + p.k * p.k + p.NN +
      2 * p.N ∧ p.Kw = p.Bw + 16 * (p.NN + 1) := by
  refine ⟨?_, rfl⟩
  simp only [Bw, kBL, aOUT]; ring

end FeP

/-- Unfold the layout of the encoder and close a linear goal. -/
macro "fe_omega" p:term : tactic =>
  `(tactic| (have := FeP.eqs $p; omega))

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- **Phase A**: the dart arrays of the map with the sources copied, then the ones. -/
def feAProg (p : FeP) : Stmt :=
  .seq (feSet [(2300, p.nD), (2301, p.k), (2302, p.nV), (2303, p.nF), (2304, p.β),
      (2305, p.SL), (2306, p.I0), (2307, p.I0 + p.nD), (2308, p.I0 + 2 * p.nD),
      (2309, p.I0 + 3 * p.nD), (2310, p.I0 + 4 * p.nD), (2311, p.I0 + 5 * p.nD)])
    (.seq srcArrProg (feFill p.ONE p.N 1))

theorem feAProg_natOnly (p : FeP) : natOnly (feAProg p) = true := by
  simp only [feAProg, natOnly, feSet_natOnly, srcArrProg_natOnly, feFill_natOnly,
    Bool.and_self]

/-- The length of the slot written by `srcArrProg` fits in the slot of Klein's input. -/
lemma FeP.slot_le (p : FeP) : 9 * p.N + 14 * p.AE + 2 * p.k + 4 ≤ p.Kw ∧ 2 * p.AE ≤ p.Kw ∧
    p.NN + p.N ≤ p.Kw := by
  simp only [FeP.Kw, FeP.Bw, kBL, aOUT, FeP.NN, FeP.AE]
  omega

set_option maxHeartbeats 2000000 in
/-- **Phase A on the machine**: from the plain arrays of `M` at `I0` (`RV`, `NT`, `NF`, `IS`,
`LN` by `σ₀`, then the darts of the face cycle), the words of `srcArrProg` (`SrcArrM`) and ones at
`ONE`; the memory changes only in `[β, END)`. -/
theorem feA_exec (hf : MSSP.FaceCycle M k g) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (p : FeP)
    (hD : p.nD = Fintype.card D) (hk : p.k = k) (hV : p.nV = Fintype.card V)
    (hF : p.nF = Fintype.card F) (hW : p.END ≤ W) (hSW : (srcW S ℓ).toNat ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hQRV : ∀ d, c.nmem (p.I0 + σ₀ d) = σ₀ (M.rev d))
    (hQNT : ∀ d, c.nmem (p.I0 + p.nD + σ₀ d) = νv₀ (M.tail d))
    (hQNF : ∀ d, c.nmem (p.I0 + 2 * p.nD + σ₀ d) = τ₀ (M.face d))
    (hQIS : ∀ d, c.nmem (p.I0 + 3 * p.nD + σ₀ d) = if d ∈ S then 1 else 0)
    (hQLN : ∀ d, c.nmem (p.I0 + 4 * p.nD + σ₀ d) = (ℓ d).toNat)
    (hQG : ∀ i < k, c.nmem (p.I0 + 5 * p.nD + i) = σ₀ (g i)) :
    ∃ c' t, Exec P W (feAProg p) c c' t ∧ t ≤ 43 * p.nD + 284 * p.k + 5 * p.N + 64 ∧
      SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE c'.nmem ∧
      (∀ j < p.N, c'.nmem (p.ONE + j) = 1) ∧
      (∀ x, x < p.β ∨ p.END ≤ x → c'.nmem x = c.nmem x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  subst hk
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ : p.N = Fintype.card D + 8 * p.k ∧
      p.A = Fintype.card V + 2 * p.k ∧ p.AE = p.A + p.N + (Fintype.card F + 2 * p.k) ∧
      p.β + 9 * p.N + 14 * p.AE + 2 * p.k + 4 ≤ p.SL ∧ p.SL + p.N ≤ p.ONE ∧
      p.ONE + p.N ≤ p.END ∧ p.END ≤ W ∧ p.I0 + 5 * p.nD + p.k = p.β ∧ 2 * p.AE ≤ p.Kw := by
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hD hV hF hW; omega
  rw [hD] at l8
  have hk2 : 2 ≤ p.k := hf.two_le
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) [(2300, p.nD), (2301, p.k), (2302, p.nV), (2303, p.nF), (2304, p.β),
      (2305, p.SL), (2306, p.I0), (2307, p.I0 + p.nD), (2308, p.I0 + 2 * p.nD),
      (2309, p.I0 + 3 * p.nD), (2310, p.I0 + 4 * p.nD), (2311, p.I0 + 5 * p.nD)]
      (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp only <;> clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD hV hF <;> omega) c hc
  have hm' : ∀ x, c₁.nmem x = c.nmem x := fun x => by rw [hm₁]
  rw [hD] at hQNT hQNF hQIS hQLN hQG
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hbx₂, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    srcArrProg_exec (P := P) (M := M) (S := S) (ℓ := ℓ) (σ₀ := σ₀) (νv₀ := νv₀) (τ₀ := τ₀)
      (QRVb := p.I0) (QNTb := p.I0 + Fintype.card D) (QNFb := p.I0 + 2 * Fintype.card D)
      (QISb := p.I0 + 3 * Fintype.card D) (QLNb := p.I0 + 4 * Fintype.card D)
      (QGb := p.I0 + 5 * Fintype.card D) (N := p.N) (a := p.A) (ae := p.AE)
      (β := p.β) (SLb := p.SL) hf hnn l1 l2 l3 (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) (by clear * - l1 l2 l3 l4 l5 l6 l7 l8 hD; omega) hSW
      c₁ e₁.wb_right
      (by rw [hn₁]; simp [feSetV, hD]) (by rw [hn₁]; simp [feSetV]) (by rw [hn₁]; simp [feSetV, hV])
      (by rw [hn₁]; simp [feSetV, hF]) (by rw [hn₁]; simp [feSetV]) (by rw [hn₁]; simp [feSetV])
      (by rw [hn₁]; simp [feSetV]) (by rw [hn₁]; simp [feSetV, hD])
      (by rw [hn₁]; simp [feSetV, hD]) (by rw [hn₁]; simp [feSetV, hD])
      (by rw [hn₁]; simp [feSetV, hD]) (by rw [hn₁]; simp [feSetV, hD])
      (fun d => by rw [hm']; exact hQRV d) (fun d => by rw [hm']; exact hQNT d)
      (fun d => by rw [hm']; exact hQNF d) (fun d => by rw [hm']; exact hQIS d)
      (fun d => by rw [hm']; exact hQLN d) (fun i hi => by rw [hm']; exact hQG i hi)
  obtain ⟨c₃, k₃, e₃, hk₃, h1₃, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    feFill_exec (P := P) (Dst := p.ONE) (len := p.N) (v := 1) (by clear * - l1 l5 l6 l7 hk2; omega)
      (by clear * - l1 l5 l6 l7 hk2; omega) (by clear * - l1 l5 l6 l7 hk2; omega) c₂ e₂.wb_right
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), by simp at hk₁; clear * - hk₁ hk₂ hk₃ hD l1; omega, ?_, h1₃,
    fun x hx => ?_, by rw [hr₃, hr₂, hr₁], by rw [hrm₃, hrm₂, hrm₁], by rw [ho₃, ho₂, ho₁]⟩
  · refine SrcArrM.of (Bd := 2 * p.AE) l1 l2 l3 le_rfl ⟨hw₂, hbx₂⟩
      (fun j hj => ClampAg.of_eq (hm₃ _ (by clear * - hj l4 l5; omega)))
      (fun i hi => ClampAg.of_eq (hm₃ _ (by clear * - hi l4 l5; omega)))
      (fun j hj => hm₃ _ (by clear * - hj l4 l5; omega))
  · rw [hm₃ _ (by clear * - hx l4 l5 l6; omega), hm₂ _ (by clear * - hx l4 l5 l6; omega)
      (by clear * - hx l4 l5 l6; omega), hm']

end NegSSSP

end PlanarFlow
