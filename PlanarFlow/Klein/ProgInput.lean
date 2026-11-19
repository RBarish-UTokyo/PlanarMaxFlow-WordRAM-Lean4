module

public import PlanarFlow.Klein.PivotOps
public import PlanarFlow.DynTree.RegList

/-!
# Klein's algorithm on the machine: the input and the mutable arrays

**The input** (`KInput`). The darts are numbered by an equivalence `σ : D ≃ Fin nD`, and the
nodes of the dynamic trees are those of a `Layout` (`ιv`, `ιg`, `ιf`, `ιe` on `n` nodes). The
input words are the arrays, each indexed by the number of a dart (`nD` words):

| array | offset | word for the dart `d` |
|-------|--------|------------------------|
| `RV`  | `0`      | the number of `M.rev d` |
| `NF`  | `nD`     | the node `ιf (M.face d)` of its face |
| `NE`  | `2 nD`   | the node `ιe d` of its edge in the cotree |
| `NG`  | `3 nD`   | the node `ιg d` of its edge in the spanning tree |
| `NT`  | `4 nD`   | the node `ιv (M.tail d)` of its tail |
| `NH`  | `5 nD`   | the node `ιv (M.head d)` of its head |
| `IS`  | `6 nD`   | `1` if `d ∈ S`, `0` otherwise |
| `LN`  | `7 nD`   | its length `ℓ d` for `d ∈ S` (positive on the piece) |

followed by one array indexed by the nodes (`n` words): `ED` at `8 nD`, for the node `ιe d` of an
edge, the number of `d` or of `M.rev d`. The program reads these words with `readIn` (one step
each), never copying them.

**The mutable arrays** (`KMem`), below the structure of the dynamic trees (at `B`): in the
natural memory, `TP` at `0`: for the node `ιv x` of a vertex other than the root, the number of
its parent dart in the stored spanning tree; in the real memory, `WT` at `0` (the weights `wt`
of the values of the move) and `PH` at `nD` (the weights `φ` of the labels), by the numbers of
the darts.

* `readArr_exec`, `loadArr_exec`, `loadArrR_exec`: reading one entry of the input, of the
  natural memory, of the real memory (three steps).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### The layout of the input -/

/-- The offset of the array `RV` (reverses). -/
def iRV (_nD : ℕ) : ℕ := 0
/-- The offset of the array `NF` (nodes of the faces). -/
def iNF (nD : ℕ) : ℕ := nD
/-- The offset of the array `NE` (nodes of the edges of the cotree). -/
def iNE (nD : ℕ) : ℕ := 2 * nD
/-- The offset of the array `NG` (nodes of the edges of the spanning tree). -/
def iNG (nD : ℕ) : ℕ := 3 * nD
/-- The offset of the array `NT` (nodes of the tails). -/
def iNT (nD : ℕ) : ℕ := 4 * nD
/-- The offset of the array `NH` (nodes of the heads). -/
def iNH (nD : ℕ) : ℕ := 5 * nD
/-- The offset of the array `IS` (membership in the piece). -/
def iIS (nD : ℕ) : ℕ := 6 * nD
/-- The offset of the array `LN` (lengths). -/
def iLN (nD : ℕ) : ℕ := 7 * nD
/-- The offset of the array `ED` (a dart of the node of an edge), indexed by the nodes. -/
def iED (nD : ℕ) : ℕ := 8 * nD

/-- The natural array `TP` (parent darts of the vertices, by their nodes). -/
def aTP : ℕ := 0
/-- The real array `WT` (weights of the values, by the darts). -/
def aWT : ℕ := 0
/-- The real array `PH` (weights of the labels, by the darts). -/
def aPH (nD : ℕ) : ℕ := nD

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The input describes the map**: the arrays of the module docstring. -/
structure KInput (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ} (σ : D ≃ Fin nD)
    (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (P : Input) : Prop where
  rv : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)
  nf : ∀ d, P.data.getD (iNF nD + σ d) 0 = ιf (M.face d)
  ne : ∀ d, P.data.getD (iNE nD + σ d) 0 = ιe d
  ng : ∀ d, P.data.getD (iNG nD + σ d) 0 = ιg d
  nt : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d)
  nh : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)
  is : ∀ d, P.data.getD (iIS nD + σ d) 0 = if d ∈ S then 1 else 0
  ln : ∀ d ∈ S, P.data.getD (iLN nD + σ d) 0 = (ℓ d).toNat
  ed : ∀ d, P.data.getD (iED nD + ιe d) 0 = σ d ∨ P.data.getD (iED nD + ιe d) 0 = σ (M.rev d)

/-- **The mutable arrays hold the stored spanning tree and the weights.** -/
structure KMem (M : CombMap D V F) {nD : ℕ} (σ : D ≃ Fin nD) (ιv : V → ℕ) (T : DTree M.dual)
    (wt φ : D → ℤ) (c : Config) : Prop where
  tp : ∀ x, x ≠ T.root → c.nmem (aTP + ιv x) = σ (T.par x)
  wt : ∀ d, c.rmem (aWT + σ d) = wt d
  ph : ∀ d, c.rmem (aPH nD + σ d) = φ d

/-! ### Reading one entry -/

section Read
variable {P : Input} {W : ℕ}

/-- Read the input word `off + r i` into `r` (`i ≠ r`). -/
theorem readArr_exec {c : Config} (hc : WordsBounded W c) (r i off : ℕ) (hi : i ≠ r)
    (hw : off + c.nreg i ≤ W) (hv : P.data.getD (off + c.nreg i) 0 ≤ W) :
    Exec P W (block [.constN r off, .addN r r i, .readIn r r]) c
      { c with nreg := upd c.nreg r (P.data.getD (off + c.nreg i) 0) } 3 := by
  have e1 := Exec.constN (P := P) hc r off (by omega)
  have e2 := Exec.addN (P := P) e1.wb_right r r i (by simp [upd, hi]; omega)
  have e3 := Exec.readIn (P := P) e2.wb_right r r (by simp [upd, hi]; exact hv)
  have e := Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_nil
    e3.wb_right)))
  convert e using 2; simp [upd, hi]

/-- Load the natural memory word `off + r i` into `r` (`i ≠ r`). -/
theorem loadArr_exec {c : Config} (hc : WordsBounded W c) (r i off : ℕ) (hi : i ≠ r)
    (hw : off + c.nreg i ≤ W) :
    Exec P W (block [.constN r off, .addN r r i, .loadN r r]) c
      { c with nreg := upd c.nreg r (c.nmem (off + c.nreg i)) } 3 := by
  have e1 := Exec.constN (P := P) hc r off (by omega)
  have e2 := Exec.addN (P := P) e1.wb_right r r i (by simp [upd, hi]; omega)
  have e3 := Exec.loadN (P := P) e2.wb_right r r
  have e := Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_nil
    e3.wb_right)))
  convert e using 2; simp [upd, hi]

/-- Load the real memory word `off + r i` into the real `q`, through the natural `r`
(`i ≠ r`). -/
theorem loadArrR_exec {c : Config} (hc : WordsBounded W c) (r q i off : ℕ) (hi : i ≠ r)
    (hw : off + c.nreg i ≤ W) :
    Exec P W (block [.constN r off, .addN r r i, .loadR q r]) c
      { c with
        nreg := upd c.nreg r (off + c.nreg i)
        rreg := upd c.rreg q (c.rmem (off + c.nreg i)) } 3 := by
  have e1 := Exec.constN (P := P) hc r off (by omega)
  have e2 := Exec.addN (P := P) e1.wb_right r r i (by simp [upd, hi]; omega)
  have e3 := Exec.loadR (P := P) e2.wb_right q r
  have e := Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_nil
    e3.wb_right)))
  convert e using 2 <;> simp [upd, hi]

end Read

end Klein

end PlanarFlow
