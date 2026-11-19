module

public import PlanarFlow.Klein.ProgInit
public import PlanarFlow.Klein.Bridge
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Klein's algorithm on the machine: the trip around the face

The program `kleinProg` of Klein's multiple-source shortest-path algorithm, in the form of
Cabello, Chambers and Erickson, on the evertable link-cut trees: the initialisation (`inS`,
`PlanarFlow/Klein/ProgInit.lean`), then for each move `j < k` (`tBodyS`): the answers at the `t`
target vertices `X i` given in the input (`KTgt`; `qLoopS`): the path sums of the stored tree
into the real array `OUT` at `3 nD + 3` and the reach bits of the targets into the natural array
`RB` at `n`, then the pivot loop (`mvLoopS`), the trees (`nxAS`) and the weights (`wtS`) of the
next move.

**The answers.** At the start of the move `j` the path sum at a vertex reached from the source
`tail (g j)` is its distance from it (`stored_label`). The targets are not roots, so (by
`SameReach`) whether they are reached does not depend on the root; the reach bits are given in
the input (`KTgt.xr`, as the reach bits behind the weights `tripWt 0` of the first move), and the
program copies them beside the path sums. The answer of the move `j` at `X i` read from a
configuration is `kOut j i`: `OUT[j t + i]` where `RB[j t + i] = 1`, none otherwise.

* `TInv`: the invariant of the loop over the moves (the first `J` moves of a trip,
  `IsTripUpTo`, the data at the start of the move `J` stored, the mutable arrays, the constants,
  the answers of the moves `j < J`: `kOut j i = odist`); `tBody_orun`, `tLoop_orun`: one move,
  the `k` moves.
* `kleinS_orun`: the whole program from the initialised structure, counted at most `kleinOps`
  operations (`6 (#V + #F) + 2 nD` for the initialisation, `k t + 64 #S + 31 k` for the moves:
  `t` queries, `2 (27 m + 1)` for the pivot loop, `29 + 5 #(tripΔ j)` for the step to the next
  move, with `∑ m ≤ #S`, `IsTripUpTo.pivots`, and `∑ #(tripΔ j) ≤ 2 #S`, `sum_tripΔ_le`) and
  `kleinExt` further steps.
* `lctE_adaptive_exec`, `klein_exec`: **the end-to-end theorem**: an execution of `kleinProg`
  from any configuration meeting the preconditions (listed in its docstring), within
  `140 (n + 1) + 21 + kleinOps · opCostE n + kleinExt` steps, **ending with the answers in its
  output**: `kOut j i` is the distance in the piece from `tail (g j)` to `X i`, none when `X i`
  is not reached (`odist`); `klein_steps_le`: on `n = 2 (#V + #F + #D)` nodes this is
  `O(N log N + k t log N)`.
* `klein_init_exists`: the initial trees and orders of `KInit` exist (all the preconditions can
  be met: `klein_exec_pre`, `PlanarFlow/Klein/ProgExists.lean`); `klein_out_ans`: the answers
  `kleinAns` of the trip at the targets are the answers in the output; `msspCutK_eq_out`: the
  answers of `msspPlaneK` on the chosen cut are those in the output of the program on the cut
  (with the copies of the faces as targets), divided by `2^|D'|` (`outNN`).

**The cost on the cuts of the maximum-flow algorithm.** `kleinProg` answers every one of its `k`
roots at every one of its `t` targets: `O(N log N + k t log N)` steps (`klein_steps_le`). On the
cut along a simple path of `p` darts (`PlanarFlow/BKMNW/CutBuild.lean`) there is one root per
dart leaving the path, so `k` can be of the order of `N` (through a vertex of high degree on the
path), and with the `O(p)` faces along the path as targets this is `O(N p log N)`, above the
allowance `K (m lg m + p² lg m)` of `PlanarFlow.BKMNW.SubCosts.Bounds.mssp`. The pivots stay
`O(N)` in total (`klein_pivots`); only the queries are too many. The variant `kleinProgM`
(`PlanarFlow/Klein/ProgTripMask.lean`) queries only at flagged moves, `O(N log N + f t log N)`
steps for `f` flagged moves (`kleinM_exec`, `kleinM_steps_le`); flagging the first move of each
face along the path suffices for `msspPlaneK` (`msspCutK_eq_outM`), which gives
`O(N log N + p² log N)` steps on these cuts (`msspPlaneK_masked`,
`PlanarFlow/Klein/ProgExistsMask.lean`). `kleinProg` and its statements are kept unchanged.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### The program of the trip -/

/-- The real array `OUT` of the distances: `OUT[j t + i]` for the move `j` and the target
`X i`. -/
def aOUT (nD : ℕ) : ℕ := 3 * nD + 3

/-- The natural array `RB` of the reach bits: `RB[j t + i]` for the move `j` and the target
`X i`. -/
def aRB (n : ℕ) : ℕ := n

/-- **One move and the step to the next** (`r80 = j`, `r81 = k`): the path sums at the `t`
targets into `OUT[j t …]` and their reach bits into `RB[j t …]` (`qLoopS`), the pivot loop
(`mvLoopS`, with the threshold from `TH`), the trees and the weights of the next move (`nxAS`,
`wtS`). -/
def tBodyS (B nD n k t : ℕ) : Stmt :=
  .seq (block [.modN 90 80 81, .constN 92 1, .addN 91 80 92, .modN 91 91 81, .constN 105 t,
    .mulN 93 80 105, .constN 106 (aOUT nD), .addN 106 106 93, .constN 109 (aRB n),
    .addN 109 109 93, .constN 104 0]) <|
  .seq (qLoopS B nD n k t) <|
  .seq (block [.constN 94 (aTH nD), .loadR 100 94, .constN 102 0, .constN 103 1]) <|
  .seq (mvLoopS B nD) <|
  .seq (.seq (nxAS B nD n) (wtS B nD n k)) <|
  block [.constN 92 1, .addN 80 80 92]

/-- **The loop over the `k` moves.** -/
def tLoopS (B nD n k t : ℕ) : Stmt := .whileLtN 80 81 (tBodyS B nD n k t)

/-- **The answer in the output** for the move `j` and the target `X i`: the real word
`OUT[j t + i]` when the reach bit `RB[j t + i]` is `1`, none otherwise. -/
def kOut (nD n t : ℕ) (c : Config) (j i : ℕ) : Option ℝ :=
  if c.nmem (aRB n + j * t + i) = 1 then some (c.rmem (aOUT nD + j * t + i)) else none

/-- An answer of the program on perturbed lengths (`MSSP.pert`, `2^m` times the lengths plus
less than `2^m`) read back: its integer part divided by `2^m`. -/
def outNN (m : ℕ) (o : Option ℝ) : Option ℤ := o.map fun r => Int.floor r / 2 ^ m

lemma outNN_map (m : ℕ) (o : Option ℤ) : outNN m (o.map ((↑) : ℤ → ℝ)) = o.map (· / 2 ^ m) := by
  unfold outNN
  rw [Option.map_map]
  congr 1
  funext z
  simp

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V}

local notation "𝒢" => pieceGraph M S ℓ

variable (V S ℓ) in
/-- The threshold of the pivot loops. -/
def tripTh : ℤ := tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ)

variable (V S ℓ) in
/-- **The value at the nodes of the faces at the start**, high enough for `k` moves. -/
def tripH0 (k : ℕ) : ℤ := tripTh V S ℓ + (k + 1) * ((Fintype.card V + 1) * tripK V S ℓ)

/-- The operations counted for the move `j` of the loop (`t` queries). -/
def tCnt (t : ℕ) (Rj : MoveData M S) (Δ : ℕ) : ℕ := t + 2 * (27 * Rj.m + 1) + 29 + 5 * Δ

/-- **The targets are reached from every root alike** (`SameReach`, the targets not being
roots). -/
lemma reach_tgt (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {x : V}
    (hx : ¬ IsRoot M k g x) (j : ℕ) :
    Reach 𝒢 (tripSrc M k g j) x ↔ Reach 𝒢 (M.tail (g 0)) x := by
  have hk := H.two_le_k
  have hj : j % k < k := Nat.mod_lt _ (by omega)
  exact ⟨hR _ hj 0 (by omega) x hx, hR 0 (by omega) _ hj x hx⟩

variable (M k g S ℓ σ n ιv ιg ιf ιe) in
/-- **The invariant of the loop over the moves**: the first `J` moves of a trip (`IsTripUpTo`)
made, the data at the start of the move `J` stored (from the forest `F₀` after the
initialisation, by the operations `hs`), the mutable arrays and the registers for the move `J`,
the constants kept, and the answers of the moves `j < J` at the targets in `OUT` and `RB`. -/
structure TInv (t : ℕ) (X : ℕ → V) (B W : ℕ) (F₀ : Forest) (c₀ : Config)
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config) : Prop where
  jle : y.1 ≤ k
  trip : IsTripUpTo M k g S ℓ y.1 y.2.1
  start : StartOK M k g S ℓ y.1 ((y.2.1 y.1).T 0) ((y.2.1 y.1).val 0)
  lcte : LCTE B n (runOpsE n F₀ hs).1 G c
  wb : WordsBounded W c
  st : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (y.1 % k))) y.2.2 (runOpsE n F₀ hs).1
    ((y.2.1 y.1).T 0) ((y.2.1 y.1).val 0)
  lo : (tripH0 V S ℓ k : ℝ) - y.1 * ((Fintype.card V + 1) * (tripK V S ℓ : ℝ)) ≤ y.2.2
  out : (runOpsE n F₀ hs).2 = []
  len : hs.length ≤ ∑ j ∈ range y.1, (16 * (y.2.1 j).m + 18 + 4 * (tripΔ M k g S j).card)
  kmem : KMem M σ ιv ((y.2.1 y.1).T 0) (tripWt M k g S ℓ y.1) (tripφ S ℓ) c
  r80 : c.nreg 80 = y.1
  r81 : c.nreg 81 = k
  r100 : c.nreg 100 = ιf (M.face (M.rev (g (y.1 % k))))
  r101 : c.nreg 101 = ιf (M.face (g (y.1 % k)))
  tl : c.rmem (aTL nD) = tripL V S ℓ
  th : c.rmem (aTH nD) = tripTh V S ℓ
  dist : ∀ j < y.1, ∀ i < t,
    kOut nD n t c j i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)
  output : c.output = c₀.output
  regs : ∀ r, r < 80 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r

section
variable {P : Input} {W B : ℕ}

/-- **One iteration of the loop over the moves**: the move `J` and the step to the move
`J + 1`, counted `t + 2 (27 m + 1) + 29 + 5 #(tripΔ J)` operations and
`14 t + 174 + 30 #(tripΔ J)` further steps. -/
theorem tBody_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config}
    (y : ℕ × (ℕ → MoveData M S) × ℝ) (hs : List EOp) (G : List VT) (c : Config)
    (h : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y hs G c) (ht : y.1 < k) :
    ∃ (y' : ℕ × (ℕ → MoveData M S) × ℝ) (c' : Config) (os : List EOp) (G' : List VT),
      ORun P W B n (tBodyS B nD n k t) c (runOpsE n F₀ hs).1 G c' os G'
        (tCnt t (y'.2.1 y.1) (tripΔ M k g S y.1).card)
        (14 * t + 174 + 30 * (tripΔ M k g S y.1).card) ∧
      TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y' (hs ++ os) G' c' ∧ y'.1 = y.1 + 1 ∧
      ∀ j < y.1, y'.2.1 j = y.2.1 j := by
  classical
  obtain ⟨J, R, Lo⟩ := y
  simp only at h ht ⊢
  set F := (runOpsE n F₀ hs).1 with hF
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hk := H.two_le_k
  have hJk : J * t ≤ k * t := Nat.mul_le_mul_right _ ht.le
  have hJk2 : J * t + t ≤ k * t := by
    have := Nat.mul_le_mul_right t (show J + 1 ≤ k by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  have hc := h.wb
  have hBW : B ≤ W := by omega
  have h80 : c.nreg 80 = J := h.r80
  -- the registers of the move
  obtain ⟨c₁, k₁, e₁, hk₁, p90, p91, p104, p105, p106, p109, n₁, r₁, mm₁, rm₁, out₁⟩ : ∃ c' k',
      Exec P W (block [.modN 90 80 81, .constN 92 1, .addN 91 80 92, .modN 91 91 81,
        .constN 105 t, .mulN 93 80 105, .constN 106 (aOUT nD), .addN 106 106 93,
        .constN 109 (aRB n), .addN 109 109 93, .constN 104 0]) c c' k' ∧ k' = 11 ∧
      c'.nreg 90 = J % k ∧ c'.nreg 91 = (J + 1) % k ∧
      c'.nreg 104 = 0 ∧ c'.nreg 105 = t ∧ c'.nreg 106 = aOUT nD + J * t ∧
      c'.nreg 109 = aRB n + J * t ∧
      (∀ r, (r < 90 ∨ (94 ≤ r ∧ r < 104) ∨ 110 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (first
      | omega
      | (config_simp; rw [h80]; omega))
    refine ⟨rfl, ?_, ?_, by config_simp, by config_simp, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl,
      rfl⟩
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h80, h.r81]
    · config_simp; rw [h80]
    · config_simp; rw [h80]
    · config_simp
      simp only [upd_other _ _ _ (show r ≠ 105 by omega), upd_other _ _ _ (show r ≠ 104 by omega),
        upd_other _ _ _ (show r ≠ 106 by omega), upd_other _ _ _ (show r ≠ 93 by omega),
        upd_other _ _ _ (show r ≠ 91 by omega), upd_other _ _ _ (show r ≠ 92 by omega),
        upd_other _ _ _ (show r ≠ 90 by omega), upd_other _ _ _ (show r ≠ 109 by omega)]
  have o₁ : ORun P W B n _ c F G c₁ [] G 0 k₁ := ORun.glue e₁ h.lcte
    (fun a _ _ => by rw [mm₁, rm₁]; exact ⟨rfl, rfl⟩) (n₁ 151 (by omega))
  -- the answers at the targets
  obtain ⟨c₂, G₂, o₂, q₂, rg₂, out₂, nm₂, rm₂, -⟩ := qry_orun (P := P) (k := k) (X := X)
    (xb := fun i => if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0) hW
    (by unfold iXT; omega) hP hL hX.xn hX.xr (base := aOUT nD + J * t)
    (rbase := aRB n + J * t) (by omega) (by omega) e₁.wb_right o₁.2.lcte p104 p105
    p106 p109
  -- the threshold
  have hc₂ := o₂.2.wb
  have hth₂ : c₂.rmem (aTH nD) = tripTh V S ℓ := by
    rw [rm₂ _ (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (Or.inl (by unfold aTH aOUT; omega)), rm₁, h.th]
  obtain ⟨c₃, k₃, e₃, hk₃, s100, s102, s103, n₃, r₃, mm₃, rm₃, out₃⟩ : ∃ c' k', Exec P W
      (block [.constN 94 (aTH nD), .loadR 100 94, .constN 102 0, .constN 103 1]) c₂ c' k' ∧
      k' = 4 ∧ c'.rreg 100 = ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) ∧
      c'.nreg 102 = 0 ∧ c'.nreg 103 = 1 ∧
      (∀ r, r ≠ 94 → r ≠ 102 → r ≠ 103 → c'.nreg r = c₂.nreg r) ∧
      (∀ r, r ≠ 100 → c'.rreg r = c₂.rreg r) ∧ c'.nmem = c₂.nmem ∧ c'.rmem = c₂.rmem ∧
      c'.output = c₂.output := by
    exec_block
    all_goals try (first | omega | (unfold aTH; omega))
    refine ⟨rfl, by config_simp; exact hth₂, by config_simp, by config_simp, fun r h1 h2 h3 => ?_,
      fun r hr => ?_, rfl, rfl, rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
    · config_simp; simp only [upd_other _ _ _ hr]
  have o₃ : ORun P W B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORun.glue e₃ o₂.2.lcte
    (fun a _ _ => by rw [mm₃, rm₃]; exact ⟨rfl, rfl⟩) (n₃ 151 (by omega) (by omega) (by omega))
  -- the memory and the registers at the start of the pivot loop
  have hnm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aRB n ∨ aRB n + k * t ≤ a) →
      c₃.nmem a = c.nmem a := fun a ha ha' => by
    rw [mm₃, nm₂ a ha (by omega), mm₁]
  have hrm₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aOUT nD ∨ aOUT nD + k * t ≤ a) →
      c₃.rmem a = c.rmem a := fun a ha ha' => by
    rw [rm₃, rm₂ a ha (by omega), rm₁]
  have hKM₃ : KMem M σ ιv ((R J).T 0) (tripWt M k g S ℓ J) (tripφ S ℓ) c₃ := by
    refine ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩
    · have := hL.prim.f_lt x
      rw [hnm₃ _ (Or.inl (by unfold aTP; omega)) (Or.inl (by unfold aTP aRB; omega))]
      exact h.kmem.tp x hx
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aOUT; omega))]
      exact h.kmem.wt d
    · have := hσ d
      rw [hrm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aOUT; omega))]
      exact h.kmem.ph d
  have hreg₃ : ∀ r, r < 90 → c₃.nreg r = c.nreg r ∧ c₃.rreg r = c.rreg r := fun r hr => by
    rw [n₃ r (by omega) (by omega) (by omega), r₃ r (by omega), (rg₂ r (by omega)).1,
      (rg₂ r (by omega)).2, n₁ r (Or.inl hr), r₁]; exact ⟨rfl, rfl⟩
  have u100 : c₃.nreg 100 = ιf (M.face (M.rev (g (J % k)))) := by
    rw [n₃ 100 (by omega) (by omega) (by omega), (rg₂ 100 (by omega)).1,
      n₁ 100 (Or.inr (Or.inl (by omega))), h.r100]
  have u101 : c₃.nreg 101 = ιf (M.face (g (J % k))) := by
    rw [n₃ 101 (by omega) (by omega) (by omega), (rg₂ 101 (by omega)).1,
      n₁ 101 (Or.inr (Or.inl (by omega))), h.r101]
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hJk' : (J : ℝ) + 1 ≤ k := by exact_mod_cast ht
  have hLo : ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) +
      Fintype.card V * (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) ≤ Lo := by
    have h1 := h.lo
    have e : (tripH0 V S ℓ k : ℝ) = ((tripL V S ℓ - 2 * (Fintype.card V * tripW S ℓ) : ℤ) : ℝ) +
        (k + 1) * ((Fintype.card V + 1) * (tripK V S ℓ : ℝ)) := by
      unfold tripH0 tripTh; push_cast; ring
    have e2 : (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) = tripK V S ℓ := rfl
    rw [e] at h1; rw [e2]
    have hV0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.2 hJk') (mul_nonneg (by linarith : (0 : ℝ) ≤
      Fintype.card V + 1) hK0)]
  -- the pivot loop
  obtain ⟨T, val, d, m, os₄, c₄, G₄, Lo₄, o₄, hT0, hv0, hrun, hTs, hl₄, ho₄, hS₄, hLo₄, hKM₄, fr₄,
    v100, v101, -, -⟩ := mv_orunA (P := P) hW (by omega) hB hP H.plane (H.tripMoveHyp hR J) H.uniq
    (H.g_not_mem J) (H.rev_g_not_mem J) (fun d hd => tripφ_of_mem hd) (W := tripW S ℓ)
    abs_tripφ_le (fun d hd hr => tripWt_elig J hd hr) (fun d hd => tripWt_inelig J hd)
    (fun d hd => tripL_gt hd) hL hK h.start.1 h.start.2 h.st hLo e₃.wb_right o₃.2.lcte hKM₃
    u100 u101 s100 s102 s103
  set RJ : MoveData M S := ⟨T, val, selForest M S (tpar 𝒢 (tripSrc M k g J)) d, d, m⟩ with hRJ
  have hMJ : MoveSpec M k g S ℓ J RJ := ⟨hrun, hTs⟩
  -- the next move
  have hc₄ := o₄.2.wb
  have w90 : c₄.nreg 90 = J % k := by rw [(fr₄.1 90 (by omega)).1, n₃ 90 (by omega) (by omega)
    (by omega), (rg₂ 90 (by omega)).1, p90]
  have w91 : c₄.nreg 91 = (J + 1) % k := by rw [(fr₄.1 91 (by omega)).1, n₃ 91 (by omega)
    (by omega) (by omega), (rg₂ 91 (by omega)).1, p91]
  have wtl : c₄.rmem (aTL nD) = tripL V S ℓ := by
    rw [fr₄.2.2.1 _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega)),
      hrm₃ _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
        (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  obtain ⟨c₅, G₅, os₅, T', val', o₅, hl₅, ho₅, hS₅, hstart, hr, hpw, hpu, hpx, hKM₅, x100, x101,
    rg₅, out₅, rm₅, nm₅⟩ := nx_orun (P := P) hW (by omega) hB (by unfold aOUT at hOUT; omega) hP
    H hR hL hK hG hO hMJ hc₄ o₄.2.lcte hS₄ hKM₄ wtl w90 w91 (by rw [v101, u101])
  -- the next index
  have hc₅ := o₅.2.wb
  have w80 : c₅.nreg 80 = J := by
    rw [(rg₅ 80 (by omega)).1, (fr₄.1 80 (by omega)).1, (hreg₃ 80 (by omega)).1, h.r80]
  obtain ⟨c₆, k₆, e₆, hk₆, z80, n₆, r₆, mm₆, rm₆, out₆⟩ : ∃ c' k', Exec P W
      (block [.constN 92 1, .addN 80 80 92]) c₅ c' k' ∧ k' = 2 ∧ c'.nreg 80 = J + 1 ∧
      (∀ r, r ≠ 80 → r ≠ 92 → c'.nreg r = c₅.nreg r) ∧ c'.rreg = c₅.rreg ∧
      c'.nmem = c₅.nmem ∧ c'.rmem = c₅.rmem ∧ c'.output = c₅.output := by
    exec_block
    · omega
    · config_simp; rw [w80]; omega
    · refine ⟨rfl, by config_simp; rw [w80], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have o₆ : ORun P W B n _ c₅ _ G₅ c₆ [] G₅ 0 k₆ := ORun.glue e₆ o₅.2.lcte
    (fun a _ _ => by rw [mm₆, rm₆]; exact ⟨rfl, rfl⟩) (n₆ 151 (by omega) (by omega))
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append, List.append_nil] at o
  -- the data of the next move
  set R' : ℕ → MoveData M S := fun i =>
    if i < J then R i else if i = J then RJ else startData T' val' (g 0) with hR'
  have hlt : ∀ i < J, R' i = R i := fun i hi => by simp [hR', hi]
  have hJ : R' J = RJ := by simp [hR']
  have hJ1 : R' (J + 1) = startData T' val' (g 0) := by simp [hR']
  have hT0' : ∀ i ≤ J, (R' i).T 0 = (R i).T 0 ∧ (R' i).val 0 = (R i).val 0 := by
    intro i hi
    rcases Nat.lt_or_ge i J with h' | h'
    · rw [hlt i h']; exact ⟨rfl, rfl⟩
    · obtain rfl : i = J := by omega
      rw [hJ]; exact ⟨hT0, hv0⟩
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hrun : (runOpsE n F₀ (hs ++ (os₄ ++ os₅))).1 = (runOpsE n (runOpsE n F os₄).1 os₅).1 := by
    rw [runOpsE_fst_append, runOpsE_fst_append]
  have hrm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (∀ d : D, a ≠ aWT + σ d) →
      (a < aOUT nD + J * t ∨ aOUT nD + J * t + t ≤ a) → c₆.rmem a = c.rmem a := by
    intro a ha hne ha'
    rw [rm₆, rm₅ a ha hne, fr₄.2.2.1 a ha, rm₃, rm₂ a ha ha', rm₁]
  have hnm₆ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a →
      (a < aRB n + J * t ∨ aRB n + J * t + t ≤ a) → c₆.nmem a = c.nmem a := by
    intro a ha hn ha'
    rw [mm₆, nm₅ a ha hn, fr₄.2.2.2 a ha hn, mm₃, nm₂ a ha ha', mm₁]
  have htrip : IsTripUpTo M k g S ℓ (J + 1) R' := by
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [hlt j h']; exact h.trip.move j h'
      · obtain rfl : j = J := by omega
        rw [hJ]; exact hMJ
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.root j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hr
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.par_dst j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hpw
    · rcases Nat.lt_or_ge j J with h' | h'
      · rw [(hT0' (j + 1) h').1]; exact h.trip.par_src j h'
      · obtain rfl : j = J := by omega
        rw [hJ1]; exact hpu
    · rcases Nat.lt_or_ge j J with h' | h'
      · intro x hx1 hx2
        rw [(hT0' (j + 1) h').1, hlt j h']; exact h.trip.par_other j h' x hx1 hx2
      · obtain rfl : j = J := by omega
        rw [hJ1, hJ]; exact hpx
  refine ⟨(J + 1, R', Lo₄ - tripK V S ℓ), c₆, os₄ ++ os₅, G₅, o.mono (by
    show _ ≤ tCnt t (R' J) _; rw [hJ]; unfold tCnt; show _ ≤ t + 2 * (27 * m + 1) + 29 + _; omega)
    (by omega), ⟨by simp only; omega, htrip, ?_, ?_, o₆.2.wb, ?_, ?_, ?_, ?_, ?_, z80, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩, rfl, fun j hj => hlt j hj⟩
  · show StartOK M k g S ℓ (J + 1) ((R' (J + 1)).T 0) ((R' (J + 1)).val 0)
    rw [hJ1]; exact hstart
  · rw [runOpsE_fst_append]; exact o.2.lcte
  · show Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g ((J + 1) % k))) (Lo₄ - tripK V S ℓ)
      (runOpsE n F₀ (hs ++ (os₄ ++ os₅))).1 ((R' (J + 1)).T 0) ((R' (J + 1)).val 0)
    rw [hJ1, hrun]; exact hS₅
  · show (tripH0 V S ℓ k : ℝ) - ((J + 1 : ℕ) : ℝ) * _ ≤ Lo₄ - _
    have h1 := h.lo
    have e2 : (driftK (tripL V S ℓ) (tripW S ℓ) (Fintype.card V) : ℝ) = tripK V S ℓ := rfl
    rw [e2] at hLo₄
    push_cast
    nlinarith
  · rw [runOpsE_append, h.out, runOpsE_append, ho₄]; exact ho₅
  · show (hs ++ (os₄ ++ os₅)).length ≤ ∑ j ∈ range (J + 1),
      (16 * (R' j).m + 18 + 4 * (tripΔ M k g S j).card)
    rw [sum_range_succ, hJ, sum_congr rfl fun i hi => by rw [hlt i (mem_range.1 hi)]]
    have := h.len
    simp only at this
    have hm : RJ.m = m := rfl
    simp only [List.length_append, hl₄, hm]
    omega
  · show KMem M σ ιv ((R' (J + 1)).T 0) _ _ c₆
    rw [hJ1]
    exact ⟨fun x hx => by rw [mm₆]; exact hKM₅.tp x hx, fun d => by rw [rm₆]; exact hKM₅.wt d,
      fun d => by rw [rm₆]; exact hKM₅.ph d⟩
  · rw [n₆ 81 (by omega) (by omega), (rg₅ 81 (by omega)).1, (fr₄.1 81 (by omega)).1,
      (hreg₃ 81 (by omega)).1, h.r81]
  · rw [n₆ 100 (by omega) (by omega), x100]
  · rw [n₆ 101 (by omega) (by omega), x101]
  · rw [hrm₆ (aTL nD) (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTL aWT at h'; omega)
      (Or.inl (by unfold aTL aOUT; omega)), h.tl]
  · rw [hrm₆ (aTH nD) (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
      (fun d h' => by have := hσ d; unfold aTH aWT at h'; omega)
      (Or.inl (by unfold aTH aOUT; omega)), h.th]
  · intro j hj i hi
    simp only at hj
    have hjk : j * t + i < k * t := by
      have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    have hout : aOUT nD + j * t + i < B := by omega
    have hrb : aRB n + j * t + i < B := by omega
    rcases Nat.lt_or_ge j J with h' | h'
    · have := Nat.mul_le_mul_right t (show j + 1 ≤ J by omega)
      rw [Nat.add_mul, one_mul] at this
      have e : kOut nD n t c₆ j i = kOut nD n t c j i := by
        unfold kOut
        rw [hrm₆ _ (Or.inl hout) (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega)
          (Or.inl (by omega)), hnm₆ _ (Or.inl hrb) (by unfold aRB; omega) (Or.inl (by omega))]
      rw [e]
      exact h.dist j h' i hi
    · obtain rfl : j = J := by omega
      have hS0 := h.st
      rw [← hT0] at hS0
      have hnr := hX.nr i hi
      have hb : c₆.nmem (aRB n + j * t + i) =
          if Reach 𝒢 (M.tail (g 0)) (X i) then 1 else 0 := by
        rw [mm₆, nm₅ _ (Or.inl hrb) (by unfold aRB; omega),
          fr₄.2.2.2 _ (Or.inl hrb) (by unfold aRB; omega), mm₃, (q₂ i hi).2]
      unfold kOut odist
      rw [hb, rm₆, rm₅ _ (Or.inl hout)
        (fun d h'' => by have := hσ d; unfold aOUT aWT at h''; omega),
        fr₄.2.2.1 _ (Or.inl hout), rm₃, (q₂ i hi).1]
      by_cases hr : Reach 𝒢 (M.tail (g 0)) (X i)
      · have hr' := (reach_tgt H hR hnr j).2 hr
        simp only [hr, hr', ↓reduceIte, Option.map_some]
        exact congrArg some (stored_label H hR hL hMJ hS0 hr')
      · have hr' : ¬ Reach 𝒢 (tripSrc M k g j) (X i) := fun h => hr ((reach_tgt H hR hnr j).1 h)
        simp [hr, hr']
  · rw [out₆, out₅, fr₄.2.1, out₃, out₂, out₁, h.output]
  · intro r hr
    rw [n₆ r (by omega) (by omega), r₆, (rg₅ r (by omega)).1, (rg₅ r (by omega)).2,
      (fr₄.1 r (by omega)).1, (fr₄.1 r (by omega)).2, (hreg₃ r (by omega)).1,
      (hreg₃ r (by omega)).2]
    exact h.regs r hr

/-- **The loop over the moves**: from the invariant at the start of the first move, the loop
makes the `k` moves, counted `∑ j < k, tCnt` operations and
`k (14 t + 182) + 30 ∑ j < k, #(tripΔ j) + 2` further steps, and ends with the invariant at the
move `k`. -/
theorem tLoop_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {F₀ : Forest} {c₀ : Config} {R₀ : ℕ → MoveData M S}
    {Lo₀ : ℝ} {G : List VT} {c : Config}
    (h : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ (0, R₀, Lo₀) [] G c) :
    ∃ (R : ℕ → MoveData M S) (Lo : ℝ) (os : List EOp) (c' : Config) (G' : List VT),
      ORun P W B n (tLoopS B nD n k t) c F₀ G c' os G'
        (∑ j ∈ range k, tCnt t (R j) (tripΔ M k g S j).card)
        (k * (14 * t + 182) + 30 * ∑ j ∈ range k, (tripΔ M k g S j).card + 2) ∧
      TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ (k, R, Lo) os G' c' := by
  classical
  set cnt : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    ∑ j ∈ range y.1, tCnt t (y.2.1 j) (tripΔ M k g S j).card with hcnt
  set ext : ℕ × (ℕ → MoveData M S) × ℝ → ℕ := fun y =>
    (k - y.1) * (14 * t + 182) + 30 * ∑ j ∈ Ico y.1 k, (tripΔ M k g S j).card with hext
  obtain ⟨y, os, c', G', hrun, hI, ht, -, -⟩ := ORun.whileLtN (P := P) (W := W) (B := B)
    (n := n) (a := 80) (b := 81) (body := tBodyS B nD n k t) F₀
    (fun y hs G₁ c₁ => TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₀ y hs G₁ c₁) cnt ext
    (fun _ _ _ _ h' _ => ⟨h'.lcte, h'.wb⟩)
    (fun y hs G₁ c₁ h' _ ht => by
      have hJ : y.1 < k := by rw [h'.r80, h'.r81] at ht; exact ht
      obtain ⟨y', c₂, os, G₂, o, hI', hy1, hagree⟩ :=
        tBody_orun hW hWa hB hOUT hRB hP H hR hL hK hG hO hX y hs G₁ c₁ h' hJ
      refine ⟨y', c₂, os, G₂, _, _, o, hI', ?_, ?_⟩
      · simp only [hcnt, hy1, sum_range_succ]
        rw [sum_congr rfl fun j hj => by rw [hagree j (mem_range.1 hj)]]
      · simp only [hext, hy1]
        rw [sum_eq_sum_Ico_succ_bot hJ]
        have : k - y.1 = k - (y.1 + 1) + 1 := by omega
        rw [this]
        ring_nf
        omega)
    (x := (0, R₀, Lo₀)) (hs := []) h trivial
  have hk : y.1 = k := by
    have := hI.jle; rw [hI.r80, hI.r81] at ht; omega
  obtain ⟨J, R, Lo⟩ := y
  simp only at hk
  subst hk
  refine ⟨R, Lo, os, c', G', hrun.mono (by simp [hcnt]) ?_, by simpa using hI⟩
  simp only [hext, Nat.sub_zero, Nat.sub_self, zero_mul, Ico_self, sum_empty, mul_zero,
    add_zero]
  rw [range_eq_Ico]

end

/-! ### The whole program -/

/-- The registers of the loop and the query nodes of the first move. -/
def setupI (nD n k : ℕ) : List Instr :=
  [.constN 80 0, .constN 81 k, .constN 85 (iGB nD n), .readIn 85 85,
    .constN 101 (iNF nD), .addN 101 101 85, .readIn 101 101,
    .constN 86 (iRV nD), .addN 86 86 85, .readIn 86 86,
    .constN 100 (iNF nD), .addN 100 100 86, .readIn 100 100]

/-- **Klein's algorithm on the evertable link-cut trees** (after `r151 := n` and the
initialisation of the structure): the initial trees (`inS`), then the `k` moves around the
face (`tLoopS`), with the answers at the `t` targets at the start of every move. -/
def kleinS (B nD n k t : ℕ) : Stmt := .seq (inS B nD n k) (.seq (block (setupI nD n k))
  (tLoopS B nD n k t))

/-- **The program**: `r151 := n`, the initialisation of the structure, `kleinS`. -/
def kleinProg (B nD n k t : ℕ) : Stmt :=
  .seq (.instr (.constN 151 n)) (.seq (initS B) (kleinS B nD n k t))

/-- The bound of the counted operations of `kleinS` (`k t` queries). -/
def kleinOps (nV nF nD nS k t : ℕ) : ℕ := 6 * (nV + nF) + 2 * nD + k * t + 64 * nS + 31 * k

/-- The bound of the further steps of `kleinS`. -/
def kleinExt (nV nF nD nS k t : ℕ) : ℕ :=
  60 * (nV + nF) + 20 * nD + 57 + k * (14 * t + 182) + 60 * nS

/-- **An adaptive program from a given configuration** (`lctE_adaptive_run` with the final
configuration): `r151 := n`, the initialisation, then `s`, from `c₀`. -/
theorem _root_.PlanarFlow.DynTree.lctE_adaptive_exec (B n : ℕ) (s : Stmt) (P : Input)
    (m g : ℕ) {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀) (Q : Config → Prop)
    (hs : ∀ c, WordsBounded (B + 16 * (n + 1)) c → LCTE B n (Forest.init n) (G0 n) c →
      c.output = c₀.output → MemFrame B n (mem c₀) (mem c) →
      (∀ r, (r < 160 ∨ 200 ≤ r) → r ≠ 151 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r) →
      ∃ c' F' G' m', LRun P (B + 16 * (n + 1)) B n s c (G0 n) c' F' G' m' g ∧ m' ≤ m ∧
        Q c') :
    ∃ c' k, Exec P (B + 16 * (n + 1)) (.seq (.instr (.constN 151 n)) (.seq (initS B) s)) c₀ c'
      k ∧ k ≤ 140 * (n + 1) + 21 + m * opCostE n + g ∧ Q c' := by
  have e1 := Exec.constN (P := P) hc₀ 151 n (by omega)
  obtain ⟨c2, k2, e2, hk2, hS2, hpot, hmf2, hfr2⟩ := init_exec (P := P) B n e1.wb_right le_rfl
    (by simp)
  obtain ⟨c3, F3, G3, m', ⟨k3, e3, -, hk3⟩, hm', hQ⟩ := hs c2 e2.wb_right hS2.toE
    (by rw [hfr2.2.2]) hmf2 (fun r hr h151 => by
      rw [(hfr2.1 r hr).1, (hfr2.1 r hr).2]; simp [upd_other _ _ _ h151])
  refine ⟨c3, _, .seq e1 (.seq e2 e3), ?_, hQ⟩
  rw [hpot] at hk3
  have := Nat.mul_le_mul_right (opCostE n) hm'
  omega

section
variable {P : Input} {W B : ℕ}

lemma sum_tCnt_le (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {R : ℕ → MoveData M S}
    (hT : IsTripUpTo M k g S ℓ k R) :
    ∑ j ∈ range k, tCnt t (R j) (tripΔ M k g S j).card ≤ k * t + 64 * S.card + 31 * k := by
  have e : ∀ j, tCnt t (R j) (tripΔ M k g S j).card =
      (t + 31) + 54 * (R j).m + 5 * (tripΔ M k g S j).card := fun j => by unfold tCnt; ring
  rw [sum_congr rfl fun j _ => e j, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_const, card_range, smul_eq_mul]
  have h1 := hT.pivots H hR le_rfl
  have h2 := sum_tripΔ_le H
  have e2 : k * (t + 31) = k * t + 31 * k := by ring
  omega

/-- **Klein's algorithm on the machine, from the initialised structure**: from the empty forest
stored at `B`, the input describing the map (`KInput`), the boundary (`KBnd`), the out-darts of
the piece (`KOut`) and initial trees (`KInit`: a tree `T` compatible with the first move, a cotree
`C` of it rooted at the face of `g 0`), and the real memory holding `tripWt 0` (`WT`), `tripφ`
(`PH`), `tripL` (`TL`), the threshold (`TH`) and `tripH0` (`H0`), the program `kleinS` makes the
`k` moves of a trip (`IsTripUpTo k`), counted at most `kleinOps` operations and `kleinExt`
further steps, printing nothing; at the end the answer `kOut j i` in the output (`OUT[j t + i]`
where the reach bit `RB[j t + i]` is `1`) is the distance from the source of the move `j` to the
target `X i` (`KTgt`), none when it is not reached. -/
theorem kleinS_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ W)
    (hB : n + 2 * nD ≤ B) (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W)
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)))
    {c : Config} (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = tripφ S ℓ d) (htl : c.rmem (aTL nD) = tripL V S ℓ)
    (hth : c.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c.rmem (aH0 nD) = tripH0 V S ℓ k) :
    ∃ c' F' G' m', LRun P W B n (kleinS B nD n k t) c G c' F' G' m'
        (kleinExt (Fintype.card V) (Fintype.card F) nD S.card k t) ∧
      m' ≤ kleinOps (Fintype.card V) (Fintype.card F) nD S.card k t ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, ∀ i < t,
        kOut nD n t c' j i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c.output := by
  classical
  have hk := H.two_le_k
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  -- the initial trees
  obtain ⟨c₁, G₁, os₁, o₁, -, ho₁, hS₁, hKM₁, -, out₁, -, rm₁⟩ := in_orun hW (by omega) hB
    (by unfold aOUT at hOUT; omega) hP hL hK hI hoff hc hS hwt hph hh0
  set F₀ := (runOpsE n (Forest.init n) os₁).1 with hF₀
  -- the registers of the loop
  have hg0 : P.data.getD (iGB nD n) 0 = σ (g 0) := by simpa using hG 0 (by omega)
  have hc₁ := o₁.2.wb
  have h0 := hσ (g 0)
  have h0' := hσ (M.rev (g 0))
  obtain ⟨c₂, k₂, e₂, hk₂, p80, p81, p100, p101, n₂, r₂, mm₂, rm₂, out₂⟩ : ∃ c' k', Exec P W
      (block (setupI nD n k)) c₁ c' k' ∧ k' = 13 ∧ c'.nreg 80 = 0 ∧ c'.nreg 81 = k ∧
      c'.nreg 100 = ιf (M.face (M.rev (g 0))) ∧ c'.nreg 101 = ιf (M.face (g 0)) ∧
      (∀ r, r ≠ 80 → r ≠ 81 → r ≠ 85 → r ≠ 86 → r ≠ 100 → r ≠ 101 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
    unfold setupI
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (simp only [iGB, iNF, iRV]; omega)
      | (config_simp; rw [hg0]; simp only [iNF, iRV]; omega)
      | (config_simp; rw [hg0, hK.rv]; simp only [iNF]; omega))
    refine ⟨rfl, by config_simp, by config_simp, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl,
      rfl, rfl⟩
    · config_simp; rw [hg0, hK.rv, hK.nf]
    · config_simp; rw [hg0, hK.nf]
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, upd_other _ _ _ h4,
        upd_other _ _ _ h5, upd_other _ _ _ h6]
  have o₂ : ORun P W B n _ c₁ F₀ G₁ c₂ [] G₁ 0 k₂ := ORun.glue e₂ o₁.2.lcte
    (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩)
    (n₂ 151 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  -- the invariant at the first move
  have hI₀ : TInv M k g S ℓ σ n ιv ιg ιf ιe t X B W F₀ c₂
      (0, fun _ => startData T (fun d => tripWt M k g S ℓ 0 d + T.psum (tripφ S ℓ) (M.tail d) -
        T.psum (tripφ S ℓ) (M.head d)) (g 0), (tripH0 V S ℓ k : ℝ)) [] G₁ c₂ := by
    refine ⟨Nat.zero_le _, ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩, ⟨hT, fun d _ => rfl⟩, o₂.2.lcte, e₂.wb_right, ?_,
      by simp, rfl, by simp, ?_, p80, p81, ?_, ?_, ?_, ?_,
      fun j hj => absurd hj (by omega), rfl, fun _ _ => ⟨rfl, rfl⟩⟩
    · simp only [Nat.zero_mod]; rw [← hCr]; exact hS₁
    · exact ⟨fun x hx => by rw [mm₂]; exact hKM₁.tp x hx, fun d => by rw [rm₂]; exact hKM₁.wt d,
        fun d => by rw [rm₂]; exact hKM₁.ph d⟩
    · simp only [Nat.zero_mod]; exact p100
    · simp only [Nat.zero_mod]; exact p101
    · rw [rm₂, rm₁ _ (Or.inl (by unfold aTL; unfold aOUT at hOUT; omega))
        (Or.inr (by unfold aTL aVL; omega)), htl]
    · rw [rm₂, rm₁ _ (Or.inl (by unfold aTH; unfold aOUT at hOUT; omega))
        (Or.inr (by unfold aTH aVL; omega)), hth]
  -- the moves
  obtain ⟨R, Lo, os, c₃, G₃, o₃, hI₃⟩ :=
    tLoop_orun hW hWa hB hOUT hRB hP H hR hL hK hG hO hX hI₀
  have o := o₁.seq (o₂.seq o₃)
  have hTk : IsTripUpTo M k g S ℓ k R := hI₃.trip
  refine ⟨c₃, _, G₃, _, o.2.mono le_rfl ?_, ?_, ⟨R, hTk⟩, hI₃.dist, ?_⟩
  · have := sum_tripΔ_le H
    unfold kleinExt; omega
  · have := sum_tCnt_le (t := t) (R := R) H hR hI₃.trip
    unfold kleinOps; omega
  · rw [hI₃.output, out₂, out₁]

end

/-! ### The end-to-end theorem -/

section
variable {P : Input} {B : ℕ}

/-- **Klein's algorithm on the machine** (multiple-source shortest paths from the `k` vertices
of a face, in the form of Cabello, Chambers and Erickson, on evertable link-cut trees): the
program `kleinProg` runs from a configuration `c₀` in which

* the input holds the map (`KInput`: reverses, nodes of faces, edges, tails and heads, the piece
  and its lengths), the boundary darts (`KBnd`), the out-darts of the piece (`KOut`) and an
  initial spanning tree `T` (compatible with the first move: the shortest-path tree from the
  first root, as Dijkstra's algorithm computes) with a cotree `C` of it rooted at the face of
  `g 0`, by orders of their nodes and depth orders (`KInit`);
* the real memory holds the weights `tripWt 0` (`WT`, from the reach bits of the first target),
  `tripφ` (`PH`), and the constants `tripL` (`TL`), `tripTh` (`TH`) and `tripH0` (`H0`), which
  the caller computes in its real registers (the machine has no conversion from naturals to
  reals);

* the input also holds the `t` targets `X i` (`KTgt`: not roots, by their nodes, with their
  reach bits from the roots);

within `140 (n + 1) + 21 + kleinOps · opCostE n + kleinExt` steps (every executed step counted,
the operations of the link-cut trees at their amortised cost); it makes the `k` moves of a trip
around the face (`IsTripUpTo k`), prints nothing, and **ends with the answers in its output**:
for every move `j` and target `X i`, the real word `OUT[j t + i]` and the natural word
`RB[j t + i]` give (`kOut`) the distance in the piece from the source `tail (g j)` of the move `j`
to `X i` when it is reached, `none` otherwise (`odist`). -/
theorem klein_exec (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
    (hOUT : aOUT nD + k * t ≤ B) (hRB : aRB n + k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1))
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)))
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = tripφ S ℓ d) (htl : c₀.rmem (aTL nD) = tripL V S ℓ)
    (hth : c₀.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c₀.rmem (aH0 nD) = tripH0 V S ℓ k) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (kleinProg B nD n k t) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 +
        kleinOps (Fintype.card V) (Fintype.card F) nD S.card k t * opCostE n +
        kleinExt (Fintype.card V) (Fintype.card F) nD S.card k t ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, ∀ i < t,
        kOut nD n t c' j i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c₀.output := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  unfold aOUT at hOUT
  exact lctE_adaptive_exec B n (kleinS B nD n k t) P _ _ hc₀ _ fun c hc hS hout hmf _ => by
    have hm : ∀ a, a < B → c.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
    obtain ⟨c', F', G', m', hrun, hm', htrip, hd, hout'⟩ := kleinS_orun le_rfl (by omega) hB
      (by unfold aOUT; omega) hRB hP H hR hL hK hG hO hX hI hoff hCr hT hc hS
      (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
      (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
      (by rw [hm _ (by unfold aTL; omega)]; exact htl)
      (by rw [hm _ (by unfold aTH; omega)]; exact hth)
      (by rw [hm _ (by unfold aH0; omega)]; exact hh0)
    exact ⟨c', F', G', m', hrun, hm', htrip, hd, hout'.trans hout⟩

end

/-- **The step bound is `O(N log N + k t log N)`** on `n = 2 N` nodes,
`N = #V + #F + #D`, for `t` targets (all `k` roots answered; on the cuts of the maximum-flow
algorithm `k` can be of the order of `N`, see `kleinM_steps_le` for the masked variant). -/
theorem klein_steps_le {nV nF nD nS k t : ℕ} (hN : 1 ≤ nV + nF + nD) (hS : nS ≤ nD)
    (hk : k ≤ nV) :
    140 * (2 * (nV + nF + nD) + 1) + 21 +
        kleinOps nV nF nD nS k t * opCostE (2 * (nV + nF + nD)) + kleinExt nV nF nD nS k t ≤
      36500000 * ((nV + nF + nD) * BKMNW.lg (nV + nF + nD) +
        k * t * BKMNW.lg (nV + nF + nD)) := by
  set N := nV + nF + nD with hNdef
  set l := BKMNW.lg N with hldef
  have hl1 : 1 ≤ l := BKMNW.one_le_lg N
  have hlog2 : Nat.log 2 (2 * N) = l := by
    rw [hldef]; unfold BKMNW.lg
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hops : kleinOps nV nF nD nS k t ≤ 103 * N + k * t := by unfold kleinOps; omega
  have hcost : opCostE (2 * N) ≤ 353820 * l := by unfold opCostE; rw [hlog2]; omega
  have hext : kleinExt nV nF nD nS k t ≤ 377 * N + 14 * (k * t) + 182 * k := by
    unfold kleinExt
    have : k * (14 * t + 182) = 14 * (k * t) + 182 * k := by ring
    omega
  have h1 : kleinOps nV nF nD nS k t * opCostE (2 * N) ≤ (103 * N + k * t) * (353820 * l) :=
    Nat.mul_le_mul hops hcost
  have h2 : N ≤ N * l := Nat.le_mul_of_pos_right N hl1
  have h3 : k * t ≤ k * t * l := Nat.le_mul_of_pos_right _ hl1
  have e : (103 * N + k * t) * (353820 * l) = 36443460 * (N * l) + 353820 * (k * t * l) := by
    ring
  have e2 : 36500000 * (N * l + k * t * l) = 36500000 * (N * l) + 36500000 * (k * t * l) := by
    ring
  omega

/-! ### The answers -/

/-- **The initial data exist**: a tree compatible with the first move (with the values of
`StartOK 0`), a cotree of it rooted at the face of `g 0`, and orders of both (the semantic part of
`KInit`). -/
theorem klein_init_exists (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) :
    ∃ (T : DTree M.dual) (C : DTree M) (vs ts : List V) (fs cs : List F),
      Orders T vs ts ∧ Orders C fs cs ∧ (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
      C.root = M.face (g 0) ∧
      Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)) := by
  obtain ⟨T, val, hs⟩ := exists_start0 H hR
  have : Nonempty D := ⟨g 0⟩
  obtain ⟨C, hCr, hoff⟩ := exists_cotree H.plane T (M.face (g 0))
  exact ⟨T, C, _, _, _, _, orders_exist T, orders_exist C, hoff, hCr, hs.1⟩

/-- **The answers of the trip are the program's output**: the answers `kleinAns` of the trip
(`PlanarFlow.Klein.Bridge`, from which `msspPlaneK` is built) at the targets are the answers
`kOut` read from the final configuration of `klein_exec`. -/
theorem klein_out_ans (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {out : ℕ → ℕ → Option ℝ}
    (hd : ∀ j < k, ∀ i < t, out j i = (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ))
    {j i : ℕ} (hj : j < k) (hi : i < t) :
    out j i = (kleinAns H hR j (X i)).map ((↑) : ℤ → ℝ) := by
  rw [kleinAns_eq, hd j hj i hi]

/-- **The answers of `msspPlaneK` on the chosen cut** are those of the trip on that cut
(`kleinAns`, on the perturbed lengths), divided by `2^|D'|`. -/
theorem msspCutK_eq_ans {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {L : List D} {ℓ : D → ℤ}
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) :
    msspCutK M D' V' F' L ℓ x y =
      (kleinAns h.choose.hyp.hyp h.choose_spec (Nat.find hx) (h.choose.vx y)).map
        (· / 2 ^ Fintype.card D') := by
  classical
  simp only [msspCutK, h, ↓reduceDIte, BKMNW.Cut.answerK, hx, kleinNN]

/-- **The answers of `msspPlaneK` on the chosen cut are read from the output of the program**:
for an output meeting the conclusion of `klein_exec` on that cut (with the perturbed lengths) and
a target `X i` the copy of the face `y`, the answer from `x` at `y` is the answer `out j i` of the
move `j` of the root of `x`, its integer part divided by `2^|D'|` (`outNN`). -/
theorem msspCutK_eq_out {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {L : List D} {ℓ : D → ℤ}
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) {t : ℕ} {X : ℕ → V'}
    {out : ℕ → ℕ → Option ℝ}
    (hd : ∀ j < h.choose.k, ∀ i < t, out j i = (odist (pieceGraph h.choose.map h.choose.piece
      (pert h.choose.len)) (tripSrc h.choose.map h.choose.k h.choose.g j) (X i)).map
      ((↑) : ℤ → ℝ))
    {i : ℕ} (hi : i < t) (hXi : X i = h.choose.vx y) :
    msspCutK M D' V' F' L ℓ x y = outNN (Fintype.card D') (out (Nat.find hx) i) := by
  rw [msspCutK_eq_ans h hx y, klein_out_ans h.choose.hyp.hyp h.choose_spec hd
    (Nat.find_spec hx).1 hi, hXi]
  unfold outNN
  rw [Option.map_map]
  congr 1
  funext z
  simp

end Klein

end PlanarFlow
