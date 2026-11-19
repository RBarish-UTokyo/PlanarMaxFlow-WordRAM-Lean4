module

public import PlanarFlow.DynTree.RegOps

/-!
# Dynamic trees with evert: reading and writing the values of one node

Register-operand blocks (the interface of `PlanarFlow/DynTree/RegOps.lean`: `RegFr`, the scratch
registers `r160 … r199`, real `r160 … r200`) for the values of a single node; `k : Bool` selects
the value (`false`: `val`, `true`: `val2`; `Forest.valc`).

* `regValS B k ra`: real `r195 := F.valc k v`, `v = r ra`, for any node `v`. The value is the
  difference of the path sums at `v` and at its parent (`pathSum_par`: the root path of `v` is
  `v` followed by the root path of its parent); three accesses, within the amortised cost of two
  operations of `PlanarFlow/DynTree/RunE.lean`.
* `regSetS B k ra rz`: for a root `v = r ra` (for example an isolated node), set its value to the
  real `r rz`: the path sum at `v` is its value (`pathSum_root`), and the difference is added on
  the root path, which is `[v]` (`addPathC_root`). In the terms of `EOp` this is the single
  operation `add v (x - val v)` (`add2` for `k = true`); two accesses, within the amortised
  cost of one operation.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-! ### The root path -/

/-- The path sum of channel `k`. -/
def pathSumC (F : Forest) (n v : ℕ) (k : Bool) : ℝ := if k then pathSum2 F n v else pathSum F n v

/-- More fuel does not change a path that ends at a root. -/
lemma upPath_succ (F : Forest) (n : ℕ) : ∀ (f u : ℕ),
    (∀ x, (upPath F n f u).getLast? = some x → F.par x = n) →
    (upPath F n f u = [] → n ≤ u) → upPath F n (f + 1) u = upPath F n f u
  | 0, u, _, h2 => by
    have := h2 rfl
    simp [upPath, show ¬ u < n by omega]
  | f + 1, u, h1, h2 => by
    by_cases hu : u < n
    · have e : ∀ g, upPath F n (g + 1) u = u :: upPath F n g (F.par u) := fun g => by
        simp [upPath, hu]
      rw [e (f + 1), e f]
      congr 1
      refine upPath_succ F n f (F.par u) (fun x hx => h1 x ?_) (fun h0 => ?_)
      · rw [e f, List.getLast?_cons, hx]; rfl
      · have := h1 u (by rw [e f, h0]; rfl)
        omega
    · simp [upPath, hu]

/-- The root path of a non-root `v` is `v` followed by the root path of its parent (the forest
stored by the structure is a forest: the path from `v` ends at a root). -/
theorem LCTE.rootPath_par {W : ℕ} (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ}
    (hvn : v < n) (hp : F.par v < n) : rootPath F n v = v :: rootPath F n (F.par v) := by
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have e0 := Exec.constN (P := ⟨[], fun _ => 0⟩) hc 189 v (by omega)
  obtain ⟨c', k, l, dv, -, hS', -⟩ := access_execE (P := ⟨[], fun _ => 0⟩) B n e0.wb_right
    hW (hS.updN 189 v (by omega)) (by simp) hvn hG hvT
  have hseq : VT.seq (node l v leaf dv) = VT.seq l ++ [v] := by simp [VT.seq]
  have hrp := rootPath_top B n hS'.inv hS'.rep (gb := []) rfl hseq
  have hch : ∀ e ∈ VT.chain n (VT.seq l ++ [v]), F.par e.1 = e.2 := fun e he =>
    hS'.rep.par e.1 e.2 (by simp [he])
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdef : rootPath F (m + 1) v = v :: upPath F (m + 1) m (F.par v) := by
    simp [rootPath, upPath, hvn]
  rw [hdef, List.reverse_append] at hrp
  have hR : upPath F (m + 1) m (F.par v) = (VT.seq l).reverse := by simpa using hrp
  rw [hdef, rootPath, upPath_succ F (m + 1) m (F.par v)]
  · intro x hx
    rw [hR, List.getLast?_reverse] at hx
    rcases hl : VT.seq l with _ | ⟨y, L⟩
    · simp [hl] at hx
    · rw [hl] at hx hch
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      exact hch (y, m + 1) (by simp)
  · intro h0
    rw [hR, List.reverse_eq_nil_iff] at h0
    rw [h0] at hch
    have : F.par v = m + 1 := hch (v, m + 1) (by simp)
    omega

/-- The path sum at a non-root `v` is its value plus the path sum at its parent. -/
theorem LCTE.pathSumC_par {W : ℕ} (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ}
    (hvn : v < n) (hp : F.par v < n) (k : Bool) :
    pathSumC F n v k = F.valc k v + pathSumC F n (F.par v) k := by
  have h := hS.rootPath_par B n hc hW hvn hp
  cases k <;> simp [pathSumC, pathSum, pathSum2, Forest.valc, h]

/-- The root path of a root is the root alone. -/
lemma rootPath_of_le {F : Forest} {n v : ℕ} (hvn : v < n) (hp : n ≤ F.par v) :
    rootPath F n v = [v] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases m with
  | zero => simp [rootPath, upPath, hvn]
  | succ m => simp [rootPath, upPath, hvn, show ¬ F.par v < m + 1 + 1 by omega]

/-- The path sum at a root is its value. -/
lemma pathSumC_root {F : Forest} {n v : ℕ} (hvn : v < n) (hp : n ≤ F.par v) (k : Bool) :
    pathSumC F n v k = F.valc k v := by
  cases k <;> simp [pathSumC, pathSum, pathSum2, Forest.valc, rootPath_of_le hvn hp]

/-- The forest with the value of channel `k` of `v` set to `x`. -/
def Forest.setValC (F : Forest) (k : Bool) (v : ℕ) (x : ℝ) : Forest :=
  if k then ⟨F.par, F.val, Function.update F.val2 v x⟩
  else ⟨F.par, Function.update F.val v x, F.val2⟩

/-- At a root `v`, adding `x - valc k v` on the root path sets the value of `v` to `x`. -/
lemma addPathC_root {F : Forest} {n v : ℕ} (hvn : v < n) (hp : n ≤ F.par v) (k : Bool)
    (x : ℝ) : addPathC F n v (x - F.valc k v) k = F.setValC k v x := by
  have h := rootPath_of_le hvn hp
  cases k
  · simp only [addPathC, addPath, Forest.setValC, h, Forest.valc, Bool.false_eq_true,
      ↓reduceIte, List.mem_singleton]
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · simp [hu]
  · simp only [addPathC, addPath2, Forest.setValC, h, Forest.valc, ↓reduceIte,
      List.mem_singleton]
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · simp [hu]

/-! ### The blocks -/

/-- The queries of channel `k` at `v = r193` (`opQueryS`, `opQuery2S`). -/
def opQueryCS (B : ℕ) (k : Bool) : Stmt := if k then opQuery2S B else opQueryS B

/-- The addition of the real `r200` to channel `k` on the root path of `v = r193` (`opAddS`,
`opAdd2S`). -/
def opAddCS (B : ℕ) (k : Bool) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
    block (ldR B 197 189 (tgf k) ++ [.addR 197 197 200] ++ stR B 189 (tgf k) 197)

/-- **The value of channel `k` of `v = r ra`**, into the real `r195` (also left in the real
`r200`): the path sum at `v`, less the path sum at the parent of `v` if `v` is not a root. -/
def regValS (B : ℕ) (k : Bool) (ra : ℕ) : Stmt :=
  .seq (.instr (.copyN 193 ra)) <| .seq (opQueryCS B k) <| .seq (.instr (.copyR 200 196)) <|
  .seq (opParentAccS B) <|
  .seq (.ifLtN 195 151
    (.seq (.instr (.copyN 193 195)) (.seq (opQueryCS B k) (.instr (.subR 200 200 196)))) .skip)
    (.instr (.copyR 195 200))

/-- **Set the value of channel `k` of a root `v = r ra` to the real `r rz`.** -/
def regSetS (B : ℕ) (k : Bool) (ra rz : ℕ) : Stmt :=
  .seq (.instr (.copyN 193 ra)) <| .seq (.instr (.copyR 200 rz)) <| .seq (opQueryCS B k) <|
  .seq (.instr (.subR 200 200 196)) (opAddCS B k)

section
variable {P : Input} {W : ℕ}

theorem opQueryC_exec (B n : ℕ) (k : Bool) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ}
    (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k' G', Exec P W (opQueryCS B k) c c' k' ∧ LCTE B n F G' c' ∧
      c'.rreg 196 = pathSumC F n v k ∧ MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧
      c'.nreg 193 = v ∧
      k' + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 := by
  cases k
  · obtain ⟨c', k', G', e, hS', -, -, -, h4, hmf, hfr, h193, -, hk, -⟩ :=
      opQuery_execE (P := P) B n hc hW hS hv hvn
    exact ⟨c', k', G', e, hS', by simpa [pathSumC] using h4, hmf, hfr, h193, hk⟩
  · obtain ⟨c', k', G', e, hS', -, -, h4, hmf, hfr, h193, -, hk⟩ :=
      opQuery2_exec (P := P) B n hc hW hS hv hvn
    exact ⟨c', k', G', e, hS', by simpa [pathSumC] using h4, hmf, hfr, h193, hk⟩

/-- **Reading the value of one node** (channel `k`, `v = r ra`): real `r195 := F.valc k v`.
Three accesses: the amortised cost of at most two operations of `eopStmt_exec`. -/
theorem regVal_exec (B n : ℕ) (k : Bool) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra v : ℕ}
    (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' k', Exec P W (regValS B k ra) c c' k' ∧ ∃ G', LCTE B n F G' c' ∧
      c'.rreg 195 = F.valc k v ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k' + 16400 * potL G' ≤ 16400 * potL G + 442800 * Nat.log 2 n + 63310 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  obtain ⟨c2, k2, G2, e2, hS2, s2, hmf2, hfr2, h193, hk2⟩ := opQueryC_exec (P := P) B n k
    e1.wb_right hW (hS.updN 193 _ (by omega)) (by simp [hv]) hvn
  have e3 := Exec.copyR (P := P) e2.wb_right 200 196
  obtain ⟨c4, k4, G4, e4, hS4, p4, hmf4, hfr4, h193', -, hk4⟩ := opParentAcc_exec (P := P) B n
    e3.wb_right hW (hS2.updR 200 _) (by simpa using h193) hvn
  have r200 : c4.rreg 200 = pathSumC F n v k := by
    rw [(hfr4.1 200 (by omega)).2]; simpa using s2
  have hn4 : c4.nreg 151 = n := hS4.hn
  -- the branch on the parent
  have hbr : ∃ c6 k6, Exec P W (.ifLtN 195 151
      (.seq (.instr (.copyN 193 195)) (.seq (opQueryCS B k) (.instr (.subR 200 200 196)))) .skip)
      c4 c6 k6 ∧ ∃ G6, LCTE B n F G6 c6 ∧ c6.rreg 200 = F.valc k v ∧
      MemFrame B n (mem c4) (mem c6) ∧ RegFr c4 c6 ∧
      k6 + 16400 * potL G6 ≤ 16400 * potL G4 + 147600 * Nat.log 2 n + 21104 := by
    by_cases hp : F.par v < n
    · have e5 := Exec.copyN (P := P) e4.wb_right 193 195
      obtain ⟨c6, k6, G6, e6, hS6, s6, hmf6, hfr6, -, hk6⟩ := opQueryC_exec (P := P) B n k
        e5.wb_right hW (hS4.updN 193 _ (by omega)) (by simp [p4]) hp
      have e7 := Exec.subR (P := P) e6.wb_right 200 200 196
      refine ⟨_, _, .ifLtN_true (by rw [p4, hn4]; exact hp) (.seq e5 (.seq e6 e7)), G6,
        hS6.updR 200 _, ?_, hmf6, ((regFr_updN (by omega) _ _).trans hfr6.regFr).trans
        (regFr_updR (by omega) _ _), by omega⟩
      have h200 : c6.rreg 200 = c4.rreg 200 := (hfr6.1 200 (by omega)).2
      simp only [upd_same]
      rw [h200, r200, s6, hS.pathSumC_par B n hc hW hvn hp k]
      ring
    · refine ⟨c4, 2, .ifLtN_false (by rw [p4, hn4]; exact hp) (.skip e4.wb_right), G4, hS4,
        ?_, MemFrame.refl B n _, RegFr.refl _, by omega⟩
      rw [r200, pathSumC_root hvn (by omega)]
  obtain ⟨c6, k6, e6, G6, hS6, s6, hmf6, hfr6, hk6⟩ := hbr
  have e7 := Exec.copyR (P := P) e6.wb_right 195 200
  refine ⟨_, 1 + (k2 + (1 + (k4 + (k6 + 1)))), .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e6 e7)))),
    G6, hS6.updR 195 _, by simpa using s6, (hmf2.trans B n hmf4).trans B n hmf6, ?_, by omega⟩
  exact (((((regFr_updN (by omega) c _).trans hfr2.regFr).trans (regFr_updR (by omega) _ _)).trans
    hfr4.regFr).trans hfr6).trans (regFr_updR (by omega) _ _)

/-- **Setting the value of a root** (channel `k`, `v = r ra`, for example an isolated node) to
the real `r rz`. The forest is `addPathC F n v (x - F.valc k v) k` (`addPathC_root`): in the
terms of `EOp`, the one operation `add v (x - val v)` (`add2` for `k = true`). -/
theorem regSet_exec (B n : ℕ) (k : Bool) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {ra rz v : ℕ}
    (hv : c.nreg ra = v) (hvn : v < n) (hp : F.par v = n) :
    ∃ c' k', Exec P W (regSetS B k ra rz) c c' k' ∧
      ∃ G', LCTE B n (F.setValC k v (c.rreg rz)) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' ∧
      k' + 16400 * potL G' ≤ 16400 * potL G + 295200 * Nat.log 2 n + 42203 := by
  have e1 := Exec.copyN (P := P) hc 193 ra
  have e2 := Exec.copyR (P := P) e1.wb_right 200 rz
  obtain ⟨c3, k3, G3, e3, hS3, s3, hmf3, hfr3, h193, hk3⟩ := opQueryC_exec (P := P) B n k
    e2.wb_right hW ((hS.updN 193 _ (by omega)).updR 200 _) (by simp [hv]) hvn
  have e4 := Exec.subR (P := P) e3.wb_right 200 200 196
  obtain ⟨c5, k5, G5, e5, hS5, hmf5, hfr5, -, -, hk5, -⟩ := opAddC_execE (P := P) B n k
    e4.wb_right hW (hS3.updR 200 _) (by simpa using h193) hvn
  have h200 : (({ c3 with rreg := upd c3.rreg 200 (c3.rreg 200 - c3.rreg 196) } : Config).rreg
      200) = c.rreg rz - F.valc k v := by
    simp only [upd_same]
    rw [(hfr3.1 200 (by omega)).2, s3, pathSumC_root hvn hp.ge]
    simp
  rw [h200, addPathC_root hvn hp.ge] at hS5
  exact ⟨c5, 1 + (1 + (k3 + (1 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))), G5, hS5,
    hmf3.trans B n hmf5, ((((regFr_updN (by omega) c _).trans (regFr_updR (by omega) _ _)).trans
    hfr3.regFr).trans (regFr_updR (by omega) _ _)).trans hfr5.regFr, by omega⟩

end

end DynTree

end PlanarFlow
