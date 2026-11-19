module

public import PlanarSeparator.Machine.TreeMath

/-!
# The division into light pieces on the machine

**`PlanarSeparator.Piece.divProg`**: the division `SepRoutine.divide` of the separator routine
of the square (`squareProg`) with an explicit worklist in memory (`dv`, `dFold` of
`PlanarSeparator/Machine/TreeMath.lean`).

* `SBase`: the state `SPre` without the vertex list; `SBase.toSPre`, `SBase.of_sDone`,
  `SBase.congr`.
* `whileLtN_abs`: a loop rule with an abstract state and a potential on it.
* The rounds: `dPopSum_exec` (the top frame and its weight), `dLeafCase` (the names of a leaf),
  `dSplitCase` (the copy to `1200`, `squareProg`, the two parts in place of the frame's list, the
  separator flags, the two new frames), `dBody_exec`.
* **`divLoop_exec`**: from a worklist state `DCore` (frames `(U i, k i)` with their sorted lists
  in a list area, a frame stack, flag and name arrays), the loop `divLoop` ends with no frame
  and the flags and names `dFold (sqSep hR hΔ) μ L` of the frames, within
  `DFr.cost` (the sum of `dcost` over the frames: per round `15 #U + 23` for a leaf and
  `40 #U + 51` plus the bound `sqC` of `squareProg` for a split) plus `2` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-! ### A loop rule with an abstract state -/

theorem whileLtN_abs {σ : Type*} {a b : ℕ} {body : Stmt} (I : σ → Config → Prop) (Φ : σ → ℕ)
    (hI : ∀ s c, I s c → WordsBounded W c)
    (hbody : ∀ s c, I s c → c.nreg a < c.nreg b →
      ∃ s' c' k, Exec P W body c c' k ∧ I s' c' ∧ Φ s' + k + 2 ≤ Φ s)
    {s : σ} {c : Config} (hc : I s c) :
    ∃ s' c' k, Exec P W (.whileLtN a b body) c c' k ∧ I s' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ s + 2 := by
  let J : Config → Prop := fun c => ∃ s, I s c
  let Ψ : Config → ℕ := fun c => sInf {n | ∃ s, I s c ∧ Φ s = n}
  have hmin : ∀ c, J c → ∃ s, I s c ∧ Φ s = Ψ c := fun c ⟨s, hs⟩ =>
    Nat.sInf_mem (s := {n | ∃ s, I s c ∧ Φ s = n}) ⟨Φ s, s, hs, rfl⟩
  have hle : ∀ c s, I s c → Ψ c ≤ Φ s := fun c s hs => Nat.sInf_le ⟨s, hs, rfl⟩
  obtain ⟨c', k, e, ⟨s', hs'⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := a)
    (b := b) (body := body) J Ψ (fun c ⟨s, hs⟩ => hI s c hs)
    (fun c hJ ht => by
      obtain ⟨s, hs, hΦ⟩ := hmin c hJ
      obtain ⟨s', c', k, e, hs', hk⟩ := hbody s c hs ht
      exact ⟨c', k, e, ⟨s', hs'⟩, by have := hle c' s' hs'; omega⟩) ⟨s, hc⟩
  exact ⟨s', c', k, e, hs', hn, by have := hle c s hc; omega⟩

/-! ### The state between calls of the separator of the square -/

variable (G) in
/-- **The state between calls of `squareProg`**: `SPre` without the vertex list, with a bound
`M` on the total weight. -/
structure SBase (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (Z W M : ℕ) (c : Config) :
    Prop where
  wb : WordsBounded W c
  one : c.nreg 1001 = 1
  r0 : c.nreg 0 = 0
  lU : c.nreg 1100 + N ≤ c.nreg 1102
  lC : c.nreg 1102 + N ≤ c.nreg 1103
  lQ : c.nreg 1103 + N ≤ c.nreg 1104
  lW : c.nreg 1104 + N + 1 ≤ c.nreg 1105
  lS : c.nreg 1105 + N + 1 ≤ c.nreg 1010
  l0 : c.nreg 1010 + N < c.nreg 1011
  l1 : c.nreg 1011 + nD G ≤ c.nreg 1012
  l2 : c.nreg 1012 + nD G ≤ c.nreg 1013
  l3 : c.nreg 1013 + nD G ≤ c.nreg 1014
  l4 : c.nreg 1014 + N ≤ c.nreg 1015
  l5 : c.nreg 1015 + N ≤ c.nreg 1017
  l6 : c.nreg 1017 + N ≤ c.nreg 1018
  l7 : c.nreg 1018 + nD G ≤ c.nreg 1019
  lA : c.nreg 1019 + N ≤ c.nreg 1200
  lB : c.nreg 1200 + N ≤ c.nreg 1202
  lF : c.nreg 1202 + N ≤ c.nreg 1203
  lV : c.nreg 1203 + N ≤ W
  ofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = gofs G v
  tl : ∀ g < nD G, c.nmem (c.nreg 1011 + g) = tlG G g
  rv : ∀ g < nD G, c.nmem (c.nreg 1012 + g) = rvG G g
  wt : ∀ v < N, c.nmem (c.nreg 1014 + v) = SepProg.wI w v
  cid : ∀ x < N, c.nmem (c.nreg 1102 + x) = 0
  cw : ∀ j ≤ N, c.nmem (c.nreg 1104 + j) = 0
  sn : ∀ j ≤ N, c.nmem (c.nreg 1105 + j) = 0
  ro : ∀ g < nD G, c.nmem (c.nreg 1013 + g) = roG G R g
  lab : ∀ x < N, c.nmem (c.nreg 1017 + x) = 0
  rk : ∀ g < nD G, c.nmem (c.nreg 1018 + g) = 0
  lZ : Z ≤ c.nreg 1100
  zero : ∀ a < Z, c.nmem a = 0
  zreg : ∀ r < 1000, c.nreg r = 0
  rz : ∀ r, r < 1000 ∨ r = 1060 ∨ r = 1001 → c.rreg r = 0
  rmz : ∀ a < Z, c.rmem a = 0
  nN : c.nreg 1204 = N
  fz : ∀ x < N, c.nmem (c.nreg 1202 + x) = 0
  sw : 6 * M ≤ W
  big : 2 * bB N (mI G univ) M ≤ Z
  wM : ∑ v, w v ≤ M

/-- `SBase` with the sorted list of `U` at `1200` and `#U` in `1201` is `SPre`. -/
theorem SBase.toSPre {R : Kasteleyn.RotationSystem G} {Z M : ℕ} {c : Config}
    (h : SBase G R w Z W M c) (uu : c.nreg 1201 = #U)
    (ul : ∀ l < #U, c.nmem (c.nreg 1200 + l) = lv U l) : SPre G R w U Z W c := by
  have hsum : ∑ v ∈ U, w v ≤ M := (sum_le_sum_of_subset (subset_univ U)).trans h.wM
  have hbig : 2 * bB #(closedNbhd G U) (mI G (closedNbhd G U)) (∑ v ∈ U, w v) ≤ Z :=
    le_trans (Nat.mul_le_mul_left 2 (bB_mono (card_le_N _) (mI_mono (subset_univ _)) hsum)) h.big
  exact ⟨h.wb, h.one, h.r0, h.lU, h.lC, h.lQ, h.lW, h.lS, h.l0, h.l1, h.l2, h.l3, h.l4, h.l5,
    h.l6, h.l7, h.lA, h.lB, h.lF, h.lV, h.ofs, h.tl, h.rv, h.wt, h.cid, h.cw, h.sn, h.ro, h.lab,
    h.rk, h.lZ, h.zero, h.zreg, h.rz, h.rmz, h.nN, uu, ul, h.fz, by have := h.sw; omega, hbig⟩

/-- After `squareProg`, `SBase` holds again. -/
theorem SBase.of_sDone {R : Kasteleyn.RotationSystem G} {Z M : ℕ} {c d : Config}
    {sq : Finset (Fin N) × Finset (Fin N) × Finset (Fin N)} (h : SBase G R w Z W M c)
    (hd : SDone G w U W sq c d) : SBase G R w Z W M d := by
  have := h.lU; have := h.lC; have := h.lQ; have := h.lW; have := h.lS; have := h.l0
  have := h.l1; have := h.l2; have := h.l3; have := h.l4; have := h.l5; have := h.l6
  have := h.l7; have := h.lA; have := h.lB; have := h.lF; have := h.lV; have := h.lZ
  have K : ∀ r, KeptS r → d.nreg r = c.nreg r := hd.regs
  have k1001 := K 1001 (by unfold KeptS; omega)
  have k1100 := K 1100 (by unfold KeptS; omega)
  have k1102 := K 1102 (by unfold KeptS; omega)
  have k1103 := K 1103 (by unfold KeptS; omega)
  have k1104 := K 1104 (by unfold KeptS; omega)
  have k1105 := K 1105 (by unfold KeptS; omega)
  have k1010 := K 1010 (by unfold KeptS; omega)
  have k1011 := K 1011 (by unfold KeptS; omega)
  have k1012 := K 1012 (by unfold KeptS; omega)
  have k1013 := K 1013 (by unfold KeptS; omega)
  have k1014 := K 1014 (by unfold KeptS; omega)
  have k1015 := K 1015 (by unfold KeptS; omega)
  have k1017 := K 1017 (by unfold KeptS; omega)
  have k1018 := K 1018 (by unfold KeptS; omega)
  have k1019 := K 1019 (by unfold KeptS; omega)
  have k1200 := K 1200 (by unfold KeptS; omega)
  have k1202 := K 1202 (by unfold KeptS; omega)
  have k1203 := K 1203 (by unfold KeptS; omega)
  have k1204 := K 1204 (by unfold KeptS; omega)
  have hm : ∀ a, (∀ v : Fin N, a ≠ c.nreg 1019 + v) →
      (a < c.nreg 1100 ∨ c.nreg 1100 + N ≤ a) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
      (a < c.nreg 1103 ∨ c.nreg 1103 + N ≤ a) → (a < c.nreg 1203 ∨ c.nreg 1203 + N ≤ a) →
      d.nmem a = c.nmem a := fun a h1 => hd.frame a (fun v _ => h1 v)
  have hz : ∀ a < Z, d.nmem a = c.nmem a := fun a ha =>
    hd.frame a (fun v _ => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨hd.wb, by rw [k1001]; exact h.one, by rw [K 0 (by unfold KeptS; omega)]; exact h.r0,
    by rw [k1100, k1102]; exact h.lU, by rw [k1102, k1103]; exact h.lC,
    by rw [k1103, k1104]; exact h.lQ, by rw [k1104, k1105]; exact h.lW,
    by rw [k1105, k1010]; exact h.lS, by rw [k1010, k1011]; exact h.l0,
    by rw [k1011, k1012]; exact h.l1, by rw [k1012, k1013]; exact h.l2,
    by rw [k1013, k1014]; exact h.l3, by rw [k1014, k1015]; exact h.l4,
    by rw [k1015, k1017]; exact h.l5, by rw [k1017, k1018]; exact h.l6,
    by rw [k1018, k1019]; exact h.l7, by rw [k1019, k1200]; exact h.lA,
    by rw [k1200, k1202]; exact h.lB, by rw [k1202, k1203]; exact h.lF,
    by rw [k1203]; exact h.lV, fun v hv => ?_, fun g hg => ?_, fun g hg => ?_, fun v hv => ?_,
    fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, fun g hg => ?_, fun x hx => ?_,
    fun g hg => ?_, by rw [k1100]; exact h.lZ, fun a ha => by rw [hz a ha]; exact h.zero a ha,
    fun r hr => by rw [K r (by unfold KeptS; omega)]; exact h.zreg r hr,
    fun r hr => by rw [hd.rr]; exact h.rz r hr, fun a ha => by rw [hd.rm]; exact h.rmz a ha,
    by rw [k1204]; exact h.nN, fun x hx => ?_, h.sw, h.big, h.wM⟩
  · rw [k1010, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.ofs v hv
  · rw [k1011, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.tl g hg
  · rw [k1012, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rv g hg
  · rw [k1014, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.wt v hv
  · rw [k1102, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.cid x hx
  · rw [k1104, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.cw j hj
  · rw [k1105, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.sn j hj
  · rw [k1013, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.ro g hg
  · rw [k1017, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.lab x hx
  · rw [k1018, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rk g hg
  · rw [k1202, hm _ (fun v => by have := v.2; omega) (by omega) (by omega) (by omega) (by omega)]; exact h.fz x hx

/-! ### The loops of a round

Registers: `1321` the start `s` of the frame's list, `1322` its length `n`, `1323` its fuel,
`1324` the weight, `1325` the counter, `1320`, `1326`–`1328` scratch, `1329`, `1330` the write
positions of the two parts, `1332` the constant `2`. -/

/-- The weight of the frame's list. -/
def dSumBody : Stmt := block [.addN 1320 1321 1325, .loadN 1326 1320, .addN 1320 1014 1326,
  .loadN 1327 1320, .addN 1324 1324 1327, .addN 1325 1325 1001]

def dSum : Stmt := .seq (block [.constN 1324 0, .constN 1325 0]) (.whileLtN 1325 1322 dSumBody)

theorem dSum_exec {d : Config} (hw : WordsBounded W d) {s aw : ℕ} (μ : Fin N → ℕ)
    (h01 : d.nreg 1001 = 1) (h21 : d.nreg 1321 = s) (h22 : d.nreg 1322 = #U)
    (h14 : d.nreg 1014 = aw) (hU : ∀ j < #U, d.nmem (s + j) = lv U j)
    (hwt : ∀ v < N, d.nmem (aw + v) = SepProg.wI μ v) (hS : ∑ v ∈ U, μ v + N ≤ W)
    (hs : s + N ≤ W) (haw : aw + N ≤ W) :
    ∃ d' k, Exec P W dSum d d' k ∧ WordsBounded W d' ∧ d'.nreg 1324 = ∑ v ∈ U, μ v ∧
      d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1320 → r ≠ 1324 → r ≠ 1325 → r ≠ 1326 → r ≠ 1327 → d'.nreg r = d.nreg r) ∧
      k ≤ 8 * #U + 4 := by
  have hUN := card_le_N U
  have hsum : ∀ j ≤ #U, ∑ l ∈ range j, SepProg.wI μ (lv U l) ≤ ∑ v ∈ U, μ v := fun j hj =>
    (sum_lv_le U _ hj).trans (sum_UN U μ).le
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1325 = j ∧
    d'.nreg 1322 = #U ∧ d'.nreg 1324 = ∑ l ∈ range j, SepProg.wI μ (lv U l) ∧
    d'.nmem = d.nmem ∧
    (∀ r, r ≠ 1320 → r ≠ 1324 → r ≠ 1325 → r ≠ 1326 → r ≠ 1327 → d'.nreg r = d.nreg r)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1324 0, .constN 1325 0])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h22,
        by config_simp; simp, rfl, fun r h1 h2 h3 _ _ => by simp [h2, h3]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1325) (rN := 1322)
    (N := #U) (lo := 0) (B := 6) (body := dSumBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h25, h22', h24, hm, hq⟩ := h
      have hx := lv_ltN U hi
      have r21 : d'.nreg 1321 = s := by rw [hq 1321 (by omega) (by omega) (by omega) (by omega)
        (by omega), h21]
      have r14 : d'.nreg 1014 = aw := by rw [hq 1014 (by omega) (by omega) (by omega)
        (by omega) (by omega), h14]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega), h01]
      have mU : d'.nmem (s + i) = lv U i := by rw [hm]; exact hU i hi
      have mw : d'.nmem (aw + lv U i) = SepProg.wI μ (lv U i) := by rw [hm]; exact hwt _ hx
      have hs1 := hsum (i + 1) hi
      rw [sum_range_succ] at hs1
      unfold dSumBody
      exec_block
      · rw [r21, h25]; omega
      · config_simp; rw [r14, r21, h25, mU]; omega
      · config_simp; rw [r14, r21, h25, mU, mw, h24]; omega
      · config_simp; rw [h25]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h25, r1], by config_simp; exact h22',
          by config_simp; rw [r14, r21, h25, mU, mw, h24, sum_range_succ], hm,
          fun r a b c' e f => ?_⟩, by omega⟩
        simp only [upd_apply, a, b, c', e, f, ite_false]; exact hq r a b c' e f)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h24₁, hm₁, hq₁⟩ := h₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, ?_, hm₁, hq₁, by omega⟩
  rw [h24₁, sum_lv_eq, sum_UN]

/-- The names of a leaf: every vertex of the list named by the first. -/
def dLeafBody : Stmt := block [.addN 1320 1321 1325, .loadN 1326 1320, .addN 1320 1311 1326,
  .storeN 1320 1328, .addN 1325 1325 1001]

def dLeafP : Stmt := .seq (block [.loadN 1328 1321, .constN 1325 0]) (.whileLtN 1325 1322 dLeafBody)

theorem dLeafP_exec {d : Config} (hw : WordsBounded W d) {s aP : ℕ}
    (h01 : d.nreg 1001 = 1) (h21 : d.nreg 1321 = s) (h22 : d.nreg 1322 = #U)
    (h11 : d.nreg 1311 = aP) (hU : ∀ j < #U, d.nmem (s + j) = lv U j)
    (hs : s + N ≤ aP ∨ aP + N ≤ s) (hs' : s + N ≤ W) (haP : aP + N ≤ W) :
    ∃ d' k, Exec P W dLeafP d d' k ∧ WordsBounded W d' ∧
      (∀ x < N, d'.nmem (aP + x) = if x ∈ UN U then lv U 0 else d.nmem (aP + x)) ∧
      (∀ a, (a < aP ∨ aP + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → d'.nreg r = d.nreg r) ∧
      k ≤ 7 * #U + 4 := by
  have hUN := card_le_N U
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1325 = j ∧
    d'.nreg 1322 = #U ∧ (0 < #U → d'.nreg 1328 = lv U 0) ∧
    (∀ x < N, d'.nmem (aP + x) = if ∃ l < j, lv U l = x then lv U 0 else d.nmem (aP + x)) ∧
    (∀ a, (a < aP ∨ aP + N ≤ a) → d'.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → d'.nreg r = d.nreg r)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.loadN 1328 1321, .constN 1325 0])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h22,
        fun h => by config_simp; rw [h21]; simpa using hU 0 h,
        fun x _ => by simp, fun _ _ => rfl, fun r h1 h2 _ h4 => by simp [h2, h4]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1325) (rN := 1322)
    (N := #U) (lo := 0) (B := 5) (body := dLeafBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h25, h22', h28, hF, hfr, hq⟩ := h
      have hx := lv_ltN U hi
      have r21 : d'.nreg 1321 = s := by rw [hq 1321 (by omega) (by omega) (by omega) (by omega),
        h21]
      have r11 : d'.nreg 1311 = aP := by rw [hq 1311 (by omega) (by omega) (by omega)
        (by omega), h11]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega),
        h01]
      have mU : d'.nmem (s + i) = lv U i := by
        rw [hfr _ (by omega)]; exact hU i hi
      unfold dLeafBody
      exec_block
      · rw [r21, h25]; omega
      · config_simp; rw [r11, r21, h25, mU]; omega
      · config_simp; rw [h25]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h25, r1], by config_simp; exact h22',
          fun h => by config_simp; exact h28 h, fun y hy => ?_, fun a ha => ?_,
          fun r a b c' e => ?_⟩, by omega⟩
        · simp only [Config.nmem_mk]
          rw [r11, r21, h25, mU, h28 (by omega)]
          simp only [upd_apply]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd ⟨i, Nat.lt_succ_self _, by omega⟩ h2
          · obtain ⟨j, hj, hjx⟩ := h2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · rw [hF y hy, iteT ⟨j, hj, hjx⟩]
            · omega
          · rw [hF y hy, iteF (fun ⟨j, hj, hjx⟩ => h2 ⟨j, by omega, hjx⟩)]
        · simp only [Config.nmem_mk]
          rw [r11, r21, h25, mU, upd_other _ _ _ (by have := lv_ltN U hi; omega)]
          exact hfr a ha
        · simp only [upd_apply, a, b, c', e, ite_false]; exact hq r a b c' e)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, -, hF₁, hfr₁, hq₁⟩ := h₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, fun x hx => ?_, hfr₁, hq₁, by omega⟩
  rw [hF₁ x hx]
  by_cases h : x ∈ UN U
  · rw [iteT ((lv_mem_iff U).2 h), iteT h]
  · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]

/-- The copy of the frame's list to the vertex list `1200` of `squareProg`. -/
def dCopyBody : Stmt := block [.addN 1320 1321 1325, .loadN 1326 1320, .addN 1320 1200 1325,
  .storeN 1320 1326, .addN 1325 1325 1001]

def dCopy : Stmt := .seq (block [.constN 1325 0, .copyN 1201 1322]) (.whileLtN 1325 1322 dCopyBody)

theorem dCopy_exec {d : Config} (hw : WordsBounded W d) {s a0 : ℕ}
    (h01 : d.nreg 1001 = 1) (h21 : d.nreg 1321 = s) (h22 : d.nreg 1322 = #U)
    (h00 : d.nreg 1200 = a0) (hU : ∀ j < #U, d.nmem (s + j) = lv U j)
    (hs : s + N ≤ a0 ∨ a0 + N ≤ s) (hs' : s + N ≤ W) (ha0 : a0 + N ≤ W) :
    ∃ d' k, Exec P W dCopy d d' k ∧ WordsBounded W d' ∧ d'.nreg 1201 = #U ∧
      (∀ l < #U, d'.nmem (a0 + l) = lv U l) ∧
      (∀ a, (a < a0 ∨ a0 + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1201 → r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → d'.nreg r = d.nreg r) ∧
      k ≤ 7 * #U + 4 := by
  have hUN := card_le_N U
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1325 = j ∧
    d'.nreg 1322 = #U ∧ d'.nreg 1201 = #U ∧ (∀ l < j, d'.nmem (a0 + l) = lv U l) ∧
    (∀ a, (a < a0 ∨ a0 + N ≤ a) → d'.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1201 → r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → d'.nreg r = d.nreg r)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1325 0, .copyN 1201 1322])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h22,
        by config_simp; exact h22, fun l hl => absurd hl (by omega), fun _ _ => rfl,
        fun r h1 _ h3 _ => by simp [h1, h3]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1325) (rN := 1322)
    (N := #U) (lo := 0) (B := 5) (body := dCopyBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h25, h22', h201, hF, hfr, hq⟩ := h
      have r21 : d'.nreg 1321 = s := by rw [hq 1321 (by omega) (by omega) (by omega) (by omega),
        h21]
      have r00 : d'.nreg 1200 = a0 := by rw [hq 1200 (by omega) (by omega) (by omega)
        (by omega), h00]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega),
        h01]
      have mU : d'.nmem (s + i) = lv U i := by
        rw [hfr _ (by omega)]; exact hU i hi
      unfold dCopyBody
      exec_block
      · rw [r21, h25]; omega
      · config_simp; rw [r00, h25]; omega
      · config_simp; rw [h25]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h25, r1], by config_simp; exact h22',
          by config_simp; exact h201, fun l hl => ?_, fun a ha => ?_,
          fun r a b c' e => ?_⟩, by omega⟩
        · simp only [Config.nmem_mk]
          rw [r00, r21, h25, mU]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hF l hl
          · rw [upd_same]
        · simp only [Config.nmem_mk]
          rw [r00, h25, upd_other _ _ _ (by omega)]
          exact hfr a ha
        · simp only [upd_apply, a, b, c', e, ite_false]; exact hq r a b c' e)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h201₁, hF₁, hfr₁, hq₁⟩ := h₁
  exact ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h201₁, hF₁, hfr₁, hq₁, by omega⟩

/-! ### Filtering the sorted list -/

/-- The members of `A` among the first `j` vertices of the sorted list of `U`. -/
def fT (U A : Finset (Fin N)) (j : ℕ) : Finset ℕ := (UN A).filter fun x => ∃ l < j, lv U l = x

theorem fT_eq_lt {U A : Finset (Fin N)} (hAU : A ⊆ U) {j : ℕ} (hj : j < #U) :
    fT U A j = (UN A).filter (· < lv U j) := by
  ext x
  simp only [fT, mem_filter, and_congr_right_iff]
  intro hx
  have hxU : x ∈ UN U := by
    obtain ⟨hxN, hm⟩ := mem_UN.1 hx; exact mem_UN.2 ⟨hxN, hAU hm⟩
  obtain ⟨l, hl, rfl⟩ := (lv_mem_iff U).2 hxU
  have hl' : l < (clist (ord N) U).length := by rw [length_clist_ord]; exact hl
  have hj' : j < (clist (ord N) U).length := by rw [length_clist_ord]; exact hj
  constructor
  · rintro ⟨l', hl'j, he⟩
    have := lv_inj' U (by omega) hl he
    subst this
    exact lv_inc U l' j hl'j hj'
  · intro hlt
    refine ⟨l, ?_, rfl⟩
    by_contra h
    rcases Nat.lt_or_ge j l with h' | h'
    · have := lv_inc U j l h' hl'; omega
    · obtain rfl : l = j := by omega
      omega

theorem fT_succ {U A : Finset (Fin N)} (hAU : A ⊆ U) {j : ℕ} (hj : j < #U) :
    #(fT U A (j + 1)) = #(fT U A j) + if lv U j ∈ UN A then 1 else 0 := by
  have e : fT U A (j + 1) = fT U A j ∪ (UN A).filter (· = lv U j) := by
    ext x
    simp only [fT, mem_filter, mem_union]
    constructor
    · rintro ⟨hx, l, hl, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact Or.inl ⟨hx, l, hl, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩
    · rintro (⟨hx, l, hl, rfl⟩ | ⟨hx, rfl⟩)
      · exact ⟨hx, l, by omega, rfl⟩
      · exact ⟨hx, j, by omega, rfl⟩
  rw [e, card_union_of_disjoint]
  · congr 1
    split_ifs with h
    · rw [card_eq_one]; refine ⟨lv U j, ?_⟩
      ext y; simp only [mem_filter, mem_singleton]
      exact ⟨fun h' => h'.2, by rintro rfl; exact ⟨h, rfl⟩⟩
    · rw [card_eq_zero, filter_eq_empty_iff]; rintro y hy rfl; exact h hy
  · rw [disjoint_left]
    rintro x hx1 hx2
    simp only [fT, mem_filter] at hx1 hx2
    obtain ⟨-, l, hl, rfl⟩ := hx1
    have := lv_inj' U (by omega) hj hx2.2
    omega

theorem fT_all {U A : Finset (Fin N)} (hAU : A ⊆ U) : #(fT U A #U) = #A := by
  rw [← card_UN A]
  congr 1
  refine filter_true_of_mem fun x hx => ?_
  have hxU : x ∈ UN U := by
    obtain ⟨hxN, hm⟩ := mem_UN.1 hx; exact mem_UN.2 ⟨hxN, hAU hm⟩
  exact (lv_mem_iff U).2 hxU

theorem fT_le {U A : Finset (Fin N)} (j : ℕ) : #(fT U A j) ≤ #A :=
  (card_filter_le _ _).trans (card_UN A).le

/-- The position of a member of `A` in the sorted list of `A`. -/
theorem lv_fT {U A : Finset (Fin N)} (hAU : A ⊆ U) {j : ℕ} (hj : j < #U)
    (h : lv U j ∈ UN A) : lv A #(fT U A j) = lv U j := by
  rw [fT_eq_lt hAU hj]; exact lv_card_filter A h

/-! ### The two parts -/

/-- The separator flags and the first part (marks `0` and `1`). -/
def dPassABody : Stmt :=
  .seq (block [.addN 1320 1200 1325, .loadN 1326 1320, .addN 1320 1019 1326, .loadN 1328 1320])
    (.seq (.ifLtN 1328 1001 (block [.addN 1320 1310 1326, .storeN 1320 1001])
      (.ifLtN 1328 1332 (block [.storeN 1329 1326, .addN 1329 1329 1001]) .skip))
      (.instr (.addN 1325 1325 1001)))

def dPassA : Stmt := .seq (block [.copyN 1329 1321, .constN 1325 0, .constN 1332 2])
  (.whileLtN 1325 1322 dPassABody)

theorem dPassA_exec {d : Config} (hw : WordsBounded W d) {S A B : Finset (Fin N)}
    {s a0 am aS : ℕ} (hU : S ∪ A ∪ B = U)
    (hmk : ∀ v ∈ U, (d.nmem (am + v) = 0 ↔ v ∈ S) ∧ (d.nmem (am + v) = 1 ↔ v ∈ A) ∧
      (d.nmem (am + v) = 2 ↔ v ∈ B))
    (h01 : d.nreg 1001 = 1) (h21 : d.nreg 1321 = s) (h22 : d.nreg 1322 = #U)
    (h00 : d.nreg 1200 = a0) (h19 : d.nreg 1019 = am) (h10 : d.nreg 1310 = aS)
    (hl : ∀ l < #U, d.nmem (a0 + l) = lv U l)
    (l1 : am + N ≤ a0) (l2 : a0 + N ≤ aS) (l3 : aS + N ≤ s) (l4 : s + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W dPassA d d' k ∧ WordsBounded W d' ∧ d'.nreg 1329 = s + #A ∧
      (∀ t < #A, d'.nmem (s + t) = lv A t) ∧
      (∀ x < N, d'.nmem (aS + x) = if x ∈ UN S then 1 else d.nmem (aS + x)) ∧
      (∀ a, (a < aS ∨ aS + N ≤ a) → (a < s ∨ s + #A ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → r ≠ 1329 → r ≠ 1332 →
        d'.nreg r = d.nreg r) ∧ d'.nreg 1332 = 2 ∧ k ≤ 14 * #U + 5 := by
  have hUN := card_le_N U
  have hAU : A ⊆ U := fun x hx => hU ▸ mem_union_left _ (mem_union_right _ hx)
  have hSU : S ⊆ U := fun x hx => hU ▸ mem_union_left _ (mem_union_left _ hx)
  have hAN := card_le_N A
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1325 = j ∧
    d'.nreg 1322 = #U ∧ d'.nreg 1332 = 2 ∧ d'.nreg 1329 = s + #(fT U A j) ∧
    (∀ t < #(fT U A j), d'.nmem (s + t) = lv A t) ∧
    (∀ x < N, d'.nmem (aS + x) = if x ∈ fT U S j then 1 else d.nmem (aS + x)) ∧
    (∀ a, (a < aS ∨ aS + N ≤ a) → (a < s ∨ s + #(fT U A j) ≤ a) → d'.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → r ≠ 1329 → r ≠ 1332 →
      d'.nreg r = d.nreg r)
  have fT0 : ∀ X : Finset (Fin N), fT U X 0 = ∅ := fun X => by
    ext x; simp [fT]
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.copyN 1329 1321, .constN 1325 0,
      .constN 1332 2]) d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 3 := by
    exec_block
    · omega
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h22, by config_simp,
        by config_simp; rw [h21, fT0]; rfl, fun t ht => by rw [fT0] at ht; simp at ht,
        fun x _ => by rw [fT0]; simp, fun _ _ _ => rfl,
        fun r _ h2 _ _ h5 h6 => by simp [h2, h5, h6]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1325) (rN := 1322)
    (N := #U) (lo := 0) (B := 12) (body := dPassABody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h25, h22', h32, h29, hA, hS, hfr, hq⟩ := h
      have hx := lv_ltN U hi
      have hxU := lv_mem_UN U hi
      obtain ⟨hxN, hxU'⟩ := mem_UN.1 hxU
      have r00 : d'.nreg 1200 = a0 := by rw [hq 1200 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), h00]
      have r19 : d'.nreg 1019 = am := by rw [hq 1019 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), h19]
      have r10 : d'.nreg 1310 = aS := by rw [hq 1310 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), h10]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h01]
      have ml : d'.nmem (a0 + i) = lv U i := by
        rw [hfr _ (by omega) (by omega)]; exact hl i hi
      have mm : d'.nmem (am + lv U i) = d.nmem (am + lv U i) := hfr _ (by omega) (by omega)
      obtain ⟨q0, q1, q2⟩ := hmk _ hxU'
      have hcA := fT_succ hAU hi
      have hcS := fT_succ hSU hi
      have hle := fT_le (U := U) (A := A) (i + 1)
      refine spec_seq ?_
      exec_block
      · rw [r00, h25]; omega
      · config_simp; rw [r19, r00, h25, ml]; omega
      · refine spec_seq ?_
        by_cases hS0 : lv U i ∈ UN S
        · have hm0 : d.nmem (am + lv U i) = 0 := q0.2 (val_mem_UN.1 hS0)
          have hA0 : lv U i ∉ UN A := fun h => by
            have : d.nmem (am + lv U i) = 1 := q1.2 (val_mem_UN.1 h); omega
          refine spec_ifLtN_true (by config_simp; rw [r19, r00, h25, ml, mm, hm0, r1]; omega) ?_
          exec_block
          · config_simp; rw [r10, r00, h25, ml]; omega
          · refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h25]; omega))
              fun hw₂ => ?_
            refine ⟨⟨hw₂, by config_simp; rw [h25, r1], by config_simp; exact h22',
              by config_simp; exact h32, by config_simp; rw [h29, hcA, iteF hA0]; rfl,
              fun t ht => ?_, fun y hy => ?_, fun a ha1 ha2 => ?_,
              fun r a b c' e f g => ?_⟩, by omega⟩
            · rw [hcA, iteF hA0, Nat.add_zero] at ht
              simp only [Config.nmem_mk]
              rw [r10, r00, h25, ml, upd_other _ _ _ (by omega)]; exact hA t ht
            · simp only [Config.nmem_mk]
              rw [r10, r00, h25, ml, r1]
              by_cases hyx : y = lv U i
              · subst hyx
                rw [upd_same, iteT]
                simp only [fT, mem_filter]; exact ⟨hS0, i, by omega, rfl⟩
              · rw [upd_other _ _ _ (by omega), hS y hy]
                congr 1
                simp only [fT, mem_filter, eq_iff_iff]
                constructor
                · rintro ⟨h1, l, hl, rfl⟩; exact ⟨h1, l, by omega, rfl⟩
                · rintro ⟨h1, l, hl, rfl⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
                  · exact ⟨h1, l, hl, rfl⟩
                  · exact absurd rfl hyx
            · simp only [Config.nmem_mk]
              rw [r10, r00, h25, ml, upd_other _ _ _ (by omega)]
              exact hfr a ha1 (by rw [hcA, iteF hA0, Nat.add_zero] at ha2; exact ha2)
            · simp only [upd_apply, a, b, c', e, f, g, ite_false]; exact hq r a b c' e f g
        · by_cases hA1 : lv U i ∈ UN A
          · have hm1 : d.nmem (am + lv U i) = 1 := q1.2 (val_mem_UN.1 hA1)
            refine spec_ifLtN_false (by config_simp; rw [r19, r00, h25, ml, mm, hm1, r1]; omega) ?_
            refine spec_ifLtN_true (by config_simp; rw [r19, r00, h25, ml, mm, hm1, h32]; omega) ?_
            exec_block
            · config_simp; rw [h29, r1]; rw [hcA, iteT hA1] at hle; omega
            · refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h25]; omega))
                fun hw₂ => ?_
              refine ⟨⟨hw₂, by config_simp; rw [h25, r1], by config_simp; exact h22',
                by config_simp; exact h32, by config_simp; rw [h29, r1, hcA, iteT hA1]; omega,
                fun t ht => ?_, fun y hy => ?_, fun a ha1 ha2 => ?_,
                fun r a b c' e f g => ?_⟩, by omega⟩
              · rw [hcA, iteT hA1] at ht
                simp only [Config.nmem_mk]
                rw [h29]
                rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
                · rw [upd_other _ _ _ (by omega)]; exact hA t ht
                · rw [upd_same, r00, h25, ml, lv_fT hAU hi hA1]
              · simp only [Config.nmem_mk]
                rw [h29, upd_other _ _ _ (by omega), hS y hy]
                congr 1
                simp only [fT, mem_filter, eq_iff_iff]
                constructor
                · rintro ⟨h1, l, hl, rfl⟩; exact ⟨h1, l, by omega, rfl⟩
                · rintro ⟨h1, l, hl, rfl⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
                  · exact ⟨h1, l, hl, rfl⟩
                  · exact absurd h1 hS0
              · simp only [Config.nmem_mk]
                rw [hcA, iteT hA1] at ha2
                rw [h29, upd_other _ _ _ (by omega)]
                exact hfr a ha1 (by omega)
              · simp only [upd_apply, a, b, c', e, f, g, ite_false]; exact hq r a b c' e f g
          · have hm2 : d.nmem (am + lv U i) = 2 := by
              have : (⟨lv U i, hxN⟩ : Fin N) ∈ S ∪ A ∪ B := by rw [hU]; exact hxU'
              simp only [mem_union] at this
              rcases this with (h | h) | h
              · exact absurd (val_mem_UN.2 h) hS0
              · exact absurd (val_mem_UN.2 h) hA1
              · exact q2.2 h
            refine spec_ifLtN_false (by config_simp; rw [r19, r00, h25, ml, mm, hm2, r1]; omega) ?_
            refine spec_ifLtN_false (by config_simp; rw [r19, r00, h25, ml, mm, hm2, h32]; omega) ?_
            refine spec_skip ‹_› ?_
            refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h25]; omega))
              fun hw₂ => ?_
            refine ⟨⟨hw₂, by config_simp; rw [h25, r1], by config_simp; exact h22',
              by config_simp; exact h32, by config_simp; rw [h29, hcA, iteF hA1]; rfl,
              fun t ht => ?_, fun y hy => ?_, fun a ha1 ha2 => ?_,
              fun r a b c' e f g => ?_⟩, by omega⟩
            · rw [hcA, iteF hA1, Nat.add_zero] at ht; exact hA t ht
            · rw [hS y hy]
              congr 1
              simp only [fT, mem_filter, eq_iff_iff]
              constructor
              · rintro ⟨h1, l, hl, rfl⟩; exact ⟨h1, l, by omega, rfl⟩
              · rintro ⟨h1, l, hl, rfl⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
                · exact ⟨h1, l, hl, rfl⟩
                · exact absurd h1 hS0
            · rw [hcA, iteF hA1, Nat.add_zero] at ha2; exact hfr a ha1 ha2
            · simp only [upd_apply, a, b, c', e, f, g, ite_false]; exact hq r a b c' e f g)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h32₁, h29₁, hA₁, hS₁, hfr₁, hq₁⟩ := h₁
  rw [fT_all hAU] at h29₁ hA₁ hfr₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h29₁, hA₁, fun x hx => ?_, hfr₁, hq₁, h32₁, by omega⟩
  rw [hS₁ x hx]
  congr 1
  simp only [fT, mem_filter, eq_iff_iff, and_iff_left_iff_imp]
  intro h
  have hxU : x ∈ UN U := by
    obtain ⟨hxN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hxN, hSU hm⟩
  exact (lv_mem_iff U).2 hxU

/-- The second part (marks `2`). -/
def dPassBBody : Stmt :=
  .seq (block [.addN 1320 1200 1325, .loadN 1326 1320, .addN 1320 1019 1326, .loadN 1328 1320])
    (.seq (.ifLtN 1001 1328 (block [.storeN 1330 1326, .addN 1330 1330 1001]) .skip)
      (.instr (.addN 1325 1325 1001)))

def dPassB : Stmt := .seq (block [.copyN 1330 1329, .constN 1325 0])
  (.whileLtN 1325 1322 dPassBBody)

theorem dPassB_exec {d : Config} (hw : WordsBounded W d) {S A B : Finset (Fin N)}
    {p0 a0 am : ℕ} (hU : S ∪ A ∪ B = U)
    (hmk : ∀ v ∈ U, (d.nmem (am + v) = 0 ↔ v ∈ S) ∧ (d.nmem (am + v) = 1 ↔ v ∈ A) ∧
      (d.nmem (am + v) = 2 ↔ v ∈ B))
    (h01 : d.nreg 1001 = 1) (h29 : d.nreg 1329 = p0) (h22 : d.nreg 1322 = #U)
    (h00 : d.nreg 1200 = a0) (h19 : d.nreg 1019 = am)
    (hl : ∀ l < #U, d.nmem (a0 + l) = lv U l)
    (l1 : am + N ≤ a0) (l2 : a0 + N ≤ p0) (l3 : p0 + #B ≤ W) (hNW : N ≤ W) :
    ∃ d' k, Exec P W dPassB d d' k ∧ WordsBounded W d' ∧ d'.nreg 1330 = p0 + #B ∧
      (∀ t < #B, d'.nmem (p0 + t) = lv B t) ∧
      (∀ a, (a < p0 ∨ p0 + #B ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → r ≠ 1330 → d'.nreg r = d.nreg r) ∧
      k ≤ 11 * #U + 4 := by
  have hUN := card_le_N U
  have hBU : B ⊆ U := fun x hx => hU ▸ mem_union_right _ hx
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1325 = j ∧
    d'.nreg 1322 = #U ∧ d'.nreg 1330 = p0 + #(fT U B j) ∧
    (∀ t < #(fT U B j), d'.nmem (p0 + t) = lv B t) ∧
    (∀ a, (a < p0 ∨ p0 + #(fT U B j) ≤ a) → d'.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → r ≠ 1330 → d'.nreg r = d.nreg r)
  have fT0 : fT U B 0 = ∅ := by ext x; simp [fT]
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.copyN 1330 1329, .constN 1325 0])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h22,
        by config_simp; rw [h29, fT0]; rfl, fun t ht => by rw [fT0] at ht; simp at ht,
        fun _ _ => rfl, fun r _ h2 _ _ h5 => by simp [h2, h5]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1325) (rN := 1322)
    (N := #U) (lo := 0) (B := 9) (body := dPassBBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h25, h22', h30, hB, hfr, hq⟩ := h
      have hx := lv_ltN U hi
      have hxU := lv_mem_UN U hi
      obtain ⟨hxN, hxU'⟩ := mem_UN.1 hxU
      have r00 : d'.nreg 1200 = a0 := by rw [hq 1200 (by omega) (by omega) (by omega)
        (by omega) (by omega), h00]
      have r19 : d'.nreg 1019 = am := by rw [hq 1019 (by omega) (by omega) (by omega)
        (by omega) (by omega), h19]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega), h01]
      have ml : d'.nmem (a0 + i) = lv U i := by
        rw [hfr _ (by omega)]; exact hl i hi
      have mm : d'.nmem (am + lv U i) = d.nmem (am + lv U i) := hfr _ (by omega)
      obtain ⟨q0, q1, q2⟩ := hmk _ hxU'
      have hcB := fT_succ hBU hi
      have hle := fT_le (U := U) (A := B) (i + 1)
      refine spec_seq ?_
      exec_block
      · rw [r00, h25]; omega
      · config_simp; rw [r19, r00, h25, ml]; omega
      · refine spec_seq ?_
        by_cases hB1 : lv U i ∈ UN B
        · have hm2 : d.nmem (am + lv U i) = 2 := q2.2 (val_mem_UN.1 hB1)
          refine spec_ifLtN_true (by config_simp; rw [r19, r00, h25, ml, mm, hm2, r1]; omega) ?_
          exec_block
          · config_simp; rw [h30, r1]; rw [hcB, iteT hB1] at hle; omega
          · refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h25]; omega))
              fun hw₂ => ?_
            refine ⟨⟨hw₂, by config_simp; rw [h25, r1], by config_simp; exact h22',
              by config_simp; rw [h30, r1, hcB, iteT hB1]; omega,
              fun t ht => ?_, fun a ha => ?_, fun r a b c' e f => ?_⟩, by omega⟩
            · rw [hcB, iteT hB1] at ht
              simp only [Config.nmem_mk]
              rw [h30]
              rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
              · rw [upd_other _ _ _ (by omega)]; exact hB t ht
              · rw [upd_same, r00, h25, ml, lv_fT hBU hi hB1]
            · simp only [Config.nmem_mk]
              rw [hcB, iteT hB1] at ha
              rw [h30, upd_other _ _ _ (by omega)]
              exact hfr a (by omega)
            · simp only [upd_apply, a, b, c', e, f, ite_false]; exact hq r a b c' e f
        · have hm2 : ¬ 1 < d.nmem (am + lv U i) := by
            intro h
            have : (⟨lv U i, hxN⟩ : Fin N) ∈ S ∪ A ∪ B := by rw [hU]; exact hxU'
            simp only [mem_union] at this
            rcases this with (h' | h') | h'
            · have : d.nmem (am + lv U i) = 0 := q0.2 h'; omega
            · have : d.nmem (am + lv U i) = 1 := q1.2 h'; omega
            · exact hB1 (val_mem_UN.2 h')
          refine spec_ifLtN_false (by config_simp; rw [r19, r00, h25, ml, mm, r1]; omega) ?_
          refine spec_skip ‹_› ?_
          refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h25]; omega))
            fun hw₂ => ?_
          refine ⟨⟨hw₂, by config_simp; rw [h25, r1], by config_simp; exact h22',
            by config_simp; rw [h30, hcB, iteF hB1]; rfl,
            fun t ht => ?_, fun a ha => ?_, fun r a b c' e f => ?_⟩, by omega⟩
          · rw [hcB, iteF hB1, Nat.add_zero] at ht; exact hB t ht
          · rw [hcB, iteF hB1, Nat.add_zero] at ha; exact hfr a ha
          · simp only [upd_apply, a, b, c', e, f, ite_false]; exact hq r a b c' e f)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h30₁, hB₁, hfr₁, hq₁⟩ := h₁
  rw [fT_all hBU] at h30₁ hB₁ hfr₁
  exact ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h30₁, hB₁, hfr₁, hq₁, by omega⟩

/-- `SBase` survives changes of the free registers and of the memory at `1200` and above the
flag array. -/
theorem SBase.congr {R : Kasteleyn.RotationSystem G} {Z M : ℕ} {c d : Config}
    (h : SBase G R w Z W M c) (hw : WordsBounded W d)
    (hr : ∀ r, KeptS r → r ≠ 1201 → d.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg 1200 ∨ (c.nreg 1202 ≤ a ∧ a < c.nreg 1203) → d.nmem a = c.nmem a)
    (hrr : d.rreg = c.rreg) (hrm : d.rmem = c.rmem) : SBase G R w Z W M d := by
  have := h.lU; have := h.lC; have := h.lQ; have := h.lW; have := h.lS; have := h.l0
  have := h.l1; have := h.l2; have := h.l3; have := h.l4; have := h.l5; have := h.l6
  have := h.l7; have := h.lA; have := h.lB; have := h.lF; have := h.lV; have := h.lZ
  have K : ∀ r, KeptS r → r ≠ 1201 → d.nreg r = c.nreg r := hr
  have k1001 := K 1001 (by unfold KeptS; omega) (by omega)
  have k1100 := K 1100 (by unfold KeptS; omega) (by omega)
  have k1102 := K 1102 (by unfold KeptS; omega) (by omega)
  have k1103 := K 1103 (by unfold KeptS; omega) (by omega)
  have k1104 := K 1104 (by unfold KeptS; omega) (by omega)
  have k1105 := K 1105 (by unfold KeptS; omega) (by omega)
  have k1010 := K 1010 (by unfold KeptS; omega) (by omega)
  have k1011 := K 1011 (by unfold KeptS; omega) (by omega)
  have k1012 := K 1012 (by unfold KeptS; omega) (by omega)
  have k1013 := K 1013 (by unfold KeptS; omega) (by omega)
  have k1014 := K 1014 (by unfold KeptS; omega) (by omega)
  have k1015 := K 1015 (by unfold KeptS; omega) (by omega)
  have k1017 := K 1017 (by unfold KeptS; omega) (by omega)
  have k1018 := K 1018 (by unfold KeptS; omega) (by omega)
  have k1019 := K 1019 (by unfold KeptS; omega) (by omega)
  have k1200 := K 1200 (by unfold KeptS; omega) (by omega)
  have k1202 := K 1202 (by unfold KeptS; omega) (by omega)
  have k1203 := K 1203 (by unfold KeptS; omega) (by omega)
  have k1204 := K 1204 (by unfold KeptS; omega) (by omega)
  refine ⟨hw, by rw [k1001]; exact h.one, (by rw [K 0 (by unfold KeptS; omega) (by omega)]; exact h.r0),
    by rw [k1100, k1102]; exact h.lU, by rw [k1102, k1103]; exact h.lC,
    by rw [k1103, k1104]; exact h.lQ, by rw [k1104, k1105]; exact h.lW,
    by rw [k1105, k1010]; exact h.lS, by rw [k1010, k1011]; exact h.l0,
    by rw [k1011, k1012]; exact h.l1, by rw [k1012, k1013]; exact h.l2,
    by rw [k1013, k1014]; exact h.l3, by rw [k1014, k1015]; exact h.l4,
    by rw [k1015, k1017]; exact h.l5, by rw [k1017, k1018]; exact h.l6,
    by rw [k1018, k1019]; exact h.l7, by rw [k1019, k1200]; exact h.lA,
    by rw [k1200, k1202]; exact h.lB, by rw [k1202, k1203]; exact h.lF,
    by rw [k1203]; exact h.lV, fun v hv => ?_, fun g hg => ?_, fun g hg => ?_, fun v hv => ?_,
    fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, fun g hg => ?_, fun x hx => ?_,
    fun g hg => ?_, by rw [k1100]; exact h.lZ,
    fun a ha => by rw [hm a (Or.inl (by omega))]; exact h.zero a ha,
    fun r hr => by rw [K r (by unfold KeptS; omega) (by omega)]; exact h.zreg r hr,
    fun r hr => by rw [hrr]; exact h.rz r hr, fun a ha => by rw [hrm]; exact h.rmz a ha,
    by rw [k1204]; exact h.nN, fun x hx => ?_, h.sw, h.big, h.wM⟩
  · rw [k1010, hm _ (Or.inl (by omega))]; exact h.ofs v hv
  · rw [k1011, hm _ (Or.inl (by omega))]; exact h.tl g hg
  · rw [k1012, hm _ (Or.inl (by omega))]; exact h.rv g hg
  · rw [k1014, hm _ (Or.inl (by omega))]; exact h.wt v hv
  · rw [k1102, hm _ (Or.inl (by omega))]; exact h.cid x hx
  · rw [k1104, hm _ (Or.inl (by omega))]; exact h.cw j hj
  · rw [k1105, hm _ (Or.inl (by omega))]; exact h.sn j hj
  · rw [k1013, hm _ (Or.inl (by omega))]; exact h.ro g hg
  · rw [k1017, hm _ (Or.inl (by omega))]; exact h.lab x hx
  · rw [k1018, hm _ (Or.inl (by omega))]; exact h.rk g hg
  · rw [k1202, hm _ (Or.inr ⟨by omega, by omega⟩)]; exact h.fz x hx

/-! ### The worklist loop -/

/-- The abstract worklist: `m` frames, frame `i` with vertex set `U i`, fuel `k i` and its
sorted list at `s i`; and the state of the division. -/
structure DFr (N : ℕ) where
  /-- The number of frames. -/
  m : ℕ
  /-- The vertex sets. -/
  U : ℕ → Finset (Fin N)
  /-- The fuels. -/
  k : ℕ → ℕ
  /-- The positions of the lists. -/
  s : ℕ → ℕ
  /-- The flags and names. -/
  st : DSt

/-- The frames from the top. -/
def DFr.flist (a : DFr N) : List (Finset (Fin N) × ℕ) :=
  (List.range a.m).reverse.map fun i => (a.U i, a.k i)

/-- The cost of the rounds from a frame, for the weights `μ` and the bound `L`. -/
def dcost (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L Δ : ℕ) : ℕ → Finset (Fin N) → ℕ
  | 0, U => 15 * #U + 23
  | k + 1, U =>
    if ∑ v ∈ U, μ v ≤ L then 15 * #U + 23
    else 40 * #U + 51 + (15 * N + ((Δ + 1) * (6 * Δ ^ 2 + 3415 * Δ + 2411) + 22 * Δ + 43) * #U +
        12 * ∑ v ∈ U, μ v + 5420) +
      dcost sep μ L Δ k (sep U μ).2.1 + dcost sep μ L Δ k (sep U μ).2.2

/-- The registers kept by the worklist loop. -/
def DKept (r : ℕ) : Prop := (KeptS r ∧ r ≠ 1201) ∨ (1310 ≤ r ∧ r ≤ 1314) ∨ 1333 ≤ r

variable (N) in
/-- The addresses kept by the worklist loop (from the state `c0` at the start). -/
def DOut (c0 : Config) (aF k0 a : ℕ) : Prop :=
  (a < c0.nreg 1100 ∨ c0.nreg 1100 + N ≤ a) ∧ (a < c0.nreg 1015 ∨ c0.nreg 1015 + N ≤ a) ∧
    (a < c0.nreg 1103 ∨ c0.nreg 1103 + N ≤ a) ∧ (a < c0.nreg 1019 ∨ c0.nreg 1019 + N ≤ a) ∧
    (a < c0.nreg 1200 ∨ c0.nreg 1200 + N ≤ a) ∧ (a < c0.nreg 1203 ∨ aF + 3 * (k0 + 1) ≤ a)

variable (G) in
/-- **The worklist state** (without the frame count and the target): `SBase`, the bases of the
flag array `aS`, the name array `aP`, the list area `aV` and the frame stack `aF`, the bound `L`
in `1314`, the frames and the arrays, and the frame relative to the start `c0`. -/
structure DCore (R : Kasteleyn.RotationSystem G) (μ : Fin N → ℕ) (Z W M aS aP aV aF L k0 : ℕ)
    (c0 : Config) (a : DFr N) (c : Config) : Prop where
  base : SBase G R μ Z W M c
  rS : c.nreg 1310 = aS
  rP : c.nreg 1311 = aP
  rV : c.nreg 1312 = aV
  rF : c.nreg 1313 = aF
  rL : c.nreg 1314 = L
  lay1 : c0.nreg 1203 + N ≤ aS
  lay2 : aS + N ≤ aP
  lay3 : aP + N ≤ aV
  lay4 : aV + N ≤ aF
  lay5 : aF + 3 * (k0 + 1) + N ≤ W
  hMN : M + N ≤ W
  fr : ∀ i < a.m, c.nmem (aF + 3 * i) = a.s i ∧ c.nmem (aF + 3 * i + 1) = #(a.U i) ∧
    c.nmem (aF + 3 * i + 2) = a.k i ∧ (∀ j < #(a.U i), c.nmem (a.s i + j) = lv (a.U i) j) ∧
    aV ≤ a.s i ∧ a.s i + #(a.U i) ≤ aV + N ∧ a.k i + i ≤ k0
  ord : ∀ i j, i < j → j < a.m → a.s j + #(a.U j) ≤ a.s i
  arr : ∀ x < N, c.nmem (aS + x) = a.st.sf x ∧ c.nmem (aP + x) = a.st.pid x
  keep : ∀ r, DKept r → c.nreg r = c0.nreg r
  mem : ∀ a, DOut N c0 aF k0 a → c.nmem a = c0.nmem a
  out : c.output = c0.output

/-- The removal of the top frame. -/
def dPop : Stmt := block [.subN 1315 1315 1001, .addN 1320 1315 1315, .addN 1320 1320 1315,
  .addN 1320 1320 1313, .loadN 1321 1320, .addN 1320 1320 1001, .loadN 1322 1320,
  .addN 1320 1320 1001, .loadN 1323 1320]

theorem dPopSum_exec {R : Kasteleyn.RotationSystem G} {μ : Fin N → ℕ}
    {Z M aS aP aV aF L k0 : ℕ} {c0 : Config} {a : DFr N} {c : Config}
    (h : DCore G R μ Z W M aS aP aV aF L k0 c0 a c) (hm : c.nreg 1315 = a.m) (h0 : 0 < a.m) :
    ∃ c₂ k, Exec P W (.seq dPop dSum) c c₂ k ∧ k ≤ 8 * #(a.U (a.m - 1)) + 13 ∧
      DCore G R μ Z W M aS aP aV aF L k0 c0 a c₂ ∧ c₂.nreg 1315 = a.m - 1 ∧
      c₂.nreg 1321 = a.s (a.m - 1) ∧ c₂.nreg 1322 = #(a.U (a.m - 1)) ∧
      c₂.nreg 1323 = a.k (a.m - 1) ∧ c₂.nreg 1324 = ∑ v ∈ a.U (a.m - 1), μ v := by
  have hb := h.base
  have := h.lay1; have := h.lay2; have := h.lay3; have := h.lay4; have := h.lay5
  have := h.hMN; have := hb.lV; have := hb.l4; have := hb.l5; have := hb.l6; have := hb.l7
  have := hb.lA; have := hb.lB; have := hb.lF
  obtain ⟨f0, f1, f2, fl, fs1, fs2, fk⟩ := h.fr (a.m - 1) (by omega)
  have hUN := card_le_N (a.U (a.m - 1))
  have hw := hb.wb
  obtain ⟨c₁, k₁, e₁, hk₁, h₁⟩ : ∃ c₁ k₁, Exec P W dPop c c₁ k₁ ∧ k₁ = 9 ∧
      (WordsBounded W c₁ ∧ c₁.nreg 1315 = a.m - 1 ∧ c₁.nreg 1321 = a.s (a.m - 1) ∧
      c₁.nreg 1322 = #(a.U (a.m - 1)) ∧ c₁.nreg 1323 = a.k (a.m - 1) ∧ c₁.nmem = c.nmem ∧
      ∀ r, r ≠ 1315 → r ≠ 1320 → r ≠ 1321 → r ≠ 1322 → r ≠ 1323 → c₁.nreg r = c.nreg r) := by
    unfold dPop
    exec_block
    · config_simp; rw [hm, hb.one]; omega
    · config_simp; rw [hm, hb.one]; omega
    · config_simp; rw [hm, hb.one, h.rF]; omega
    · config_simp; rw [hm, hb.one, h.rF]; omega
    · config_simp; rw [hm, hb.one, h.rF]; omega
    · refine ⟨rfl, ‹_›, by config_simp; rw [hm, hb.one], ?_, ?_, ?_, rfl, ?_⟩
      · config_simp; rw [hm, hb.one, h.rF]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + aF = aF + 3 * (a.m - 1) by omega]; exact f0
      · config_simp; rw [hm, hb.one, h.rF]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + aF + 1 = aF + 3 * (a.m - 1) + 1 by omega]
        exact f1
      · config_simp; rw [hm, hb.one, h.rF]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + aF + 1 + 1 = aF + 3 * (a.m - 1) + 2 by
          omega]
        exact f2
      · intro r h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
  obtain ⟨hw₁, m₁, s₁, n₁, k₁', nm₁, q₁⟩ := h₁
  have hwt : ∀ v < N, c₁.nmem (c₁.nreg 1014 + v) = SepProg.wI μ v := fun v hv => by
    rw [nm₁, q₁ 1014 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hb.wt v hv
  have hsumM : ∑ v ∈ a.U (a.m - 1), μ v ≤ M :=
    (sum_le_sum_of_subset (subset_univ _)).trans hb.wM
  obtain ⟨c₂, k₂, e₂, hw₂, h24, nm₂, q₂, hk₂⟩ := dSum_exec (P := P) hw₁ μ
    (by rw [q₁ 1001 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hb.one)
    s₁ n₁ rfl (fun j hj => by rw [nm₁]; exact fl j hj) hwt (by omega) (by omega)
    (by rw [q₁ 1014 (by omega) (by omega) (by omega) (by omega) (by omega)]; omega)
  have Q : ∀ r, r ≠ 1315 → r ≠ 1320 → r ≠ 1321 → r ≠ 1322 → r ≠ 1323 → r ≠ 1324 → r ≠ 1325 →
      r ≠ 1326 → r ≠ 1327 → c₂.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 => by
    rw [q₂ r a2 a6 a7 a8 a9, q₁ r a1 a2 a3 a4 a5]
  have nm : c₂.nmem = c.nmem := by rw [nm₂, nm₁]
  have rr : c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem :=
    Exec.real_of_noReal (Exec.seq e₁ e₂ : Exec P W (.seq dPop dSum) c c₂ (k₁ + k₂)) (by decide)
  have ou : c₂.output = c.output :=
    Exec.output_of_ou (Exec.seq e₁ e₂ : Exec P W (.seq dPop dSum) c c₂ (k₁ + k₂)) (by decide)
  have QQ : ∀ r, 1310 ≤ r → r ≤ 1314 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    Q r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hD : DCore G R μ Z W M aS aP aV aF L k0 c0 a c₂ :=
    { base := hb.congr hw₂ (fun r hr _ => by
        unfold KeptS at hr
        exact Q r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)) (fun a _ => by rw [nm]) rr.1 rr.2
      rS := by rw [QQ 1310 (by omega) (by omega)]; exact h.rS
      rP := by rw [QQ 1311 (by omega) (by omega)]; exact h.rP
      rV := by rw [QQ 1312 (by omega) (by omega)]; exact h.rV
      rF := by rw [QQ 1313 (by omega) (by omega)]; exact h.rF
      rL := by rw [QQ 1314 (by omega) (by omega)]; exact h.rL
      lay1 := h.lay1, lay2 := h.lay2, lay3 := h.lay3, lay4 := h.lay4, lay5 := h.lay5
      hMN := h.hMN
      fr := fun i hi => by rw [nm]; exact h.fr i hi
      ord := h.ord
      arr := fun x hx => by rw [nm]; exact h.arr x hx
      keep := fun r hr => by
        have hr' := hr
        unfold DKept KeptS at hr'
        rw [Q r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)]
        exact h.keep r hr
      mem := fun a' ha => by rw [nm]; exact h.mem a' ha
      out := by rw [ou]; exact h.out }
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, hD, ?_, ?_, ?_, ?_, h24⟩
  · rw [q₂ 1315 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact m₁
  · rw [q₂ 1321 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s₁
  · rw [q₂ 1322 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact n₁
  · rw [q₂ 1323 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact k₁'

/-- A leaf round after the pop and the weight: the names of the frame's vertices. -/
theorem dLeafCase {R : Kasteleyn.RotationSystem G} {μ : Fin N → ℕ}
    {Z M aS aP aV aF L k0 : ℕ} {c0 : Config} {a : DFr N} {c : Config}
    (h : DCore G R μ Z W M aS aP aV aF L k0 c0 a c) (h0 : 0 < a.m)
    (h15 : c.nreg 1315 = a.m - 1) (h21 : c.nreg 1321 = a.s (a.m - 1))
    (h22 : c.nreg 1322 = #(a.U (a.m - 1))) :
    ∃ c' k, Exec P W dLeafP c c' k ∧ k ≤ 7 * #(a.U (a.m - 1)) + 4 ∧
      DCore G R μ Z W M aS aP aV aF L k0 c0
        ⟨a.m - 1, a.U, a.k, a.s, dLeaf (a.U (a.m - 1)) a.st⟩ c' ∧ c'.nreg 1315 = a.m - 1 := by
  have hb := h.base
  have := h.lay1; have := h.lay2; have := h.lay3; have := h.lay4; have := h.lay5
  have := hb.lV; have := hb.lA; have := hb.lB; have := hb.lF
  obtain ⟨f0, f1, f2, fl, fs1, fs2, fk⟩ := h.fr (a.m - 1) (by omega)
  have k1203 : c.nreg 1203 = c0.nreg 1203 := h.keep 1203 (by unfold DKept KeptS; omega)
  obtain ⟨c', k, e, hw', hP, hfr, hq, hk⟩ := dLeafP_exec (P := P) hb.wb hb.one h21 h22 h.rP fl
    (Or.inr (by omega)) (by omega) (by omega)
  have rr : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := Exec.real_of_noReal e (by decide)
  have ou : c'.output = c.output := Exec.output_of_ou e (by decide)
  have Q : ∀ r, 1310 ≤ r → r ≤ 1315 → c'.nreg r = c.nreg r := fun r h1 h2 =>
    hq r (by omega) (by omega) (by omega) (by omega)
  refine ⟨c', k, e, hk, ?_, by rw [Q 1315 (by omega) (by omega)]; exact h15⟩
  exact
    { base := hb.congr hw' (fun r hr _ => by
        unfold KeptS at hr; exact hq r (by omega) (by omega) (by omega) (by omega))
        (fun a ha => hfr a (Or.inl (by omega))) rr.1 rr.2
      rS := by rw [Q 1310 (by omega) (by omega)]; exact h.rS
      rP := by rw [Q 1311 (by omega) (by omega)]; exact h.rP
      rV := by rw [Q 1312 (by omega) (by omega)]; exact h.rV
      rF := by rw [Q 1313 (by omega) (by omega)]; exact h.rF
      rL := by rw [Q 1314 (by omega) (by omega)]; exact h.rL
      lay1 := h.lay1, lay2 := h.lay2, lay3 := h.lay3, lay4 := h.lay4, lay5 := h.lay5
      hMN := h.hMN
      fr := fun i hi => by
        simp only at hi ⊢
        obtain ⟨g0, g1, g2, gl, gs1, gs2, gk⟩ := h.fr i (by omega)
        refine ⟨by rw [hfr _ (Or.inr (by omega))]; exact g0,
          by rw [hfr _ (Or.inr (by omega))]; exact g1, by rw [hfr _ (Or.inr (by omega))]; exact g2,
          fun j hj => by rw [hfr _ (Or.inr (by omega))]; exact gl j hj, gs1, gs2, gk⟩
      ord := fun i j hij hj => h.ord i j hij (by simp only at hj; omega)
      arr := fun x hx => by
        refine ⟨by rw [hfr _ (Or.inl (by omega))]; exact (h.arr x hx).1, ?_⟩
        rw [hP x hx, (h.arr x hx).2]
        rfl
      keep := fun r hr => by
        have hr' := hr
        unfold DKept KeptS at hr'
        rw [hq r (by omega) (by omega) (by omega) (by omega)]
        exact h.keep r hr
      mem := fun a' ha => by
        rw [hfr a' (by unfold DOut at ha; omega)]; exact h.mem a' ha
      out := by rw [ou]; exact h.out }

/-- The frames of the two parts: the second part at the place of the removed frame, the first
part on top. -/
def dPush : Stmt := block [.subN 1323 1323 1001,
  .addN 1320 1315 1315, .addN 1320 1320 1315, .addN 1320 1320 1313, .storeN 1320 1329,
  .addN 1320 1320 1001, .subN 1327 1330 1329, .storeN 1320 1327, .addN 1320 1320 1001,
  .storeN 1320 1323, .addN 1315 1315 1001,
  .addN 1320 1315 1315, .addN 1320 1320 1315, .addN 1320 1320 1313, .storeN 1320 1321,
  .addN 1320 1320 1001, .subN 1327 1329 1321, .storeN 1320 1327, .addN 1320 1320 1001,
  .storeN 1320 1323, .addN 1315 1315 1001]

theorem dPush_exec {d : Config} (hw : WordsBounded W d) {i aF s pa pb k : ℕ}
    (h01 : d.nreg 1001 = 1) (h15 : d.nreg 1315 = i) (h13 : d.nreg 1313 = aF)
    (h21 : d.nreg 1321 = s) (h29 : d.nreg 1329 = pa) (h30 : d.nreg 1330 = pb)
    (h23 : d.nreg 1323 = k + 1) (hb : aF + 3 * i + 6 ≤ W) :
    ∃ d' k', Exec P W dPush d d' k' ∧ k' = 21 ∧ WordsBounded W d' ∧ d'.nreg 1315 = i + 2 ∧
      d'.nmem (aF + 3 * i) = pa ∧ d'.nmem (aF + 3 * i + 1) = pb - pa ∧
      d'.nmem (aF + 3 * i + 2) = k ∧ d'.nmem (aF + 3 * (i + 1)) = s ∧
      d'.nmem (aF + 3 * (i + 1) + 1) = pa - s ∧ d'.nmem (aF + 3 * (i + 1) + 2) = k ∧
      (∀ x, (x < aF + 3 * i ∨ aF + 3 * i + 6 ≤ x) → d'.nmem x = d.nmem x) ∧
      (∀ r, r ≠ 1315 → r ≠ 1320 → r ≠ 1323 → r ≠ 1327 → d'.nreg r = d.nreg r) := by
  unfold dPush
  exec_block
  all_goals try (config_simp; simp (config := {failIfUnchanged := false}) only [h15, h13, h01,
    h21, h29, h30, h23]; omega)
  refine ⟨rfl, ‹_›, by config_simp; rw [h15, h01], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Config.nmem_mk, Config.nreg_mk, upd_apply, h15, h13, h01, h21, h29, h30,
    h23]
  all_goals norm_num
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · intro x hx; split_ifs <;> first | omega | rfl
  · intro r h1 h2 h3 h4; simp [h1, h2, h3, h4]

theorem squareProg_wmax : squareProg.wmax < 1300 := by decide +kernel

/-- The separation of the square used by the program. -/
noncomputable abbrev sqSep {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) : Finset (Fin N) → (Fin N → ℕ) →
      Finset (Fin N) × Finset (Fin N) × Finset (Fin N) :=
  ((ltRoutine R hR (ord N) mem_ord).square hΔ).sep

/-- The splitting part of a round. -/
def dSplit : Stmt := .seq dCopy (.seq squareProg (.seq dPassA (.seq dPassB dPush)))

/-- The cost bound of `squareProg` in terms of `#U` and the weight of `U`. -/
def sqC (Δ N n sw : ℕ) : ℕ :=
  15 * N + ((Δ + 1) * (6 * Δ ^ 2 + 3415 * Δ + 2411) + 22 * Δ + 43) * n + 12 * sw + 5420

/-- The worklist after a splitting round. -/
def dSplitFr (a : DFr N) (i k : ℕ) (S A B : Finset (Fin N)) : DFr N :=
  ⟨i + 2, fun j => if j = i + 1 then A else if j = i then B else a.U j,
    fun j => if j = i + 1 then k else if j = i then k else a.k j,
    fun j => if j = i + 1 then a.s i else if j = i then a.s i + #A else a.s j, dMark S a.st⟩

set_option maxHeartbeats 1000000 in
/-- A splitting round after the pop and the weight. -/
theorem dSplitCase {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {μ : Fin N → ℕ}
    {Z M aS aP aV aF L k0 : ℕ} {c0 : Config} {a : DFr N} {c : Config} {i k : ℕ}
    (h : DCore G R μ Z W M aS aP aV aF L k0 c0 a c) (hm : a.m = i + 1)
    (h15 : c.nreg 1315 = i) (h21 : c.nreg 1321 = a.s i) (h22 : c.nreg 1322 = #(a.U i))
    (h23 : c.nreg 1323 = k + 1) (hk : a.k i = k + 1) :
    ∃ c' k', Exec P W dSplit c c' k' ∧
      k' ≤ 32 * #(a.U i) + 34 + sqC Δ N #(a.U i) (∑ v ∈ a.U i, μ v) ∧
      DCore G R μ Z W M aS aP aV aF L k0 c0
        (dSplitFr a i k (sqSep hR hΔ (a.U i) μ).1 (sqSep hR hΔ (a.U i) μ).2.1
          (sqSep hR hΔ (a.U i) μ).2.2) c' ∧ c'.nreg 1315 = i + 2 := by
  obtain ⟨f0, f1, f2, fl, fs1, fs2, fk⟩ := h.fr i (by omega)
  set U := a.U i with hUdef
  set s := a.s i with hsdef
  set S := (sqSep hR hΔ U μ).1
  set A := (sqSep hR hΔ U μ).2.1
  set B := (sqSep hR hΔ U μ).2.2
  have hsep : IsSeparation (PlanarSeparator.square G) U S A B :=
    ((ltRoutine R hR (ord N) mem_ord).square hΔ).isSeparation U μ
  have hU : S ∪ A ∪ B = U := hsep.union_eq
  have hAU : A ⊆ U := fun x hx => hU ▸ mem_union_left _ (mem_union_right _ hx)
  have hBU : B ⊆ U := fun x hx => hU ▸ mem_union_right _ hx
  have hAB : #A + #B ≤ #U := by
    rw [← card_union_of_disjoint hsep.disjoint]; exact card_le_card (union_subset hAU hBU)
  have hb := h.base
  have := h.lay1; have := h.lay2; have := h.lay3; have := h.lay4; have := h.lay5
  have := hb.lV; have := hb.lA; have := hb.lB; have := hb.lF; have := hb.lU; have := hb.lC
  have := hb.lQ; have := hb.lW; have := hb.lS; have := hb.l0; have := hb.l1; have := hb.l2
  have := hb.l3; have := hb.l4; have := hb.l5; have := hb.l6; have := hb.l7
  have hUN := card_le_N U
  have k1203 : c.nreg 1203 = c0.nreg 1203 := h.keep 1203 (by unfold DKept KeptS; omega)
  -- the copy
  obtain ⟨c₃, k₃, e₃, hw₃, h01₃, hl₃, hfr₃, hq₃, hk₃⟩ := dCopy_exec (P := P) hb.wb hb.one h21
    h22 rfl fl (Or.inr (by omega)) (by omega) (by omega)
  have rr₃ : c₃.rreg = c.rreg ∧ c₃.rmem = c.rmem := Exec.real_of_noReal e₃ (by decide)
  have ou₃ : c₃.output = c.output := Exec.output_of_ou e₃ (by decide)
  have Q₃ : ∀ r, r ≠ 1201 → r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → c₃.nreg r = c.nreg r := hq₃
  have hb₃ : SBase G R μ Z W M c₃ := hb.congr hw₃
    (fun r hr h1 => by unfold KeptS at hr; exact Q₃ r h1 (by omega) (by omega) (by omega))
    (fun a ha => hfr₃ a (by rcases ha with ha | ha <;> omega)) rr₃.1 rr₃.2
  have r00₃ : c₃.nreg 1200 = c.nreg 1200 := Q₃ 1200 (by omega) (by omega) (by omega) (by omega)
  have hpre : SPre G R μ U Z W c₃ := hb₃.toSPre h01₃ (fun l hl => by rw [r00₃]; exact hl₃ l hl)
  -- the separator of the square
  obtain ⟨c₄, k₄, e₄, hk₄, hD⟩ := squareProg_exec (P := P) hR hΔ hpre
  have hk₄' := squareProg_cost_le (U := U) (w := μ) hΔ
  have hb₄ : SBase G R μ Z W M c₄ := hb₃.of_sDone hD
  have Kh : ∀ r, 1300 ≤ r → c₄.nreg r = c₃.nreg r := fun r hr =>
    Exec.nreg_of_wr e₄ (Stmt.wr_of_wmax (by have := squareProg_wmax; omega))
  have K₄ : ∀ r, KeptS r → c₄.nreg r = c₃.nreg r := hD.regs
  have r1019 : c₃.nreg 1019 = c.nreg 1019 := Q₃ 1019 (by omega) (by omega) (by omega) (by omega)
  have r1100 : c₃.nreg 1100 = c.nreg 1100 := Q₃ 1100 (by omega) (by omega) (by omega) (by omega)
  have r1015 : c₃.nreg 1015 = c.nreg 1015 := Q₃ 1015 (by omega) (by omega) (by omega) (by omega)
  have r1103 : c₃.nreg 1103 = c.nreg 1103 := Q₃ 1103 (by omega) (by omega) (by omega) (by omega)
  have r1203 : c₃.nreg 1203 = c.nreg 1203 := Q₃ 1203 (by omega) (by omega) (by omega) (by omega)
  have F₄ : ∀ x, (x < c.nreg 1019 ∨ c.nreg 1019 + N ≤ x) →
      (x < c.nreg 1100 ∨ c.nreg 1100 + N ≤ x) → (x < c.nreg 1015 ∨ c.nreg 1015 + N ≤ x) →
      (x < c.nreg 1103 ∨ c.nreg 1103 + N ≤ x) → (x < c.nreg 1203 ∨ c.nreg 1203 + N ≤ x) →
      c₄.nmem x = c₃.nmem x := fun x h1 h2 h3 h4 h5 => hD.frame x
    (fun v _ => by have := v.2; rw [r1019]; omega) (by rw [r1100]; exact h2)
    (by rw [r1015]; exact h3) (by rw [r1103]; exact h4) (by rw [r1203]; exact h5)
  have hmk₄ := hD.mark
  rw [r1019] at hmk₄
  -- the first part
  have c4_1321 : c₄.nreg 1321 = s := by
    rw [Kh 1321 (by omega), Q₃ 1321 (by omega) (by omega) (by omega) (by omega)]; exact h21
  have c4_1322 : c₄.nreg 1322 = #U := by
    rw [Kh 1322 (by omega), Q₃ 1322 (by omega) (by omega) (by omega) (by omega)]; exact h22
  have c4_1200 : c₄.nreg 1200 = c.nreg 1200 := by rw [K₄ 1200 (by unfold KeptS; omega), r00₃]
  have c4_1019 : c₄.nreg 1019 = c.nreg 1019 := by rw [K₄ 1019 (by unfold KeptS; omega), r1019]
  have c4_1310 : c₄.nreg 1310 = aS := by
    rw [Kh 1310 (by omega), Q₃ 1310 (by omega) (by omega) (by omega) (by omega)]; exact h.rS
  have c4_l : ∀ l < #U, c₄.nmem (c.nreg 1200 + l) = lv U l := fun l hl => by
    rw [F₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hl₃ l hl
  obtain ⟨c₅, k₅, e₅, hw₅, h29₅, hA₅, hS₅, hfr₅, hq₅, -, hk₅⟩ := dPassA_exec (P := P) hb₄.wb hU
    hmk₄ hb₄.one c4_1321 c4_1322 c4_1200 c4_1019 c4_1310 c4_l
    (by omega) (by omega) (by omega) (by omega) (by have := hb.lV; omega)
  have rr₅ : c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem := Exec.real_of_noReal e₅ (by decide)
  have ou₅ : c₅.output = c₄.output := Exec.output_of_ou e₅ (by decide)
  -- the second part
  have c5_1001 : c₅.nreg 1001 = 1 := by
    rw [hq₅ 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hb₄.one
  have c5_1322 : c₅.nreg 1322 = #U := by
    rw [hq₅ 1322 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact c4_1322
  have c5_1200 : c₅.nreg 1200 = c.nreg 1200 := by
    rw [hq₅ 1200 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact c4_1200
  have c5_1019 : c₅.nreg 1019 = c.nreg 1019 := by
    rw [hq₅ 1019 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact c4_1019
  have c5_l : ∀ l < #U, c₅.nmem (c.nreg 1200 + l) = lv U l := fun l hl => by
    rw [hfr₅ _ (Or.inl (by omega)) (Or.inl (by omega))]; exact c4_l l hl
  have c5_mk : ∀ v ∈ U, (c₅.nmem (c.nreg 1019 + v) = 0 ↔ v ∈ S) ∧
      (c₅.nmem (c.nreg 1019 + v) = 1 ↔ v ∈ A) ∧ (c₅.nmem (c.nreg 1019 + v) = 2 ↔ v ∈ B) :=
    fun v hv => by
      rw [hfr₅ _ (Or.inl (by have := v.2; omega)) (Or.inl (by have := v.2; omega))]
      exact hmk₄ v hv
  obtain ⟨c₆, k₆, e₆, hw₆, h30₆, hB₆, hfr₆, hq₆, hk₆⟩ := dPassB_exec (P := P) hw₅ hU
    c5_mk c5_1001 h29₅ c5_1322 c5_1200 c5_1019 c5_l (by omega) (by omega) (by omega) (by omega)
  have rr₆ : c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem := Exec.real_of_noReal e₆ (by decide)
  have ou₆ : c₆.output = c₅.output := Exec.output_of_ou e₆ (by decide)
  -- the frames
  have R6 : ∀ r, 1300 ≤ r → r ≠ 1320 → r ≠ 1325 → r ≠ 1326 → r ≠ 1328 → r ≠ 1329 →
      r ≠ 1330 → r ≠ 1332 → c₆.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 h6 h7 => by
    rw [hq₆ r h1 h2 h3 h4 h6, hq₅ r h1 h2 h3 h4 h5 h7, Kh r h0,
      Q₃ r (by omega) h1 h2 h3]
  have c6_1001 : c₆.nreg 1001 = 1 := by
    rw [hq₆ 1001 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact c5_1001
  have c6_1315 : c₆.nreg 1315 = i := by
    rw [R6 1315 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h15
  have c6_1313 : c₆.nreg 1313 = aF := by
    rw [R6 1313 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h.rF
  have c6_1321 : c₆.nreg 1321 = s := by
    rw [R6 1321 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h21
  have c6_1329 : c₆.nreg 1329 = s + #A := by
    rw [hq₆ 1329 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h29₅
  have c6_1323 : c₆.nreg 1323 = k + 1 := by
    rw [R6 1323 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; exact h23
  obtain ⟨c₇, k₇, e₇, hk₇, hw₇, h15₇, p0, p1, p2, p3, p4, p5, hfr₇, hq₇⟩ := dPush_exec (P := P)
    hw₆ c6_1001 c6_1315 c6_1313 c6_1321 c6_1329 h30₆ c6_1323 (by omega)
  have rr₇ : c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem := Exec.real_of_noReal e₇ (by decide)
  have ou₇ : c₇.output = c₆.output := Exec.output_of_ou e₇ (by decide)
  have R7 : ∀ r, 1300 ≤ r → r ≠ 1315 → r ≠ 1320 → r ≠ 1323 → r ≠ 1325 → r ≠ 1326 → r ≠ 1327 →
      r ≠ 1328 → r ≠ 1329 → r ≠ 1330 → r ≠ 1332 → c₇.nreg r = c.nreg r :=
    fun r h0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 => by
      rw [hq₇ r a1 a2 a3 a6, R6 r h0 a2 a4 a5 a7 a8 a9 a10]
  have K7 : ∀ r, KeptS r → r ≠ 1201 → c₇.nreg r = c.nreg r := fun r hr h1 => by
    have hr' := hr
    unfold KeptS at hr'
    rw [hq₇ r (by omega) (by omega) (by omega) (by omega),
      hq₆ r (by omega) (by omega) (by omega) (by omega) (by omega),
      hq₅ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), K₄ r hr,
      Q₃ r h1 (by omega) (by omega) (by omega)]
  -- the memory
  have M7 : ∀ x, x < c.nreg 1203 → (x < c.nreg 1019 ∨ c.nreg 1019 + N ≤ x) →
      (x < c.nreg 1100 ∨ c.nreg 1100 + N ≤ x) → (x < c.nreg 1015 ∨ c.nreg 1015 + N ≤ x) →
      (x < c.nreg 1103 ∨ c.nreg 1103 + N ≤ x) → (x < c.nreg 1200 ∨ c.nreg 1200 + N ≤ x) →
      c₇.nmem x = c.nmem x := fun x h0 h1 h2 h3 h4 h5 => by
    rw [hfr₇ x (Or.inl (by omega)), hfr₆ x (Or.inl (by omega)),
      hfr₅ x (Or.inl (by omega)) (Or.inl (by omega)), F₄ x h1 h2 h3 h4 (Or.inl h0),
      hfr₃ x h5]
  have Mhi : ∀ x, aF + 3 * (k0 + 1) ≤ x → c₇.nmem x = c.nmem x := fun x hx => by
    rw [hfr₇ x (Or.inr (by omega)), hfr₆ x (Or.inr (by omega)),
      hfr₅ x (Or.inr (by omega)) (Or.inr (by omega)),
      F₄ x (by omega) (by omega) (by omega) (by omega) (by omega), hfr₃ x (Or.inr (by omega))]
  have Mmid : ∀ x, aS ≤ x → x < aF → (x < aS + N ∨ aP ≤ x) → (x < s ∨ s + #U ≤ x) →
      x ∉ Set.Ico (aS + 0) (aS + N) ∨ True → (x < aS ∨ aS + N ≤ x) →
      c₇.nmem x = c.nmem x := fun x h0 h1 _ h3 _ h5 => by
    rw [hfr₇ x (Or.inl (by omega)), hfr₆ x (by omega), hfr₅ x h5 (by omega),
      F₄ x (by omega) (by omega) (by omega) (by omega) (by omega), hfr₃ x (Or.inr (by omega))]
  have Mfr : ∀ x, aF ≤ x → x < aF + 3 * i → c₇.nmem x = c.nmem x := fun x h0 h1 => by
    rw [hfr₇ x (Or.inl h1), hfr₆ x (Or.inr (by omega)),
      hfr₅ x (Or.inr (by omega)) (Or.inr (by omega)),
      F₄ x (by omega) (by omega) (by omega) (by omega) (by omega), hfr₃ x (Or.inr (by omega))]
  have hcost : k₃ + (k₄ + (k₅ + (k₆ + k₇))) ≤
      32 * #U + 34 + sqC Δ N #U (∑ v ∈ U, μ v) := by
    unfold sqC; omega
  refine ⟨c₇, k₃ + (k₄ + (k₅ + (k₆ + k₇))), .seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))), hcost,
    ?_, h15₇⟩
  have hb₇ : SBase G R μ Z W M c₇ := hb₄.congr hw₇
    (fun r hr h1 => by
      have hr' := hr
      unfold KeptS at hr'
      rw [hq₇ r (by omega) (by omega) (by omega) (by omega),
        hq₆ r (by omega) (by omega) (by omega) (by omega) (by omega),
        hq₅ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
    (fun x hx => by
      rw [K₄ 1200 (by unfold KeptS; omega), K₄ 1202 (by unfold KeptS; omega),
        K₄ 1203 (by unfold KeptS; omega), Q₃ 1200 (by omega) (by omega) (by omega) (by omega),
        Q₃ 1202 (by omega) (by omega) (by omega) (by omega), r1203] at hx
      rw [hfr₇ x (Or.inl (by omega)), hfr₆ x (Or.inl (by omega)),
        hfr₅ x (Or.inl (by omega)) (Or.inl (by omega))])
    (by rw [rr₇.1, rr₆.1, rr₅.1]) (by rw [rr₇.2, rr₆.2, rr₅.2])
  exact
    { base := hb₇
      rS := by rw [R7 1310 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rS
      rP := by rw [R7 1311 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rP
      rV := by rw [R7 1312 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rV
      rF := by rw [R7 1313 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rF
      rL := by rw [R7 1314 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.rL
      lay1 := h.lay1, lay2 := h.lay2, lay3 := h.lay3, lay4 := h.lay4, lay5 := h.lay5
      hMN := h.hMN
      fr := fun j hj => by
        simp only [dSplitFr] at hj ⊢
        by_cases hj1 : j = i + 1
        · rw [hj1]
          simp only [ite_true]
          refine ⟨p3, by rw [p4]; omega, p5, fun t ht => ?_, fs1, by omega, by omega⟩
          rw [hfr₇ _ (Or.inl (by omega)), hfr₆ _ (Or.inl (by omega))]; exact hA₅ t ht
        by_cases hj0 : j = i
        · rw [hj0]
          simp only [show i ≠ i + 1 by omega, ite_true, ite_false]
          refine ⟨p0, by rw [p1]; omega, p2, fun t ht => ?_, by omega,
            by omega, by omega⟩
          rw [hfr₇ _ (Or.inl (by omega))]; exact hB₆ t ht
        · simp only [hj1, hj0, ite_false]
          have hji : j < i := by omega
          obtain ⟨g0, g1, g2, gl, gs1, gs2, gk⟩ := h.fr j (by omega)
          have ho := h.ord j i hji (by omega)
          rw [← hsdef, ← hUdef] at ho
          refine ⟨by rw [Mfr _ (by omega) (by omega)]; exact g0,
            by rw [Mfr _ (by omega) (by omega)]; exact g1,
            by rw [Mfr _ (by omega) (by omega)]; exact g2, fun t ht => ?_, gs1, gs2, gk⟩
          rw [Mmid _ (by omega) (by omega) (by omega) (by omega) (Or.inr trivial) (by omega)]
          exact gl t ht
      ord := fun j1 j2 h12 h2 => by
        simp only [dSplitFr] at h2 ⊢
        by_cases e2 : j2 = i + 1
        · rw [e2]
          simp only [ite_true]
          by_cases e1 : j1 = i
          · rw [e1]; simp only [ite_true, show i ≠ i + 1 by omega, ite_false]; omega
          · simp only [show j1 ≠ i + 1 by omega, e1, ite_false]
            have := h.ord j1 i (by omega) (by omega)
            rw [← hsdef, ← hUdef] at this; omega
        · have e2' : j2 = i ∨ j2 < i := by omega
          rcases e2' with e2' | e2'
          · rw [e2']
            simp only [show j1 ≠ i + 1 by omega, show j1 ≠ i by omega, show i ≠ i + 1 by omega,
              ite_true, ite_false]
            have := h.ord j1 i (by omega) (by omega)
            rw [← hsdef, ← hUdef] at this; omega
          · simp only [show j1 ≠ i + 1 by omega, show j1 ≠ i by omega, e2, show j2 ≠ i by omega,
              ite_false]
            exact h.ord j1 j2 h12 (by omega)
      arr := fun x hx => by
        simp only [dSplitFr, dMark]
        refine ⟨?_, ?_⟩
        · rw [hfr₇ _ (Or.inl (by omega)), hfr₆ _ (Or.inl (by omega)), hS₅ x hx,
            F₄ _ (by omega) (by omega) (by omega) (by omega) (by omega),
            hfr₃ _ (Or.inr (by omega)), (h.arr x hx).1]
        · rw [Mmid _ (by omega) (by omega) (by omega) (by omega) (Or.inr trivial) (by omega)]
          exact (h.arr x hx).2
      keep := fun r hr => by
        have hr' := hr
        unfold DKept at hr'
        rcases hr' with ⟨h1, h2⟩ | h1 | h1
        · rw [K7 r h1 h2]; exact h.keep r hr
        · rw [R7 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)]; exact h.keep r hr
        · rw [R7 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)]; exact h.keep r hr
      mem := fun x hx => by
        have k1019 : c.nreg 1019 = c0.nreg 1019 := h.keep 1019 (by unfold DKept KeptS; omega)
        have k1100 : c.nreg 1100 = c0.nreg 1100 := h.keep 1100 (by unfold DKept KeptS; omega)
        have k1015 : c.nreg 1015 = c0.nreg 1015 := h.keep 1015 (by unfold DKept KeptS; omega)
        have k1103 : c.nreg 1103 = c0.nreg 1103 := h.keep 1103 (by unfold DKept KeptS; omega)
        have k1200 : c.nreg 1200 = c0.nreg 1200 := h.keep 1200 (by unfold DKept KeptS; omega)
        obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hx
        rcases d6 with d6 | d6
        · rw [M7 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          exact h.mem x ⟨d1, d2, d3, d4, d5, Or.inl d6⟩
        · rw [Mhi x d6]; exact h.mem x ⟨d1, d2, d3, d4, d5, Or.inr d6⟩
      out := by rw [ou₇, ou₆, ou₅, hD.out, ou₃]; exact h.out }

/-- A round of the worklist loop. -/
def dBody : Stmt := .seq (.seq dPop dSum) (.ifLtN 0 1323 (.ifLtN 1314 1324 dSplit dLeafP) dLeafP)

/-- **The worklist loop of the division**: while frames remain, a round. -/
def divLoop : Stmt := .whileLtN 0 1315 dBody

/-- The cost of the remaining rounds. -/
def DFr.cost (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L Δ : ℕ) (a : DFr N) : ℕ :=
  ∑ j ∈ range a.m, dcost sep μ L Δ (a.k j) (a.U j)

theorem flist_succ (a : DFr N) {i : ℕ} (hm : a.m = i + 1) :
    a.flist = (a.U i, a.k i) :: (⟨i, a.U, a.k, a.s, a.st⟩ : DFr N).flist := by
  simp only [DFr.flist, hm, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons]

theorem flist_split (a : DFr N) {i k : ℕ} (S A B : Finset (Fin N)) :
    (dSplitFr a i k S A B).flist =
      (A, k) :: (B, k) :: (⟨i, a.U, a.k, a.s, a.st⟩ : DFr N).flist := by
  simp only [DFr.flist, dSplitFr, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.map_cons, ite_true, show i ≠ i + 1 by omega, ite_false,
    List.cons.injEq, true_and]
  refine List.map_congr_left fun j hj => ?_
  have : j < i := by simpa using hj
  simp only [show j ≠ i + 1 by omega, show j ≠ i by omega, ite_false]

theorem dBody_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {μ : Fin N → ℕ}
    {Z M aS aP aV aF L k0 : ℕ} {c0 : Config} {a : DFr N} {c : Config}
    (h : DCore G R μ Z W M aS aP aV aF L k0 c0 a c) (hm : c.nreg 1315 = a.m) (h0 : 0 < a.m) :
    ∃ a' c' k, Exec P W dBody c c' k ∧
      (DCore G R μ Z W M aS aP aV aF L k0 c0 a' c' ∧ c'.nreg 1315 = a'.m ∧
        dFold (sqSep hR hΔ) μ L a'.flist a'.st = dFold (sqSep hR hΔ) μ L a.flist a.st) ∧
      a'.cost (sqSep hR hΔ) μ L Δ + k + 2 ≤ a.cost (sqSep hR hΔ) μ L Δ := by
  obtain ⟨i, hi⟩ : ∃ i, a.m = i + 1 := ⟨a.m - 1, by omega⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hD₂, h15, h21, h22, h23, h24⟩ := dPopSum_exec (P := P) h hm h0
  rw [hi, Nat.add_sub_cancel] at h15 h21 h22 h23 h24 hk₂
  have hfl := flist_succ a hi
  have hcost : a.cost (sqSep hR hΔ) μ L Δ = (⟨i, a.U, a.k, a.s, a.st⟩ : DFr N).cost
      (sqSep hR hΔ) μ L Δ + dcost (sqSep hR hΔ) μ L Δ (a.k i) (a.U i) := by
    simp only [DFr.cost, hi, sum_range_succ]
  have hb₂ := hD₂.base
  have hleaf : ∀ (hl : a.k i = 0 ∨ ∑ v ∈ a.U i, μ v ≤ L), ∃ c' k', Exec P W dLeafP c₂ c' k' ∧
      k' ≤ 7 * #(a.U i) + 4 ∧
      (DCore G R μ Z W M aS aP aV aF L k0 c0 ⟨i, a.U, a.k, a.s, dLeaf (a.U i) a.st⟩ c' ∧
        c'.nreg 1315 = i ∧
        dFold (sqSep hR hΔ) μ L (⟨i, a.U, a.k, a.s, dLeaf (a.U i) a.st⟩ : DFr N).flist
          (dLeaf (a.U i) a.st) = dFold (sqSep hR hΔ) μ L a.flist a.st) := fun hl => by
    obtain ⟨c', k', e', hk', hD', h15'⟩ := dLeafCase (P := P) hD₂ h0
      (by rw [h15, hi, Nat.add_sub_cancel]) (by rw [h21, hi, Nat.add_sub_cancel])
      (by rw [h22, hi, Nat.add_sub_cancel])
    rw [hi, Nat.add_sub_cancel] at hk' hD' h15'
    refine ⟨c', k', e', hk', hD', h15', ?_⟩
    rw [hfl, dFold_step_leaf _ _ _ hl]
    rfl
  have hc0 : (⟨i, a.U, a.k, a.s, dLeaf (a.U i) a.st⟩ : DFr N).cost (sqSep hR hΔ) μ L Δ =
      (⟨i, a.U, a.k, a.s, a.st⟩ : DFr N).cost (sqSep hR hΔ) μ L Δ := rfl
  have hr0 := hb₂.r0
  by_cases hk0 : a.k i = 0
  · obtain ⟨c', k', e', hk', hD'⟩ := hleaf (Or.inl hk0)
    refine ⟨_, c', k₂ + (k' + 2), .seq e₂ (.ifLtN_false (by rw [hr0, h23, hk0]; omega) e'), hD', ?_⟩
    rw [hcost, hc0, hk0]
    simp only [dcost]
    omega
  obtain ⟨k, hk⟩ : ∃ k, a.k i = k + 1 := ⟨a.k i - 1, by omega⟩
  by_cases hL : ∑ v ∈ a.U i, μ v ≤ L
  · obtain ⟨c', k', e', hk', hD'⟩ := hleaf (Or.inr hL)
    refine ⟨_, c', k₂ + (k' + 2 + 1), .seq e₂ (.ifLtN_true (by rw [hr0, h23, hk]; omega)
      (.ifLtN_false (by rw [hD₂.rL, h24]; omega) e')), hD', ?_⟩
    rw [hcost, hc0, hk]
    simp only [dcost, hL, ite_true]
    omega
  obtain ⟨c', k', e', hk', hD', h15'⟩ := dSplitCase (P := P) hR hΔ hD₂ hi h15 h21 h22
    (by rw [h23, hk]) hk
  refine ⟨_, c', k₂ + (k' + 1 + 1), .seq e₂ (.ifLtN_true (by rw [hr0, h23, hk]; omega)
    (.ifLtN_true (by rw [hD₂.rL, h24]; omega) e')), ⟨hD', by rw [h15']; rfl, ?_⟩, ?_⟩
  · rw [flist_split, hfl, hk, dFold_step_split _ _ _ hL]
    rfl
  · rw [hcost, hk]
    simp only [dcost, hL, ite_false]
    have : (dSplitFr a i k (sqSep hR hΔ (a.U i) μ).1 (sqSep hR hΔ (a.U i) μ).2.1
        (sqSep hR hΔ (a.U i) μ).2.2).cost (sqSep hR hΔ) μ L Δ =
        (⟨i, a.U, a.k, a.s, a.st⟩ : DFr N).cost (sqSep hR hΔ) μ L Δ +
          dcost (sqSep hR hΔ) μ L Δ k (sqSep hR hΔ (a.U i) μ).2.2 +
          dcost (sqSep hR hΔ) μ L Δ k (sqSep hR hΔ (a.U i) μ).2.1 := by
      simp only [DFr.cost, dSplitFr, sum_range_succ, ite_true, show i ≠ i + 1 by omega,
        ite_false]
      congr 2
      refine sum_congr rfl fun j hj => ?_
      have : j < i := by simpa using hj
      simp only [show j ≠ i + 1 by omega, show j ≠ i by omega, ite_false]
    rw [this]
    unfold sqC at hk'
    omega

/-- **The worklist loop of the division**: from a worklist state, the loop ends with no frame
left and the flags and names of `dFold` of the frames, within the cost of the frames. -/
theorem divLoop_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {μ : Fin N → ℕ}
    {Z M aS aP aV aF L k0 : ℕ} {c0 : Config} {a : DFr N} {c : Config}
    (h : DCore G R μ Z W M aS aP aV aF L k0 c0 a c) (hm : c.nreg 1315 = a.m) :
    ∃ a' c' k, Exec P W divLoop c c' k ∧ DCore G R μ Z W M aS aP aV aF L k0 c0 a' c' ∧
      a'.m = 0 ∧ c'.nreg 1315 = 0 ∧ a'.st = dFold (sqSep hR hΔ) μ L a.flist a.st ∧
      k ≤ a.cost (sqSep hR hΔ) μ L Δ + 2 := by
  obtain ⟨a', c', k, e, ⟨hD, hm', hf⟩, hn, hk⟩ := whileLtN_abs (P := P) (W := W) (a := 0)
    (b := 1315) (body := dBody)
    (fun a' c' => DCore G R μ Z W M aS aP aV aF L k0 c0 a' c' ∧ c'.nreg 1315 = a'.m ∧
      dFold (sqSep hR hΔ) μ L a'.flist a'.st = dFold (sqSep hR hΔ) μ L a.flist a.st)
    (fun a' => a'.cost (sqSep hR hΔ) μ L Δ) (fun _ _ h => h.1.base.wb)
    (fun a' c' ⟨hD, hm', hf⟩ ht => by
      rw [hD.base.r0, hm'] at ht
      obtain ⟨a'', c'', k, e, ⟨hD', hm'', hf'⟩, hk⟩ := dBody_exec (P := P) hR hΔ hD hm' ht
      exact ⟨a'', c'', k, e, ⟨hD', hm'', hf'.trans hf⟩, hk⟩) ⟨h, hm, rfl⟩
  rw [hD.base.r0, hm'] at hn
  have h0 : a'.m = 0 := by omega
  refine ⟨a', c', k, e, hD, h0, by rw [hm', h0], ?_, hk⟩
  rw [← hf]
  simp only [DFr.flist, h0, List.range_zero, List.reverse_nil, List.map_nil, dFold]

end Piece

end PlanarSeparator
