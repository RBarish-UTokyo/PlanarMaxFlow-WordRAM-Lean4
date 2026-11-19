module

public import PlanarSeparator.Machine.SplitWFront

/-!
# The split of a node on the machine: the back

After the division (`divLoop`) of `D = U ∪ B` with the weights `spMu`, the rest of the machine
form of `PlanarSeparator.SepRoutine.splitW` for the square of `G`:

* `swPieces`: the names of the pieces in increasing order (`spPc`) and the balanced split
  (`bsProg` with `p = 5`, `q = 3 #B`), marks `1` on the chosen names;
* `swOut`: the separator `U ∩ S` to the output buffer `aO`, the two parts in place of the list of
  `U` (`spMk2`, `dPassB`, `spMk1`, `dPassA`, `dPassB`);
* `swClear`: the zones, counts, seen names, marks and weights cleared.

Main result: **`swBack_exec`** (the three parts of `splitW` by `splitW_eq_sp`, and the state
between splits `SWB` again).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {W : ℕ} {P : Input}

/-- The names of the pieces and the balanced split. -/
def swPieces : Stmt :=
  .seq (block [.addN 1350 1203 1204, .constN 1351 0]) (.seq spPc
    (.seq (block [.copyN 1352 1391, .copyN 1353 1392, .copyN 1354 1394, .constN 1355 5,
      .addN 1356 1404 1404, .addN 1356 1356 1404]) bsProg))

/-- The separator and the two parts. -/
def swOut : Stmt :=
  .seq (block [.copyN 1321 1420, .copyN 1322 1421]) (.seq dCopy (.seq spMk2
    (.seq (.instr (.copyN 1329 1422)) (.seq dPassB (.seq (.instr (.subN 1423 1330 1422))
    (.seq spMk1 (.seq dPassA (.seq (.instr (.subN 1424 1329 1420))
    (.seq dPassB (.instr (.subN 1425 1330 1329)))))))))))

/-- The zeros on the arrays of the split and on the weights. -/
def swClear : Stmt :=
  .seq (spClr 1390) (.seq (spClr 1391) (.seq (spClr 1392) (.seq (spClr 1393)
    (.seq (spClr 1394) (spClr 1014)))))

/-- The back of the split. -/
def swBack : Stmt := .seq swPieces (.seq swOut swClear)

/-- The registers written by the back. -/
def pB (r : ℕ) : Bool :=
  r == 1201 || (1320 ≤ r && r ≤ 1332) || (1350 ≤ r && r ≤ 1387) || (1410 ≤ r && r ≤ 1418) ||
    (1423 ≤ r && r ≤ 1425)

theorem swBack_wok : swBack.wok pB = true := by decide

theorem lsum_le_sq {x : ℕ → ℕ} {l : List ℕ} {B : ℕ} (hl : l.length ≤ N) (hx : ∀ i, x i ≤ B) :
    lsum x l ≤ N * B := by
  unfold lsum
  refine (List.sum_le_length_nsmul _ B (fun y hy => ?_)).trans ?_
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy; exact hx i
  · rw [List.length_map, smul_eq_mul]; exact Nat.mul_le_mul_right _ hl

theorem length_spList_le (p : ℕ → ℕ) (D : Finset (Fin N)) : (spList p D).length ≤ N := by
  rw [spList_eq_range']; exact length_dedup_range'_le p D _ N

/-- The state of the division of `splitW` from the zero flags and names. -/
noncomputable abbrev swSt {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (U : Finset (Fin N)) : DSt :=
  spSt (square G) (sqSep hR hΔ) U ⟨fun _ => 0, fun _ => 0⟩

set_option maxHeartbeats 4000000 in
/-- **The back of the split**: after the division, the separator `U ∩ S` of `splitW` at `aO`,
the two parts at `aW` (sizes in `1423`, `1424`, `1425`), and the state between splits. -/
theorem swBack_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {μ : Fin N → ℕ}
    {Z M aS aP aV aF aZ aCW aCB aSn aJ aW aO : ℕ} {c : Config} {U : Finset (Fin N)}
    (hb : SBase G R μ Z W M c)
    (r10 : c.nreg 1310 = aS) (r11 : c.nreg 1311 = aP) (r12 : c.nreg 1312 = aV)
    (r13 : c.nreg 1313 = aF) (r89 : c.nreg 1389 = 2) (r90 : c.nreg 1390 = aZ)
    (r91 : c.nreg 1391 = aCW) (r92 : c.nreg 1392 = aCB) (r93 : c.nreg 1393 = aSn)
    (r94 : c.nreg 1394 = aJ) (r20 : c.nreg 1420 = aW) (r21 : c.nreg 1421 = #U)
    (r22 : c.nreg 1422 = aO) (r04 : c.nreg 1404 = #(bdry (square G) U))
    (lay1 : c.nreg 1203 + N ≤ aS) (lay2 : aS + N ≤ aP) (lay3 : aP + N ≤ aV)
    (lay4 : aV + N ≤ aF) (lay5 : aF + 3 * (N + 1) ≤ aZ) (lay6 : aZ + N ≤ aCW)
    (lay7 : aCW + N ≤ aCB) (lay8 : aCB + N ≤ aSn) (lay9 : aSn + N ≤ aJ) (lay10 : aJ + N ≤ W)
    (lW : aJ + N ≤ aW) (lW' : aW + N ≤ W) (lO : aJ + N ≤ aO) (lO' : aO + N ≤ W)
    (ldisj : aO + #U ≤ aW ∨ aW + #U ≤ aO) (hMN : M + N ≤ W) (hM : 40 * (N * N + 1) ≤ M)
    (hsf : ∀ x < N, c.nmem (aS + x) = (swSt hR hΔ U).sf x)
    (hpid : ∀ x < N, c.nmem (aP + x) = (swSt hR hΔ U).pid x)
    (hZ : ∀ x < N, c.nmem (aZ + x) =
      if x ∈ UN U then 1 else if x ∈ UN (closedNbhd G (closedNbhd G U)) then 2 else 0)
    (zCW : ∀ x < N, c.nmem (aCW + x) = 0) (zCB : ∀ x < N, c.nmem (aCB + x) = 0)
    (zSn : ∀ x < N, c.nmem (aSn + x) = 0) (zJ : ∀ x < N, c.nmem (aJ + x) = 0)
    (hl : ∀ l < #U, c.nmem (aW + l) = lv U l) :
    ∃ c' k, Exec P W swBack c c' k ∧ k ≤ 300 * N + 300 ∧
      SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ c' ∧
      c'.nreg 1423 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1,
        c'.nmem (aO + t) = lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 t) ∧
      c'.nreg 1424 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1,
        c'.nmem (aW + t) = lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 t) ∧
      c'.nreg 1425 = #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2 ∧
      (∀ t < #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2,
        c'.nmem (aW + #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 + t) =
          lv (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2 t) ∧
      (∀ r, pB r = false → c'.nreg r = c.nreg r) ∧
      (∀ a, aJ + N ≤ a → (a < aO ∨ aO + #U ≤ a) → (a < aW ∨ aW + #U ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  have hw := hb.wb
  have := hb.lU; have := hb.lC; have := hb.lQ; have := hb.lW; have := hb.lS; have := hb.l0
  have := hb.l1; have := hb.l2; have := hb.l3; have := hb.l4; have := hb.l5; have := hb.l6
  have := hb.l7; have := hb.lA; have := hb.lB; have := hb.lF; have := hb.lV; have := hb.sw
  have hUN := card_le_N U
  have := hb.lZ
  set r1100 := c.nreg 1100
  set r1102 := c.nreg 1102
  set r1103 := c.nreg 1103
  set r1104 := c.nreg 1104
  set r1105 := c.nreg 1105
  set r1010 := c.nreg 1010
  set r1011 := c.nreg 1011
  set r1012 := c.nreg 1012
  set r1013 := c.nreg 1013
  set r1015 := c.nreg 1015
  set r1017 := c.nreg 1017
  set r1018 := c.nreg 1018
  set r1202 := c.nreg 1202
  have hNN : N ≤ N * N + 1 := Nat.le_succ_of_le (Nat.le_mul_self N)
  have hW40 : 40 * (N * N + 1) ≤ W := by spomega
  set st := swSt hR hΔ U with hst
  set Sm := univ.filter fun v : Fin N => st.sf v = 1 with hSm
  set B := bdry (square G) U with hBdef
  set D := closedNbhd G (closedNbhd G U) with hDdef
  have hbd : B = D \ U := bdry_square_eq U
  have hUD : U ⊆ D := (subset_closedNbhd U).trans (subset_closedNbhd _)
  have hDUB : U ∪ B = D := by rw [hbd, union_sdiff_of_subset hUD]
  have hBN := card_le_N B
  have hsepH : ∀ U' w, IsSeparation (square G) U' (sqSep hR hΔ U' w).1 (sqSep hR hΔ U' w).2.1
      (sqSep hR hΔ U' w).2.2 := fun U' w => ((ltRoutine R hR (ord N) mem_ord).square hΔ).isSeparation U' w
  obtain ⟨hf, -, -, hcκ⟩ := dv_spec hsepH (spMu (square G) U) (spL (square G) U) #(U ∪ B) (U ∪ B)
    ⟨fun _ => 0, fun _ => 0⟩
  have hstsf : ∀ x, st.sf x = if x ∈ UN (SepRoutine.divide (sqSep hR hΔ) (spMu (square G) U)
      (spL (square G) U) #(U ∪ B) (U ∪ B)).1 then 1 else 0 := fun x => congrFun hf x
  have hsf01 : ∀ x, st.sf x = 0 ∨ st.sf x = 1 := fun x => by
    rw [hstsf x]; split_ifs <;> simp
  have hSmd : Sm = (SepRoutine.divide (sqSep hR hΔ) (spMu (square G) U) (spL (square G) U)
      #(U ∪ B) (U ∪ B)).1 := by
    ext v
    simp only [Sm, mem_filter, mem_univ, true_and]
    rw [hstsf]
    by_cases h : (v : ℕ) ∈ UN (SepRoutine.divide (sqSep hR hΔ) (spMu (square G) U)
      (spL (square G) U) #(U ∪ B) (U ∪ B)).1
    · rw [iteT h]; exact ⟨fun _ => val_mem_UN.1 h, fun _ => rfl⟩
    · rw [iteF h]; exact ⟨fun h' => absurd h' (by spomega), fun h' => absurd (val_mem_UN.2 h') h⟩
  have hpidN : ∀ x ∈ UN ((U ∪ B) \ Sm), st.pid x < N := fun x hx => by
    obtain ⟨hxN, hm⟩ := mem_UN.1 hx
    rw [hSmd] at hm
    have := (hcκ _ hm).1
    simp only [st, swSt, spSt]
    rw [show x = ((⟨x, hxN⟩ : Fin N) : ℕ) from rfl, this]
    exact lt_of_mem_UN (lv_zero_mem (hcκ _ hm).2.1)
  have hpidle : ∀ x, st.pid x ≤ N := dv_pid_le _ _ _ _ _ _ (fun _ => Nat.zero_le _)
  have hsplit := splitW_eq_sp hsepH U ⟨fun _ => 0, fun _ => 0⟩ (fun _ => rfl)
  -- the pieces pass
  set aL := c.nreg 1203 with haL
  obtain ⟨c₀, k₀, e₀, hk₀, hw₀, g50, g51, gm₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.addN 1350 1203 1204, .constN 1351 0]) c c₀ k₀ ∧ k₀ = 2 ∧ WordsBounded W c₀ ∧
      c₀.nreg 1350 = aL + N ∧ c₀.nreg 1351 = 0 ∧ c₀.nmem = c.nmem := by
    exec_block
    · rw [hb.nN]; spomega
    · spomega
    · exact ⟨rfl, ‹_›, by config_simp; rw [hb.nN], by config_simp, rfl⟩
  have K₀ : ∀ r, pB r = false → c₀.nreg r = c.nreg r := fun r hr =>
    Exec.nreg_of_wok e₀ (by decide) hr
  obtain ⟨c₁, k₁, e₁, hw₁, g51₁, g50₁, gl₁, gcw₁, gcb₁, gm₁, -, hk₁⟩ := spPc_exec (P := P)
    (X := U) (Y := B) (S := Sm) (p := st.pid) (aZ := aZ) (aS := aS) (aP := aP) (aW := aCW)
    (aB := aCB) (aN := aSn) (aL := aL) hw₀ (by rw [hbd]; exact disjoint_sdiff) hpidN
    (by rw [K₀ 1001 (by decide)]; exact hb.one) (by rw [K₀ 0 (by decide)]; exact hb.r0)
    (by rw [K₀ 1204 (by decide)]; exact hb.nN) (by rw [K₀ 1389 (by decide)]; exact r89)
    (by rw [K₀ 1390 (by decide)]; exact r90) (by rw [K₀ 1310 (by decide)]; exact r10)
    (by rw [K₀ 1311 (by decide)]; exact r11) (by rw [K₀ 1391 (by decide)]; exact r91)
    (by rw [K₀ 1392 (by decide)]; exact r92) (by rw [K₀ 1393 (by decide)]; exact r93) g50 g51
    (fun x hx => by
      rw [gm₀, hZ x hx]
      by_cases hxU : x ∈ UN U
      · rw [iteT hxU, iteT hxU]
      · rw [iteF hxU, iteF hxU, hbd]
        congr 1
        exact propext ⟨fun h => mem_UN_sdiff.2 ⟨h, hxU⟩, fun h => (mem_UN_sdiff.1 h).1⟩)
    (fun x hx => by rw [gm₀, hsf x hx]; exact sf_eq_UN hsf01 hx)
    (fun x hx => by rw [gm₀, hpid x (lt_of_mem_UN hx)])
    (fun i hi => by rw [gm₀]; exact zCW i hi) (fun i hi => by rw [gm₀]; exact zCB i hi)
    (fun i hi => by rw [gm₀]; exact zSn i hi)
    (by spomega) (by spomega) (by spomega) (by spomega) (by spomega) (by spomega) (by spomega) (by spomega)
  have K₁ : ∀ r, pB r = false → c₁.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁ (by decide) hr, K₀ r hr]
  set l := spList st.pid ((U ∪ B) \ Sm) with hldef
  have hlN : l.length ≤ N := length_spList_le _ _
  -- the balanced split
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, g52, g53, g54, g55, g56, g50₂, g51₂, gm₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 1352 1391, .copyN 1353 1392, .copyN 1354 1394, .constN 1355 5,
        .addN 1356 1404 1404, .addN 1356 1356 1404]) c₁ c₂ k₂ ∧ k₂ = 6 ∧ WordsBounded W c₂ ∧
      c₂.nreg 1352 = aCW ∧ c₂.nreg 1353 = aCB ∧ c₂.nreg 1354 = aJ ∧ c₂.nreg 1355 = 5 ∧
      c₂.nreg 1356 = 3 * #B ∧ c₂.nreg 1350 = aL + N - l.length ∧ c₂.nreg 1351 = l.length ∧
      c₂.nmem = c₁.nmem := by
    have e04 : c₁.nreg 1404 = #B := by rw [K₁ 1404 (by decide)]; exact r04
    exec_block
    · spomega
    · config_simp; rw [e04]; spomega
    · config_simp; rw [e04]; spomega
    · refine ⟨rfl, ‹_›, by config_simp; rw [K₁ 1391 (by decide)]; exact r91,
        by config_simp; rw [K₁ 1392 (by decide)]; exact r92,
        by config_simp; rw [K₁ 1394 (by decide)]; exact r94, by config_simp,
        by config_simp; rw [e04]; spomega, by config_simp; exact g50₁,
        by config_simp; exact g51₁, rfl⟩
  have K₂ : ∀ r, pB r = false → c₂.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₂ (by decide) hr, K₁ r hr]
  have hLL : LLay N W l c₂ :=
    ⟨hw₂, by rw [K₂ 1001 (by decide)]; exact hb.one, g51₂,
      fun t ht => by rw [g50₂, gm₂]; exact gl₁ t ht,
      fun t ht => by
        rw [hldef, spList_eq_range'] at ht ⊢
        exact lt_of_mem_dedup_range' hpidN (List.getD_eq_getElem _ _ ht ▸ List.getElem_mem ht),
      by rw [g50₂]; spomega⟩
  have hcwle : ∀ i, spCnt st.pid (U \ Sm) i ≤ N := fun i => (card_filter_le _ _).trans (card_le_N _)
  have hcble : ∀ i, spCnt st.pid (B \ Sm) i ≤ N := fun i => (card_filter_le _ _).trans (card_le_N _)
  obtain ⟨c₃, k₃, e₃, hw₃, gj₃, gm₃, gq₃, hk₃⟩ := bsProg_exec (P := P) hLL
    (spCnt st.pid (U \ Sm)) (spCnt st.pid (B \ Sm)) g52 g53 g54 g55 g56
    (fun i hi => by rw [gm₂]; exact gcw₁ i hi) (fun i hi => by rw [gm₂]; exact gcb₁ i hi)
    (by spomega) (by spomega) (by spomega) (Or.inl (by rw [g50₂]; spomega))
    (by have := lsum_le_sq hlN hcwle; spomega) (by have := lsum_le_sq hlN hcble; spomega) (by spomega)
  have K₃ : ∀ r, pB r = false → c₃.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₃ (by decide) hr, K₂ r hr]
  set J := bsplit (spCnt st.pid (U \ Sm)) (spCnt st.pid (B \ Sm)) 5 (3 * #B) l with hJ
  have hJm : ∀ i < N, c₃.nmem (aJ + i) = if i ∈ J then 1 else 0 := fun i hi => by
    rw [gj₃ i hi, gm₂, gm₁ _ (Or.inr (by spomega)) (Or.inr (by spomega)), gm₀, zJ i hi]
  have M₃ : ∀ a, (a < aL ∨ aL + N ≤ a) → (a < aCW ∨ aJ + N ≤ a) → c₃.nmem a = c.nmem a :=
    fun a h1 h2 => by
      rw [gm₃ a (by spomega), gm₂, gm₁ a h1 (by spomega), gm₀]
  -- the copy of the list of `U`
  set a0 := c.nreg 1200 with ha0
  set am := c.nreg 1019 with ham
  obtain ⟨c₄, k₄, e₄, hk₄, hw₄, g21, g22, gm₄⟩ : ∃ c₄ k₄, Exec P W
      (block [.copyN 1321 1420, .copyN 1322 1421]) c₃ c₄ k₄ ∧ k₄ = 2 ∧ WordsBounded W c₄ ∧
      c₄.nreg 1321 = aW ∧ c₄.nreg 1322 = #U ∧ c₄.nmem = c₃.nmem := by
    exec_block
    exact ⟨rfl, ‹_›, by config_simp; rw [K₃ 1420 (by decide)]; exact r20,
      by config_simp; rw [K₃ 1421 (by decide)]; exact r21, rfl⟩
  have K₄ : ∀ r, pB r = false → c₄.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₄ (by decide) hr, K₃ r hr]
  obtain ⟨c₅, k₅, e₅, hw₅, g01₅, gl₅, gm₅, -, hk₅⟩ := dCopy_exec (P := P) (U := U) (a0 := a0) hw₄
    (by rw [K₄ 1001 (by decide)]; exact hb.one) g21 g22 (K₄ 1200 (by decide))
    (fun j hj => by rw [gm₄, M₃ _ (Or.inr (by spomega)) (Or.inr (by spomega))]; exact hl j hj)
    (Or.inr (by spomega)) (by spomega) (by spomega)
  have K₅ : ∀ r, pB r = false → c₅.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₅ (by decide) hr, K₄ r hr]
  have g22₅ : c₅.nreg 1322 = #U := by rw [Exec.nreg_of_wr e₅ (by decide)]; exact g22
  have M₅ : ∀ a, (a < a0 ∨ a0 + N ≤ a) → c₅.nmem a = c₃.nmem a := fun a ha => by
    rw [gm₅ a ha, gm₄]
  have vS : ∀ v : Fin N, c₅.nmem (aS + v) = st.sf v := fun v => by
    rw [M₅ _ (Or.inr (by spomega)), M₃ _ (Or.inr (by spomega)) (Or.inl (by spomega))]
    exact hsf v v.2
  -- the marks `2 sf`
  obtain ⟨c₆, k₆, e₆, hw₆, hm₆, gm₆, -, hk₆⟩ := spMk2_exec (P := P) (U := U) (a0 := a0) (am := am)
    (aS := aS) hw₅ (by rw [K₅ 1001 (by decide)]; exact hb.one) (K₅ 1200 (by decide)) g01₅
    (K₅ 1019 (by decide)) (by rw [K₅ 1310 (by decide)]; exact r10) gl₅
    (fun v _ => by rw [vS]; rcases hsf01 v with h | h <;> spomega) (by spomega) (by spomega) (by spomega)
    (by spomega)
  have K₆ : ∀ r, pB r = false → c₆.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₆ (by decide) hr, K₅ r hr]
  have hmem : ∀ v : Fin N, v ∈ Sm ↔ st.sf v = 1 := fun v => by simp [Sm]
  -- the separator to the output buffer
  obtain ⟨c₇, k₇, e₇, hk₇, hw₇, g29, gm₇⟩ : ∃ c₇ k₇, Exec P W (.instr (.copyN 1329 1422)) c₆ c₇ k₇ ∧
      k₇ = 1 ∧ WordsBounded W c₇ ∧ c₇.nreg 1329 = aO ∧ c₇.nmem = c₆.nmem := by
    refine spec_instr (Exec.copyN hw₆ _ _) fun hw' => ?_
    exact ⟨rfl, hw', by config_simp; rw [K₆ 1422 (by decide)]; exact r22, rfl⟩
  have K₇ : ∀ r, pB r = false → c₇.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₇ (by decide) hr, K₆ r hr]
  have g22₇ : c₇.nreg 1322 = #U := by
    rw [Exec.nreg_of_wr e₇ (by decide), Exec.nreg_of_wr e₆ (by decide)]; exact g22₅
  have hUS : (U \ Sm) ∪ ∅ ∪ (U ∩ Sm) = U := by
    rw [union_empty, sdiff_union_inter]
  have hSU : #(U ∩ Sm) ≤ #U := card_le_card inter_subset_left
  obtain ⟨c₈, k₈, e₈, hw₈, g30₈, gS₈, gm₈, -, hk₈⟩ := dPassB_exec (P := P) (U := U) (a0 := a0)
    (am := am) (p0 := aO) hw₇ hUS
    (fun v hv => by
      rw [gm₇, hm₆ v hv, vS]
      rcases hsf01 v with h | h
      · rw [h]; simp [mem_sdiff, hv, hmem, h]
      · rw [h]; simp [mem_inter, hv, hmem, h])
    (by rw [K₇ 1001 (by decide)]; exact hb.one) g29 g22₇ (K₇ 1200 (by decide)) (K₇ 1019 (by decide))
    (fun l' hl' => by rw [gm₇, gm₆ _ (Or.inr (by spomega))]; exact gl₅ l' hl')
    (by spomega) (by spomega) (by spomega) (by spomega)
  have K₈ : ∀ r, pB r = false → c₈.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₈ (by decide) hr, K₇ r hr]
  obtain ⟨c₉, k₉, e₉, hk₉, hw₉, g23, gm₉⟩ : ∃ c₉ k₉, Exec P W (.instr (.subN 1423 1330 1422)) c₈ c₉ k₉ ∧
      k₉ = 1 ∧ WordsBounded W c₉ ∧ c₉.nreg 1423 = #(U ∩ Sm) ∧ c₉.nmem = c₈.nmem := by
    refine spec_instr (Exec.subN hw₈ _ _ _) fun hw' => ?_
    exact ⟨rfl, hw', by config_simp; rw [g30₈, K₈ 1422 (by decide), r22]; spomega, rfl⟩
  have K₉ : ∀ r, pB r = false → c₉.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₉ (by decide) hr, K₈ r hr]
  have N₉ : ∀ a, (a < am ∨ am + N ≤ a) → (a < a0 ∨ a0 + N ≤ a) → (a < aO ∨ aO + #U ≤ a) →
      c₉.nmem a = c₃.nmem a := fun a h1 h2 h3 => by
    rw [gm₉, gm₈ a (by spomega), gm₇, gm₆ a h1, M₅ a h2]
  have g01₉ : c₉.nreg 1201 = #U := by
    rw [Exec.nreg_of_wr e₉ (by decide), Exec.nreg_of_wr e₈ (by decide),
      Exec.nreg_of_wr e₇ (by decide), Exec.nreg_of_wr e₆ (by decide)]; exact g01₅
  have g22₉ : c₉.nreg 1322 = #U := by
    rw [Exec.nreg_of_wr e₉ (by decide), Exec.nreg_of_wr e₈ (by decide)]; exact g22₇
  have g21₉ : c₉.nreg 1321 = aW := by
    rw [Exec.nreg_of_wr e₉ (by decide), Exec.nreg_of_wr e₈ (by decide),
      Exec.nreg_of_wr e₇ (by decide), Exec.nreg_of_wr e₆ (by decide),
      Exec.nreg_of_wr e₅ (by decide)]; exact g21
  have gl₉ : ∀ l' < #U, c₉.nmem (a0 + l') = lv U l' := fun l' hl' => by
    rw [gm₉, gm₈ _ (Or.inl (by spomega)), gm₇, gm₆ _ (Or.inr (by spomega))]; exact gl₅ l' hl'
  have vS₉ : ∀ v : Fin N, c₉.nmem (aS + v) = st.sf v := fun v => by
    rw [N₉ _ (Or.inr (by spomega)) (Or.inr (by spomega)) (Or.inl (by spomega)),
      M₃ _ (Or.inr (by spomega)) (Or.inl (by spomega))]; exact hsf v v.2
  have vP₉ : ∀ v : Fin N, c₉.nmem (aP + v) = st.pid v := fun v => by
    rw [N₉ _ (Or.inr (by spomega)) (Or.inr (by spomega)) (Or.inl (by spomega)),
      M₃ _ (Or.inr (by spomega)) (Or.inl (by spomega))]; exact hpid v v.2
  have vJ₉ : ∀ i < N, c₉.nmem (aJ + i) = if i ∈ J then 1 else 0 := fun i hi => by
    rw [N₉ _ (Or.inr (by spomega)) (Or.inr (by spomega)) (Or.inl (by spomega))]; exact hJm i hi
  -- the marks of the two parts
  obtain ⟨c₁₀, k₁₀, e₁₀, hw₁₀, hm₁₀, gm₁₀, -, hk₁₀⟩ := spMk1_exec (P := P) (U := U) (a0 := a0)
    (am := am) (aS := aS) (aP := aP) (aJ := aJ) hw₉ (by rw [K₉ 1001 (by decide)]; exact hb.one)
    (K₉ 1200 (by decide)) g01₉ (K₉ 1019 (by decide)) (by rw [K₉ 1310 (by decide)]; exact r10)
    (by rw [K₉ 1311 (by decide)]; exact r11) (by rw [K₉ 1394 (by decide)]; exact r94)
    (by rw [K₉ 1389 (by decide)]; exact r89) gl₉ (fun v _ => by rw [vP₉]; exact hpidle v)
    (by spomega) (by spomega) (by spomega) (by spomega) (by spomega) (by spomega)
  have K₁₀ : ∀ r, pB r = false → c₁₀.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₀ (by decide) hr, K₉ r hr]
  set A := (U \ Sm).filter (fun v : Fin N => st.pid v ∈ J) with hA
  set A' := (U \ Sm).filter (fun v : Fin N => st.pid v ∉ J) with hA'
  have hUA : (U ∩ Sm) ∪ A ∪ A' = U := by
    ext v; simp only [hA, hA', mem_union, mem_inter, mem_filter, mem_sdiff]; tauto
  have hmk : ∀ v ∈ U, (c₁₀.nmem (am + v) = 0 ↔ v ∈ U ∩ Sm) ∧ (c₁₀.nmem (am + v) = 1 ↔ v ∈ A) ∧
      (c₁₀.nmem (am + v) = 2 ↔ v ∈ A') := fun v hv => by
    rw [hm₁₀ v hv, vS₉, vP₉]
    rcases hsf01 v with h | h
    · have hvD : (v : ℕ) ∈ UN ((U ∪ B) \ Sm) :=
        val_mem_UN.2 (mem_sdiff.2 ⟨mem_union_left _ hv, fun h' => by
          rw [hmem] at h'; spomega⟩)
      have hvS : v ∉ Sm := fun h' => by rw [hmem] at h'; spomega
      rw [vJ₉ _ (hpidN _ hvD), h]
      by_cases hj : st.pid v ∈ J
      · rw [iteT hj]; simp [hA, hA', hv, hvS, hj]
      · rw [iteF hj]; simp [hA, hA', hv, hvS, hj]
    · have hvS : v ∈ Sm := (hmem v).2 h
      rw [h]; simp [hA, hA', hv, hvS]
  have hAU : #A + #A' ≤ #U := by
    rw [← card_union_of_disjoint (disjoint_filter_filter_not _ _ _)]
    exact card_le_card (union_subset (fun v hv => (mem_sdiff.1 (mem_filter.1 hv).1).1)
      (fun v hv => (mem_sdiff.1 (mem_filter.1 hv).1).1))
  have gl₁₀ : ∀ l' < #U, c₁₀.nmem (a0 + l') = lv U l' := fun l' hl' => by
    rw [gm₁₀ _ (Or.inr (by spomega))]; exact gl₉ l' hl'
  obtain ⟨c₁₁, k₁₁, e₁₁, hw₁₁, g29₁₁, gA₁₁, -, gm₁₁, -, -, hk₁₁⟩ := dPassA_exec (P := P) (U := U)
    (s := aW) (a0 := a0) (am := am) (aS := aS) hw₁₀ hUA hmk
    (by rw [K₁₀ 1001 (by decide)]; exact hb.one)
    (by rw [Exec.nreg_of_wr e₁₀ (by decide)]; exact g21₉)
    (by rw [Exec.nreg_of_wr e₁₀ (by decide)]; exact g22₉) (K₁₀ 1200 (by decide))
    (K₁₀ 1019 (by decide)) (by rw [K₁₀ 1310 (by decide)]; exact r10) gl₁₀
    (by spomega) (by spomega) (by spomega) (by spomega) (by spomega)
  have K₁₁ : ∀ r, pB r = false → c₁₁.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₁ (by decide) hr, K₁₀ r hr]
  obtain ⟨c₁₂, k₁₂, e₁₂, hk₁₂, hw₁₂, g24, gm₁₂⟩ : ∃ c₁₂ k₁₂,
      Exec P W (.instr (.subN 1424 1329 1420)) c₁₁ c₁₂ k₁₂ ∧
      k₁₂ = 1 ∧ WordsBounded W c₁₂ ∧ c₁₂.nreg 1424 = #A ∧ c₁₂.nmem = c₁₁.nmem := by
    refine spec_instr (Exec.subN hw₁₁ _ _ _) fun hw' => ?_
    exact ⟨rfl, hw', by config_simp; rw [g29₁₁, K₁₁ 1420 (by decide), r20]; spomega, rfl⟩
  have K₁₂ : ∀ r, pB r = false → c₁₂.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₂ (by decide) hr, K₁₁ r hr]
  obtain ⟨c₁₃, k₁₃, e₁₃, hw₁₃, g30₁₃, gA'₁₃, gm₁₃, -, hk₁₃⟩ := dPassB_exec (P := P) (U := U)
    (a0 := a0) (am := am) (p0 := aW + #A) hw₁₂ hUA
    (fun v hv => by
      rw [gm₁₂, gm₁₁ _ (Or.inl (by have := v.2; spomega)) (Or.inl (by have := v.2; spomega))]
      exact hmk v hv)
    (by rw [K₁₂ 1001 (by decide)]; exact hb.one)
    (by rw [Exec.nreg_of_wr e₁₂ (by decide)]; exact g29₁₁)
    (by rw [Exec.nreg_of_wr e₁₂ (by decide), Exec.nreg_of_wr e₁₁ (by decide),
      Exec.nreg_of_wr e₁₀ (by decide)]; exact g22₉) (K₁₂ 1200 (by decide))
    (K₁₂ 1019 (by decide))
    (fun l' hl' => by
      rw [gm₁₂, gm₁₁ _ (Or.inl (by spomega)) (Or.inl (by spomega))]; exact gl₁₀ l' hl')
    (by spomega) (by spomega) (by spomega) (by spomega)
  have K₁₃ : ∀ r, pB r = false → c₁₃.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₃ (by decide) hr, K₁₂ r hr]
  obtain ⟨c₁₄, k₁₄, e₁₄, hk₁₄, hw₁₄, g25, gm₁₄⟩ : ∃ c₁₄ k₁₄,
      Exec P W (.instr (.subN 1425 1330 1329)) c₁₃ c₁₄ k₁₄ ∧
      k₁₄ = 1 ∧ WordsBounded W c₁₄ ∧ c₁₄.nreg 1425 = #A' ∧ c₁₄.nmem = c₁₃.nmem := by
    refine spec_instr (Exec.subN hw₁₃ _ _ _) fun hw' => ?_
    refine ⟨rfl, hw', ?_, rfl⟩
    config_simp
    rw [g30₁₃, Exec.nreg_of_wr e₁₃ (by decide), Exec.nreg_of_wr e₁₂ (by decide), g29₁₁]
    omega
  have K₁₄ : ∀ r, pB r = false → c₁₄.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₄ (by decide) hr, K₁₃ r hr]
  -- the zeros
  have Z1 : ∀ c₀' : Config, (∀ r, pB r = false → c₀'.nreg r = c.nreg r) →
      c₀'.nreg 1001 = 1 ∧ c₀'.nreg 0 = 0 ∧ c₀'.nreg 1204 = N := fun c₀' K =>
    ⟨by rw [K 1001 (by decide)]; exact hb.one, by rw [K 0 (by decide)]; exact hb.r0,
      by rw [K 1204 (by decide)]; exact hb.nN⟩
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₄ K₁₄
  obtain ⟨c₁₅, k₁₅, e₁₅, hw₁₅, hz₁₅, gm₁₅, -, hk₁₅⟩ := spClr_exec (P := P) (N := N) (r := 1390)
    (b := aZ) hw₁₄ (by decide) (by decide) z1 z2 z3 (by rw [K₁₄ 1390 (by decide)]; exact r90)
    (by spomega)
  have K₁₅ : ∀ r, pB r = false → c₁₅.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₅ (by decide) hr, K₁₄ r hr]
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₅ K₁₅
  obtain ⟨c₁₆, k₁₆, e₁₆, hw₁₆, hz₁₆, gm₁₆, -, hk₁₆⟩ := spClr_exec (P := P) (N := N) (r := 1391)
    (b := aCW) hw₁₅ (by decide) (by decide) z1 z2 z3 (by rw [K₁₅ 1391 (by decide)]; exact r91)
    (by spomega)
  have K₁₆ : ∀ r, pB r = false → c₁₆.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₆ (by decide) hr, K₁₅ r hr]
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₆ K₁₆
  obtain ⟨c₁₇, k₁₇, e₁₇, hw₁₇, hz₁₇, gm₁₇, -, hk₁₇⟩ := spClr_exec (P := P) (N := N) (r := 1392)
    (b := aCB) hw₁₆ (by decide) (by decide) z1 z2 z3 (by rw [K₁₆ 1392 (by decide)]; exact r92)
    (by spomega)
  have K₁₇ : ∀ r, pB r = false → c₁₇.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₇ (by decide) hr, K₁₆ r hr]
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₇ K₁₇
  obtain ⟨c₁₈, k₁₈, e₁₈, hw₁₈, hz₁₈, gm₁₈, -, hk₁₈⟩ := spClr_exec (P := P) (N := N) (r := 1393)
    (b := aSn) hw₁₇ (by decide) (by decide) z1 z2 z3 (by rw [K₁₇ 1393 (by decide)]; exact r93)
    (by spomega)
  have K₁₈ : ∀ r, pB r = false → c₁₈.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₈ (by decide) hr, K₁₇ r hr]
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₈ K₁₈
  obtain ⟨c₁₉, k₁₉, e₁₉, hw₁₉, hz₁₉, gm₁₉, -, hk₁₉⟩ := spClr_exec (P := P) (N := N) (r := 1394)
    (b := aJ) hw₁₈ (by decide) (by decide) z1 z2 z3 (by rw [K₁₈ 1394 (by decide)]; exact r94)
    (by spomega)
  have K₁₉ : ∀ r, pB r = false → c₁₉.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e₁₉ (by decide) hr, K₁₈ r hr]
  obtain ⟨z1, z2, z3⟩ := Z1 c₁₉ K₁₉
  set aw := c.nreg 1014 with haw
  obtain ⟨c', k₂₀, e₂₀, hw', hz₂₀, gm₂₀, -, hk₂₀⟩ := spClr_exec (P := P) (N := N) (r := 1014)
    (b := aw) hw₁₉ (by decide) (by decide) z1 z2 z3 (K₁₉ 1014 (by decide)) (by spomega)
  have e : Exec P W swBack c c' (k₀ + (k₁ + (k₂ + k₃)) + ((k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ +
      (k₁₀ + (k₁₁ + (k₁₂ + (k₁₃ + k₁₄)))))))))) + (k₁₅ + (k₁₆ + (k₁₇ + (k₁₈ + (k₁₉ + k₂₀))))))) :=
    .seq (.seq e₀ (.seq e₁ (.seq e₂ e₃))) (.seq (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈
      (.seq e₉ (.seq e₁₀ (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ e₁₄))))))))))
      (.seq e₁₅ (.seq e₁₆ (.seq e₁₇ (.seq e₁₈ (.seq e₁₉ e₂₀))))))
  have K' : ∀ r, pB r = false → c'.nreg r = c.nreg r := fun r hr => by
    rw [Exec.nreg_of_wok e swBack_wok hr]
  have eT14 := Exec.seq e₁₅ (.seq e₁₆ (.seq e₁₇ (.seq e₁₈ (.seq e₁₉ e₂₀))))
  have eT12 := Exec.seq e₁₃ (.seq e₁₄ eT14)
  have eT9 := Exec.seq e₁₀ (.seq e₁₁ (.seq e₁₂ eT12))
  have rr : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := Exec.real_of_noReal e (by decide)
  have ou : c'.output = c.output := Exec.output_of_ou e (by decide)
  -- the memory
  have C20 : ∀ a, (a < aZ ∨ aJ + N ≤ a) → (a < aw ∨ aw + N ≤ a) → c'.nmem a = c₁₄.nmem a :=
    fun a h1 h2 => by
      rw [gm₂₀ a h2, gm₁₉ a (by spomega), gm₁₈ a (by spomega), gm₁₇ a (by spomega),
        gm₁₆ a (by spomega), gm₁₅ a (by spomega)]
  have C14 : ∀ a, (a < aZ ∨ aJ + N ≤ a) → (a < aw ∨ aw + N ≤ a) → (a < am ∨ am + N ≤ a) →
      (a < a0 ∨ a0 + N ≤ a) → (a < aO ∨ aO + #U ≤ a) → (a < aS ∨ aS + N ≤ a) →
      (a < aW ∨ aW + #U ≤ a) → c'.nmem a = c₃.nmem a := fun a h1 h2 h3 h4 h5 h6 h7 => by
    rw [C20 a h1 h2, gm₁₄, gm₁₃ a (by spomega), gm₁₂, gm₁₁ a h6 (by spomega), gm₁₀ a h3,
      N₉ a h3 h4 h5]
  have hbase : SBase G R (fun _ => 0) Z W M c' := hb.congr' hw'
    (fun r hr h1 => K' r (by unfold KeptS at hr; simp only [pB]; simp; spomega))
    (fun a ha => by
      have ha' : (a < aw ∨ (aw + N ≤ a ∧ a < am)) ∨ (r1202 ≤ a ∧ a < r1202 + N) := by
        rcases ha with ha | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; left; spomega
        · change r1010 ≤ a at h1; change a < aw at h2; left; left; spomega
        · change r1017 ≤ a at h1; change a < am at h2; left; right; spomega
        · change r1102 ≤ a at h1; change a < r1103 at h2; left; left; spomega
        · change r1104 ≤ a at h1; change a < r1010 at h2; left; left; spomega
        · change r1202 ≤ a at h1; change a < r1202 + N at h2; right; spomega
      rcases ha' with (ha' | ha') | ha'
      · rw [C14 a (Or.inl (by spomega)) (Or.inl ha') (Or.inl (by spomega)) (Or.inl (by spomega))
          (Or.inl (by spomega)) (Or.inl (by spomega)) (Or.inl (by spomega)),
          M₃ a (Or.inl (by spomega)) (Or.inl (by spomega))]
      · rw [C14 a (Or.inl (by spomega)) (Or.inr ha'.1) (Or.inl ha'.2) (Or.inl (by spomega))
          (Or.inl (by spomega)) (Or.inl (by spomega)) (Or.inl (by spomega)),
          M₃ a (Or.inl (by spomega)) (Or.inl (by spomega))]
      · rw [C14 a (Or.inl (by spomega)) (Or.inr (by spomega)) (Or.inr (by spomega))
          (Or.inr (by spomega)) (Or.inl (by spomega)) (Or.inl (by spomega)) (Or.inl (by spomega)),
          M₃ a (Or.inl (by spomega)) (Or.inl (by spomega))])
    (fun v hv => by rw [hz₂₀ v hv]; simp [SepProg.wI]) (by simp) rr.1 rr.2
  have hS1 : #(U ∩ Sm) ≤ N := hSU.trans hUN
  have hsplit' : SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U = (U ∩ Sm, A, A') :=
    hsplit
  rw [hsplit']
  refine ⟨c', _, e, by spomega, ⟨hbase, by rw [K' 1310 (by decide)]; exact r10,
    by rw [K' 1311 (by decide)]; exact r11, by rw [K' 1312 (by decide)]; exact r12,
    by rw [K' 1313 (by decide)]; exact r13, by rw [K' 1390 (by decide)]; exact r90,
    by rw [K' 1391 (by decide)]; exact r91, by rw [K' 1392 (by decide)]; exact r92,
    by rw [K' 1393 (by decide)]; exact r93, by rw [K' 1394 (by decide)]; exact r94,
    by rw [K' 1203 (by decide)]; exact lay1, lay2, lay3, lay4, lay5, lay6, lay7, lay8, lay9,
    lay10, hMN, hM,
    fun x hx => by
      rw [gm₂₀ _ (Or.inr (by spomega)), gm₁₉ _ (Or.inl (by spomega)), gm₁₈ _ (Or.inl (by spomega)),
        gm₁₇ _ (Or.inl (by spomega)), gm₁₆ _ (Or.inl (by spomega))]; exact hz₁₅ x hx,
    fun x hx => by
      rw [gm₂₀ _ (Or.inr (by spomega)), gm₁₉ _ (Or.inl (by spomega)), gm₁₈ _ (Or.inl (by spomega)),
        gm₁₇ _ (Or.inl (by spomega))]; exact hz₁₆ x hx,
    fun x hx => by
      rw [gm₂₀ _ (Or.inr (by spomega)), gm₁₉ _ (Or.inl (by spomega)),
        gm₁₈ _ (Or.inl (by spomega))]; exact hz₁₇ x hx,
    fun x hx => by
      rw [gm₂₀ _ (Or.inr (by spomega)), gm₁₉ _ (Or.inl (by spomega))]; exact hz₁₈ x hx,
    fun x hx => by rw [gm₂₀ _ (Or.inr (by spomega))]; exact hz₁₉ x hx⟩,
    by rw [Exec.nreg_of_wr eT9 (by decide)]; exact g23, fun t ht => ?_,
    by rw [Exec.nreg_of_wr eT12 (by decide)]; exact g24, fun t ht => ?_,
    by rw [Exec.nreg_of_wr eT14 (by decide)]; exact g25,
    fun t ht => ?_, K', fun a h1 h2 h3 => ?_, ou⟩
  · dsimp only at ht ⊢
    have h1 : aO + t < aW ∨ aW + #U ≤ aO + t := by rcases ldisj with h | h <;> spomega
    rw [C20 (aO + t) (Or.inr (by spomega)) (Or.inr (by spomega)), gm₁₄,
      gm₁₃ (aO + t) (by spomega), gm₁₂, gm₁₁ (aO + t) (Or.inr (by spomega)) (by spomega),
      gm₁₀ (aO + t) (Or.inr (by spomega)), gm₉]
    exact gS₈ t ht
  · dsimp only at ht ⊢
    rw [C20 (aW + t) (Or.inr (by spomega)) (Or.inr (by spomega)), gm₁₄,
      gm₁₃ (aW + t) (Or.inl (by spomega)), gm₁₂]
    exact gA₁₁ t ht
  · dsimp only at ht ⊢
    rw [C20 (aW + #A + t) (Or.inr (by spomega)) (Or.inr (by spomega)), gm₁₄]
    exact gA'₁₃ t ht
  · rw [C14 a (Or.inr h1) (Or.inr (by spomega)) (Or.inr (by spomega)) (Or.inr (by spomega))
      h2 (Or.inr (by spomega)) h3, M₃ a (Or.inr (by spomega)) (Or.inr h1)]

end Piece

end PlanarSeparator
