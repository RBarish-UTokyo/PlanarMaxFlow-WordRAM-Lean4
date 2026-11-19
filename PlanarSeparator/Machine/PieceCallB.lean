module

public import PlanarSeparator.Machine.PieceCallA

/-!
# The program of a piece, second part: the input words of the separator program

From the state `S1` of the first passes: the layout (`setupB`: the output base `pP`, the base
`bB` and the length `lenL` of the input words, the bases of the offsets, weights and darts, the
words `k`, `m'`, `m'`), the second rank pass with the real bases and the dart pass. The words
at `bB` are then the words of `ltIn R (ord N) C w` (`data_eq`, from
`PlanarSeparator.Piece.ltIn_words`): **`front2_exec`**, the state `Mid`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G} {w : Fin N → ℕ} {C : Finset (Fin N)} {Z W : ℕ}

/-! ### The words of the piece -/

theorem rkA_of_inner {d : G.Dart} (h1 : d.fst ∈ C) (h2 : d.snd ∈ C) :
    rkA G C (dartNum G d) = rkC G C (dartNum G d) + 1 := by
  rw [rkA_dartNum]; simp [h1, h2]

variable (G R w C) in
/-- **The words at the base**, from the facts written by the passes. -/
theorem data_eq (f : ℕ → ℕ) (B : ℕ)
    (h0 : f 0 = #C) (h1 : f 1 = mI G C) (hO : ∀ j < #C, f (2 + j) = sC G C (lv C j))
    (hm : f (2 + #C) = mI G C) (hW : ∀ j < #C, f (#C + 3 + j) = SepProg.wI w (lv C j))
    (hD : ∀ j < #C, ∀ g, gofs G (lv C j) ≤ g → g < gofs G (lv C j + 1) → 0 < rkA G C g →
      f (2 * #C + 3 + 3 * (rkA G C g - 1)) = j ∧
      f (2 * #C + 3 + 3 * (rkA G C g - 1) + 1) = rkA G C (rvG G g) - 1 ∧
      f (2 * #C + 3 + 3 * (rkA G C g - 1) + 2) = rkA G C (frA G C R g) - 1)
    (hZ : ∀ i, lenL #C (mI G C) ≤ i → i < B → f i = 0) :
    ∀ i < B, f i = (ltIn R (ord N) C w).data.getD i 0 := by
  have hk := length_clist_ord C
  obtain ⟨hlen, hD0, hD1, hDO, hDm, hDW, hDd, hDall⟩ := ltIn_words G R C w
  simp only [hk] at hlen hD0 hD1 hDO hDm hDW hDd hDall
  set D := (ltIn R (ord N) C w).data
  set k := #C
  set m' := mI G C
  have hm' : #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C) = m' := rfl
  rw [hm'] at hlen hD1 hDm hDd hDall
  intro i hiB
  by_cases hi0 : i = 0
  · subst hi0; rw [h0, hD0]
  by_cases hi1 : i = 1
  · subst hi1; rw [h1, hD1]
  by_cases hiO : i < 2 + k
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
    have hj : j < k := by omega
    rw [hO j hj, hDO j (by omega), rkC_gofs, lv_eq C (by omega)]
  by_cases hik : i = 2 + k
  · subst hik; rw [hm, hDm]
  by_cases hiW : i < 2 * k + 3
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + 3 + j := ⟨i - (k + 3), by omega⟩
    have hj : j < k := by omega
    rw [hW j hj, hDW j (by omega), lv_eq C (by omega)]
    simp [SepProg.wI]
  by_cases hiD : i < lenL k m'
  · unfold lenL at hiD
    obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 3 ∧ i = 2 * k + 3 + 3 * t + r :=
      ⟨(i - (2 * k + 3)) / 3, (i - (2 * k + 3)) % 3, Nat.mod_lt _ (by omega), by omega⟩
    have ht : t < m' := by omega
    obtain ⟨d, hd1, hd2, hdt⟩ := hDall t ht
    obtain ⟨-, hDj, hDr, hDf⟩ := hDd d hd1 hd2
    obtain ⟨j, hj, hjd, hb1, hb2⟩ := block_of_mem G C d hd1
    have hrk : rkA G C (dartNum G d) = t + 1 := by
      rw [rkA_of_inner hd1 hd2, hdt]
    obtain ⟨f0, f1, f2⟩ := hD j (by omega) _ hb1 hb2 (by omega)
    rw [hrk, Nat.add_sub_cancel] at f0 f1 f2
    rw [hdt] at hDj hDr hDf
    interval_cases r
    · rw [Nat.add_zero, f0, hDj j (by omega) (Fin.ext (by rw [← lv_eq C]; exact hjd))]
    · rw [f1, hDr, rvG_dartNum, rkA_of_inner (d := d.symm) hd2 hd1]; rfl
    · have hA : d ∈ InducedRot.inDarts G (cemb (ord N) C) := (mem_inDarts_iff G C).2 ⟨hd1, hd2⟩
      have hr := (mem_inDarts_iff G C).1 (PlanarFlow.Orbit.ret_mem (π :=
        PlanarFlow.Orbit.rotPerm (PlanarFlow.CombMap.ofRotation R)) hA)
      rw [f2, hDf, frA_dartNum, rkA_of_inner hr.1 hr.2]; rfl
  · push Not at hiD
    rw [hZ i hiD hiB, List.getD_eq_default _ _ (by rw [hlen]; unfold lenL at hiD; omega)]

/-! ### The layout block -/

/-- **The layout**: `p` (in `1060` and `1064`), `β = p + K + 1` (`1062`), the length (`1063`),
the bases `β + 2`, `β + k + 3`, `β + 2k + 3` (`1050`–`1052`), and the words `β[0] = k`,
`β[1] = m'`, `β[k + 2] = m'`. -/
def setupB : Stmt :=
  block [.constN 1067 16, .mulN 1060 1037 1067, .constN 1067 12, .mulN 1068 1016 1067,
    .addN 1060 1060 1068, .constN 1067 3, .mulN 1068 1038 1067, .addN 1060 1060 1068,
    .constN 1067 23, .addN 1060 1060 1067, .copyN 1064 1060,
    .constN 1067 320, .mulN 1068 1037 1067, .constN 1067 191, .mulN 1069 1016 1067,
    .addN 1068 1068 1069, .constN 1067 404, .addN 1068 1068 1067, .addN 1062 1060 1068,
    .addN 1063 1016 1016, .constN 1067 3, .addN 1063 1063 1067, .mulN 1068 1037 1067,
    .addN 1063 1063 1068,
    .constN 1067 2, .addN 1050 1062 1067, .addN 1051 1050 1016, .addN 1051 1051 1001,
    .addN 1052 1051 1016,
    .storeN 1062 1016, .addN 1067 1062 1001, .storeN 1067 1037, .addN 1067 1050 1016,
    .storeN 1067 1037]

/-- The configuration after the layout block. -/
structure SetupPost (k m sw : ℕ) (d d' : Config) : Prop where
  r60 : d'.nreg 1060 = pP k m sw
  r64 : d'.nreg 1064 = pP k m sw
  r62 : d'.nreg 1062 = bB k m sw
  r63 : d'.nreg 1063 = lenL k m
  r50 : d'.nreg 1050 = bB k m sw + 2
  r51 : d'.nreg 1051 = bB k m sw + k + 3
  r52 : d'.nreg 1052 = bB k m sw + 2 * k + 3
  regs : ∀ r < 1030, d'.nreg r = d.nreg r
  m0 : d'.nmem (bB k m sw) = k
  m1 : d'.nmem (bB k m sw + 1) = m
  m2 : d'.nmem (bB k m sw + 2 + k) = m
  mo : ∀ a, a ≠ bB k m sw → a ≠ bB k m sw + 1 → a ≠ bB k m sw + 2 + k → d'.nmem a = d.nmem a

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem setupB_exec {P : Input} {d : Config} (hw : WordsBounded W d) {k m sw : ℕ}
    (h01 : d.nreg 1001 = 1) (h16 : d.nreg 1016 = k) (h37 : d.nreg 1037 = m)
    (h38 : d.nreg 1038 = sw) (hW : 2 * bB k m sw ≤ W) :
    ∃ d' t, Exec P W setupB d d' t ∧ WordsBounded W d' ∧ SetupPost k m sw d d' ∧ t = 34 := by
  unfold bB pP kK at hW
  unfold setupB
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp only [h01, h16, h37, h38]; omega)
  refine ⟨‹WordsBounded _ _›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_,
    fun a h1 h2 h3 => ?_⟩, rfl⟩
  rotate_right
  · simp only [bB, pP, kK] at h1 h2 h3
    config_simp
    simp only [h01, h16, h37, h38, upd_apply]
    split_ifs <;> first | omega | rfl
  all_goals config_simp
  all_goals simp only [h01, h16, h37, h38, upd_apply, bB, pP, kK, lenL]
  all_goals (try split_ifs) <;> first | omega | rfl

/-! ### The state before the separator program -/

variable (G R w C Z W) in
/-- **The state before the separator program**: the layout in registers, the zero cells below
`β`, the words of `ltIn R (ord N) C w` at `β`, the labels and ranks as in `S1`, the rest as
before. -/
structure Mid (c d : Config) : Prop where
  wb : WordsBounded W d
  regs : ∀ r, (r < 1000 ∨ Kept r) → d.nreg r = c.nreg r
  r60 : d.nreg 1060 = pP #C (mI G C) (∑ v ∈ C, w v)
  r64 : d.nreg 1064 = pP #C (mI G C) (∑ v ∈ C, w v)
  r62 : d.nreg 1062 = bB #C (mI G C) (∑ v ∈ C, w v)
  r63 : d.nreg 1063 = lenL #C (mI G C)
  low : ∀ a < bB #C (mI G C) (∑ v ∈ C, w v), d.nmem a = 0
  data : ∀ i, bB #C (mI G C) (∑ v ∈ C, w v) + i < Z →
    d.nmem (bB #C (mI G C) (∑ v ∈ C, w v) + i) = (ltIn R (ord N) C w).data.getD i 0
  lab : ∀ x < N, d.nmem (c.nreg 1017 + x) = labV C x
  rk : ∀ g < nD G, d.nmem (c.nreg 1018 + g) = rkA G C g
  rest : ∀ a, Z ≤ a → (a < c.nreg 1017 ∨ c.nreg 1017 + N ≤ a) →
    (a < c.nreg 1018 ∨ c.nreg 1018 + nD G ≤ a) → d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

/-- **The second part**: layout, ranks, darts. -/
def front2 : Stmt := .seq setupB (.seq rankLoop dartLoop)

end Piece

end PlanarSeparator
