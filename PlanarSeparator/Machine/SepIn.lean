module

public import PlanarSeparator.Machine.MillerA
public import PlanarSeparator.MillerFace

/-!
# The input of Miller's program: the coded stellar subdivisions

The split of a piece in the recursion for negative lengths (`PlanarFlow.NegSSSP.exists_cycle_cut`)
applies Miller's theorem with weights on darts to the stellar subdivision `kst = M.stellar` of
the piece map `M` (`exists_short_cycle_separator_card`), whose proof applies Miller's theorem
with weights on vertices to the stellar subdivision of `kst`
(`exists_short_cycle_separator_stellar`): the triangulation that `millerA` runs on is
`M.stellar.stellar`, with the weight of a dart of the piece on the centre of its triangle.

* **The plain encoding of a map** (`MillerProg.Enc`): the darts numbered `0 … m-1`, and arrays
  of the numbers of `α d`, `φ d`, `φ⁻¹ d`, of the vertex and of the face of `d`.
* **One stellar subdivision** (`Map.stCode`, `Map.stVi`, `Map.stFn`, `Map.stellar_code`): the
  triangle of `d` (`old d`, `up (φ d)`, `down d`) gets the dart numbers `3c(d) + j`, so that the
  faces are the triples of `phi3`; the program `stA ; stV` (`MillerProg.stPhase`, `40 m + 6`
  steps) writes the reversals and the vertex numbers, and `trip` the arrays `phi3`, `phi3i`,
  `· / 3` that encode the subdivision in turn (`MillerProg.enc_stellar`).
* **The input of `millerA`** (`MillerProg.sepIn`, `MillerProg.sepIn_exec`): from the plain
  encoding of `M` and flags at `B₀`, twice the subdivision, the weights `wSt c fl` (the flag of
  `d` on the centre of the triangle of `d`), and the layout `aBase` and registers of `millerA`
  (`MillerProg.aSetup_exec`), within `221 m + 5 (nV + nF) + 4 log₂ n + 110` steps.
* **`MillerProg.sepMiller`**: `sepIn ; millerA` and the band theorem: a simple cycle separator
  of `M.stellar.stellar` of at most `6 ⌊√n⌋ + 4` darts for these weights exists (the
  conclusion of `exists_short_cycle_separator_stellar`); computing it is steps 9–10.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

open Finset StDart

namespace Map

/-! ### The numbering of the stellar subdivision -/

section Code

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] (M : Map D P)
  {m nV nF : ℕ}

/-- The number of a dart of the stellar subdivision: the triangle of `d` (the darts `old d`,
`up (φ d)`, `down d`) gets the numbers `3 c(d)`, `3 c(d) + 1`, `3 c(d) + 2`. -/
def stNum (c : D ≃ Fin m) : StDart D → ℕ
  | old d => 3 * c d
  | up e => 3 * c (M.φ.symm e) + 1
  | down d => 3 * c d + 2

lemma stNum_lt (c : D ≃ Fin m) (x : StDart D) : M.stNum c x < 3 * m := by
  cases x with
  | old d => have := (c d).2; simp only [stNum]; omega
  | up e => have := (c (M.φ.symm e)).2; simp only [stNum]; omega
  | down d => have := (c d).2; simp only [stNum]; omega

lemma stNum_injective (c : D ≃ Fin m) : Function.Injective (M.stNum c) := by
  intro x y h
  cases x with
  | old d =>
    cases y with
    | old e => simp only [stNum] at h; exact congrArg old (c.injective (Fin.ext (by omega)))
    | up e => simp only [stNum] at h; omega
    | down e => simp only [stNum] at h; omega
  | up d =>
    cases y with
    | old e => simp only [stNum] at h; omega
    | up e =>
      simp only [stNum] at h
      have := c.injective (Fin.ext (by omega : (c (M.φ.symm d) : ℕ) = c (M.φ.symm e)))
      exact congrArg up (M.φ.symm.injective this)
    | down e => simp only [stNum] at h; omega
  | down d =>
    cases y with
    | old e => simp only [stNum] at h; omega
    | up e => simp only [stNum] at h; omega
    | down e => simp only [stNum] at h; exact congrArg down (c.injective (Fin.ext (by omega)))

/-- **The numbering of the darts of the stellar subdivision** (`stNum`). -/
noncomputable def stCode (c : D ≃ Fin m) : StDart D ≃ Fin (3 * m) :=
  Equiv.ofBijective (fun x => ⟨M.stNum c x, M.stNum_lt c x⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun x y h => M.stNum_injective c (congrArg Fin.val h), by
        rw [StDart.card, Fintype.card_fin, Fintype.card_congr c, Fintype.card_fin]⟩)

@[simp] lemma stCode_val (c : D ≃ Fin m) (x : StDart D) :
    (M.stCode c x : ℕ) = M.stNum c x := rfl

/-- **The numbering of the vertices of the stellar subdivision**: the vertices first, then the
centres of the faces. -/
def stVi (vn : P ≃ Fin nV) (fn : M.Face ≃ Fin nF) : P ⊕ M.Face ≃ Fin (nV + nF) :=
  (vn.sumCongr fn).trans finSumFinEquiv

@[simp] lemma stVi_inl (vn : P ≃ Fin nV) (fn : M.Face ≃ Fin nF) (v : P) :
    (M.stVi vn fn (.inl v) : ℕ) = vn v := by
  simp [stVi]

@[simp] lemma stVi_inr (vn : P ≃ Fin nV) (fn : M.Face ≃ Fin nF) (f : M.Face) :
    (M.stVi vn fn (.inr f) : ℕ) = nV + fn f := by
  simp [stVi]

/-- **The numbering of the faces of the stellar subdivision**: the triangle of `d` gets `c(d)`. -/
noncomputable def stFn (c : D ≃ Fin m) : M.stellar.Face ≃ Fin m :=
  (Equiv.ofBijective M.stTri ⟨stTri_injective, stTri_surjective⟩).symm.trans c

lemma stFn_stTri (c : D ≃ Fin m) (d : D) : M.stFn c (M.stTri d) = c d := by
  simp only [stFn, Equiv.trans_apply]
  congr 1
  exact (Equiv.ofBijective M.stTri _).symm_apply_apply d

/-- The face number is the dart number divided by `3`. -/
lemma stFn_face (c : D ≃ Fin m) (x : StDart D) :
    (M.stFn c (M.stellar.face x) : ℕ) = M.stCode c x / 3 := by
  cases x with
  | old d => rw [stellar_face_old, stFn_stTri]; simp only [stCode_val, stNum]; omega
  | up e =>
    rw [stellar_face_up, stellar_face_old, stFn_stTri]; simp only [stCode_val, stNum]; omega
  | down d =>
    rw [stellar_face_down, stellar_face_old, stFn_stTri]; simp only [stCode_val, stNum]; omega

/-- The inverse of `phi3` on the numbers of the darts of the triangles. -/
def phi3i (y : ℕ) : ℕ := if y % 3 = 0 then y + 2 else y - 1

lemma phi3i_phi3 (y : ℕ) : phi3i (CycleSearch.phi3 y) = y := by
  unfold phi3i CycleSearch.phi3
  split_ifs <;> omega

lemma phi3_0 (a : ℕ) : CycleSearch.phi3 (3 * a) = 3 * a + 1 := by
  unfold CycleSearch.phi3; split_ifs <;> omega

lemma phi3_1 (a : ℕ) : CycleSearch.phi3 (3 * a + 1) = 3 * a + 2 := by
  unfold CycleSearch.phi3; split_ifs <;> omega

lemma phi3_2 (a : ℕ) : CycleSearch.phi3 (3 * a + 2) = 3 * a := by
  unfold CycleSearch.phi3; split_ifs <;> omega

/-- **The coded stellar subdivision.** If the arrays `A` and `V` hold, at `3 c(d) + j`, the
reversal, the face successor, and the vertices of the triangle of `d` (computed from the codes
of `α d`, `φ d`, `φ⁻¹ d`, the vertex numbers and the face numbers), then `A` and `V` are the
reversal and the vertex numbers of the stellar subdivision for `stCode`, whose faces are the
triples `phi3`. -/
theorem stellar_code (c : D ≃ Fin m) (vn : P ≃ Fin nV) (fn : M.Face ≃ Fin nF) {A V : ℕ → ℕ}
    (hA : ∀ d, A (3 * c d) = 3 * c (M.α d) ∧ A (3 * c d + 1) = 3 * c (M.φ d) + 2 ∧
      A (3 * c d + 2) = 3 * c (M.φ.symm d) + 1)
    (hV : ∀ d, V (3 * c d) = vn (M.vert d) ∧ V (3 * c d + 1) = vn (M.vert (M.φ d)) ∧
      V (3 * c d + 2) = nV + fn (M.face d)) :
    (∀ x, A (M.stCode c x) = M.stCode c (M.stellar.α x)) ∧
    (∀ x, (M.stCode c (M.stellar.φ x) : ℕ) = CycleSearch.phi3 (M.stCode c x)) ∧
    (∀ x, V (M.stCode c x) = M.stVi vn fn (M.stellar.vert x)) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · cases x with
    | old d => simp only [stCode_val, stNum]; rw [(hA d).1]; rfl
    | up e =>
      simp only [stCode_val, stNum]; rw [(hA _).2.1]
      show _ = M.stNum c (down e)
      simp [stNum]
    | down d =>
      simp only [stCode_val, stNum]; rw [(hA d).2.2]
      show _ = M.stNum c (up d)
      simp [stNum]
  · rw [stCode_val, stCode_val]
    cases x with
    | old d =>
      show M.stNum c (up (M.φ d)) = CycleSearch.phi3 (M.stNum c (old d))
      simp only [stNum, Equiv.symm_apply_apply, phi3_0]
    | up e =>
      show M.stNum c (down (M.φ.symm e)) = CycleSearch.phi3 (M.stNum c (up e))
      simp only [stNum, phi3_1]
    | down d =>
      show M.stNum c (old d) = CycleSearch.phi3 (M.stNum c (down d))
      simp only [stNum, phi3_2]
  · cases x with
    | old d => simp only [stCode_val, stNum]; rw [(hV d).1]; rfl
    | up e =>
      simp only [stCode_val, stNum]; rw [(hV _).2.1, Equiv.apply_symm_apply]; rfl
    | down d =>
      simp only [stCode_val, stNum]; rw [(hV d).2.2]
      show _ = (M.stVi vn fn (.inr (M.face d)) : ℕ)
      rw [stVi_inr]

end Code

end Map

/-! ### The programs -/

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- One triangle of the reversals: `A[3u] = 3 α[u]`, `A[3u+1] = 3 φ[u] + 2`,
`A[3u+2] = 3 φ⁻¹[u] + 1` (registers: `r300 = u`, `r302 … r305` the bases of `α`, `φ`, `φ⁻¹`
and `A`, `r306 = 3`, `r307 = 1`, `r308 = 2`, scratch `r310 … r314`). -/
def stAbody : Stmt :=
  block [.addN 310 302 300, .loadN 311 310, .addN 310 303 300, .loadN 312 310,
    .addN 310 304 300, .loadN 313 310, .mulN 311 311 306, .mulN 312 312 306,
    .addN 312 312 308, .mulN 313 313 306, .addN 313 313 307, .mulN 314 300 306,
    .addN 314 314 305, .storeN 314 311, .addN 314 314 307, .storeN 314 312,
    .addN 314 314 307, .storeN 314 313, .addN 300 300 307]

/-- **The reversals of the stellar subdivision** (`r301 = m` darts). -/
def stA : Stmt := .seq (.instr (.constN 300 0)) (.whileLtN 300 301 stAbody)

/-- The registers of `stA` and `stV`. -/
structure StR (m bα bφ bφi bA bvn bfn bV nV : ℕ) (c : Config) : Prop where
  r301 : c.nreg 301 = m
  r302 : c.nreg 302 = bα
  r303 : c.nreg 303 = bφ
  r304 : c.nreg 304 = bφi
  r305 : c.nreg 305 = bA
  r306 : c.nreg 306 = 3
  r307 : c.nreg 307 = 1
  r308 : c.nreg 308 = 2
  r315 : c.nreg 315 = bvn
  r316 : c.nreg 316 = bfn
  r317 : c.nreg 317 = bV
  r318 : c.nreg 318 = nV

theorem StR.of {m bα bφ bφi bA bvn bfn bV nV : ℕ} {c c' : Config}
    (h : StR m bα bφ bφi bA bvn bfn bV nV c)
    (e : ∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) :
    StR m bα bφ bφi bA bvn bfn bV nV c' :=
  ⟨(e 301 (by omega) (by omega)).trans h.r301, (e 302 (by omega) (by omega)).trans h.r302,
    (e 303 (by omega) (by omega)).trans h.r303, (e 304 (by omega) (by omega)).trans h.r304,
    (e 305 (by omega) (by omega)).trans h.r305, (e 306 (by omega) (by omega)).trans h.r306,
    (e 307 (by omega) (by omega)).trans h.r307, (e 308 (by omega) (by omega)).trans h.r308,
    (e 315 (by omega) (by omega)).trans h.r315, (e 316 (by omega) (by omega)).trans h.r316,
    (e 317 (by omega) (by omega)).trans h.r317, (e 318 (by omega) (by omega)).trans h.r318⟩

variable {W : ℕ} {P : Input}

theorem stA_exec {m bα bφ bφi bA bvn bfn bV nV : ℕ}
    (hd : (bα + m ≤ bA ∨ bA + 3 * m ≤ bα) ∧ (bφ + m ≤ bA ∨ bA + 3 * m ≤ bφ) ∧
      (bφi + m ≤ bA ∨ bA + 3 * m ≤ bφi))
    (hW : bα + m ≤ W ∧ bφ + m ≤ W ∧ bφi + m ≤ W ∧ bA + 3 * m ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : StR m bα bφ bφi bA bvn bfn bV nV c)
    (hα : ∀ u < m, c.nmem (bα + u) < m) (hφ : ∀ u < m, c.nmem (bφ + u) < m)
    (hφi : ∀ u < m, c.nmem (bφi + u) < m) :
    ∃ c' t, Exec P W stA c c' t ∧ t ≤ 21 * m + 3 ∧
      (∀ u < m, c'.nmem (bA + 3 * u) = 3 * c.nmem (bα + u) ∧
        c'.nmem (bA + 3 * u + 1) = 3 * c.nmem (bφ + u) + 2 ∧
        c'.nmem (bA + 3 * u + 2) = 3 * c.nmem (bφi + u) + 1) ∧
      (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bA ∨ bA + 3 * m ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨d1, d2, d3⟩ := hd
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 300 = i ∧ i ≤ m ∧
    (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
    (∀ u < i, c'.nmem (bA + 3 * u) = 3 * c.nmem (bα + u) ∧
        c'.nmem (bA + 3 * u + 1) = 3 * c.nmem (bφ + u) + 2 ∧
        c'.nmem (bA + 3 * u + 2) = 3 * c.nmem (bφi + u) + 1) ∧
    (∀ a, ¬ (bA ≤ a ∧ a < bA + 3 * i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 300 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 300) (rN := 301) (N := m)
    (lo := 0) (B := 19) (body := stAbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 301 (by omega) (by omega)).trans hR.r301⟩)
    (fun i c₁ ⟨hw, h300, hi, hr, hd, hm, ho⟩ hlt => by
      have hc := hw
      have hR₁ := hR.of hr
      have mα : c₁.nmem (bα + i) = c.nmem (bα + i) := hm _ (by omega)
      have mφ : c₁.nmem (bφ + i) = c.nmem (bφ + i) := hm _ (by omega)
      have mφi : c₁.nmem (bφi + i) = c.nmem (bφi + i) := hm _ (by omega)
      have bα' := hα i hlt
      have bφ' := hφ i hlt
      have bφi' := hφi i hlt
      unfold stAbody
      exec_block
      all_goals try (config_simp; simp only [hR₁.r302, hR₁.r303, hR₁.r304, hR₁.r305, hR₁.r306,
        hR₁.r307, hR₁.r308, h300, mα, mφ, mφi]; omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h300, hR₁.r307]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b
      · simp only [hR₁.r302, hR₁.r303, hR₁.r304, hR₁.r305, hR₁.r306, hR₁.r307, hR₁.r308, h300,
          mα, mφ, mφi]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · simp only [upd_apply]
          have h1 := hd u hu
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;>
            (first | omega | exact h1.1 | exact h1.2.1 | exact h1.2.2)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
      · simp only [hR₁.r302, hR₁.r303, hR₁.r304, hR₁.r305, hR₁.r306, hR₁.r307, hR₁.r308, h300,
          mα, mφ, mφi, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd, hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd, hr, fun a ha => hm a (by omega), ho⟩

/-- One triangle of the vertex numbers: `V[3u] = vn[u]`, `V[3u+1] = vn[φ[u]]`,
`V[3u+2] = nV + fn[u]` (`r315`, `r316`, `r317` the bases of `vn`, `fn` and `V`, `r318 = nV`). -/
def stVbody : Stmt :=
  block [.addN 310 315 300, .loadN 311 310, .addN 310 303 300, .loadN 312 310,
    .addN 310 315 312, .loadN 312 310, .addN 310 316 300, .loadN 313 310,
    .addN 313 313 318, .mulN 314 300 306, .addN 314 314 317, .storeN 314 311,
    .addN 314 314 307, .storeN 314 312, .addN 314 314 307, .storeN 314 313,
    .addN 300 300 307]

/-- **The vertex numbers of the stellar subdivision.** -/
def stV : Stmt := .seq (.instr (.constN 300 0)) (.whileLtN 300 301 stVbody)

theorem stV_exec {m bα bφ bφi bA bvn bfn bV nV : ℕ}
    (hd : (bvn + m ≤ bV ∨ bV + 3 * m ≤ bvn) ∧ (bφ + m ≤ bV ∨ bV + 3 * m ≤ bφ) ∧
      (bfn + m ≤ bV ∨ bV + 3 * m ≤ bfn))
    (hW : bvn + m ≤ W ∧ bφ + m ≤ W ∧ bfn + m ≤ W ∧ bV + 3 * m ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : StR m bα bφ bφi bA bvn bfn bV nV c)
    (hφ : ∀ u < m, c.nmem (bφ + u) < m) (hfn : ∀ u < m, nV + c.nmem (bfn + u) ≤ W) :
    ∃ c' t, Exec P W stV c c' t ∧ t ≤ 19 * m + 3 ∧
      (∀ u < m, c'.nmem (bV + 3 * u) = c.nmem (bvn + u) ∧
        c'.nmem (bV + 3 * u + 1) = c.nmem (bvn + c.nmem (bφ + u)) ∧
        c'.nmem (bV + 3 * u + 2) = nV + c.nmem (bfn + u)) ∧
      (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bV ∨ bV + 3 * m ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨d1, d2, d3⟩ := hd
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 300 = i ∧ i ≤ m ∧
    (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
    (∀ u < i, c'.nmem (bV + 3 * u) = c.nmem (bvn + u) ∧
        c'.nmem (bV + 3 * u + 1) = c.nmem (bvn + c.nmem (bφ + u)) ∧
        c'.nmem (bV + 3 * u + 2) = nV + c.nmem (bfn + u)) ∧
    (∀ a, ¬ (bV ≤ a ∧ a < bV + 3 * i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 300 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 300) (rN := 301) (N := m)
    (lo := 0) (B := 17) (body := stVbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 301 (by omega) (by omega)).trans hR.r301⟩)
    (fun i c₁ ⟨hw, h300, hi, hr, hd, hm, ho⟩ hlt => by
      have hc := hw
      have hR₁ := hR.of hr
      have bφ' := hφ i hlt
      have mvn : c₁.nmem (bvn + i) = c.nmem (bvn + i) := hm _ (by omega)
      have mφ : c₁.nmem (bφ + i) = c.nmem (bφ + i) := hm _ (by omega)
      have mvn' : c₁.nmem (bvn + c.nmem (bφ + i)) = c.nmem (bvn + c.nmem (bφ + i)) :=
        hm _ (by omega)
      have mfn : c₁.nmem (bfn + i) = c.nmem (bfn + i) := hm _ (by omega)
      have bfn' := hfn i hlt
      unfold stVbody
      exec_block
      all_goals try (config_simp; simp only [hR₁.r303, hR₁.r306, hR₁.r307, hR₁.r315, hR₁.r316,
        hR₁.r317, hR₁.r318, h300, mvn, mφ, mvn', mfn]; omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h300, hR₁.r307]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b
      · simp only [hR₁.r303, hR₁.r306, hR₁.r307, hR₁.r315, hR₁.r316, hR₁.r317, hR₁.r318, h300,
          mvn, mφ, mvn', mfn]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · simp only [upd_apply]
          have h1 := hd u hu
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;>
            (first | omega | exact h1.1 | exact h1.2.1 | exact h1.2.2)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
      · simp only [hR₁.r303, hR₁.r306, hR₁.r307, hR₁.r315, hR₁.r316, hR₁.r317, hR₁.r318, h300,
          mvn, mφ, mvn', mfn, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd, hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd, hr, fun a ha => hm a (by omega), ho⟩

/-- One dart of a coded triangulation: `φ[x] = phi3 x`, `φ⁻¹[x] = phi3i x`, `fn[x] = x / 3`
(`r303`, `r304`, `r316` the bases, `r319` the number of darts). -/
def tribody : Stmt :=
  block [.divN 311 300 306, .modN 312 300 306, .addN 313 312 307, .modN 313 313 306,
    .mulN 314 311 306, .addN 313 313 314, .addN 312 312 308, .modN 312 312 306,
    .addN 312 312 314, .addN 310 303 300, .storeN 310 313, .addN 310 304 300,
    .storeN 310 312, .addN 310 316 300, .storeN 310 311, .addN 300 300 307]

/-- **The face successors, predecessors and face numbers of a coded triangulation.** -/
def trip : Stmt := .seq (.instr (.constN 300 0)) (.whileLtN 300 319 tribody)

lemma phi3_eq (x : ℕ) : CycleSearch.phi3 x = (x % 3 + 1) % 3 + 3 * (x / 3) := by
  unfold CycleSearch.phi3; split_ifs <;> omega

lemma phi3i_eq (x : ℕ) : Map.phi3i x = (x % 3 + 2) % 3 + 3 * (x / 3) := by
  unfold Map.phi3i; split_ifs <;> omega

theorem trip_exec {K bφ bφi bfn : ℕ}
    (hd : (bφ + K ≤ bφi ∨ bφi + K ≤ bφ) ∧ (bφ + K ≤ bfn ∨ bfn + K ≤ bφ) ∧
      (bφi + K ≤ bfn ∨ bfn + K ≤ bφi))
    (hW : bφ + K + 2 ≤ W ∧ bφi + K + 2 ≤ W ∧ bfn + K + 2 ≤ W)
    (c : Config) (hc : WordsBounded W c) (h303 : c.nreg 303 = bφ) (h304 : c.nreg 304 = bφi)
    (h306 : c.nreg 306 = 3) (h307 : c.nreg 307 = 1) (h308 : c.nreg 308 = 2)
    (h316 : c.nreg 316 = bfn) (h319 : c.nreg 319 = K) :
    ∃ c' t, Exec P W trip c c' t ∧ t ≤ 18 * K + 3 ∧
      (∀ x < K, c'.nmem (bφ + x) = CycleSearch.phi3 x ∧ c'.nmem (bφi + x) = Map.phi3i x ∧
        c'.nmem (bfn + x) = x / 3) ∧
      (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < bφ ∨ bφ + K ≤ a) → (a < bφi ∨ bφi + K ≤ a) → (a < bfn ∨ bfn + K ≤ a) →
        c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨d1, d2, d3⟩ := hd
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 300 = i ∧ i ≤ K ∧
    (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c.nreg r) ∧
    (∀ x < i, c'.nmem (bφ + x) = CycleSearch.phi3 x ∧ c'.nmem (bφi + x) = Map.phi3i x ∧
        c'.nmem (bfn + x) = x / 3) ∧
    (∀ a, ¬ (bφ ≤ a ∧ a < bφ + i) → ¬ (bφi ≤ a ∧ a < bφi + i) → ¬ (bfn ≤ a ∧ a < bfn + i) →
      c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 300 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 300) (rN := 319) (N := K)
    (lo := 0) (B := 16) (body := tribody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 319 (by omega) (by omega)).trans h319⟩)
    (fun i c₁ ⟨hw, h300, hi, hr, hd, hm, ho⟩ hlt => by
      have hc := hw
      have g303 := (hr 303 (by omega) (by omega)).trans h303
      have g304 := (hr 304 (by omega) (by omega)).trans h304
      have g306 := (hr 306 (by omega) (by omega)).trans h306
      have g307 := (hr 307 (by omega) (by omega)).trans h307
      have g308 := (hr 308 (by omega) (by omega)).trans h308
      have g316 := (hr 316 (by omega) (by omega)).trans h316
      unfold tribody
      exec_block
      all_goals try (config_simp; simp only [g303, g304, g306, g307, g308, g316, h300]; omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b => ?_, fun u hu => ?_, fun a ha hb hd' => ?_, ho⟩,
        le_rfl⟩
      all_goals config_simp
      · rw [h300, g307]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b
      · simp only [g303, g304, g306, g307, g308, g316, h300, phi3_eq, phi3i_eq]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · simp only [upd_apply]
          have h1 := hd u hu
          rw [phi3_eq, phi3i_eq] at h1
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;>
            (first | omega | exact h1.1 | exact h1.2.1 | exact h1.2.2)
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
      · simp only [g303, g304, g306, g307, g308, g316, h300, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega) (by omega) (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun u hu => absurd hu (by omega), fun a _ _ _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd, hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd, hr,
    fun a h1 h2 h3 => hm a (by omega) (by omega) (by omega), ho⟩

/-- Clear `r321 = N` words from `r322 = b` (`r320` the counter, `r307 = 1`). -/
def zrbody : Stmt := block [.addN 323 322 320, .storeN 323 324, .addN 320 320 307]

/-- **Clear an array** (`r324 = 0`). -/
def zrclear : Stmt := .seq (block [.constN 320 0, .constN 324 0]) (.whileLtN 320 321 zrbody)

theorem zrclear_exec {N b : ℕ} (hW : b + N ≤ W) (c : Config) (hc : WordsBounded W c)
    (h307 : c.nreg 307 = 1) (h321 : c.nreg 321 = N) (h322 : c.nreg 322 = b) :
    ∃ c' t, Exec P W zrclear c c' t ∧ t ≤ 5 * N + 4 ∧ (∀ x < N, c'.nmem (b + x) = 0) ∧
      (∀ r, r ≠ 320 → r ≠ 323 → r ≠ 324 → c'.nreg r = c.nreg r) ∧
      (∀ a, a < b ∨ b + N ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 320 = i ∧ i ≤ N ∧
    c'.nreg 324 = 0 ∧ (∀ r, r ≠ 320 → r ≠ 323 → r ≠ 324 → c'.nreg r = c.nreg r) ∧
    (∀ x < i, c'.nmem (b + x) = 0) ∧
    (∀ a, ¬ (b ≤ a ∧ a < b + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 320 0 (by omega)
  have e₂ := Exec.constN (P := P) e₁.wb_right 324 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 320) (rN := 321) (N := N)
    (lo := 0) (B := 3) (body := zrbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.2.1 321 (by omega) (by omega) (by omega)).trans h321⟩)
    (fun i c₁ ⟨hw, h320, hi, h324, hr, hd, hm, ho⟩ hlt => by
      have hc := hw
      have g307 := (hr 307 (by omega) (by omega) (by omega)).trans h307
      have g322 := (hr 322 (by omega) (by omega) (by omega)).trans h322
      unfold zrbody
      exec_block
      all_goals try (config_simp; simp only [g307, g322, h320]; omega)
      refine ⟨⟨‹_›, ?_, by omega, ?_, fun r a b d => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩,
        le_rfl⟩
      all_goals config_simp
      · rw [h320, g307]
      · exact h324
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b d
      · simp only [g322, h320, h324, upd_apply]
        split_ifs <;> first | rfl | (exact hd u (by omega)) | omega
      · simp only [g322, h320, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₂.wb_right, by config_simp, by omega, by config_simp,
      fun r a _ d => by config_simp; rw [upd_other _ _ _ d, upd_other _ _ _ a],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, -, hr, hd, hm, ho⟩ := hI
  exact ⟨c', 1 + (1 + 0) + t, .seq (.seq e₁ (.seq e₂ (.skip e₂.wb_right))) e, by omega, hd, hr,
    fun a ha => hm a (by omega), ho⟩

/-! ### The layout and the registers of `millerA` -/

/-- **The layout used**: from `k` triangles, `n` vertices and `L ≥ log₂ n` (`lgprog`). -/
def aBase (k n L : ℕ) : ABase where
  bV := 11 * k
  bLv := 14 * k
  bPr := 14 * k + n
  bMk := 14 * k + 2 * n
  bQ := 14 * k + 3 * n
  bHd := 14 * k + 4 * n
  bNx := 14 * k + 5 * n
  bF := 17 * k + 5 * n
  bw := 17 * k + 6 * n
  bA := 17 * k + 7 * n
  bL := 18 * k + 7 * n
  bS := 19 * k + 7 * n
  bSum := 20 * k + 7 * n
  bRep := 21 * k + 7 * n + 1
  bCN := 22 * k + 7 * n + 2
  bLC := 22 * k + 8 * n + 2
  bU := 22 * k + 10 * n + 3
  bWC := 22 * k + 10 * n + 3 + (L + 1) * n
  bD := 22 * k + 11 * n + 3 + (L + 1) * n
  bS8 := 22 * k + 12 * n + 3 + (L + 1) * n
  bD₂ := 22 * k + 13 * n + 3 + (L + 1) * n
  bS₂ := 22 * k + 14 * n + 3 + (L + 1) * n

/-- The end of the arrays of `millerA` for `k` triangles and `n` vertices. -/
def aEnd (k n : ℕ) : ℕ := 25 * k + 18 * n + 7 + (Nat.log 2 n + 2) * n

lemma aLay_of {k n L W : ℕ} (hL : Nat.log 2 n ≤ L) (hL' : L ≤ Nat.log 2 n + 1)
    (hW : aEnd k n ≤ W) : ALay (aBase k n L) k n W := by
  have h1 : (Nat.log 2 n + 1) * n ≤ (L + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have h2 : (L + 1) * n ≤ (Nat.log 2 n + 2) * n := Nat.mul_le_mul_right _ (by omega)
  unfold aEnd at hW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> simp only [aBase] <;> omega

/-- The constant registers and the bases (`r326 = k`, `r330 = n`, `r271 = L`). -/
def aRegBlock : Stmt :=
  block [.constN 0 0, .constN 1 1, .constN 2 2, .constN 3 3, .copyN 4 326,
    .addN 331 326 326, .addN 5 331 326, .addN 6 5 5, .addN 7 6 326, .addN 8 7 326,
    .addN 9 8 326, .addN 10 9 326, .constN 140 0, .constN 142 3, .copyN 143 326,
    .constN 147 0, .addN 162 10 326, .addN 163 162 5, .addN 215 163 330, .addN 216 215 330,
    .addN 217 216 330, .addN 218 217 330, .addN 219 218 330, .addN 164 219 5,
    .addN 165 164 330, .addN 144 165 330, .addN 145 144 326, .addN 146 145 326,
    .addN 166 146 326, .addN 188 166 326, .addN 188 188 141, .addN 189 188 326,
    .addN 189 189 141, .addN 200 189 330, .addN 254 200 330, .addN 254 254 330,
    .addN 254 254 141, .addN 332 271 141, .mulN 332 332 330, .addN 190 254 332,
    .addN 253 190 330, .addN 252 253 330, .addN 381 252 330, .addN 382 381 330]

/-- **The registers of `millerA`**: `r141 = 1`, `r161 = n`, `r271 = L` by `lgprog`, then the
constants and the bases of `aBase k n L`. -/
def aSetup : Stmt := .seq (block [.constN 141 1, .copyN 161 330]) (.seq lgprog aRegBlock)

set_option maxHeartbeats 4000000 in
/-- **The registers of `millerA` are set up** within `4 log₂ n + 50` steps. -/
theorem aSetup_exec {k n : ℕ} (hn : 1 ≤ n) (hW : aEnd k n ≤ W) (c : Config)
    (hc : WordsBounded W c) (h326 : c.nreg 326 = k) (h330 : c.nreg 330 = n) :
    ∃ c' t L, Exec P W aSetup c c' t ∧ t ≤ 4 * Nat.log 2 n + 50 ∧ Nat.log 2 n ≤ L ∧
      L ≤ Nat.log 2 n + 1 ∧ ARegs (aBase k n L) k n c' ∧
      (∀ r, 10 < r → r < 140 ∨ (147 < r ∧ r < 161) ∨ (166 < r ∧ r < 188) ∨
        (190 < r ∧ r < 200) ∨ (200 < r ∧ r < 215) ∨ (219 < r ∧ r < 252) ∨
        (254 < r ∧ r < 270) ∨ (271 < r ∧ r < 326) ∨ (326 < r ∧ r < 330) ∨
        (332 < r ∧ r < 381) ∨ 382 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  have hlog2 : (Nat.log 2 n + 2) * n = Nat.log 2 n * n + 2 * n := by ring
  unfold aEnd at hW
  have e₁ := Exec.constN (P := P) hc 141 1 (by omega)
  have e₂ := Exec.copyN (P := P) e₁.wb_right 161 330
  set c₂ : Config := { ({ c with nreg := upd c.nreg 141 1 } : Config) with
    nreg := upd (upd c.nreg 141 1) 161 ((upd c.nreg 141 1) 330) }
  have g141 : c₂.nreg 141 = 1 := by simp [c₂]
  have g161 : c₂.nreg 161 = n := by simp [c₂, h330]
  have g₂ : ∀ r, r ≠ 141 → r ≠ 161 → c₂.nreg r = c.nreg r := fun r a b => by
    simp [c₂, upd_other _ _ _ a, upd_other _ _ _ b]
  have eb : Exec P W (block [.constN 141 1, .copyN 161 330]) c c₂ 2 :=
    .seq e₁ (.seq e₂ (.skip e₂.wb_right))
  obtain ⟨c₃, t₃, e₃, ht₃, hL1, hL2, hL3, hr₃, hm₃, ho₃⟩ :=
    lgprog_exec (P := P) (W := W) (n := n) (by omega) c₂ e₂.wb_right g141 g161
  set L := c₃.nreg 271 with hL
  have hlogL : Nat.log 2 n ≤ L := by
    have := Nat.log_mono_right (b := 2) hL2
    rwa [Nat.log_pow (by norm_num)] at this
  have hLn : (L + 1) * n ≤ Nat.log 2 n * n + 2 * n := by
    have := Nat.mul_le_mul_right n (show L + 1 ≤ Nat.log 2 n + 2 by omega); nlinarith
  have k326 : c₃.nreg 326 = k := (hr₃ 326 (by omega) (by omega)).trans ((g₂ 326 (by omega)
    (by omega)).trans h326)
  have k330 : c₃.nreg 330 = n := (hr₃ 330 (by omega) (by omega)).trans ((g₂ 330 (by omega)
    (by omega)).trans h330)
  have k141 : c₃.nreg 141 = 1 := (hr₃ 141 (by omega) (by omega)).trans g141
  have k161 : c₃.nreg 161 = n := (hr₃ 161 (by omega) (by omega)).trans g161
  have hc := e₃.wb_right
  have hlogn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  obtain ⟨c₄, t₄, e₄, ht₄, hpost⟩ : ∃ c₄ t₄, Exec P W aRegBlock c₃ c₄ t₄ ∧ t₄ ≤ 44 ∧
      (ARegs (aBase k n L) k n c₄ ∧ c₄.nmem = c₃.nmem ∧ c₄.output = c₃.output) := by
    unfold aRegBlock
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [k326, k330, k141, ← hL]); omega)
    refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
    · unfold CycleSearch.CRegs; config_simp; simp only [k326, true_and]; omega
    all_goals (config_simp <;> (try simp only [aBase, k326, k330, k141, k161, ← hL]) <;> omega)
  obtain ⟨hA, hm₄, ho₄⟩ := hpost
  have hfr : ∀ r, 10 < r → r < 140 ∨ (147 < r ∧ r < 161) ∨ (166 < r ∧ r < 188) ∨
      (190 < r ∧ r < 200) ∨ (200 < r ∧ r < 215) ∨ (219 < r ∧ r < 252) ∨
      (254 < r ∧ r < 270) ∨ (271 < r ∧ r < 326) ∨ (326 < r ∧ r < 330) ∨
      (332 < r ∧ r < 381) ∨ 382 < r → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    e₄.nreg_of_wr (by
      simp only [aRegBlock, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]
      omega)
  refine ⟨c₄, 2 + (t₃ + t₄), L, .seq eb (.seq e₃ e₄), by omega, hlogL, hL3, hA, fun r h1 h2 => ?_,
    by rw [hm₄, hm₃], by rw [ho₄, ho₃]⟩
  rw [hfr r h1 h2, hr₃ r (by omega) (by omega), g₂ r (by omega) (by omega)]

/-! ### One stellar subdivision on the machine -/

section Phase

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- **The plain encoding of a map** `M` in memory, for numberings `c` of the darts, `vn` of the
vertices and `fn` of the faces: at `bα`, `bφ`, `bφi`, `bvn`, `bfn` the arrays indexed by the
dart numbers holding the numbers of `α d`, `φ d`, `φ⁻¹ d`, of the vertex of `d` and of its
face. -/
structure Enc (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (mem : ℕ → ℕ) (bα bφ bφi bvn bfn : ℕ) : Prop where
  α : ∀ d, mem (bα + c d) = c (M.α d)
  φ : ∀ d, mem (bφ + c d) = c (M.φ d)
  φi : ∀ d, mem (bφi + c d) = c (M.φ.symm d)
  vn : ∀ d, mem (bvn + c d) = vn (M.vert d)
  fn : ∀ d, mem (bfn + c d) = fn (M.face d)

/-- The disjointness of the arrays of `stA ; stV`: the inputs (of `m` words) and the outputs
(of `3 m` words at `bA` and `bV`). -/
def StDisj (m bα bφ bφi bA bvn bfn bV : ℕ) : Prop :=
  (bα + m ≤ bA ∨ bA + 3 * m ≤ bα) ∧ (bφ + m ≤ bA ∨ bA + 3 * m ≤ bφ) ∧
    (bφi + m ≤ bA ∨ bA + 3 * m ≤ bφi) ∧ (bvn + m ≤ bA ∨ bA + 3 * m ≤ bvn) ∧
    (bfn + m ≤ bA ∨ bA + 3 * m ≤ bfn) ∧ (bvn + m ≤ bV ∨ bV + 3 * m ≤ bvn) ∧
    (bφ + m ≤ bV ∨ bV + 3 * m ≤ bφ) ∧ (bfn + m ≤ bV ∨ bV + 3 * m ≤ bfn) ∧
    (bA + 3 * m ≤ bV ∨ bV + 3 * m ≤ bA)

lemma enc_lt {M : Map D Q} {m nV nF : ℕ} {c : D ≃ Fin m} {vn : Q ≃ Fin nV}
    {fn : M.Face ≃ Fin nF} {mem : ℕ → ℕ} {bα bφ bφi bvn bfn : ℕ}
    (h : Enc M c vn fn mem bα bφ bφi bvn bfn) :
    (∀ u < m, mem (bα + u) < m) ∧ (∀ u < m, mem (bφ + u) < m) ∧ (∀ u < m, mem (bφi + u) < m) ∧
      (∀ u < m, mem (bvn + u) < nV) ∧ (∀ u < m, mem (bfn + u) < nF) := by
  have e : ∀ u (hu : u < m), u = c (c.symm ⟨u, hu⟩) := fun u hu => by simp
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [e u hu, h.α]; exact Fin.isLt _
  · rw [e u hu, h.φ]; exact Fin.isLt _
  · rw [e u hu, h.φi]; exact Fin.isLt _
  · rw [e u hu, h.vn]; exact Fin.isLt _
  · rw [e u hu, h.fn]; exact Fin.isLt _

variable {W : ℕ} {P : Input}

/-- **One stellar subdivision on the machine**: from the plain encoding of `M`, `stA ; stV`
writes the reversals and the vertex numbers of the stellar subdivision, numbered by `stCode`,
whose faces are the triples `phi3`, within `40 m + 6` steps. -/
theorem stPhase (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) {bα bφ bφi bA bvn bfn bV : ℕ} {c₀ : Config}
    (hE : Enc M c vn fn c₀.nmem bα bφ bφi bvn bfn) (hd : StDisj m bα bφ bφi bA bvn bfn bV)
    (hW : bα + m ≤ W ∧ bφ + m ≤ W ∧ bφi + m ≤ W ∧ bvn + m ≤ W ∧ bfn + m ≤ W ∧
      bA + 3 * m ≤ W ∧ bV + 3 * m ≤ W ∧ nV + nF ≤ W)
    (hc : WordsBounded W c₀) (hR : StR m bα bφ bφi bA bvn bfn bV nV c₀) :
    ∃ c' t, Exec P W (.seq stA stV) c₀ c' t ∧ t ≤ 40 * m + 6 ∧
      (∀ x, c'.nmem (bA + M.stCode c x) = M.stCode c (M.stellar.α x)) ∧
      (∀ x, (M.stCode c (M.stellar.φ x) : ℕ) = CycleSearch.phi3 (M.stCode c x)) ∧
      (∀ x, c'.nmem (bV + M.stCode c x) = M.stVi vn fn (M.stellar.vert x)) ∧
      (∀ r, 300 < r → r < 310 ∨ 314 < r → c'.nreg r = c₀.nreg r) ∧
      (∀ a, (a < bA ∨ bA + 3 * m ≤ a) → (a < bV ∨ bV + 3 * m ≤ a) → c'.nmem a = c₀.nmem a) ∧
      c'.output = c₀.output := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hd
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hW
  obtain ⟨lα, lφ, lφi, lvn, lfn⟩ := enc_lt hE
  obtain ⟨c₁, t₁, e₁, ht₁, hA₁, hr₁, hm₁, ho₁⟩ := stA_exec (P := P) ⟨d1, d2, d3⟩
    ⟨w1, w2, w3, w6⟩ c₀ hc hR lα lφ lφi
  have m₁ : ∀ a, (a < bA ∨ bA + 3 * m ≤ a) → c₁.nmem a = c₀.nmem a := hm₁
  obtain ⟨c₂, t₂, e₂, ht₂, hV₂, hr₂, hm₂, ho₂⟩ := stV_exec (P := P) ⟨d6, d7, d8⟩
    ⟨w4, w2, w5, w7⟩ c₁ e₁.wb_right (hR.of hr₁)
    (fun u hu => by rw [m₁ _ (by omega)]; exact lφ u hu)
    (fun u hu => by rw [m₁ _ (by omega)]; have := lfn u hu; omega)
  have key := M.stellar_code c vn fn (A := fun a => c₂.nmem (bA + a))
    (V := fun a => c₂.nmem (bV + a)) (fun d => ?_) (fun d => ?_)
  · obtain ⟨k1, k2, k3⟩ := key
    exact ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, k1, k2, k3,
      fun r a b => (hr₂ r a b).trans (hr₁ r a b),
      fun a h1 h2 => (hm₂ a h2).trans (hm₁ a h1), ho₂.trans ho₁⟩
  · have hu := (c d).2
    obtain ⟨a1, a2, a3⟩ := hA₁ _ hu
    beta_reduce
    simp only [← Nat.add_assoc]
    rw [hm₂ _ (by omega), hm₂ _ (by omega), hm₂ _ (by omega), a1, a2, a3, hE.α, hE.φ, hE.φi]
    exact ⟨rfl, rfl, rfl⟩
  · have hu := (c d).2
    obtain ⟨v1, v2, v3⟩ := hV₂ _ hu
    beta_reduce
    simp only [← Nat.add_assoc]
    rw [v1, v2, v3, m₁ (bφ + c d) (by omega), hE.φ, m₁ (bvn + c d) (by omega),
      m₁ (bvn + c (M.φ d)) (by have := (c (M.φ d)).2; omega), m₁ (bfn + c d) (by omega),
      hE.vn, hE.vn, hE.fn]
    exact ⟨rfl, rfl, rfl⟩

/-- **The plain encoding of the stellar subdivision**: its reversals and vertex numbers (from
`stPhase`), and the arrays `phi3`, `phi3i`, `· / 3` of `trip`. -/
theorem enc_stellar (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) {mem : ℕ → ℕ} {bA bφ bφi bV bfn : ℕ}
    (hA : ∀ x, mem (bA + M.stCode c x) = M.stCode c (M.stellar.α x))
    (hφ : ∀ x, (M.stCode c (M.stellar.φ x) : ℕ) = CycleSearch.phi3 (M.stCode c x))
    (hV : ∀ x, mem (bV + M.stCode c x) = M.stVi vn fn (M.stellar.vert x))
    (htri : ∀ y < 3 * m, mem (bφ + y) = CycleSearch.phi3 y ∧ mem (bφi + y) = Map.phi3i y ∧
      mem (bfn + y) = y / 3) :
    Enc M.stellar (M.stCode c) (M.stVi vn fn) (M.stFn c) mem bA bφ bφi bV bfn := by
  refine ⟨hA, fun x => ?_, fun x => ?_, hV, fun x => ?_⟩
  · rw [(htri _ (M.stCode c x).2).1, hφ]
  · rw [(htri _ (M.stCode c x).2).2.1]
    have := hφ (M.stellar.φ.symm x)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Map.phi3i_phi3]
  · rw [(htri _ (M.stCode c x).2).2.2, Map.stFn_face]

/-- Copy one word: `mem[r340 + i] := mem[r339 + i]` (`r337 = i`, `r307 = 1`). -/
def cpybody : Stmt := block [.addN 341 339 337, .loadN 342 341, .addN 341 340 337,
  .storeN 341 342, .addN 337 337 307]

/-- **Copy `r338 = N` words** from `r339` to `r340`. -/
def cpyN : Stmt := .seq (.instr (.constN 337 0)) (.whileLtN 337 338 cpybody)

theorem cpyN_exec {N bs bd : ℕ} (hd : bs + N ≤ bd ∨ bd + N ≤ bs) (hW : bs + N ≤ W ∧ bd + N ≤ W)
    (c : Config) (hc : WordsBounded W c) (h307 : c.nreg 307 = 1) (h338 : c.nreg 338 = N)
    (h339 : c.nreg 339 = bs) (h340 : c.nreg 340 = bd) :
    ∃ c' t, Exec P W cpyN c c' t ∧ t ≤ 7 * N + 3 ∧ (∀ x < N, c'.nmem (bd + x) = c.nmem (bs + x)) ∧
      (∀ r, r ≠ 337 → r ≠ 341 → r ≠ 342 → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bd ∨ bd + N ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 337 = i ∧ i ≤ N ∧
    (∀ r, r ≠ 337 → r ≠ 341 → r ≠ 342 → c'.nreg r = c.nreg r) ∧
    (∀ x < i, c'.nmem (bd + x) = c.nmem (bs + x)) ∧
    (∀ a, ¬ (bd ≤ a ∧ a < bd + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.constN (P := P) hc 337 0 (by omega)
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 337) (rN := 338) (N := N)
    (lo := 0) (B := 5) (body := cpybody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 338 (by omega) (by omega) (by omega)).trans h338⟩)
    (fun i c₁ ⟨hw, h337, hi, hr, hd', hm, ho⟩ hlt => by
      have hc := hw
      have g307 := (hr 307 (by omega) (by omega) (by omega)).trans h307
      have g339 := (hr 339 (by omega) (by omega) (by omega)).trans h339
      have g340 := (hr 340 (by omega) (by omega) (by omega)).trans h340
      have ms : c₁.nmem (bs + i) = c.nmem (bs + i) := hm _ (by omega)
      unfold cpybody
      exec_block
      all_goals try (show _ ≤ W; config_simp; simp only [g307, g339, g340, h337]; omega)
      refine ⟨⟨‹_›, ?_, by omega, fun r a b d => ?_, fun u hu => ?_, fun a ha => ?_, ho⟩, le_rfl⟩
      all_goals config_simp
      · rw [h337, g307]
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr r a b d
      · simp only [g339, g340, h337, ms, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · have := hd' u hu
          split_ifs <;> first | omega | exact this
        · split_ifs <;> first | rfl | omega
      · simp only [g339, g340, h337, upd_apply]
        split_ifs <;> first | omega | exact hm a (by omega))
    (by omega) ⟨e₁.wb_right, by config_simp, by omega,
      fun r a _ _ => by config_simp; rw [upd_other _ _ _ a],
      fun u hu => absurd hu (by omega), fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, hr, hd', hm, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd', hr, fun a ha => hm a (by omega), ho⟩

/-! ### The whole input -/

/-- The bases of the first stellar subdivision (the input at `r393 = B₀`, `r390 = m`). -/
def inB1 : Stmt := block [.constN 306 3, .constN 307 1, .constN 308 2, .copyN 301 390,
  .copyN 302 393, .addN 303 302 390, .addN 304 303 390, .addN 315 304 390, .addN 316 315 390,
  .addN 325 316 390, .addN 305 325 390, .mulN 326 390 306, .addN 317 305 326, .copyN 318 391]

/-- The bases of `trip`. -/
def inB2 : Stmt := block [.copyN 319 326, .addN 303 317 326, .addN 304 303 326,
  .addN 316 304 326]

/-- The bases of the second stellar subdivision (`r391 = nV`, `r392 = nF`). -/
def inB3 : Stmt := block [.copyN 301 326, .copyN 302 305, .constN 305 0, .copyN 315 317,
  .constN 327 11, .mulN 317 326 327, .addN 318 391 392]

/-- The bases of the weights. -/
def inB4 : Stmt := block [.addN 330 318 390, .constN 334 17, .mulN 335 326 334, .constN 334 6,
  .mulN 336 330 334, .addN 322 335 336, .copyN 321 318, .copyN 338 390, .copyN 339 325,
  .addN 340 322 318]

/-- **The input of `millerA`** from the plain encoding of a map `M` with `m` darts, `nV`
vertices and `nF` faces at `B₀` and flags at `B₀ + 5 m`: the coded stellar subdivision of the
stellar subdivision of `M` (the reversals at `0`, the vertex numbers at `11 k`, `k = 3 m`), the
weights (the flags on the centres of the triangles of the darts, `0` elsewhere) and the
registers of `millerA`. -/
def sepIn : Stmt :=
  .seq inB1 <| .seq (.seq stA stV) <| .seq inB2 <| .seq trip <| .seq inB3 <|
    .seq (.seq stA stV) <| .seq inB4 <| .seq zrclear <| .seq cpyN aSetup

/-- The weights of the twice subdivided map: the flag of `d` on the centre of the triangle of
`d` (a vertex of the second subdivision), `0` on the other vertices. -/
noncomputable def wSt (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (fl : D → ℕ) :
    (Q ⊕ M.Face) ⊕ M.stellar.Face → ℕ :=
  Sum.elim (fun _ => 0) (fun F => fl (c.symm (M.stFn c F)))

theorem sepIn_wmax : sepIn.wmax < 390 := by decide

set_option maxHeartbeats 8000000 in
/-- **The input of `millerA` on the machine.** From the plain encoding (`Enc`) of a map `M` with
`m ≥ 1` darts, `nV` vertices and `nF` faces at `B₀` (and flags `fl` at `B₀ + 5 m`), above the
arrays of `millerA` (`aEnd`), `sepIn` ends within `221 m + 5 (nV + nF) + 4 log₂ n + 110` steps,
`n = nV + nF + m`, with the reversals of the twice subdivided map `M.stellar.stellar` at `0`
and its vertex numbers at `11 k` (`k = 3 m` triangles; the darts numbered by
`stCode (stCode c)`, the faces the triples `phi3`, the vertices by `stVi (stVi vn fn) (stFn c)`),
the weights `wSt c fl` at `bw`, and the registers of `millerA` (`ARegs` for `aBase`). -/
theorem sepIn_exec (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (fl : D → ℕ) {B₀ : ℕ} {c₀ : Config} (hm1 : 1 ≤ m)
    (hE : Enc M c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = fl d)
    (hB : aEnd (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 21 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t L, Exec P W sepIn c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 ∧
      Nat.log 2 (nV + nF + m) ≤ L ∧ L ≤ Nat.log 2 (nV + nF + m) + 1 ∧
      ARegs (aBase (3 * m) (nV + nF + m) L) (3 * m) (nV + nF + m) c' ∧
      (∀ y, c'.nmem (M.stellar.stCode (M.stCode c) y) =
        M.stellar.stCode (M.stCode c) (M.stellar.stellar.α y)) ∧
      (∀ y, (M.stellar.stCode (M.stCode c) (M.stellar.stellar.φ y) : ℕ) =
        CycleSearch.phi3 (M.stellar.stCode (M.stCode c) y)) ∧
      (∀ y, c'.nmem (11 * (3 * m) + M.stellar.stCode (M.stCode c) y) =
        M.stellar.stVi (M.stVi vn fn) (M.stFn c) (M.stellar.stellar.vert y)) ∧
      (∀ x, c'.nmem ((aBase (3 * m) (nV + nF + m) L).bw +
        M.stellar.stVi (M.stVi vn fn) (M.stFn c) x) = wSt M c fl x) ∧
      (∀ x, c'.nmem (B₀ + 6 * m + M.stCode c x) = M.stCode c (M.stellar.α x)) ∧
      (∀ r, 390 ≤ r → r < 400 → c'.nreg r = c₀.nreg r) ∧
      c'.output = c₀.output := by
  have hB' := hB
  unfold aEnd at hB'
  -- 1. the bases of the first subdivision
  obtain ⟨c₁, t₁, e₁, ht₁, hR₁, k325, k326, hm₁, ho₁⟩ : ∃ c₁ t₁, Exec P W inB1 c₀ c₁ t₁ ∧
      t₁ ≤ 14 ∧
      StR m B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 6 * m) (B₀ + 3 * m) (B₀ + 4 * m) (B₀ + 9 * m) nV
        c₁ ∧ c₁.nreg 325 = B₀ + 5 * m ∧ c₁.nreg 326 = 3 * m ∧ c₁.nmem = c₀.nmem ∧
        c₁.output = c₀.output := by
    unfold inB1
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [h390, h391, h393]); omega)
    refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [h390, h391, h393]) <;> omega)
  have j390 : c₁.nreg 390 = m := (e₁.nreg_of_wr (by decide)).trans h390
  have j391 : c₁.nreg 391 = nV := (e₁.nreg_of_wr (by decide)).trans h391
  have j392 : c₁.nreg 392 = nF := (e₁.nreg_of_wr (by decide)).trans h392
  -- 2. the first subdivision
  obtain ⟨c₂, t₂, e₂, ht₂, hA₁, hφ₁, hV₁, hr₂, hm₂, ho₂⟩ := stPhase (P := P) (W := W) M c vn fn
    (c₀ := c₁) (by rw [hm₁]; exact hE) (by unfold StDisj; omega) (by omega) e₁.wb_right hR₁
  have g : ∀ r, 314 < r → c₂.nreg r = c₁.nreg r := fun r h => hr₂ r (by omega) (Or.inr h)
  -- 3. the bases of `trip`
  obtain ⟨c₃, t₃, e₃, ht₃, q303, q304, q316, q319, hm₃, ho₃⟩ : ∃ c₃ t₃, Exec P W inB2 c₂ c₃ t₃ ∧
      t₃ ≤ 4 ∧ c₃.nreg 303 = B₀ + 12 * m ∧ c₃.nreg 304 = B₀ + 15 * m ∧
      c₃.nreg 316 = B₀ + 18 * m ∧ c₃.nreg 319 = 3 * m ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    have hc := e₂.wb_right
    have a326 := (g 326 (by omega)).trans k326
    have a317 := (g 317 (by omega)).trans hR₁.r317
    unfold inB2
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [a326, a317]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [a326, a317]) <;> omega)
  have i₃ : ∀ r, r ≠ 303 → r ≠ 304 → r ≠ 316 → r ≠ 319 → c₃.nreg r = c₂.nreg r :=
    fun r a b d f => e₃.nreg_of_wr (by
      simp only [inB2, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]; omega)
  have g' : ∀ r, 300 < r → r < 310 → c₂.nreg r = c₁.nreg r := fun r a b => hr₂ r a (Or.inl b)
  have i₃' : ∀ r, (305 < r ∧ r < 309) → c₃.nreg r = c₁.nreg r := fun r h =>
    (i₃ r (by omega) (by omega) (by omega) (by omega)).trans (g' r (by omega) (by omega))
  -- 4. the arrays `phi3`, `phi3i`, `· / 3`
  obtain ⟨c₄, t₄, e₄, ht₄, htri, hr₄, hm₄, ho₄⟩ := trip_exec (P := P) (W := W) (K := 3 * m)
    (bφ := B₀ + 12 * m) (bφi := B₀ + 15 * m) (bfn := B₀ + 18 * m) (by omega) (by omega) c₃
    e₃.wb_right q303 q304 ((i₃' 306 (by omega)).trans hR₁.r306)
    ((i₃' 307 (by omega)).trans hR₁.r307) ((i₃' 308 (by omega)).trans hR₁.r308) q316 q319
  have i₄ : ∀ r, 314 < r → r ≠ 316 → r ≠ 319 → c₄.nreg r = c₁.nreg r := fun r a b d =>
    (hr₄ r (by omega) (Or.inr a)).trans ((i₃ r (by omega) (by omega) b d).trans (g r a))
  -- 5. the bases of the second subdivision
  obtain ⟨c₅, t₅, e₅, ht₅, hR₅, hm₅, ho₅⟩ : ∃ c₅ t₅, Exec P W inB3 c₄ c₅ t₅ ∧ t₅ ≤ 7 ∧
      StR (3 * m) (B₀ + 6 * m) (B₀ + 12 * m) (B₀ + 15 * m) 0 (B₀ + 9 * m) (B₀ + 18 * m)
        (11 * (3 * m)) (nV + nF) c₅ ∧ c₅.nmem = c₄.nmem ∧ c₅.output = c₄.output := by
    have hc := e₄.wb_right
    have a326 := (i₄ 326 (by omega) (by omega) (by omega)).trans k326
    have a317 := (i₄ 317 (by omega) (by omega) (by omega)).trans hR₁.r317
    have a391 := (i₄ 391 (by omega) (by omega) (by omega)).trans j391
    have a392 := (i₄ 392 (by omega) (by omega) (by omega)).trans j392
    have a305 : c₄.nreg 305 = B₀ + 6 * m := (hr₄ 305 (by omega) (Or.inl (by omega))).trans
      ((i₃ 305 (by omega) (by omega) (by omega) (by omega)).trans
        ((g' 305 (by omega) (by omega)).trans hR₁.r305))
    have a303 : c₄.nreg 303 = B₀ + 12 * m := (hr₄ 303 (by omega) (Or.inl (by omega))).trans q303
    have a304 : c₄.nreg 304 = B₀ + 15 * m := (hr₄ 304 (by omega) (Or.inl (by omega))).trans q304
    have a316 : c₄.nreg 316 = B₀ + 18 * m := (hr₄ 316 (by omega) (Or.inr (by omega))).trans q316
    have a30x : ∀ r, 305 < r → r < 309 → c₄.nreg r = c₁.nreg r := fun r a b =>
      (hr₄ r (by omega) (Or.inl (by omega))).trans (i₃' r ⟨a, b⟩)
    have a306 := (a30x 306 (by omega) (by omega)).trans hR₁.r306
    have a307 := (a30x 307 (by omega) (by omega)).trans hR₁.r307
    have a308 := (a30x 308 (by omega) (by omega)).trans hR₁.r308
    unfold inB3
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [a326, a317, a391, a392]); omega)
    refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [a326, a317, a391, a392, a305, a303, a304, a316,
      a306, a307, a308]) <;> omega)
  -- 6. the second subdivision
  have hE₂ : Enc M.stellar (M.stCode c) (M.stVi vn fn) (M.stFn c) c₅.nmem (B₀ + 6 * m)
      (B₀ + 12 * m) (B₀ + 15 * m) (B₀ + 9 * m) (B₀ + 18 * m) := by
    rw [hm₅]
    refine enc_stellar M c vn fn (fun x => ?_) hφ₁ (fun x => ?_) (fun y hy => ?_)
    · have := (M.stCode c x).2
      rw [hm₄ _ (by omega) (by omega) (by omega), hm₃]; exact hA₁ x
    · have := (M.stCode c x).2
      rw [hm₄ _ (by omega) (by omega) (by omega), hm₃]; exact hV₁ x
    · exact htri y hy
  obtain ⟨c₆, t₆, e₆, ht₆, hA₂, hφ₂, hV₂, hr₆, hm₆, ho₆⟩ := stPhase (P := P) (W := W)
    M.stellar (M.stCode c) (M.stVi vn fn) (M.stFn c) (c₀ := c₅) hE₂ (by unfold StDisj; omega)
    (by omega) e₅.wb_right hR₅
  set n := nV + nF + m with hn
  set bw := 17 * (3 * m) + 6 * n with hbw
  have hbwB : bw + n ≤ B₀ := by simp only [hbw]; omega
  have i₆ : ∀ r, 318 < r → r ≠ 319 → r ≠ 327 → c₆.nreg r = c₁.nreg r := fun r a b b' =>
    (hr₆ r (by omega) (Or.inr (by omega))).trans ((by
      have : c₅.nreg r = c₄.nreg r := e₅.nreg_of_wr (by
        simp only [inB3, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
          beq_eq_false_iff_ne, ne_eq]; omega)
      exact this.trans (i₄ r (by omega) (by omega) b)))
  -- 7. the bases of the weights
  obtain ⟨c₇, t₇, e₇, ht₇, q321, q322, q330, q338, q339, q340, q307, hm₇, ho₇⟩ :
      ∃ c₇ t₇, Exec P W inB4 c₆ c₇ t₇ ∧ t₇ ≤ 10 ∧ c₇.nreg 321 = nV + nF ∧ c₇.nreg 322 = bw ∧
      c₇.nreg 330 = n ∧ c₇.nreg 338 = m ∧ c₇.nreg 339 = B₀ + 5 * m ∧
      c₇.nreg 340 = bw + (nV + nF) ∧ c₇.nreg 307 = 1 ∧ c₇.nmem = c₆.nmem ∧
      c₇.output = c₆.output := by
    have hc := e₆.wb_right
    have a318 : c₆.nreg 318 = nV + nF := (hr₆ 318 (by omega) (Or.inr (by omega))).trans hR₅.r318
    have a307 : c₆.nreg 307 = 1 := (hr₆ 307 (by omega) (Or.inl (by omega))).trans hR₅.r307
    have a390 := (i₆ 390 (by omega) (by omega) (by omega)).trans j390
    have a326 := (i₆ 326 (by omega) (by omega) (by omega)).trans k326
    have a325 := (i₆ 325 (by omega) (by omega) (by omega)).trans k325
    unfold inB4
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [a318, a390, a326, a325]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [a318, a390, a326, a325, a307, hbw, hn]) <;> omega)
  have i₇ : ∀ r, r ≠ 321 → r ≠ 322 → r ≠ 330 → r ≠ 334 → r ≠ 335 → r ≠ 336 → r ≠ 338 →
      r ≠ 339 → r ≠ 340 → c₇.nreg r = c₆.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 =>
    e₇.nreg_of_wr (by
      simp only [inB4, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]; omega)
  -- 8. the zero weights
  obtain ⟨c₈, t₈, e₈, ht₈, hz₈, hr₈, hm₈, ho₈⟩ := zrclear_exec (P := P) (W := W) (N := nV + nF)
    (b := bw) (by omega) c₇ e₇.wb_right q307 q321 q322
  -- 9. the flags
  obtain ⟨c₉, t₉, e₉, ht₉, hd₉, hr₉, hm₉, ho₉⟩ := cpyN_exec (P := P) (W := W) (N := m)
    (bs := B₀ + 5 * m) (bd := bw + (nV + nF)) (by omega) (by omega) c₈ e₈.wb_right
    ((hr₈ 307 (by omega) (by omega) (by omega)).trans q307)
    ((hr₈ 338 (by omega) (by omega) (by omega)).trans q338)
    ((hr₈ 339 (by omega) (by omega) (by omega)).trans q339)
    ((hr₈ 340 (by omega) (by omega) (by omega)).trans q340)
  -- 10. the registers of `millerA`
  obtain ⟨c', t₁₀, L, e₁₀, ht₁₀, hL1, hL2, hAR, -, hm₁₀, ho₁₀⟩ := aSetup_exec (P := P) (W := W)
    (k := 3 * m) (n := n) (by omega) (by omega) c₉ e₉.wb_right
    ((hr₉ 326 (by omega) (by omega) (by omega)).trans ((hr₈ 326 (by omega) (by omega)
      (by omega)).trans ((i₇ 326 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans ((i₆ 326 (by omega) (by omega)
      (by omega)).trans
      k326))))
    ((hr₉ 330 (by omega) (by omega) (by omega)).trans ((hr₈ 330 (by omega) (by omega)
      (by omega)).trans q330))
  -- the memory
  have M₁₀ : ∀ a, (a < bw ∨ bw + n ≤ a) → c'.nmem a = c₆.nmem a := fun a h => by
    rw [hm₁₀, hm₉ a (by omega), hm₈ a (by omega), hm₇]
  have M₆ : ∀ a, B₀ ≤ a → a < B₀ + 6 * m → c₆.nmem a = c₀.nmem a := fun a h1 h2 => by
    rw [hm₆ a (by omega) (by omega), hm₅, hm₄ a (by omega) (by omega) (by omega), hm₃,
      hm₂ a (by omega) (by omega), hm₁]
  have hk : ∀ y : StDart (StDart D), (M.stellar.stCode (M.stCode c) y : ℕ) < 9 * m := fun y => by
    have := (M.stellar.stCode (M.stCode c) y).2; omega
  have hlogeq : Nat.log 2 n = Nat.log 2 (nV + nF + m) := rfl
  have eAll : Exec P W sepIn c₀ c' _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆
    (.seq e₇ (.seq e₈ (.seq e₉ e₁₀))))))))
  refine ⟨c', _, L, eAll, by omega, hL1, hL2, hAR, fun y => ?_, hφ₂, fun y => ?_,
    fun x => ?_, fun x => ?_,
    fun r h1 h2 => eAll.nreg_of_wr (Stmt.wr_of_wmax (by have := sepIn_wmax; omega)),
    ?_⟩
  · have := hk y
    rw [M₁₀ _ (by omega), ← zero_add (M.stellar.stCode (M.stCode c) y : ℕ), hA₂ y]
  · have := hk y
    rw [M₁₀ _ (by omega), hV₂ y]
  · rcases x with y | F
    · have h1 := (M.stVi vn fn y).2
      have h2 : (M.stellar.stVi (M.stVi vn fn) (M.stFn c) (.inl y) : ℕ) = M.stVi vn fn y :=
        Map.stVi_inl _ _ _ _
      rw [show (aBase (3 * m) (nV + nF + m) L).bw = bw from rfl, h2, hm₁₀, hm₉ _ (by omega),
        hz₈ _ h1]
      rfl
    · have h1 := (M.stFn c F).2
      have h2 : (M.stellar.stVi (M.stVi vn fn) (M.stFn c) (.inr F) : ℕ) =
          (nV + nF) + M.stFn c F := Map.stVi_inr _ _ _ _
      rw [show (aBase (3 * m) (nV + nF + m) L).bw = bw from rfl, h2, hm₁₀, ← Nat.add_assoc,
        hd₉ _ h1, hm₈ _ (by omega), hm₇,
        M₆ _ (by omega) (by omega)]
      have := hfl (c.symm (M.stFn c F))
      rw [Equiv.apply_symm_apply] at this
      rw [this]
      rfl
  · have := (M.stCode c x).2
    rw [M₁₀ _ (by omega), hm₆ _ (by omega) (by omega), hm₅, hm₄ _ (by omega) (by omega)
      (by omega), hm₃]
    exact hA₁ x
  · rw [ho₁₀, ho₉, ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]

lemma sum_wSt_le (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) {fl : D → ℕ} (hfl : ∀ d, fl d ≤ 1) :
    ∑ x, wSt M c fl x ≤ m := by
  rw [Fintype.sum_sum_type]
  simp only [wSt, Sum.elim_inl, sum_const_zero, Sum.elim_inr, zero_add]
  calc ∑ F : M.stellar.Face, fl (c.symm (M.stFn c F)) ≤ ∑ _F : M.stellar.Face, 1 :=
        sum_le_sum fun F _ => hfl _
    _ = m := by
      rw [sum_const, card_univ, smul_eq_mul, mul_one, Fintype.card_congr (M.stFn c),
        Fintype.card_fin]

lemma sum_wSt_pos (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) {fl : D → ℕ} {d : D} (hd : 0 < fl d) :
    0 < ∑ x, wSt M c fl x := by
  have h : 0 < wSt M c fl (.inr (M.stTri d)) := by
    simp only [wSt, Sum.elim_inr, Map.stFn_stTri, Equiv.symm_apply_apply]; exact hd
  exact lt_of_lt_of_le h (single_le_sum (f := wSt M c fl) (fun x _ => Nat.zero_le _)
    (mem_univ _))

set_option maxHeartbeats 4000000 in
/-- **Miller's steps 1–8 on the twice subdivided map, from the plain encoding of `M`.** For a
plane map `M` without loops with `m ≥ 1` darts encoded at `B₀` (`Enc`) with `0/1` flags `fl`,
one of them `1`, the program `sepIn ; millerA` ends within
`221 m + 5 (nV + nF) + 4 log₂ n + 110 + ((231 log₂ n + 1134) 3m + (60 n + 152) log₂ n + 278 n +
637)` steps, `n = nV + nF + m` (the vertices of `M.stellar.stellar`), and the twice subdivided
map has a simple cycle `C` of at most `6 ⌊√n⌋ + 4` darts bounding faces `Z` with both strict
sides of weight at most `2/3` for the weights `wSt c fl / Σ`: the conclusion of
`PlanarSeparator.Map.exists_short_cycle_separator_stellar` for `M.stellar` and these weights,
the band theorem applied to the output of `millerA` (`millerA_band`). The cycle itself is not
yet computed (steps 9–10). -/
theorem sepMiller (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (fl : D → ℕ) {B₀ : ℕ} {c₀ : Config} (hm1 : 1 ≤ m)
    (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hfl1 : ∀ d, fl d ≤ 1) {d₀ : D} (hd₀ : 0 < fl d₀)
    (hE : Enc M c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = fl d)
    (hB : aEnd (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 21 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t, Exec P W (.seq sepIn millerA) c₀ c' t ∧
      t ≤ 221 * m + 5 * (nV + nF) + 4 * Nat.log 2 (nV + nF + m) + 110 +
        ((231 * Nat.log 2 (nV + nF + m) + 1134) * (3 * m) +
          (60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) + 278 * (nV + nF + m) + 637) ∧
      ∃ (C : M.stellar.stellar.SCycle) (Z : Finset M.stellar.stellar.Face),
        C.k ≤ 6 * Nat.sqrt (nV + nF + m) + 4 ∧ IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
        ∑ v ∈ sideIn C Z, wR (wSt M c fl) v ≤ 2 / 3 ∧
        ∑ v ∈ sideOut C Z, wR (wSt M c fl) v ≤ 2 / 3 := by
  obtain ⟨c₁, t₁, L, e₁, ht₁, hL1, hL2, hAR, hA, hφ, hV, hw, -⟩ :=
    sepIn_exec (P := P) (W := W) M c vn fn fl hm1 hE hfl hB hW hc h390 h391 h392 h393
  have hsum := sum_wSt_le M c hfl1
  have hT3 : ∀ δ, M.stellar.stellar.IsTriangle δ :=
    M.stellar.isTriangle_stellar (Map.stellar_loopless hl)
  have hB' := hB
  unfold aEnd at hB'
  obtain ⟨c', t₂, e₂, ht₂, T, l₀, l₂, K₀, h1, h2, h3, hK, C, Z, hk, hsep, hin, hout⟩ :=
    millerA_band (wSt M c fl) (isPlane_stellar (isPlane_stellar hM)) hT3 (by omega)
      (A := fun x => c₁.nmem x) (V := fun x => c₁.nmem (11 * (3 * m) + x)) hA hφ hV
      (sum_wSt_pos M c hd₀) (aLay_of hL1 hL2 (by unfold aEnd; omega)) (by omega)
      e₁.wb_right hAR (fun _ _ => rfl) (fun _ _ => rfl) hw
  refine ⟨c', t₁ + t₂, .seq e₁ e₂, by omega, C, Z, ?_, hsep, hin, hout⟩
  have h3' := Map.le_sqrt_of_mul_le' h3
  rcases hK with ⟨rfl, rfl⟩ | ⟨-, hK, hK'⟩
  · rw [card_singleton] at hk; omega
  · have := (card_le_card hK).trans (Map.le_sqrt_of_mul_le' hK'); omega

end Phase

end MillerProg

end PlanarSeparator
