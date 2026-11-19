module

public import PlanarFlow.NegSSSP.KEncCotPrep
public import WordRAM.Machine.RealsToNat

/-!
# The cotree of the one-face encoding, on the machine

The cotree of a spanning tree `T` of the dual (`Klein.KInit`, `Klein.KVal`) is computed by
`cotProg`: the inputs of the search (`cpPrep`: keep flags off `T`, keys and heads by faces), the
out-lists of the faces through the darts off `T` (`osProg`), the search with its parents
(`ctProg`), and the depth orders of the resulting tree (`toProg`).

* `osProg_bfs`: the out-lists written by `osProg` as inputs of the search (`BfsIn`).
* `cot_of_search`: **the recorded parents are a cotree** (on a plane map): a tree of the faces
  rooted at the source face whose parent darts are off `T` (`dtree_of_ct`, with the
  connectivity `STFlow.DTree.cotree_conn`).
* `inT_iff_it`: the keep flags of `cpPrep` from the parent darts `IT` of the order of `T` are
  the darts off `T`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge
  Monge.FR

variable {P : Input} {W : ℕ}

/-! ### The out-lists as inputs of the search -/

lemma mem_of_mem_pre {L : List (ℕ × ℕ × ℤ)} {N : ℕ} {a : ℕ × ℕ × ℤ} (h : a ∈ pre L N) :
    a ∈ L := by
  unfold pre at h
  obtain ⟨u, -, hu⟩ := List.mem_flatMap.1 h
  exact List.mem_of_mem_filter hu

lemma sum_pre_blk (L : List (ℕ × ℕ × ℤ)) (N : ℕ) :
    ∑ u ∈ range N, ((pre L (u + 1)).length - (pre L u).length) = (pre L N).length := by
  induction N with
  | zero => simp [pre]
  | succ N ih => rw [sum_range_succ, ih, length_pre_succ L N]; omega

section Out

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M N Tb Kb Ob Cb OBb OEb Db : ℕ} {T K : ℕ → ℕ}

/-- **The out-lists of a piece as inputs of the search**: `osProg_out`, and the offsets
nondecreasing below a bound `mm ≤ nD` (the number of kept darts), the words of `OL` below `mm`
dart numbers, the out-degrees summing to at most `mm`. -/
theorem osProg_bfs {Mp : CombMap D V F} {S : Finset D} {nD : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < N) (hT : ∀ d, T (σ d) = ιv (Mp.tail d))
    (hK : ∀ d, K (σ d) = if d ∈ S then 1 else 0)
    (hL : OsLay nD N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn nD N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost nD N ∧ OutMem Mp S σ ιv c'.nmem OBb OEb Db ∧
      (∃ mm ≤ nD, (∀ x < N, c'.nmem (OBb + x) ≤ c'.nmem (OEb + x) ∧ c'.nmem (OEb + x) ≤ mm) ∧
        (∀ e < mm, c'.nmem (Db + e) < nD) ∧
        ∑ u ∈ range N, (c'.nmem (OEb + u) - c'.nmem (OBb + u)) ≤ mm) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hOB, hOL, -, -, -, -, -⟩ := osProg_exec (P := P) hL c hc hI
  obtain ⟨c'', k', ex', hk', hO, hm, hn, hr, hrm, ho⟩ :=
    osProg_out (P := P) (M := Mp) (S := S) σ hinj hιv hT hK hL c hc hI
  obtain ⟨rfl, rfl⟩ := Exec.det ex ex'
  set L := csList T id K (fun _ => 0) nD with hLd
  refine ⟨c', k, ex, hk, hO, ⟨(pre L N).length, (length_pre_le _ _).trans (length_csList_le nD),
    fun x hx => ?_, fun e he => ?_, ?_⟩, hm, hn, hr, hrm, ho⟩
  · rw [(hOB x hx).1, (hOB x hx).2, length_pre_succ]
    have := length_pre_mono L (show x + 1 ≤ N by omega)
    rw [length_pre_succ] at this
    exact ⟨by omega, by omega⟩
  · rw [hOL e he, List.getD_eq_getElem _ _ he]
    obtain ⟨i, hi, -, e'⟩ := (mem_csList _).1 (mem_of_mem_pre (List.getElem_mem he))
    rw [e']; exact hi
  · rw [← sum_pre_blk L N]
    exact (sum_congr rfl fun u hu => by
      rw [(hOB u (mem_range.1 hu)).1, (hOB u (mem_range.1 hu)).2]).le

end Out

/-! ### The cotree from the recorded parents -/

section Cot

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The recorded parents are a cotree**: on a plane map, from the out-lists of the faces
through the darts off a spanning tree `T` of the dual (`OutMem` on `M.dual`, the faces numbered
by `τ`) with heads the faces of the reverses, at the end of the search from the face `fe`
(`CtSt`, closed), the recorded parent arcs are the parent darts of a tree of the faces rooted
at `fe`, all off `T`. -/
theorem cot_of_search [Nonempty D] (hM : M.IsPlane) (T : STFlow.DTree M.dual) {nF nD qt : ℕ}
    (τ : F ≃ Fin nF) (σ : D ≃ Fin nD) (fe : F) {mem₂ mem₃ : ℕ → ℕ}
    {OBb OEb OLb HHb Mb Qb PAb : ℕ}
    (hO : OutMem M.dual (univ.filter fun d => ¬ T.InT d) σ (fun y => (τ y : ℕ)) mem₂ OBb OEb
      OLb)
    (hH : ∀ d, mem₂ (HHb + σ d) = τ (M.face (M.rev d)))
    (hS : CtSt nF (τ fe) Mb Qb PAb qt (fun u => mem₂ (OBb + u)) (fun u => mem₂ (OEb + u))
      (fun i => mem₂ (OLb + i)) (fun a => mem₂ (HHb + a)) mem₃)
    (hcl : BfsClosed Qb qt qt (BfsAdj (fun u => mem₂ (OBb + u)) (fun u => mem₂ (OEb + u))
      (fun i => mem₂ (OLb + i)) (fun a => mem₂ (HHb + a))) mem₃) :
    ∃ C : STFlow.DTree M, C.root = fe ∧ (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
      ∀ y, y ≠ C.root → mem₃ (PAb + τ y) = σ (C.par y) := by
  classical
  have hsnd : ∀ y i, mem₂ (OBb + τ y) ≤ i → i < mem₂ (OEb + τ y) →
      ∃ d, ¬ T.InT d ∧ M.face d = y ∧ mem₂ (OLb + i) = σ d := by
    intro y i h1 h2
    obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO y
    have hj : i - mem₂ (OBb + τ y) < ds.length := by
      simp only at hl; omega
    have e := hds _ hj
    rw [show mem₂ (OBb + τ y) + (i - mem₂ (OBb + τ y)) = i by omega] at e
    obtain ⟨h3, h4⟩ := (hmem _).1 (List.getElem_mem hj)
    exact ⟨_, (mem_filter.1 h3).2, h4, e⟩
  have hcmp : ∀ d, ¬ T.InT d → ∃ i, mem₂ (OBb + τ (M.face d)) ≤ i ∧
      i < mem₂ (OEb + τ (M.face d)) ∧ mem₂ (OLb + i) = σ d := by
    intro d hd
    obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO (M.face d)
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ((hmem d).2 ⟨mem_filter.2 ⟨mem_univ _, hd⟩, rfl⟩)
    refine ⟨mem₂ (OBb + τ (M.face d)) + j, by omega, by simp only at hl; omega, ?_⟩
    rw [hds j hj, e]
  have hhd : ∀ d, ¬ T.InT d → mem₂ (HHb + σ d) = τ (M.face (M.rev d)) := fun d _ => hH d
  have hall := ct_all (N := M) (ob := fun u => mem₂ (OBb + u)) (oe := fun u => mem₂ (OEb + u))
    (ol := fun i => mem₂ (OLb + i)) (hd := fun a => mem₂ (HHb + a)) τ σ fe hcmp hhd
    (fun y => T.cotree_conn hM.dual fe y) hS hcl
  obtain ⟨C, hr, hA, hP⟩ := dtree_of_ct (N := M) (ob := fun u => mem₂ (OBb + u))
    (oe := fun u => mem₂ (OEb + u)) (ol := fun i => mem₂ (OLb + i))
    (hd := fun a => mem₂ (HHb + a)) τ σ fe hsnd hhd hS hall
  exact ⟨C, hr, hA, hP⟩

/-- **The keep flags of `cpPrep`**: with `IT[j] = σ (T.par ts[j])` for the order `ts` of the
vertices but the root, and `RV[σ d] = σ (rev d)`, a dart is a parent dart `IT[j]` or its reverse
exactly when it is in `T`. -/
theorem inT_iff_it (T : STFlow.DTree M.dual) {nD : ℕ} (σ : D ≃ Fin nD) {ts : List V}
    (hts : ∀ y, y ∈ ts ↔ y ≠ T.root) {mem : ℕ → ℕ} {ITb RVb : ℕ}
    (hIT : ∀ j (h : j < ts.length), mem (ITb + j) = σ (T.par ts[j]))
    (hRV : ∀ d, mem (RVb + σ d) = σ (M.rev d)) (d : D) :
    (∃ j < ts.length, (σ d : ℕ) = mem (ITb + j) ∨ (σ d : ℕ) = mem (RVb + mem (ITb + j))) ↔
      T.InT d := by
  constructor
  · rintro ⟨j, hj, h | h⟩
    · rw [hIT j hj] at h
      exact ⟨ts[j], (hts _).1 (List.getElem_mem hj), Or.inl (σ.injective (Fin.ext h))⟩
    · rw [hIT j hj, hRV] at h
      exact ⟨ts[j], (hts _).1 (List.getElem_mem hj), Or.inr (σ.injective (Fin.ext h))⟩
  · rintro ⟨x, hx, h | h⟩
    · obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ((hts x).2 hx)
      exact ⟨j, hj, Or.inl (by rw [hIT j hj, e, h])⟩
    · obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ((hts x).2 hx)
      exact ⟨j, hj, Or.inr (by rw [hIT j hj, hRV, e, h]; rfl)⟩


/-! ### The out-lists of the faces off the spanning tree, on the machine -/

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The out-lists of the faces through the darts off `T`**: `cpPrep` then `osProg`, from the
parent darts `IT[j] = σ (T.par ts[j])` (`ts` the vertices but the root), `RV[σ d] = σ (rev d)`
and `NF[σ d] = of + τ (face d)` below the scratch `Z`: the out-lists `OutMem` on `M.dual` of
the darts off `T` by the faces numbered `τ` at `Z + 3 nD + 2 nF + 1` (`OB`), `… + nF` (`OE`),
`… + 2 nF` (`OL`), the heads `HH[σ d] = τ (face (rev d))` at `Z + 2 nD`; the natural memory
changes only in `[Z, Z + 4 nD + 4 nF + 1)`. -/
theorem cotOut_exec (T : STFlow.DTree M.dual) {nD nF : ℕ} (σ : D ≃ Fin nD) (τ : F ≃ Fin nF)
    {ts : List V} (hts : ∀ y, y ∈ ts ↔ y ≠ T.root) {ITb RVb NFb of Z : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (r00 : c.nreg 1700 = nD) (r01 : c.nreg 1701 = ts.length) (r02 : c.nreg 1702 = ITb)
    (r03 : c.nreg 1703 = RVb) (r04 : c.nreg 1704 = NFb) (r05 : c.nreg 1705 = of)
    (r06 : c.nreg 1706 = Z)
    (s00 : c.nreg 1500 = nD) (s01 : c.nreg 1501 = nF) (s02 : c.nreg 1502 = Z + nD)
    (s04 : c.nreg 1504 = Z) (s05 : c.nreg 1505 = Z + 3 * nD)
    (s06 : c.nreg 1506 = Z + 3 * nD + nF + 1) (s07 : c.nreg 1507 = Z + 3 * nD + 2 * nF + 1)
    (s08 : c.nreg 1508 = Z + 3 * nD + 3 * nF + 1) (s09 : c.nreg 1509 = Z + 3 * nD + 4 * nF + 1)
    (hIT : ∀ j (h : j < ts.length), c.nmem (ITb + j) = σ (T.par ts[j]))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d))
    (hNF : ∀ d, c.nmem (NFb + σ d) = of + τ (M.face d))
    (lI : ITb + ts.length ≤ Z) (lR : RVb + nD ≤ Z) (lN : NFb + nD ≤ Z)
    (wZ : Z + 4 * nD + 4 * nF + 1 ≤ W) (w1 : nD + 1 ≤ W) (w2 : nF + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq cpPrep osProg) c c' t ∧
      t ≤ 17 * nD + 11 * ts.length + 10 + osCost nD nF ∧
      OutMem M.dual (univ.filter fun d => ¬ T.InT d) σ (fun y => (τ y : ℕ)) c'.nmem
        (Z + 3 * nD + 2 * nF + 1) (Z + 3 * nD + 3 * nF + 1) (Z + 3 * nD + 4 * nF + 1) ∧
      (∃ mm ≤ nD, (∀ x < nF, c'.nmem (Z + 3 * nD + 2 * nF + 1 + x) ≤
          c'.nmem (Z + 3 * nD + 3 * nF + 1 + x) ∧ c'.nmem (Z + 3 * nD + 3 * nF + 1 + x) ≤ mm) ∧
        (∀ e < mm, c'.nmem (Z + 3 * nD + 4 * nF + 1 + e) < nD) ∧
        ∑ u ∈ range nF, (c'.nmem (Z + 3 * nD + 3 * nF + 1 + u) -
          c'.nmem (Z + 3 * nD + 2 * nF + 1 + u)) ≤ mm) ∧
      (∀ d, c'.nmem (Z + 2 * nD + σ d) = τ (M.face (M.rev d))) ∧
      (∀ a, a < Z ∨ Z + 4 * nD + 4 * nF + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ (1520 < r ∧ r < 1707) ∨ 1719 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hit : ∀ j < ts.length, c.nmem (ITb + j) < nD := fun j hj => by
    rw [hIT j hj]; exact (σ _).2
  have hrv : ∀ i < nD, c.nmem (RVb + i) < nD := fun i hi => by
    have := hRV (σ.symm ⟨i, hi⟩); rw [Equiv.apply_symm_apply] at this
    rw [this]; exact (σ _).2
  obtain ⟨c₁, k₁, e₁, hk₁, KE₁, KY₁, HH₁, m₁, n₁, rr₁, rm₁, o₁⟩ :=
    cpPrep_exec (P := P) (Ob := Z) c hc r00 r01 r02 r03 r04 r05 r06 hit hrv (Or.inl lI)
      (Or.inl lR) (Or.inl lN) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw₁ := e₁.wb_right
  set S : Finset D := univ.filter fun d => ¬ T.InT d with hS
  have hKE : ∀ d, c₁.nmem (Z + σ d) = if d ∈ S then 1 else 0 := fun d => by
    rw [KE₁ _ (σ d).2]
    have hiff := inT_iff_it (M := M) T σ hts (mem := c.nmem) hIT hRV d
    by_cases h : T.InT d
    · simp only [hiff.2 h, ↓reduceIte, hS, mem_filter, mem_univ, true_and, h, not_true_eq_false]
    · have : ¬ ∃ j < ts.length, (σ d : ℕ) = c.nmem (ITb + j) ∨
          (σ d : ℕ) = c.nmem (RVb + c.nmem (ITb + j)) := fun h' => h (hiff.1 h')
      simp only [this, ↓reduceIte, hS, mem_filter, mem_univ, true_and, h, not_false_eq_true]
  have hKY : ∀ d, c₁.nmem (Z + nD + σ d) = τ (M.dual.tail d) := fun d => by
    rw [KY₁ _ (σ d).2, hNF, Nat.add_sub_cancel_left]; rfl
  have hHH : ∀ d, c₁.nmem (Z + 2 * nD + σ d) = τ (M.face (M.rev d)) := fun d => by
    rw [HH₁ _ (σ d).2, hRV, hNF]; omega
  have g : ∀ r, 1500 ≤ r → r ≤ 1509 → c₁.nreg r = c.nreg r := fun r h1 h2 => n₁ r (by omega)
  have hL : OsLay nD nF (Z + nD) Z (Z + 3 * nD) (Z + 3 * nD + nF + 1) (Z + 3 * nD + 2 * nF + 1)
      (Z + 3 * nD + 3 * nF + 1) (Z + 3 * nD + 4 * nF + 1) W
      (fun i => c₁.nmem (Z + nD + i)) (fun i => c₁.nmem (Z + i)) := by
    refine ⟨fun i hi _ => ?_, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    have := hKY (σ.symm ⟨i, hi⟩)
    rw [Equiv.apply_symm_apply] at this
    simp only [this]; exact (τ _).2
  have hI : OsIn nD nF (Z + nD) Z (Z + 3 * nD) (Z + 3 * nD + nF + 1) (Z + 3 * nD + 2 * nF + 1)
      (Z + 3 * nD + 3 * nF + 1) (Z + 3 * nD + 4 * nF + 1)
      (fun i => c₁.nmem (Z + nD + i)) (fun i => c₁.nmem (Z + i)) c₁ :=
    ⟨(g _ (by omega) (by omega)).trans s00, (g _ (by omega) (by omega)).trans s01,
      (g _ (by omega) (by omega)).trans s02, (g _ (by omega) (by omega)).trans s04,
      (g _ (by omega) (by omega)).trans s05, (g _ (by omega) (by omega)).trans s06,
      (g _ (by omega) (by omega)).trans s07, (g _ (by omega) (by omega)).trans s08,
      (g _ (by omega) (by omega)).trans s09, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hO, hmm, m₂, n₂, rr₂, rm₂, o₂⟩ :=
    osProg_bfs (P := P) (Mp := M.dual) (S := S) σ (ιv := fun y => (τ y : ℕ))
      (fun a b h => τ.injective (Fin.ext h)) (fun y => (τ y).2) hKY hKE hL c₁ hw₁ hI
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, hO, hmm, fun d => ?_, fun a ha => ?_,
    fun r hr => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · have := (σ d).2
    rw [m₂ _ (Or.inl (by omega)) (Or.inl (by omega))]; exact hHH d
  · rw [m₂ _ (by omega) (by omega), m₁ _ (by omega)]
  · rw [n₂ r (by omega), n₁ r (by omega)]


/-! ### The search and the cotree, on the machine -/

/-- The source given the parent word `0` (`PA[s] := 0`), the search giving it none. -/
def cpFix : Stmt := block [.addN 1421 1408 1401, .constN 1422 0, .storeN 1421 1422]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The cotree on the machine**: `cotOut_exec`, then the search with its parents `ctProg`
from the face `fe` (`r1400 … r1408` = `nF, τ fe, OB, OE, OL, HH, Mb, Qb, PAb`, the marks, the
queue and the parents `PA` at `Mb = Z + 4 nD + 4 nF + 1`, `Mb + nF`, `Mb + 2 nF`), and
`PA[τ fe] := 0`: on a plane map, **a cotree `C` of `T` rooted at `fe`** with
`PA[τ y] = σ (C.par y)` (`y ≠ fe`) and `PA[τ fe] = 0`; the natural memory changes only in
`[Z, Z + 4 nD + 7 nF + 1)`. -/
theorem cotSearch_exec [Nonempty D] (hM : M.IsPlane) (T : STFlow.DTree M.dual) {nD nF : ℕ}
    (σ : D ≃ Fin nD) (τ : F ≃ Fin nF) (fe : F)
    {ts : List V} (hts : ∀ y, y ∈ ts ↔ y ≠ T.root) {ITb RVb NFb of Z : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (r00 : c.nreg 1700 = nD) (r01 : c.nreg 1701 = ts.length) (r02 : c.nreg 1702 = ITb)
    (r03 : c.nreg 1703 = RVb) (r04 : c.nreg 1704 = NFb) (r05 : c.nreg 1705 = of)
    (r06 : c.nreg 1706 = Z)
    (s00 : c.nreg 1500 = nD) (s01 : c.nreg 1501 = nF) (s02 : c.nreg 1502 = Z + nD)
    (s04 : c.nreg 1504 = Z) (s05 : c.nreg 1505 = Z + 3 * nD)
    (s06 : c.nreg 1506 = Z + 3 * nD + nF + 1) (s07 : c.nreg 1507 = Z + 3 * nD + 2 * nF + 1)
    (s08 : c.nreg 1508 = Z + 3 * nD + 3 * nF + 1) (s09 : c.nreg 1509 = Z + 3 * nD + 4 * nF + 1)
    (b00 : c.nreg 1400 = nF) (b01 : c.nreg 1401 = τ fe)
    (b02 : c.nreg 1402 = Z + 3 * nD + 2 * nF + 1) (b03 : c.nreg 1403 = Z + 3 * nD + 3 * nF + 1)
    (b04 : c.nreg 1404 = Z + 3 * nD + 4 * nF + 1) (b05 : c.nreg 1405 = Z + 2 * nD)
    (b06 : c.nreg 1406 = Z + 4 * nD + 4 * nF + 1) (b07 : c.nreg 1407 = Z + 4 * nD + 5 * nF + 1)
    (b08 : c.nreg 1408 = Z + 4 * nD + 6 * nF + 1)
    (hIT : ∀ j (h : j < ts.length), c.nmem (ITb + j) = σ (T.par ts[j]))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d))
    (hNF : ∀ d, c.nmem (NFb + σ d) = of + τ (M.face d))
    (lI : ITb + ts.length ≤ Z) (lR : RVb + nD ≤ Z) (lN : NFb + nD ≤ Z)
    (wZ : Z + 4 * nD + 7 * nF + 2 ≤ W) (w1 : nD + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq (.seq cpPrep osProg) (.seq ctProg cpFix)) c c' t ∧
      t ≤ 17 * nD + 11 * ts.length + 10 + osCost nD nF + (35 * nF + 19 * nD + 12) + 3 ∧
      (∃ C : STFlow.DTree M, C.root = fe ∧ (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
        (∀ y, y ≠ C.root → c'.nmem (Z + 4 * nD + 6 * nF + 1 + τ y) = σ (C.par y)) ∧
        c'.nmem (Z + 4 * nD + 6 * nF + 1 + τ C.root) = 0) ∧
      (∀ a, a < Z ∨ Z + 4 * nD + 7 * nF + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1410 ∨ (1422 < r ∧ r < 1510) ∨ (1520 < r ∧ r < 1707) ∨ 1719 < r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hfe := (τ fe).2
  obtain ⟨c₂, k₂, e₂, hk₂, hO, ⟨mm, hmm, hbe, hol, hdeg⟩, hHH, m₂, n₂, rr₂, rm₂, o₂⟩ :=
    cotOut_exec (P := P) T σ τ hts c hc r00 r01 r02 r03 r04 r05 r06 s00 s01 s02 s04 s05 s06 s07
      s08 s09 hIT hRV hNF lI lR lN (by omega) w1 (by omega)
  have hw₂ := e₂.wb_right
  set OBb := Z + 3 * nD + 2 * nF + 1 with hOBb
  set OEb := Z + 3 * nD + 3 * nF + 1 with hOEb
  set OLb := Z + 3 * nD + 4 * nF + 1 with hOLb
  set HHb := Z + 2 * nD with hHHb
  set Mb := Z + 4 * nD + 4 * nF + 1 with hMb
  set Qb := Z + 4 * nD + 5 * nF + 1 with hQb
  set PAb := Z + 4 * nD + 6 * nF + 1 with hPAb
  have g : ∀ r, 1400 ≤ r → r ≤ 1408 → c₂.nreg r = c.nreg r := fun r h1 h2 => n₂ r (by omega)
  have hL : BfsLay nF mm nD OBb OEb OLb HHb Mb Qb Mb W :=
    ⟨by omega, by omega, by omega, by omega, le_rfl, by omega, by omega⟩
  have hI : BfsIn nF mm nD (τ fe) OBb OEb OLb HHb (fun u => c₂.nmem (OBb + u))
      (fun u => c₂.nmem (OEb + u)) (fun i => c₂.nmem (OLb + i)) (fun a => c₂.nmem (HHb + a))
      c₂.nmem := by
    refine ⟨hfe, fun _ _ => rfl, fun _ _ => rfl, fun u hu => (hbe u hu).1,
      fun u hu => (hbe u hu).2, fun _ _ => rfl, fun i hi => hol i hi, fun _ _ => rfl,
      fun a ha => ?_, hdeg⟩
    have := hHH (σ.symm ⟨a, ha⟩)
    rw [Equiv.apply_symm_apply] at this
    simp only [this]; exact (τ _).2
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨qt, hS, hcl⟩, -, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    ctProg_exec (P := P) hL (by omega) (by omega) c₂ hw₂ ((g _ (by omega) (by omega)).trans b00)
      ((g _ (by omega) (by omega)).trans b01) ((g _ (by omega) (by omega)).trans b02)
      ((g _ (by omega) (by omega)).trans b03) ((g _ (by omega) (by omega)).trans b04)
      ((g _ (by omega) (by omega)).trans b05) ((g _ (by omega) (by omega)).trans b06)
      ((g _ (by omega) (by omega)).trans b07) ((g _ (by omega) (by omega)).trans b08) hI
  obtain ⟨C, hCr, hoff, hPA⟩ := cot_of_search hM T τ σ fe hO hHH hS hcl
  have hw₃ := e₃.wb_right
  have q01 : c₃.nreg 1401 = τ fe := by
    rw [n₃ _ (by omega), g _ (by omega) (by omega)]; exact b01
  have q08 : c₃.nreg 1408 = PAb := by
    rw [n₃ _ (by omega), g _ (by omega) (by omega)]; exact b08
  obtain ⟨c₄, k₄, e₄, hk₄, hm₄, hn₄, rr₄, rm₄, o₄⟩ : ∃ c₄ k₄, Exec P W cpFix c₃ c₄ k₄ ∧ k₄ = 3 ∧
      c₄.nmem = upd c₃.nmem (PAb + τ fe) 0 ∧
      (∀ r, r ≠ 1421 → r ≠ 1422 → c₄.nreg r = c₃.nreg r) ∧ c₄.rreg = c₃.rreg ∧
      c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    unfold cpFix
    exec_block
    all_goals try ((try config_simp); (try simp only [q01, q08]); omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [q01, q08]
    · config_simp; simp only [upd_apply, h1, h2, ↓reduceIte]
  refine ⟨c₄, k₂ + (k₃ + k₄), Exec.seq e₂ (Exec.seq e₃ e₄), by omega,
    ⟨C, hCr, hoff, fun y hy => ?_, ?_⟩, fun a ha => ?_, fun r hr => ?_, by rw [rr₄, rr₃, rr₂],
    by rw [rm₄, rm₃, rm₂], by rw [o₄, o₃, o₂]⟩
  · have hne : (τ y : ℕ) ≠ τ fe := fun h => hy (by rw [hCr]; exact τ.injective (Fin.ext h))
    rw [hm₄]
    simp only [upd_apply, show PAb + (τ y : ℕ) ≠ PAb + τ fe by omega, ↓reduceIte]
    exact hPA y hy
  · rw [hm₄, hCr]; simp
  · rw [hm₄]
    simp only [upd_apply, show a ≠ PAb + τ fe by omega, ↓reduceIte]
    rw [m₃ _ (by omega) (by omega), m₂ _ (by omega)]
  · rw [hn₄ r (by omega) (by omega), n₃ r (by omega), n₂ r (by omega)]


/-- **The cotree program**: the inputs of the search, the out-lists, the search with its parents,
the depth orders of the cotree. -/
def cotProg : Stmt := .seq (.seq (.seq cpPrep osProg) (.seq ctProg cpFix)) toProg

/-- The cost bound of `cotProg` (`nD` darts, `nF` faces, `lt` parent darts of `T`). -/
def cotCost (nD nF lt : ℕ) : ℕ := 65 * nD + 178 * nF + 11 * lt + 105

set_option maxHeartbeats 4000000 in
/-- **The cotree and its orders on the machine** (natural words only): on a plane map with a
spanning tree `T` of the dual given by the parent darts `IT[j] = σ (T.par ts[j])` of its order
(`ts` the vertices but the root), the reversal `RV[σ d] = σ (rev d)` and the nodes of the faces
`NF[σ d] = of + τ (face d)`, `cotProg` ends within `cotCost nD nF |ts|` steps with **a cotree `C`
of `T` rooted at `fe`** and an order `cs` with `Klein.Orders C fs cs` (`fs` all the faces by
their numbers), `IF[i] = of + τ fs[i]`, `IC[i] = σ (C.par cs[i])`, `HD = [|fs|, |cs|]` (at
`IVb`, `ITc`, `HDc`): the fields `oC`, `if_`, `ic`, `l2`, `l3` of `Klein.KInit` and the
conditions on the cotree in `Klein.KVal` for the node layout `ιf = of + τ`. The natural memory
changes only in the scratch `[Z, Z + 4 nD + 15 nF + 2)` and the outputs `[IVb, HDc + 2)`. -/
theorem cotProg_exec [Nonempty D] (hM : M.IsPlane) (T : STFlow.DTree M.dual) {nD nF : ℕ}
    (σ : D ≃ Fin nD) (τ : F ≃ Fin nF) (fe : F)
    {ts : List V} (hts : ∀ y, y ∈ ts ↔ y ≠ T.root) {ITb RVb NFb of Z IVb ITc HDc : ℕ}
    (c : Config) (hc : WordsBounded W c)
    (r00 : c.nreg 1700 = nD) (r01 : c.nreg 1701 = ts.length) (r02 : c.nreg 1702 = ITb)
    (r03 : c.nreg 1703 = RVb) (r04 : c.nreg 1704 = NFb) (r05 : c.nreg 1705 = of)
    (r06 : c.nreg 1706 = Z)
    (s00 : c.nreg 1500 = nD) (s01 : c.nreg 1501 = nF) (s02 : c.nreg 1502 = Z + nD)
    (s04 : c.nreg 1504 = Z) (s05 : c.nreg 1505 = Z + 3 * nD)
    (s06 : c.nreg 1506 = Z + 3 * nD + nF + 1) (s07 : c.nreg 1507 = Z + 3 * nD + 2 * nF + 1)
    (s08 : c.nreg 1508 = Z + 3 * nD + 3 * nF + 1) (s09 : c.nreg 1509 = Z + 3 * nD + 4 * nF + 1)
    (b00 : c.nreg 1400 = nF) (b01 : c.nreg 1401 = τ fe)
    (b02 : c.nreg 1402 = Z + 3 * nD + 2 * nF + 1) (b03 : c.nreg 1403 = Z + 3 * nD + 3 * nF + 1)
    (b04 : c.nreg 1404 = Z + 3 * nD + 4 * nF + 1) (b05 : c.nreg 1405 = Z + 2 * nD)
    (b06 : c.nreg 1406 = Z + 4 * nD + 4 * nF + 1) (b07 : c.nreg 1407 = Z + 4 * nD + 5 * nF + 1)
    (b08 : c.nreg 1408 = Z + 4 * nD + 6 * nF + 1)
    (hR : ToRegs nF (τ fe) (Z + 4 * nD + 7 * nF + 1) (Z + 4 * nD + 6 * nF + 1) NFb IVb ITc HDc
      of c)
    (hIT : ∀ j (h : j < ts.length), c.nmem (ITb + j) = σ (T.par ts[j]))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d))
    (hNF : ∀ d, c.nmem (NFb + σ d) = of + τ (M.face d))
    (lI : ITb + ts.length ≤ Z) (lR : RVb + nD ≤ Z) (lN : NFb + nD ≤ Z) (lO : HDc + 2 ≤ Z)
    (liv : IVb + nF ≤ ITc) (lit : ITc + nF ≤ HDc)
    (wZ : Z + 4 * nD + 15 * nF + 2 ≤ W) (w1 : nD + 1 ≤ W) (wo : of + nF ≤ W) :
    ∃ c' t, Exec P W cotProg c c' t ∧ t ≤ cotCost nD nF ts.length ∧
      ∃ (C : STFlow.DTree M) (cs : List F), C.root = fe ∧
        (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧
        Klein.Orders C ((List.finRange nF).map τ.symm) cs ∧
        (∀ i (h : i < ((List.finRange nF).map τ.symm).length),
          c'.nmem (IVb + i) = of + τ ((List.finRange nF).map τ.symm)[i]) ∧
        (∀ i (h : i < cs.length), c'.nmem (ITc + i) = σ (C.par cs[i])) ∧
        c'.nmem HDc = ((List.finRange nF).map τ.symm).length ∧ c'.nmem (HDc + 1) = cs.length ∧
        (∀ a, a < Z ∨ Z + 4 * nD + 15 * nF + 2 ≤ a → a < IVb ∨ HDc + 2 ≤ a →
          c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1410 ∨ (1422 < r ∧ r < 1500) ∨ (1520 < r ∧ r < 1620) ∨
          (1634 < r ∧ r < 1707) ∨ 1719 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hfe := (τ fe).2
  have hD : 0 < nD := Fin.pos (σ (Classical.arbitrary D))
  obtain ⟨c₄, k₄, e₄, hk₄, ⟨C, hCr, hoff, hPA, hPA0⟩, m₄, n₄, rr₄, rm₄, o₄⟩ :=
    cotSearch_exec (P := P) hM T σ τ fe hts c hc r00 r01 r02 r03 r04 r05 r06 s00 s01 s02 s04 s05
      s06 s07 s08 s09 b00 b01 b02 b03 b04 b05 b06 b07 b08 hIT hRV hNF lI lR lN (by omega) w1
  have hR₄ : ToRegs nF (τ C.root) (Z + 4 * nD + 7 * nF + 1) (Z + 4 * nD + 6 * nF + 1) NFb IVb
      ITc HDc of c₄ := by
    rw [hCr]; exact hR.frame fun r h1 h2 => n₄ r (by omega)
  have hL : ToLay nF nD (τ C.root) (Z + 4 * nD + 7 * nF + 1) (Z + 4 * nD + 6 * nF + 1) NFb IVb
      ITc HDc of W := by
    rw [hCr]
    exact ⟨by omega, hfe, by omega, by omega, by omega, by omega, liv, lit, by omega, by omega,
      by omega, by omega, wo⟩
  obtain ⟨c₅, k₅, e₅, hk₅, cs, hOr, hIV, hIC, hH0, hH1, m₅, n₅, rr₅, rm₅, o₅⟩ :=
    toProg_orders (P := P) C σ τ hL c₄ e₄.wb_right hR₄ hPA (by rw [hPA0]; exact hD)
      (fun d => by rw [m₄ _ (by have := (σ d).2; omega)]; exact hNF d)
  refine ⟨c₅, k₄ + k₅, Exec.seq e₄ e₅, by unfold cotCost; unfold osCost toCost at *; omega,
    C, cs, hCr, hoff, hOr, hIV, hIC, hH0, hH1, fun a h1 h2 => ?_, fun r hr => ?_,
    by rw [rr₅, rr₄], by rw [rm₅, rm₄], by rw [o₅, o₄]⟩
  · rw [m₅ a (by omega) h2, m₄ a (by omega)]
  · rw [n₅ r (by omega), n₄ r (by omega)]

end Cot

end NegSSSP

end PlanarFlow
