module

public import PlanarFlow.NegSSSP.Enc.SrcTree

/-!
# A spanning tree of the vertices by a search, on the machine

`tree_compat_hyp` builds the initial tree `T` of Klein's encoding from the shortest-path tree of
the first root and any tree `C₀ : DTree M.dual` of the vertices rooted there. Here `C₀` is
computed: the out-lists of **all** the darts by the node of their tail (`osProg` with all keep
flags `1`), then the search recording its parents (`ctProg`) from the node of the root.

* `vt_of_search`: on a connected map (`IsPlane`), the recorded parents of a complete search are
  the parent darts of a tree of the vertices (`dtree_of_ct` on `M.dual`, `ct_all`).
* `vtSearch_exec`: **the program `osProg ; ctProg`** (natural words only), from the nodes of the
  tails at `Tb` (`NT`), ones at `Kb`, the nodes of the heads at `HHb` (`NH`), within
  `osCost nD nV + 35 nV + 19 nD + 12` steps: a tree `C₀ : DTree M.dual` rooted at `u` with
  `PA[τ y] = σ (C₀.par y)` for `y ≠ u`, `PA` at `Z + 6 nV + nD + 1`; the memory changes only in
  `[Z, Z + 7 nV + nD + 1)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The recorded parents of a complete search of the vertices are a tree.** -/
theorem vt_of_search [Nonempty D] (hM : M.IsPlane) {nV nD qt : ℕ} (τ : V ≃ Fin nV)
    (σ : D ≃ Fin nD) (u : V) {mem₂ mem₃ : ℕ → ℕ} {OBb OEb OLb HHb Mb Qb PAb : ℕ}
    (hO : OutMem M univ σ (fun y => (τ y : ℕ)) mem₂ OBb OEb OLb)
    (hH : ∀ d, mem₂ (HHb + σ d) = τ (M.head d))
    (hS : CtSt nV (τ u) Mb Qb PAb qt (fun x => mem₂ (OBb + x)) (fun x => mem₂ (OEb + x))
      (fun i => mem₂ (OLb + i)) (fun a => mem₂ (HHb + a)) mem₃)
    (hcl : BfsClosed Qb qt qt (BfsAdj (fun x => mem₂ (OBb + x)) (fun x => mem₂ (OEb + x))
      (fun i => mem₂ (OLb + i)) (fun a => mem₂ (HHb + a))) mem₃) :
    ∃ C₀ : STFlow.DTree M.dual, C₀.root = u ∧
      ∀ y, y ≠ C₀.root → mem₃ (PAb + τ y) = σ (C₀.par y) := by
  classical
  have hsnd : ∀ y i, mem₂ (OBb + τ y) ≤ i → i < mem₂ (OEb + τ y) →
      ∃ d, True ∧ M.dual.face d = y ∧ mem₂ (OLb + i) = σ d := by
    intro y i h1 h2
    obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO y
    have hj : i - mem₂ (OBb + τ y) < ds.length := by
      simp only at hl; omega
    have e := hds _ hj
    rw [show mem₂ (OBb + τ y) + (i - mem₂ (OBb + τ y)) = i by omega] at e
    obtain ⟨-, h4⟩ := (hmem _).1 (List.getElem_mem hj)
    exact ⟨_, trivial, h4, e⟩
  have hcmp : ∀ d, True → ∃ i, mem₂ (OBb + τ (M.dual.face d)) ≤ i ∧
      i < mem₂ (OEb + τ (M.dual.face d)) ∧ mem₂ (OLb + i) = σ d := by
    intro d _
    show ∃ i, mem₂ (OBb + τ (M.tail d)) ≤ i ∧ i < mem₂ (OEb + τ (M.tail d)) ∧
      mem₂ (OLb + i) = σ d
    obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO (M.tail d)
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ((hmem d).2 ⟨mem_univ _, rfl⟩)
    refine ⟨mem₂ (OBb + τ (M.tail d)) + j, by omega, by simp only at hl; omega, ?_⟩
    rw [hds j hj, e]
  have hhd : ∀ d, True → mem₂ (HHb + σ d) = τ (M.dual.face (M.dual.rev d)) := fun d _ => hH d
  have hconn : ∀ y, ReflTransGen (fun a b => ∃ d, True ∧ M.dual.face d = a ∧
      M.dual.face (M.dual.rev d) = b) u y := fun y =>
    by
      induction hM.conn u y with
      | refl => exact .refl
      | tail _ h ih =>
        obtain ⟨d, h1, h2⟩ := h
        exact ih.tail ⟨d, trivial, h1, h2⟩
  have hall := ct_all (N := M.dual) (ob := fun u => mem₂ (OBb + u))
    (oe := fun u => mem₂ (OEb + u)) (ol := fun i => mem₂ (OLb + i))
    (hd := fun a => mem₂ (HHb + a)) τ σ u hcmp hhd hconn hS hcl
  obtain ⟨C, hr, -, hP⟩ := dtree_of_ct (N := M.dual) (ob := fun u => mem₂ (OBb + u))
    (oe := fun u => mem₂ (OEb + u)) (ol := fun i => mem₂ (OLb + i))
    (hd := fun a => mem₂ (HHb + a)) τ σ u hsnd hhd hS hall
  exact ⟨C, hr, hP⟩

/-- The layout of `osProg` in `vtSearch_exec`. -/
lemma vtOsLay {nD nV Tb Kb Z : ℕ} {T K : ℕ → ℕ} (htlt : ∀ i < nD, K i ≠ 0 → T i < nV)
    (lT : Tb + nD ≤ Z) (lK : Kb + nD ≤ Z) (wZ : Z + 7 * nV + nD + 2 ≤ W) :
    OsLay nD nV Tb Kb Z (Z + nV + 1) (Z + 2 * nV + 1) (Z + 3 * nV + 1) (Z + 4 * nV + 1) W T K :=
  ⟨htlt, rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

/-- The layout of `ctProg` in `vtSearch_exec`. -/
lemma vtBfsLay {nD nV mm HHb Z : ℕ} (hmm : mm ≤ nD) (lH : HHb + nD ≤ Z)
    (wZ : Z + 7 * nV + nD + 2 ≤ W) :
    BfsLay nV mm nD (Z + 2 * nV + 1) (Z + 3 * nV + 1) (Z + 4 * nV + 1) HHb
      (Z + 4 * nV + 1 + nD) (Z + 5 * nV + 1 + nD) (Z + 4 * nV + 1 + nD) W :=
  ⟨by omega, by omega, by omega, by omega, le_rfl, by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **A spanning tree of the vertices on the machine** (see the module docstring). Registers:
`1500 … 1509` = `nD, nV, Tb, —, Kb, Z, Z + nV + 1, OBb, OEb, OLb` for `osProg`,
`1400 … 1408` = `nV, τ u, OBb, OEb, OLb, HHb, Mb, Qb, PAb` for `ctProg`, with
`OBb = Z + 2 nV + 1`, `OEb = Z + 3 nV + 1`, `OLb = Z + 4 nV + 1`, `Mb = OLb + nD`,
`Qb = Mb + nV`, `PAb = Qb + nV`. -/
theorem vtSearch_exec [Nonempty D] (hM : M.IsPlane) {nD nV : ℕ} (σ : D ≃ Fin nD)
    (τ : V ≃ Fin nV) (u : V) {Tb Kb HHb Z : ℕ} (c : Config) (hc : WordsBounded W c)
    (s00 : c.nreg 1500 = nD) (s01 : c.nreg 1501 = nV) (s02 : c.nreg 1502 = Tb)
    (s04 : c.nreg 1504 = Kb) (s05 : c.nreg 1505 = Z) (s06 : c.nreg 1506 = Z + nV + 1)
    (s07 : c.nreg 1507 = Z + 2 * nV + 1) (s08 : c.nreg 1508 = Z + 3 * nV + 1)
    (s09 : c.nreg 1509 = Z + 4 * nV + 1)
    (b00 : c.nreg 1400 = nV) (b01 : c.nreg 1401 = τ u) (b02 : c.nreg 1402 = Z + 2 * nV + 1)
    (b03 : c.nreg 1403 = Z + 3 * nV + 1) (b04 : c.nreg 1404 = Z + 4 * nV + 1)
    (b05 : c.nreg 1405 = HHb) (b06 : c.nreg 1406 = Z + 4 * nV + 1 + nD)
    (b07 : c.nreg 1407 = Z + 5 * nV + 1 + nD) (b08 : c.nreg 1408 = Z + 6 * nV + 1 + nD)
    (hNT : ∀ d, c.nmem (Tb + σ d) = τ (M.tail d)) (hK : ∀ d, c.nmem (Kb + σ d) = 1)
    (hNH : ∀ d, c.nmem (HHb + σ d) = τ (M.head d))
    (lT : Tb + nD ≤ Z) (lK : Kb + nD ≤ Z) (lH : HHb + nD ≤ Z)
    (wZ : Z + 7 * nV + nD + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq osProg ctProg) c c' t ∧
      t ≤ osCost nD nV + (35 * nV + 19 * nD + 12) ∧
      (∃ C₀ : STFlow.DTree M.dual, C₀.root = u ∧
        ∀ y, y ≠ C₀.root → c'.nmem (Z + 6 * nV + 1 + nD + τ y) = σ (C₀.par y)) ∧
      (∀ a, a < Z ∨ Z + 7 * nV + nD + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1410 ∨ (1420 < r ∧ r < 1510) ∨ 1520 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hu := (τ u).2
  set OBb := Z + 2 * nV + 1 with hOBb
  set OEb := Z + 3 * nV + 1 with hOEb
  set OLb := Z + 4 * nV + 1 with hOLb
  set Mb := Z + 4 * nV + 1 + nD with hMb
  set Qb := Z + 5 * nV + 1 + nD with hQb
  set PAb := Z + 6 * nV + 1 + nD with hPAb
  have hinj : Function.Injective fun y => (τ y : ℕ) := fun a b h => τ.injective (Fin.ext h)
  have hT : ∀ d, (fun i => c.nmem (Tb + i)) (σ d) = (τ (M.tail d) : ℕ) := hNT
  have hK' : ∀ d, (fun i => c.nmem (Kb + i)) (σ d) = if d ∈ (univ : Finset D) then 1 else 0 :=
    fun d => by simp only [mem_univ, ↓reduceIte]; exact hK d
  have hL : OsLay nD nV Tb Kb Z (Z + nV + 1) OBb OEb OLb W (fun i => c.nmem (Tb + i))
      (fun i => c.nmem (Kb + i)) := vtOsLay (tlt_of_piece σ (fun x => (τ x).2) hT) lT lK wZ
  have hI : OsIn nD nV Tb Kb Z (Z + nV + 1) OBb OEb OLb (fun i => c.nmem (Tb + i))
      (fun i => c.nmem (Kb + i)) c :=
    ⟨s00, s01, s02, s04, s05, s06, s07, s08, s09, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hO, ⟨mm, hmm, hbe, hol, hdeg⟩, m₂, n₂, rr₂, rm₂, o₂⟩ :=
    osProg_bfs (P := P) (Mp := M) (S := univ) σ hinj (fun x => (τ x).2) hT hK' hL c hc hI
  have hw₂ := e₂.wb_right
  have g : ∀ r, 1400 ≤ r → r ≤ 1408 → c₂.nreg r = c.nreg r := fun r h1 h2 => n₂ r (by omega)
  have hHH : ∀ d, c₂.nmem (HHb + σ d) = τ (M.head d) := fun d => by
    have := (σ d).2
    rw [m₂ _ (Or.inl (by clear hT hK' hNT hK hNH; omega))
      (Or.inl (by clear hT hK' hNT hK hNH; omega))]; exact hNH d
  have hL' : BfsLay nV mm nD OBb OEb OLb HHb Mb Qb Mb W := vtBfsLay hmm lH wZ
  have hI' : BfsIn nV mm nD (τ u) OBb OEb OLb HHb (fun x => c₂.nmem (OBb + x))
      (fun x => c₂.nmem (OEb + x)) (fun i => c₂.nmem (OLb + i)) (fun a => c₂.nmem (HHb + a))
      c₂.nmem := by
    refine ⟨hu, fun _ _ => rfl, fun _ _ => rfl, fun x hx => (hbe x hx).1,
      fun x hx => (hbe x hx).2, fun _ _ => rfl, fun i hi => hol i hi, fun _ _ => rfl,
      fun a ha => ?_, hdeg⟩
    have := hHH (σ.symm ⟨a, ha⟩)
    rw [Equiv.apply_symm_apply] at this
    simp only [this]; exact (τ _).2
  have hq1 : Qb + nV ≤ PAb := by clear * - hQb hPAb; omega
  have hq2 : PAb + nV ≤ W := by clear * - hPAb wZ; omega
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨qt, hS, hcl⟩, -, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    ctProg_exec (P := P) hL' hq1 hq2 c₂ hw₂ ((g _ (by norm_num) (by norm_num)).trans b00)
      ((g _ (by norm_num) (by norm_num)).trans b01) ((g _ (by norm_num) (by norm_num)).trans b02)
      ((g _ (by norm_num) (by norm_num)).trans b03) ((g _ (by norm_num) (by norm_num)).trans b04)
      ((g _ (by norm_num) (by norm_num)).trans b05) ((g _ (by norm_num) (by norm_num)).trans b06)
      ((g _ (by norm_num) (by norm_num)).trans b07) ((g _ (by norm_num) (by norm_num)).trans b08) hI'
  obtain ⟨C₀, hCr, hPA⟩ := vt_of_search hM τ σ u hO hHH hS hcl
  refine ⟨c₃, k₂ + k₃, Exec.seq e₂ e₃, by omega, ⟨C₀, hCr, hPA⟩, fun a ha => ?_,
    fun r hr => ?_, by rw [rr₃, rr₂], by rw [rm₃, rm₂], by rw [o₃, o₂]⟩
  · have a1 : a < Mb ∨ Qb + nV ≤ a := by clear * - ha hMb hQb; omega
    have a2 : a < PAb ∨ PAb + nV ≤ a := by clear * - ha hPAb; omega
    have a3 : a < Z ∨ Z + 2 * nV + 1 ≤ a := by clear * - ha; omega
    have a4 : a < OBb ∨ OLb + nD ≤ a := by clear * - ha hOBb hOLb; omega
    rw [m₃ _ a1 a2, m₂ _ a3 a4]
  · rw [n₃ r (by clear * - hr; omega), n₂ r (by clear * - hr; omega)]

end NegSSSP

end PlanarFlow
