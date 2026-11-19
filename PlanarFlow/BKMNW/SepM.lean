module

public import PlanarFlow.BKMNW.MillerOne
public import PlanarFlow.BKMNW.ChoiceE
public import PlanarFlow.BKMNW.ExistMillerM
public import WordRAM.Machine.RealsToNat
public import PlanarFlow.BKMNW.IteR23

/-!
# Miller's separator of the split chain computed by the machine

The separator of the split chain (`ScChoice.sep`, specification `SepFnOK`) is here the output of
the machine program `msep` (`PlanarFlow.BKMNW.msep_spec`: one stellar subdivision of a plain
encoding, then Miller's whole program `millerFull`) run on the plain encoding of the piece map
`psep M hσ hB` with the natural weights `coreWt (fun _ => 1) (coreExW τ N ex)`, decoded from the
output registers.

* `darr`, `varr` (arrays of a numbering), **`encMem`** (the plain encoding of a map at `B₀`:
  `α`, `φ`, `φ⁻¹`, vertex and face numbers, then the weights), `encMem_enc`, `encMem_w`,
  `encMem_le`; **`encCfg`** (the starting configuration: the encoding at
  `B₀ = aEnd10 m (nV + nF)`, `r390 … r393 = m, nV, nF, B₀`), `encW` (the word bound).
* `runOut s P W c₀` (the final configuration of a run, unique by `Exec.det`), `runOut_eq`.
* **`decCyc`**, **`decSep`** (the decoder: the darts `cd⁻¹ mem[r640 + i]`, `i < r641`, checked to
  form a simple cycle; the faces `G` with `mem[r642 + fc G] ≠ r643 ↔ r644 = 1`), `decSep_eq`,
  `sepOK_congr` (a separator depends only on its first `k` darts).
* **`msepRun`** (encode, run `msep`, decode), **`msepRun_spec`** (`some R` with
  `SepOK (wR w) (6 √(nV + nF) + 4) R`), `msepRun_exec` (the run within `msT m (nV + nF)` steps).
* **`sepM M : SepFn M`** (`msepRun` on `psep` with the numberings `Fintype.equivFin` and the
  weights `coreWt`), **`sepM_ok`**: `∀ Hs, SepFnOK M (sepM M) Hs` on a map without loops (via
  `coreSep_of_sepOK`).
* **`maxflow_plane_cost_decM`**: `maxflow_plane_cost_decE` with `sepF = sepM (lpreMap M)`: the
  separator parameter is gone.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg
  WordRAM WordRAM.Machine

/-! ### The plain encoding as memory -/

section Enc

variable {D Q X : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- The array of a dart function for the numbering `c`. -/
noncomputable def darr {m : ℕ} (c : D ≃ Fin m) (f : D → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then f (c.symm ⟨i, h⟩) else 0

lemma darr_c {m : ℕ} (c : D ≃ Fin m) (f : D → ℕ) (d : D) : darr c f (c d) = f d := by
  simp [darr]

/-- The array of a function for the numbering `vi`. -/
noncomputable def varr {n : ℕ} (vi : X ≃ Fin n) (w : X → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then w (vi.symm ⟨i, h⟩) else 0

lemma varr_vi {n : ℕ} (vi : X ≃ Fin n) (w : X → ℕ) (x : X) : varr vi w (vi x) = w x := by
  simp [varr]

/-- **The plain encoding of a map with vertex weights from `B₀`**: the numbers of `α d`, `φ d`,
`φ⁻¹ d`, of the vertex and of the face of `d` (`m` words each), then the weights of the
vertices of the stellar subdivision (numbered by `stVi vn fn`). -/
noncomputable def encMem (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (w : Q ⊕ M.Face → ℕ) (B₀ a : ℕ) : ℕ :=
  if a < B₀ then 0 else
  if a < B₀ + m then darr c (fun d => c (M.α d)) (a - B₀) else
  if a < B₀ + 2 * m then darr c (fun d => c (M.φ d)) (a - (B₀ + m)) else
  if a < B₀ + 3 * m then darr c (fun d => c (M.φ.symm d)) (a - (B₀ + 2 * m)) else
  if a < B₀ + 4 * m then darr c (fun d => vn (M.vert d)) (a - (B₀ + 3 * m)) else
  if a < B₀ + 5 * m then darr c (fun d => fn (M.face d)) (a - (B₀ + 4 * m)) else
  varr (M.stVi vn fn) w (a - (B₀ + 5 * m))

variable (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV) (fn : M.Face ≃ Fin nF)
  (w : Q ⊕ M.Face → ℕ) (B₀ : ℕ)

lemma encMem_enc :
    Enc M c vn fn (encMem M c vn fn w B₀) B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m) := by
  have hd := fun d => (c d).2
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_⟩ <;>
    (have := hd d; unfold encMem)
  · rw [iteF (by omega), iteT (by omega), show B₀ + c d - B₀ = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteT (by omega),
      show B₀ + m + c d - (B₀ + m) = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteF (by omega), iteT (by omega),
      show B₀ + 2 * m + c d - (B₀ + 2 * m) = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega),
      iteT (by omega), show B₀ + 3 * m + c d - (B₀ + 3 * m) = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega),
      iteF (by omega), iteT (by omega),
      show B₀ + 4 * m + c d - (B₀ + 4 * m) = c d by omega, darr_c]

lemma encMem_w (x : Q ⊕ M.Face) :
    encMem M c vn fn w B₀ (B₀ + 5 * m + M.stVi vn fn x) = w x := by
  unfold encMem
  rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega),
    iteF (by omega), iteF (by omega), show B₀ + 5 * m + (M.stVi vn fn x : ℕ) -
      (B₀ + 5 * m) = M.stVi vn fn x by omega, varr_vi]

lemma varr_le {n : ℕ} (vi : X ≃ Fin n) [Fintype X] (w : X → ℕ) (i : ℕ) :
    varr vi w i ≤ ∑ x, w x := by
  unfold varr
  split_ifs
  · exact single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ _)
  · exact Nat.zero_le _

lemma encMem_le (a : ℕ) : encMem M c vn fn w B₀ a ≤ m + nV + nF + ∑ x, w x := by
  unfold encMem darr
  have := varr_le (M.stVi vn fn) w (a - (B₀ + 5 * m))
  split_ifs <;> first | omega | exact le_trans (Nat.le_of_lt (Fin.isLt _)) (by omega)

/-- The start of the encoding: above the arrays of Miller's program. -/
abbrev encB (m nV nF : ℕ) : ℕ := aEnd10 m (nV + nF)

/-- **The starting configuration of `msep`**: the plain encoding with weights at
`B₀ = aEnd10 m (nV + nF)`, `r390 = m`, `r391 = nV`, `r392 = nF`, `r393 = B₀`. -/
noncomputable def encCfg : Config where
  pc := 0
  nreg r := if r = 390 then m else if r = 391 then nV else if r = 392 then nF else
    if r = 393 then encB m nV nF else 0
  rreg _ := 0
  nmem := encMem M c vn fn w (encB m nV nF)
  rmem _ := 0
  output := []

/-- The word bound of the run (polynomial in the size and the weights). -/
abbrev encW (m nV nF S : ℕ) : ℕ := encB m nV nF + 16 * m + nV + nF + 3 * S + 6

lemma encCfg_wb : WordsBounded (encW m nV nF (∑ x, w x)) (encCfg M c vn fn w) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [encCfg, encW]; split_ifs <;> omega
  · have := encMem_le M c vn fn w (encB m nV nF) a
    simp only [encCfg, encW]; omega

end Enc

/-! ### The final configuration and the decoder -/

section Dec

/-- The final configuration of a run (unique: `Exec.det`). -/
noncomputable def runOut (s : Stmt) (P : Input) (W : ℕ) (c₀ : Config) : Option Config :=
  open Classical in if h : ∃ c' t, Exec P W s c₀ c' t then some h.choose else none

open Classical in
lemma runOut_eq {s : Stmt} {P : Input} {W : ℕ} {c₀ c' : Config} {t : ℕ}
    (h : Exec P W s c₀ c' t) : runOut s P W c₀ = some c' := by
  have hx : ∃ c' t, Exec P W s c₀ c' t := ⟨c', t, h⟩
  unfold runOut
  rw [diteT hx]
  obtain ⟨t', ht'⟩ := hx.choose_spec
  exact congrArg some (Exec.det ht' h).1

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

open Classical in
/-- **The decoded cycle**: the darts `cd⁻¹ mem[base + i]` (`i < k`), if they form a simple cycle. -/
noncomputable def decCyc {K : ℕ} (cd : D ≃ Fin K) (k base : ℕ) (mem : ℕ → ℕ) :
    Option M.SCycle :=
  if hK : 0 < K then
    if h : 0 < k ∧
        (∀ i < k, M.vert (M.α (cd.symm ⟨mem (base + i) % K, Nat.mod_lt _ hK⟩)) =
          M.vert (cd.symm ⟨mem (base + (i + 1) % k) % K, Nat.mod_lt _ hK⟩)) ∧
        (∀ i < k, ∀ j < k, M.vert (cd.symm ⟨mem (base + i) % K, Nat.mod_lt _ hK⟩) =
          M.vert (cd.symm ⟨mem (base + j) % K, Nat.mod_lt _ hK⟩) → i = j) then
      some ⟨k, fun i => cd.symm ⟨mem (base + i) % K, Nat.mod_lt _ hK⟩, h.1, h.2.1, h.2.2⟩
    else none
  else none

open Classical in
/-- **The decoder of Miller's output**: the cycle of `r641` darts at `r640`, the faces `G` with
`mem[r642 + fc G] ≠ r643 ↔ r644 = 1`. -/
noncomputable def decSep {K K' : ℕ} (cd : D ≃ Fin K) (fc : M.Face ≃ Fin K') (c : Config) :
    Option (M.SCycle × Finset M.Face) :=
  (decCyc cd (c.nreg 641) (c.nreg 640) c.nmem).map fun C =>
    (C, univ.filter fun G => (c.nmem (c.nreg 642 + fc G) ≠ c.nreg 643 ↔ c.nreg 644 = 1))

/-- The decoder reads a separator written in the output form. -/
lemma decSep_eq {K K' : ℕ} (cd : D ≃ Fin K) (fc : M.Face ≃ Fin K') {c : Config}
    (R : M.SCycle × Finset M.Face) (h641 : c.nreg 641 = R.1.k)
    (h640 : ∀ i < R.1.k, c.nmem (c.nreg 640 + i) = cd (R.1.d i))
    (hZ : ∀ G, G ∈ R.2 ↔ (c.nmem (c.nreg 642 + fc G) ≠ c.nreg 643 ↔ c.nreg 644 = 1)) :
    ∃ C : M.SCycle, decSep cd fc c = some (C, R.2) ∧ C.k = R.1.k ∧
      ∀ i < R.1.k, C.d i = R.1.d i := by
  classical
  have hK : 0 < K := by
    have := (cd (R.1.d 0)).2; omega
  have hd : ∀ i < R.1.k, cd.symm ⟨c.nmem (c.nreg 640 + i) % K, Nat.mod_lt _ hK⟩ = R.1.d i := by
    intro i hi
    rw [Equiv.symm_apply_eq]
    ext
    simp only [h640 i hi, Nat.mod_eq_of_lt (cd (R.1.d i)).2]
  have hmod : ∀ i < R.1.k, (i + 1) % R.1.k < R.1.k := fun i hi => Nat.mod_lt _ (by omega)
  have hval : 0 < c.nreg 641 ∧
      (∀ i < c.nreg 641, M.vert (M.α (cd.symm ⟨c.nmem (c.nreg 640 + i) % K, Nat.mod_lt _ hK⟩)) =
        M.vert (cd.symm ⟨c.nmem (c.nreg 640 + (i + 1) % c.nreg 641) % K, Nat.mod_lt _ hK⟩)) ∧
      (∀ i < c.nreg 641, ∀ j < c.nreg 641,
        M.vert (cd.symm ⟨c.nmem (c.nreg 640 + i) % K, Nat.mod_lt _ hK⟩) =
          M.vert (cd.symm ⟨c.nmem (c.nreg 640 + j) % K, Nat.mod_lt _ hK⟩) → i = j) := by
    rw [h641]
    refine ⟨R.1.pos, fun i hi => ?_, fun i hi j hj e => ?_⟩
    · rw [hd i hi, hd _ (hmod i hi)]; exact R.1.vert_α i hi
    · rw [hd i hi, hd j hj] at e; exact R.1.inj i hi j hj e
  refine ⟨⟨c.nreg 641, fun i => cd.symm ⟨c.nmem (c.nreg 640 + i) % K, Nat.mod_lt _ hK⟩, hval.1,
    hval.2.1, hval.2.2⟩, ?_, h641, fun i hi => hd i hi⟩
  unfold decSep decCyc
  rw [diteT hK, diteT hval, Option.map_some]
  congr 2
  ext G
  simp [hZ G]

/-- **A separator depends only on its first `k` darts.** -/
lemma sepOK_congr {w : Q → ℝ} {N : ℕ} {C C' : M.SCycle} {Z : Finset M.Face}
    (hk : C'.k = C.k) (hd : ∀ i < C.k, C'.d i = C.d i) (h : SepOK w N (C, Z)) :
    SepOK w N (C', Z) := by
  classical
  have hv : C'.verts = C.verts := by
    ext v; simp only [SCycle.mem_verts, hk]
    exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [← hd i hi, e]⟩,
      fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [hd i hi, e]⟩⟩
  have hm : ∀ d, C'.Mem d ↔ C.Mem d := fun d => by
    simp only [SCycle.Mem, hk]
    exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rwa [← hd i hi]⟩,
      fun ⟨i, hi, e⟩ => ⟨i, hi, by rwa [hd i hi]⟩⟩
  have hin : sideIn C' Z = sideIn C Z := by
    ext v; simp only [mem_sideIn, hv]
  have hout : sideOut C' Z = sideOut C Z := by
    ext v; simp only [mem_sideOut, hv, hin]
  obtain ⟨h1, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩, h3, h4⟩ := h
  refine ⟨by simp only at h1 ⊢; omega, ⟨fun d => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [hin, hout, hv] at *
  · rw [hm]; exact b1 d
  all_goals assumption

end Dec

/-! ### Encode, run, decode -/

section Run

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- The input words of the run (unused by `msep`). -/
def msP : Input := ⟨[], fun _ => 0⟩

/-- **Miller's separator of `M.stellar` by the machine**: encode `M` with the weights `w`
(`encCfg`), run `msep`, decode the output (`decSep` with `stCode c`, `stFn c`). -/
noncomputable def msepRun (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (w : Q ⊕ M.Face → ℕ) :
    Option (M.stellar.SCycle × Finset M.stellar.Face) :=
  (runOut msep msP (encW m nV nF (∑ x, w x)) (encCfg M c vn fn w)).bind
    (decSep (M.stCode c) (M.stFn c))

variable (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV) (fn : M.Face ≃ Fin nF)
  (w : Q ⊕ M.Face → ℕ)

/-- **The run of `msep` on the encoding**, within `msT m (nV + nF)` steps, and `msepRun` is the
decoded output of its final configuration. -/
theorem msepRun_exec (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (hpos : 0 < ∑ v, w v) :
    ∃ c' t, Exec msP (encW m nV nF (∑ x, w x)) msep (encCfg M c vn fn w) c' t ∧
      t ≤ msT m (nV + nF) ∧ msepRun M c vn fn w = decSep (M.stCode c) (M.stFn c) c' ∧
      ∃ R : M.stellar.SCycle × Finset M.stellar.Face,
        c'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, c'.nmem (c'.nreg 640 + i) = M.stCode c (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ (c'.nmem (c'.nreg 642 + M.stFn c G) ≠ c'.nreg 643 ↔
          c'.nreg 644 = 1)) ∧
        SepOK (wR w) (6 * Nat.sqrt (nV + nF) + 4) R := by
  obtain ⟨c', t, e, ht, R, h1, h2, h3, h4, -⟩ :=
    msep_spec (P := msP) (W := encW m nV nF (∑ x, w x)) M c vn fn w (B₀ := encB m nV nF)
      (c₀ := encCfg M c vn fn w) hM hl hm2 hpos (encMem_enc M c vn fn w _)
      (encMem_w M c vn fn w _) le_rfl (by unfold encW; omega) (by unfold encW; omega) (encCfg_wb M c vn fn w)
      (by simp [encCfg]) (by simp [encCfg]) (by simp [encCfg]) (by simp [encCfg])
  refine ⟨c', t, e, ht, ?_, R, h1, h2, h3, h4⟩
  rw [msepRun, runOut_eq e, Option.bind_some]

/-- **Miller's separator by the machine is a separator**: `msepRun` returns a simple cycle of at
most `6 √(nV + nF) + 4` darts of `M.stellar` bounding faces with both strict sides of weight at
most `2/3`. -/
theorem msepRun_spec (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (hpos : 0 < ∑ v, w v) :
    ∃ R, msepRun M c vn fn w = some R ∧ SepOK (wR w) (6 * Nat.sqrt (nV + nF) + 4) R := by
  obtain ⟨c', t, -, -, hrun, R, h1, h2, h3, h4⟩ := msepRun_exec M c vn fn w hM hl hm2 hpos
  obtain ⟨C, hC, hk, hd⟩ := decSep_eq (M.stCode c) (M.stFn c) R h1 h2 h3
  exact ⟨(C, R.2), hrun.trans hC, sepOK_congr hk hd h4⟩

end Run

/-! ### The separator of the split chain -/

section Piece

open Function Equiv Orbit CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

open Classical in
/-- **The separator of the split chain computed by the machine**: `msepRun` (encode, run `msep`,
decode) on the piece map `psep M hσ hB` (numbered by `Fintype.equivFin`) with the weights
`coreWt (fun _ => 1) (coreExW τ N ex)` (`1` per dart on the face centres, `Σ ex` of its darts on
a vertex). -/
noncomputable def sepM (M : CombMap D V F) : SepFn M := fun N τ hσ hB ex =>
  msepRun (psep M hσ hB) (Fintype.equivFin _) (Fintype.equivFin _) (Fintype.equivFin _)
    (coreWt hσ hB (fun _ => 1) (coreExW τ N ex))

variable {M : CombMap D V F}

open Classical in
/-- **The machine's separator meets the specification of the split chain** (on a map without
loops): `msepRun_spec` and `coreSep_of_sepOK`. -/
theorem sepM_ok (hloopM : ∀ d, M.head d ≠ M.tail d) (Hs : List (Finset V)) :
    SepFnOK M (sepM M) Hs := by
  intro N τ hN ex hne _
  obtain ⟨x₀, hx₀⟩ := hne
  have hl : ∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠
      (psep M hN.stable hN.rev).vert d := by
    intro d h
    have h' := (hN.vert _ ((psep M hN.stable hN.rev).α d).2 _ d.2).1 ((psep_vert_eq _ _).1 h)
    rw [psep_α, CombMap.tail_rev] at h'
    rcases h' with e | ⟨H, hH, h1, h2⟩
    · exact hloopM d.1 e
    · exact hN.inner d.1 d.2 ⟨H, hH, h2, h1⟩
  have hP := psep_isPlane hN.stable hN.rev hx₀ hN.conn' hN.gap
  have hm2 : 2 ≤ Fintype.card (SDart N) := by
    rw [Fintype.card_coe]
    have hr : M.rev x₀ ∈ N := hN.rev x₀ hx₀
    have hsub : ({x₀, M.rev x₀} : Finset D) ⊆ N := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hx₀
      · exact hr
    have := card_le_card hsub
    rwa [card_pair (M.rev_ne x₀).symm] at this
  have hpos : 0 < ∑ y, coreWt hN.stable hN.rev (fun _ => 1) (coreExW τ N ex) y := by
    rw [sum_coreWt]
    have : 0 < ∑ _x : SDart N, (1 : ℕ) := by
      rw [sum_const, card_univ, smul_eq_mul, mul_one]; omega
    omega
  obtain ⟨R, hR, hok⟩ := msepRun_spec (psep M hN.stable hN.rev) (Fintype.equivFin _)
    (Fintype.equivFin _) (Fintype.equivFin _) (coreWt hN.stable hN.rev (fun _ => 1)
      (coreExW τ N ex)) hP hl hm2 hpos
  obtain ⟨h1, h2, h3, h4⟩ := coreSep_of_sepOK hN.stable hN.rev (fun _ => 1) (coreExW τ N ex)
    le_rfl hok
  exact ⟨R.1, R.2, hR, h1, h2, h3, h4⟩

end Piece

section Head

open Function Equiv Orbit CombMap

universe w

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Maximum flow in plane graphs in `O(n log³ n)` with Miller's separator computed by the
machine**: `maxflow_plane_cost_decE` for `sepF = sepM (lpreMap M)` (encode the piece map, run
`msep`, decode). The decomposition is a function of the map, an enumeration `e` of the darts of
`lpreMap M` (bijective on `[0, n)`) and a dart `d₀` only. Constants as in `maxflow_plane_cost`. -/
theorem maxflow_plane_cost_decM (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost_decE hM hrot hface hu hST e hsurj d₀ (sepM (lpreMap M))
    (fun Hs => sepM_ok (preMap_loopless nlMap_loopless nlE_tail) Hs) hc

end Head

end BKMNW

end PlanarFlow
