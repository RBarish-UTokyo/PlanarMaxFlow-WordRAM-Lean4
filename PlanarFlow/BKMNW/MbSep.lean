module

public import PlanarFlow.BKMNW.EncPsep
public import WordRAM.Machine.WordMono

/-!
# Miller's separator as a function decoded from a deterministic run, and its run in place

The base case of `scertD` (Miller) must run `encProg ; msep` **in place**, inside a larger
program, while the split chain needs a separator **function** of the piece `(N, τ, ex)`
(`SepFn`). This file defines the function as the decoded output of the run from a canonical
configuration (the frame image `encInZ` with the numbering `cNe` of the darts by their indices in
the enumeration `e`, the arrays at a base `B₀` fixed by a parameter `Bz`), and proves that a run
in place, from any configuration that agrees with the canonical one on the registers named by
`encProg ; msep` (`mbU`) and on the memory up to the canonical word bound `Wr`, decodes (memory
above `Wr` read as `0`, `mbCut`) to the same separator (`Exec.lift`, `Exec.det`).

* `mbNatI`, `mbNatS`, **`Exec.mbReals`** (a run without real instructions is the same run for
  any real registers and memory);
* `mbU` (the registers `< 700` and `4400 … 4699`), `mbU_ok` (`encProg ; msep` names only those),
  `mbRegsOK_true`, `Exec.mem_above` (a run with word bound `W` keeps the memory above `W`);
* the numbering: `eIdx` (the index of a dart in the enumeration), `eRk` (its rank among the darts
  of `N`), **`cNe e n N : SDart N ≃ Fin #N`**, `cNe_apply`, **`eRk_e`** (the rank of `e i` is the
  number of `j < i` with `e j ∈ N`: a prefix count);
* `encInZ` (the frame image with base `B₀`), `encWZ`, `encInZ_wb`, `encInZ_arr`, `mbBz`;
* **`sepC M e n Bz : SepFn M`**, **`sepC_ok`** (`SepFnOK` on a map without loops);
* `mbCut`, `decSep_congr`, **`sepC_insitu`**: the run in place within
  `encT m + msT m (#Q + #Face)` steps, decoding (`mbCut Wr`) to `sepC … N τ hσ hB ex = some R` in
  the output form, registers outside `mbU` and memory above `Wr` kept, reals kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg
  WordRAM WordRAM.Machine Relation

/-! ### Runs without real instructions -/

section Reals

variable {P : Input} {W : ℕ}

/-- An instruction not touching the real registers or memory. -/
def mbNatI : Instr → Bool
  | .constR .. | .copyR .. | .addR .. | .subR .. | .mulR .. | .divR .. | .loadR .. | .storeR ..
  | .brLtR .. => false
  | _ => true

/-- A statement without real instructions and real tests. -/
def mbNatS : Stmt → Bool
  | .skip => true
  | .instr i => mbNatI i
  | .seq s t => mbNatS s && mbNatS t
  | .ifLtN _ _ s t => mbNatS s && mbNatS t
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ s => mbNatS s
  | .whileLtR _ _ _ => false

/-- The configuration with other real registers and memory. -/
def setR (c : Config) (X : ℕ → ℝ) (Y : ℕ → ℝ) : Config := { c with rreg := X, rmem := Y }

@[simp] lemma setR_nreg (c : Config) (X Y : ℕ → ℝ) : (setR c X Y).nreg = c.nreg := rfl
@[simp] lemma setR_nmem (c : Config) (X Y : ℕ → ℝ) : (setR c X Y).nmem = c.nmem := rfl
@[simp] lemma setR_rreg (c : Config) (X Y : ℕ → ℝ) : (setR c X Y).rreg = X := rfl
@[simp] lemma setR_rmem (c : Config) (X Y : ℕ → ℝ) : (setR c X Y).rmem = Y := rfl
@[simp] lemma setR_output (c : Config) (X Y : ℕ → ℝ) : (setR c X Y).output = c.output := rfl

lemma setR_self (c : Config) : setR c c.rreg c.rmem = c := rfl

lemma setR_setR (c : Config) (X Y X' Y' : ℕ → ℝ) : setR (setR c X Y) X' Y' = setR c X' Y' := rfl

lemma wb_setR {c : Config} (h : WordsBounded W c) (X Y : ℕ → ℝ) : WordsBounded W (setR c X Y) :=
  h

lemma mbNatI_effect {i : Instr} (hi : mbNatI i = true) {c c' : Config}
    (h : i.effect P c = some c') (X Y : ℕ → ℝ) : i.effect P (setR c X Y) = some (setR c' X Y) := by
  cases i <;> simp only [Instr.effect, mbNatI, Option.some.injEq, reduceCtorEq] at h hi ⊢ <;>
    subst h <;> rfl

/-- **A run without real instructions is the same run for any reals.** -/
theorem Exec.mbReals {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : mbNatS s = true) (X Y : ℕ → ℝ) : Exec P W s (setR c X Y) (setR c' X Y) k := by
  induction h with
  | skip hw => exact .skip hw
  | instr hst he hw hw' => exact .instr hst (mbNatI_effect hs he X Y) hw hw'
  | seq _ _ ih₁ ih₂ =>
    simp only [mbNatS, Bool.and_eq_true] at hs
    exact .seq (ih₁ hs.1) (ih₂ hs.2)
  | ifLtN_true ht _ ih =>
    simp only [mbNatS, Bool.and_eq_true] at hs
    exact .ifLtN_true ht (ih hs.1)
  | ifLtN_false ht _ ih =>
    simp only [mbNatS, Bool.and_eq_true] at hs
    exact .ifLtN_false ht (ih hs.2)
  | ifLtR_true _ _ _ => simp [mbNatS] at hs
  | ifLtR_false _ _ _ => simp [mbNatS] at hs
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht (ih₁ hs) (ih₂ hs)
  | whileLtR_false _ _ => simp [mbNatS] at hs
  | whileLtR_true _ _ _ _ _ => simp [mbNatS] at hs

/-- Every statement names only registers of the full set. -/
lemma mbRegsOK_true (s : Stmt) : s.regsOK (fun _ => true) = true := by
  induction s with
  | skip => rfl
  | instr i => simp [Stmt.regsOK, Instr.regsOK]
  | seq s t ihs iht => simp [Stmt.regsOK, ihs, iht]
  | ifLtN a b t e iht ihe => simp [Stmt.regsOK, iht, ihe]
  | ifLtR a b t e iht ihe => simp [Stmt.regsOK, iht, ihe]
  | whileLtN a b body ih => simp [Stmt.regsOK, ih]
  | whileLtR a b body ih => simp [Stmt.regsOK, ih]

/-- **A run with word bound `W` keeps the memory above `W`.** -/
theorem Exec.mem_above {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hn : s.noInp = true) (hr : s.noRand = true) : ∀ a, W < a → c'.nmem a = c.nmem a := by
  obtain ⟨d', e, -, hK, -⟩ := Exec.lift (P' := P) (U := fun _ => true) h (mbRegsOK_true s) hn hr
    le_rfl ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ h.wb_left
  obtain ⟨rfl, -⟩ := Exec.det e h
  exact hK.nmem

end Reals

/-- The registers named by `encProg ; msep`: below `700` and `4400 … 4699`. -/
def mbU (r : ℕ) : Bool := decide (r < 700) || (decide (4400 ≤ r) && decide (r < 4700))

lemma mbU_ok : (Stmt.seq encProg msep).regsOK mbU = true := by decide +kernel

lemma mbS_noInp : (Stmt.seq encProg msep).noInp = true := by decide +kernel

lemma mbS_noRand : (Stmt.seq encProg msep).noRand = true := by decide +kernel

lemma mbS_nat : mbNatS (Stmt.seq encProg msep) = true := by decide +kernel

/-! ### The numbering of the darts of a piece by the enumeration -/

section Num

open Orbit

variable {D : Type*} [DecidableEq D]

open Classical in
/-- The index of a dart in the enumeration (`n` if it has none). -/
noncomputable def eIdx (e : ℕ → D) (n : ℕ) (d : D) : ℕ :=
  if h : ∃ i, i < n ∧ e i = d then Nat.find h else n

lemma eIdx_spec {e : ℕ → D} {n : ℕ} {d : D} (h : ∃ i, i < n ∧ e i = d) :
    eIdx e n d < n ∧ e (eIdx e n d) = d := by
  classical
  unfold eIdx
  rw [diteT h]
  exact Nat.find_spec h

lemma eIdx_e {e : ℕ → D} {n : ℕ} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) {i : ℕ}
    (hi : i < n) : eIdx e n (e i) = i := by
  obtain ⟨h1, h2⟩ := eIdx_spec (e := e) (n := n) ⟨i, hi, rfl⟩
  exact hinj _ h1 _ hi h2

/-- The rank of a dart among the darts of `N`, by their indices. -/
noncomputable def eRk (e : ℕ → D) (n : ℕ) (N : Finset D) (d : D) : ℕ :=
  #(N.filter fun y => eIdx e n y < eIdx e n d)

lemma eRk_lt {e : ℕ → D} {n : ℕ} {N : Finset D} {d : D} (hd : d ∈ N) : eRk e n N d < #N :=
  card_lt_card (filter_ssubset.2 ⟨d, hd, lt_irrefl _⟩)

/-- The rank as a map to `Fin #N`. -/
noncomputable def cNf (e : ℕ → D) (n : ℕ) (N : Finset D) : SDart N → Fin #N :=
  fun x => ⟨eRk e n N x.1, eRk_lt x.2⟩

lemma eRk_strict {e : ℕ → D} {n : ℕ} {N : Finset D} {x y : D} (hx : x ∈ N)
    (h : eIdx e n x < eIdx e n y) : eRk e n N x < eRk e n N y := by
  refine card_lt_card ⟨fun z hz => ?_, fun hs => ?_⟩
  · rw [mem_filter] at hz ⊢; exact ⟨hz.1, lt_trans hz.2 h⟩
  · have := hs (mem_filter.2 ⟨hx, h⟩)
    exact lt_irrefl _ (mem_filter.1 this).2

lemma cNf_injective {e : ℕ → D} {n : ℕ} {N : Finset D}
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) : Function.Injective (cNf e n N) := by
  intro x y h
  have h' : eRk e n N x.1 = eRk e n N y.1 := congrArg Fin.val h
  have hid : eIdx e n x.1 = eIdx e n y.1 := by
    rcases lt_trichotomy (eIdx e n x.1) (eIdx e n y.1) with hl | he | hl
    · exact absurd h' (eRk_strict x.2 hl).ne
    · exact he
    · exact absurd h' (eRk_strict y.2 hl).ne'
  apply Subtype.ext
  rw [← (eIdx_spec (hsurj _ x.2)).2, ← (eIdx_spec (hsurj _ y.2)).2, hid]

open Classical in
/-- **The numbering of the darts of `N` by their indices in the enumeration**: the rank. -/
noncomputable def cNe (e : ℕ → D) (n : ℕ) (N : Finset D) : SDart N ≃ Fin #N :=
  if h : Function.Injective (cNf e n N) then
    Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
      ⟨h, by rw [Fintype.card_coe, Fintype.card_fin]⟩)
  else (Fintype.equivFin _).trans (finCongr (Fintype.card_coe N))

lemma cNe_apply {e : ℕ → D} {n : ℕ} {N : Finset D} (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d)
    (x : SDart N) : (cNe e n N x : ℕ) = eRk e n N x.1 := by
  classical
  unfold cNe
  rw [diteT (cNf_injective hsurj)]
  rfl

/-- **The rank of `e i` is a prefix count**: the number of `j < i` with `e j ∈ N`. -/
lemma eRk_e {e : ℕ → D} {n : ℕ} {N : Finset D} (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) {i : ℕ} (hi : i < n) :
    eRk e n N (e i) = #((range i).filter fun j => e j ∈ N) := by
  unfold eRk
  rw [eIdx_e hinj hi]
  symm
  refine card_nbij' e (eIdx e n) (fun j hj => ?_) (fun y hy => ?_) (fun j hj => ?_)
    (fun y hy => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hj ⊢
    exact ⟨hj.2, by rw [eIdx_e hinj (by omega)]; exact hj.1⟩
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hy ⊢
    exact ⟨hy.2, by rw [(eIdx_spec (hsurj _ hy.1)).2]; exact hy.1⟩
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hj
    exact eIdx_e hinj (by omega)
  · simp only [coe_filter, Set.mem_ofPred_eq] at hy
    exact (eIdx_spec (hsurj _ hy.1)).2

end Num

/-! ### The frame image with a base parameter -/

section Frame

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- The word bound of the run from the frame image at base `B₀`. -/
abbrev encWZ (B₀ m S : ℕ) : ℕ := B₀ + 22 * m + 3 * S + 14

/-- **The frame image of a piece at base `B₀`**: `REV` at `B₀`, `SIG` at `B₀ + 7m`, `EX` at
`B₀ + 8m`, everything else zero; the registers `4660 … 4664` of `encProg` (`m`, `B₀`,
`B₀ + 7m`, `B₀ + 8m`, `B₀ + 9m`), all others zero. -/
noncomputable def encInZ (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) (B₀ : ℕ) : Config where
  pc := 0
  nreg r := if r = 4660 then m else if r = 4661 then B₀ else
    if r = 4662 then B₀ + 7 * m else if r = 4663 then B₀ + 8 * m else
    if r = 4664 then B₀ + 9 * m else 0
  rreg _ := 0
  nmem a :=
    if B₀ ≤ a ∧ a < B₀ + m then darr c (fun d => c (M.α d)) (a - B₀) else
    if B₀ + 7 * m ≤ a ∧ a < B₀ + 8 * m then
      darr c (fun d => c (M.σ d)) (a - (B₀ + 7 * m)) else
    if B₀ + 8 * m ≤ a ∧ a < B₀ + 9 * m then darr c ex (a - (B₀ + 8 * m))
    else 0
  rmem _ := 0
  output := []

variable (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) (B₀ : ℕ)

lemma encInZ_wb : WordsBounded (encWZ B₀ m (∑ d, ex d + m)) (encInZ M c ex B₀) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [encInZ, encWZ]; split_ifs <;> omega
  · have h1 := darr_lt c M.α (a - B₀)
    have h2 := darr_lt c M.σ (a - (B₀ + 7 * m))
    have h3 := darr_le_sum c ex (a - (B₀ + 8 * m))
    simp only [encInZ, encWZ]; split_ifs <;> omega

lemma encInZ_arr : EncArr M c ex (encInZ M c ex B₀).nmem B₀ (B₀ + 7 * m) (B₀ + 8 * m) := by
  have hd := fun d => (c d).2
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩ <;> (have := hd d; simp only [encInZ])
  · rw [iteT ⟨by omega, by omega⟩, show B₀ + c d - B₀ = c d by omega, darr_c]
  · rw [iteF (by omega), iteT ⟨by omega, by omega⟩,
      show B₀ + 7 * m + c d - (B₀ + 7 * m) = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteT ⟨by omega, by omega⟩,
      show B₀ + 8 * m + c d - (B₀ + 8 * m) = c d by omega, darr_c]

/-- **The run from the frame image at base `B₀ ≥ aEnd10 m (2m)`**, in the output form. -/
theorem encInZ_exec (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (hB : encB' m ≤ B₀) :
    ∃ c' t, Exec msP (encWZ B₀ m (∑ d, ex d + m)) (.seq encProg msep) (encInZ M c ex B₀) c' t ∧
      t ≤ encT m + msT m (Fintype.card Q + Fintype.card M.Face) ∧
      ∃ R : M.stellar.SCycle × Finset M.stellar.Face,
        c'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, c'.nmem (c'.nreg 640 + i) = M.stCode c (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ (c'.nmem (c'.nreg 642 + M.stFn c G) ≠ c'.nreg 643 ↔
          c'.nreg 644 = 1)) ∧
        SepOK (wR (encWt M ex)) (6 * Nat.sqrt (Fintype.card Q + Fintype.card M.Face) + 4) R :=
  encMsep_exec (P := msP) M c ex (encInZ M c ex B₀)
    (B₀ := B₀) (SIGb := B₀ + 7 * m) (EXb := B₀ + 8 * m) (Sb := B₀ + 9 * m)
    (encInZ_wb M c ex B₀) hM hl hm2 (by simp [encInZ]) (by simp [encInZ]) (by simp [encInZ])
    (by simp [encInZ]) (by simp [encInZ]) (encInZ_arr M c ex B₀) ⟨by omega, by omega, by omega,
      by unfold encWZ; omega⟩ hB
    (fun a h1 h2 => by simp only [encInZ]; rw [iteF (by omega), iteF (by omega), iteF (by omega)])
    (fun a h1 h2 => by simp only [encInZ]; rw [iteF (by omega), iteF (by omega), iteF (by omega)])
    (by unfold encWZ; omega)

end Frame

/-! ### The separator function -/

section Sep

open Function Equiv Orbit CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- The base of the arrays: `Bz` when it is large enough for `m` darts, else `aEnd10 m (2m)`. -/
def mbBz (Bz m : ℕ) : ℕ := if encB' m ≤ Bz then Bz else encB' m

lemma le_mbBz (Bz m : ℕ) : encB' m ≤ mbBz Bz m := by
  unfold mbBz; split_ifs with h
  · exact h
  · exact le_rfl

lemma mbBz_eq {Bz m : ℕ} (h : encB' m ≤ Bz) : mbBz Bz m = Bz := by unfold mbBz; rw [iteT h]

variable (M : CombMap D V F)

open Classical in
/-- **Miller's separator of the split chain, decoded from a deterministic run**: run
`encProg ; msep` from the frame image of the piece map `psep M hσ hB` at base `mbBz Bz #N`, the
darts numbered by their indices in the enumeration `e` (`cNe e n N`), weights `ex`; decode. -/
noncomputable def sepC (e : ℕ → D) (n Bz : ℕ) : SepFn M := fun N τ hσ hB ex =>
  (runOut (.seq encProg msep) msP (encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N))
    (encInZ (psep M hσ hB) (cNe e n N) (fun x => ex x.1) (mbBz Bz #N))).bind
    (decSep ((psep M hσ hB).stCode (cNe e n N)) ((psep M hσ hB).stFn (cNe e n N)))

variable {M}

open Classical in
/-- The two conditions on a piece map under which Miller's program runs. -/
lemma psep_run_conds (hloopM : ∀ d, M.head d ≠ M.tail d) {N : Finset D} {Hs : List (Finset V)}
    {τ : Perm D} (hN : PMap M N Hs τ) (hne : N.Nonempty) :
    (∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠
      (psep M hN.stable hN.rev).vert d) ∧ (psep M hN.stable hN.rev).IsPlane ∧ 2 ≤ #N := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨fun d h => ?_, psep_isPlane hN.stable hN.rev hx₀ hN.conn' hN.gap, ?_⟩
  · have h' := (hN.vert _ ((psep M hN.stable hN.rev).α d).2 _ d.2).1 ((psep_vert_eq _ _).1 h)
    rw [psep_α, CombMap.tail_rev] at h'
    rcases h' with e | ⟨H, hH, h1, h2⟩
    · exact hloopM d.1 e
    · exact hN.inner d.1 d.2 ⟨H, hH, h2, h1⟩
  · have hr : M.rev x₀ ∈ N := hN.rev x₀ hx₀
    have hsub : ({x₀, M.rev x₀} : Finset D) ⊆ N := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hx₀
      · exact hr
    have := card_le_card hsub
    rwa [card_pair (M.rev_ne x₀).symm] at this

open Classical in
/-- **The decoded separator meets the specification of the split chain** (on a map without
loops), for every enumeration and base parameter. -/
theorem sepC_ok (hloopM : ∀ d, M.head d ≠ M.tail d) (e : ℕ → D) (n Bz : ℕ)
    (Hs : List (Finset V)) : SepFnOK M (sepC M e n Bz) Hs := by
  intro N τ hN ex hne _
  obtain ⟨hl, hP, hm2⟩ := psep_run_conds hloopM hN hne
  have hm2' : 2 ≤ #N := hm2
  obtain ⟨c', t, er, -, R, h1, h2, h3, hok⟩ := encInZ_exec (psep M hN.stable hN.rev) (cNe e n N)
    (fun x => ex x.1) (mbBz Bz #N) hP hl hm2' (le_mbBz Bz _)
  obtain ⟨C, hC, hk, hd⟩ := decSep_eq _ _ R h1 h2 h3
  have hok' := sepOK_congr hk hd hok
  rw [encWt_psep] at hok'
  obtain ⟨g1, g2, g3, g4⟩ := coreSep_of_sepOK hN.stable hN.rev (fun _ => 1) (coreExW τ N ex)
    le_rfl hok'
  refine ⟨C, R.2, ?_, g1, g2, g3, g4⟩
  unfold sepC
  rw [runOut_eq er, Option.bind_some, hC]

/-! ### The run in place -/

/-- The configuration with the memory above `Wr` read as `0`. -/
def mbCut (Wr : ℕ) (c : Config) : Config :=
  { c with nmem := fun a => if a ≤ Wr then c.nmem a else 0 }

lemma decSep_congr {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {N : PlanarSeparator.Map X Y} {K K' : ℕ} (cd : X ≃ Fin K) (fc : N.Face ≃ Fin K')
    {c₁ c₂ : Config} (hm : c₁.nmem = c₂.nmem)
    (hr : ∀ r, 640 ≤ r → r ≤ 644 → c₁.nreg r = c₂.nreg r) :
    decSep cd fc c₁ = decSep cd fc c₂ := by
  unfold decSep
  rw [hr 641 (by omega) (by omega), hr 640 (by omega) (by omega), hm, hr 642 (by omega) (by omega),
    hr 643 (by omega) (by omega), hr 644 (by omega) (by omega)]

open Classical in
/-- **The run of `encProg ; msep` in place decodes to `sepC`.** From any configuration agreeing
with the frame image (numbering `cNe e n N`, base `B₀ = mbBz Bz #N`) on the registers `mbU` and on
the memory up to `Wr = encWZ B₀ #N (Σ ex + #N)`, the run takes at most
`encT #N + msT #N (#Q + #Face)` steps; read with the memory above `Wr` as `0` (`mbCut Wr`), its
output is `sepC … N τ hσ hB ex = some R` in the output form (`r641 = k`, the dart numbers at
`r640`, the face marks at `r642`), and `R` meets `SepOK`. Registers outside `mbU`, memory above
`Wr`, reals kept; the output only extended. -/
theorem sepC_insitu {P : Input} {W : ℕ} (e : ℕ → D) (n Bz : ℕ) {N : Finset D} {τ : Perm D}
    (hσ : Stable τ N) (hB : Stable (revPerm M) N) (ex : D → ℕ)
    (hP : (psep M hσ hB).IsPlane)
    (hl : ∀ d, (psep M hσ hB).vert ((psep M hσ hB).α d) ≠ (psep M hσ hB).vert d)
    (hm2 : 2 ≤ #N) (d : Config) (hd : WordsBounded W d)
    (hW : encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N) ≤ W)
    (hA : ∀ r, mbU r = true → d.nreg r = (encInZ (psep M hσ hB) (cNe e n N) (fun x => ex x.1)
      (mbBz Bz #N)).nreg r)
    (hmem : ∀ a ≤ encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N),
      d.nmem a = (encInZ (psep M hσ hB) (cNe e n N) (fun x => ex x.1) (mbBz Bz #N)).nmem a) :
    ∃ d' t, Exec P W (.seq encProg msep) d d' t ∧
      t ≤ encT #N + msT #N (Fintype.card (SVert τ N) + Fintype.card (psep M hσ hB).Face) ∧
      ∃ R, sepC M e n Bz N τ hσ hB ex = some R ∧
        decSep ((psep M hσ hB).stCode (cNe e n N)) ((psep M hσ hB).stFn (cNe e n N))
          (mbCut (encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N)) d') = some R ∧
        d'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, (mbCut (encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N)) d').nmem
          (d'.nreg 640 + i) = (psep M hσ hB).stCode (cNe e n N) (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ ((mbCut (encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N)) d').nmem
          (d'.nreg 642 + (psep M hσ hB).stFn (cNe e n N) G) ≠ d'.nreg 643 ↔ d'.nreg 644 = 1)) ∧
        SepOK (wR (encWt (psep M hσ hB) (fun x => ex x.1)))
          (6 * Nat.sqrt (Fintype.card (SVert τ N) + Fintype.card (psep M hσ hB).Face) + 4) R ∧
        (∀ r, mbU r = false → d'.nreg r = d.nreg r) ∧
        (∀ a, encWZ (mbBz Bz #N) #N (∑ x : SDart N, ex x.1 + #N) < a → d'.nmem a = d.nmem a) ∧
        d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ ∃ L, d'.output = d.output ++ L := by
  set Mp := psep M hσ hB with hMp
  set c := cNe e n N with hc
  set B₀ := mbBz Bz #N with hB₀
  set Wr := encWZ B₀ #N (∑ x : SDart N, ex x.1 + #N) with hWr
  set ref := encInZ Mp c (fun x => ex x.1) B₀ with href
  have hcard : Fintype.card (SDart N) = #N := Fintype.card_coe N
  obtain ⟨cr, t, er, ht, R, h1, h2, h3, hok⟩ := encInZ_exec Mp c (fun x => ex x.1) B₀ hP hl hm2
    (le_mbBz Bz _)
  have er' : Exec msP Wr (.seq encProg msep) ref cr t := by
    have : (∑ x : SDart N, ex x.1 + #N) = ∑ x, (fun x : SDart N => ex x.1) x + #N := rfl
    exact er
  obtain ⟨C, hC, hk, hdC⟩ := decSep_eq _ _ R h1 h2 h3
  have hsep : sepC M e n Bz N τ hσ hB ex = some (C, R.2) := by
    unfold sepC; rw [runOut_eq er', Option.bind_some, hC]
  -- the reference memory above `Wr` stays zero
  have hz : ∀ a, Wr < a → cr.nmem a = 0 := fun a ha => by
    rw [Exec.mem_above er' mbS_noInp mbS_noRand a ha]
    have ha' : B₀ + 22 * #N < a := by simp only [hWr, encWZ] at ha; omega
    have hc2 : Fintype.card (SDart N) = #N := Fintype.card_coe N
    simp only [href, encInZ, hc2]
    rw [iteF (by omega), iteF (by omega), iteF (by omega)]
  -- lift to the configuration with zero reals
  set d₀ := setR d (fun _ => 0) (fun _ => 0) with hd₀
  have hA₀ : Agree mbU Wr ref d₀ :=
    ⟨fun r hr => hA r hr, fun _ _ => rfl, fun a ha => hmem a ha, fun _ _ => rfl⟩
  obtain ⟨d₀', e₀, hA₀', hK₀, L, o1, o2⟩ := Exec.lift (P' := P) er' mbU_ok mbS_noInp mbS_noRand
    hW hA₀ (wb_setR hd _ _)
  have e₁ := Exec.mbReals e₀ mbS_nat d.rreg d.rmem
  rw [hd₀, setR_setR, setR_self] at e₁
  set d' := setR d₀' d.rreg d.rmem with hd'
  have hcut : (mbCut Wr d').nmem = cr.nmem := by
    funext a
    simp only [mbCut, hd', setR_nmem]
    split_ifs with h
    · exact hA₀'.nmem a h
    · rw [hz a (by omega)]
  have hreg : ∀ r, 640 ≤ r → r ≤ 644 → (mbCut Wr d').nreg r = cr.nreg r := fun r h1 h2 =>
    hA₀'.nreg r (by simp only [mbU]; simp; omega)
  have hdec : decSep (Mp.stCode c) (Mp.stFn c) (mbCut Wr d') = some (C, R.2) := by
    rw [decSep_congr _ _ hcut hreg, hC]
  refine ⟨d', t, e₁, ht, (C, R.2), hsep, hdec, ?_, fun i hi => ?_, fun G => ?_,
    sepOK_congr hk hdC hok, fun r hr => ?_, fun a ha => ?_, rfl, rfl, ⟨L, ?_⟩⟩
  · show (mbCut Wr d').nreg 641 = C.k
    rw [hreg 641 (by omega) (by omega), h1, hk]
  · have hi' : i < R.1.k := by rw [← hk]; exact hi
    have e640 : d'.nreg 640 = cr.nreg 640 := hreg 640 (by omega) (by omega)
    rw [e640, hcut, h2 i hi', hdC i hi']
  · have e2 : d'.nreg 642 = cr.nreg 642 := hreg 642 (by omega) (by omega)
    have e3 : d'.nreg 643 = cr.nreg 643 := hreg 643 (by omega) (by omega)
    have e4 : d'.nreg 644 = cr.nreg 644 := hreg 644 (by omega) (by omega)
    rw [e2, e3, e4, hcut]; exact h3 G
  · show d₀'.nreg r = d.nreg r
    rw [hK₀.nreg r hr]; rfl
  · show d₀'.nmem a = d.nmem a
    rw [hK₀.nmem a ha]; rfl
  · show d₀'.output = d.output ++ L
    rw [o2]; rfl

end Sep

end BKMNW

end PlanarFlow
