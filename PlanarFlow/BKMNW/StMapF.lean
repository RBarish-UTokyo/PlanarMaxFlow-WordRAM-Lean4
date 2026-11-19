module

public import PlanarFlow.BKMNW.StMapE

/-!
# The map part of the s-t flow encoding: what the words mean

For a map `M` whose darts are numbered by `en` (`NsStep.EnumOK M en m` and
`NsStep.EnumOK M.dual en m`: the faces and the vertices are the orbits of `next` and of `rot`),
the words written by `smP` from the index arrays `RV` and `RT` of `M` are **Klein's encoding
`Klein.KInput M.dual ∅ 0` of the dual map** (the input the s-t flow program
`PlanarFlow.STFlow.pcore_exec` reads), for the dart numbering `enEq` (the index in the order of
`en`) and the node layout `smLayout`:

* `ixOf_lt`-based **`enEq h : D ≃ Fin m`**; the labels `fLab` (of a face: the orbit label of `next`
  of any of its darts) and `vLab` (of a vertex: the orbit label of `rot`);
* **`smLayout`**: `Klein.Layout M.dual n (fLab + 1) (m + 1 + eIx) (2m + 1 + vLab) (3m + 1 + eIx)`
  for `4 m + 1 ≤ n`;
* `KInM` (the fields of `Klein.KInput` with `S = ∅`, read from the memory at `β`),
  **`KInM.kInput`** (any input whose words are those of the memory is a `Klein.KInput`);
* `olab_congr` (orbit labels only depend on the values on `[0, m)`);
* **`smP_kin`**: `smP` from `RV = rvI`, `RT = ixOf ∘ rot` writes `KInM M.dual (enEq h) …` at `β`,
  within `140 m + 150` steps, the scratch zero again.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep

/-! ### Orbit labels depend on the values on `[0, m)` only -/

theorem iter_congr {f g : ℕ → ℕ} {m : ℕ} (hf : PermOn f m) (hfg : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : ∀ t, f^[t] i = g^[t] i
  | 0 => rfl
  | t + 1 => by
    rw [iterate_succ_apply', iterate_succ_apply', ← iter_congr hf hfg hi t,
      hfg _ (OrbLab.iter_lt hf hi t)]

theorem permOn_congr {f g : ℕ → ℕ} {m : ℕ} (hf : PermOn f m) (hfg : ∀ x < m, f x = g x) :
    PermOn g m where
  lt x hx := by rw [← hfg x hx]; exact hf.lt x hx
  inj x hx y hy e := hf.inj x hx y hy (by rw [hfg x hx, hfg y hy, e])

theorem olab_congr {f g : ℕ → ℕ} {m : ℕ} (hf : PermOn f m) (hfg : ∀ x < m, f x = g x) {i : ℕ}
    (hi : i < m) : olab f i = olab g i := by
  have hg := permOn_congr hf hfg
  apply le_antisymm
  · obtain ⟨t, ht⟩ := olab_mem g i
    rw [← ht, ← iter_congr hf hfg hi t]
    exact olab_min f i t
  · obtain ⟨t, ht⟩ := olab_mem f i
    rw [← ht, iter_congr hf hfg hi t]
    exact olab_min g i t

/-! ### The numbering and the labels -/

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- **The dart numbering** of the order `en`: the index. -/
noncomputable def enEq (h : EnumOK M en m) : D ≃ Fin m where
  toFun d := ⟨ixOf en m d, ixOf_lt h d⟩
  invFun i := en i
  left_inv d := en_ixOf h d
  right_inv i := Fin.ext (ixOf_en h i.2)

@[simp] lemma enEq_val (h : EnumOK M en m) (d : D) : (enEq h d : ℕ) = ixOf en m d := rfl

lemma card_eq (h : EnumOK M en m) : Fintype.card D = m := by
  rw [Fintype.card_congr (enEq h), Fintype.card_fin]

variable (M) in
/-- The label of a face: the orbit label of `next` of any of its darts. -/
noncomputable def fLab (h : EnumOK M en m) (y : F) : ℕ :=
  labI M en m (ixOf en m (Classical.choose (h.fsurj y)))

lemma fLab_eq (h : EnumOK M en m) : fLab M h = (nsIds M h (en 0)).gv := rfl

lemma fLab_face (h : EnumOK M en m) {i : ℕ} (hi : i < m) :
    fLab M h (M.face (en i)) = labI M en m i := by
  rw [fLab_eq]; exact gv_face h (en 0) hi

lemma fLab_inj (h : EnumOK M en m) : Injective (fLab M h) := by
  rw [fLab_eq]; exact (nsIds M h (en 0)).gv_inj

lemma fLab_lt (h : EnumOK M en m) (y : F) : fLab M h y < m := by
  rw [fLab_eq]; exact (nsIds M h (en 0)).gv_lt y

lemma card_F_le (h : EnumOK M en m) : Fintype.card F ≤ m := by
  calc Fintype.card F ≤ Fintype.card (Fin m) :=
        Fintype.card_le_of_injective (fun y => (⟨fLab M h y, fLab_lt h y⟩ : Fin m))
          (fun a b e => fLab_inj h (congrArg Fin.val e))
    _ = m := Fintype.card_fin m

/-- The face permutation of `M.dual` is the rotation of `M`. -/
lemma phiI_dual (i : ℕ) : phiI M.dual en m i = ixOf en m (M.rot (en i)) := rfl

/-! ### The layout -/

variable (M) in
/-- The nodes of the vertices of the dual (the faces of `M`). -/
noncomputable def ιF (h : EnumOK M en m) (y : F) : ℕ := fLab M h y + 1

variable (M) in
/-- The nodes of the edges of the spanning tree. -/
noncomputable def ιG (h : EnumOK M en m) (d : D) : ℕ := m + 1 + NegSSSP.eIx M (enEq h) d

variable (M) in
/-- The nodes of the faces of the dual (the vertices of `M`). -/
noncomputable def ιV (h' : EnumOK M.dual en m) (v : V) : ℕ := 2 * m + 1 + fLab M.dual h' v

variable (M) in
/-- The nodes of the edges of the cotree. -/
noncomputable def ιE (h : EnumOK M en m) (d : D) : ℕ := 3 * m + 1 + NegSSSP.eIx M (enEq h) d

/-- **The node layout of the dual map** on `n ≥ 4 m + 1` nodes. -/
theorem smLayout (h : EnumOK M en m) (h' : EnumOK M.dual en m) {n : ℕ} (hn : 4 * m + 1 ≤ n) :
    Klein.Layout M.dual n (ιF M h) (ιG M h) (ιV M h') (ιE M h) := by
  have hF := card_F_le h
  have hV := card_F_le h'
  have he : ∀ d, NegSSSP.eIx M (enEq h) d < m := NegSSSP.eIx_lt (enEq h)
  have hl : ∀ y, fLab M h y < m := fLab_lt h
  have hl' : ∀ v, fLab M.dual h' v < m := fLab_lt h'
  refine ⟨⟨fun x y e => fLab_inj h (by simpa [ιF] using e), fun d => ?_, fun d d' e => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    ⟨fun x y e => fLab_inj h' (by simpa [ιV] using e), fun d => ?_, fun d d' e => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    by omega, by omega, fun x y => ?_, fun x d => ?_, fun d y => ?_, fun d d' => ?_⟩
  · show m + 1 + NegSSSP.eIx M (enEq h) (M.rev d) = _; rw [NegSSSP.eIx_rev]; rfl
  · exact NegSSSP.eIx_eq (M := M) (enEq h) (by simpa [ιG] using e)
  · have := hl x; simp only [ιF, ιG]; omega
  · have := hl x; simp only [ιF]; omega
  · have := he d; simp only [ιG]; omega
  · show 3 * m + 1 + NegSSSP.eIx M (enEq h) (M.rev d) = _; rw [NegSSSP.eIx_rev]; rfl
  · exact NegSSSP.eIx_eq (M := M) (enEq h) (by simpa [ιE] using e)
  · have := hl' x; simp only [ιV, ιE]; omega
  · have := hl' x; simp only [ιV]; omega
  · have := he d; simp only [ιE]; omega
  · have := hl x; simp only [ιF, ιV]; omega
  · have := hl x; simp only [ιF, ιE]; omega
  · have := he d; have := hl' y; simp only [ιG, ιV]; omega
  · have := he d; have := he d'; simp only [ιG, ιE]; omega

/-! ### Klein's encoding in memory -/

section KIn

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]

/-- **Klein's encoding of a map with no piece, in the memory at `β`** (the fields of
`Klein.KInput Q ∅ 0`). -/
structure KInM (Q : CombMap D' X Y) {nD : ℕ} (σ : D' ≃ Fin nD) (ιv : X → ℕ) (ιg : D' → ℕ)
    (ιf : Y → ℕ) (ιe : D' → ℕ) (mem : ℕ → ℕ) (β : ℕ) : Prop where
  rv : ∀ d, mem (β + Klein.iRV nD + σ d) = σ (Q.rev d)
  nf : ∀ d, mem (β + Klein.iNF nD + σ d) = ιf (Q.face d)
  ne : ∀ d, mem (β + Klein.iNE nD + σ d) = ιe d
  ng : ∀ d, mem (β + Klein.iNG nD + σ d) = ιg d
  nt : ∀ d, mem (β + Klein.iNT nD + σ d) = ιv (Q.tail d)
  nh : ∀ d, mem (β + Klein.iNH nD + σ d) = ιv (Q.head d)
  is : ∀ d, mem (β + Klein.iIS nD + σ d) = 0
  ed : ∀ d, mem (β + Klein.iED nD + ιe d) = σ d ∨ mem (β + Klein.iED nD + ιe d) = σ (Q.rev d)

/-- **An input holding the words of the memory is Klein's encoding.** -/
theorem KInM.kInput {Q : CombMap D' X Y} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ}
    {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem : ℕ → ℕ} {β n : ℕ}
    (h : KInM Q σ ιv ιg ιf ιe mem β) (hn : ∀ d, ιe d < n) (P : Input)
    (hP : ∀ i, i < 8 * nD + n → P.data.getD i 0 = mem (β + i)) :
    Klein.KInput Q ∅ 0 σ ιv ιg ιf ιe P where
  rv d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iRV; omega), ← add_assoc]; exact h.rv d
  nf d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNF; omega), ← add_assoc]; exact h.nf d
  ne d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNE; omega), ← add_assoc]; exact h.ne d
  ng d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNG; omega), ← add_assoc]; exact h.ng d
  nt d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNT; omega), ← add_assoc]; exact h.nt d
  nh d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iNH; omega), ← add_assoc]; exact h.nh d
  is d := by
    have := (σ d).2; rw [hP _ (by unfold Klein.iIS; omega), ← add_assoc, h.is d]
    simp
  ln d hd := absurd hd (Finset.notMem_empty d)
  ed d := by
    have := hn d; rw [hP _ (by unfold Klein.iED; omega), ← add_assoc]; exact h.ed d

end KIn

/-! ### The words of `smP` -/

variable {P : Input} {W : ℕ}

/-- **The map part of the s-t flow encoding** (see the module docstring): from `RV = rvI` at
`RVb` and `RT = ixOf ∘ rot` at `RTb`, `smP` writes `KInM M.dual (enEq h) (ιF …) (ιG …) (ιV …)
(ιE …)` at `β` within `140 m + 150` steps. -/
theorem smP_kin (h : EnumOK M en m) (h' : EnumOK M.dual en m) (c : Config)
    (hc : WordsBounded W c) {RVb RTb S β : ℕ}
    (r00 : c.nreg 7700 = m) (r01 : c.nreg 7701 = RVb) (r02 : c.nreg 7702 = RTb)
    (r03 : c.nreg 7703 = S) (r04 : c.nreg 7704 = β)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (l1 : RVb + m ≤ S) (l2 : RTb + m ≤ S) (l3 : S + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smP c c' t ∧ t ≤ 140 * m + 150 ∧
      KInM M.dual (enEq h) (ιF M h) (ιG M h) (ιV M h') (ιE M h) c'.nmem β ∧
      (∀ i < 3 * m, c'.nmem (S + i) = 0) ∧
      (∀ a, ¬ (S ≤ a ∧ a < S + 3 * m) → ¬ (β ≤ a ∧ a < β + 12 * m + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the arrays agree with the permutations on `[0, m)`
  have eNX : ∀ x < m, phiI M en m x = c.nmem (RTb + c.nmem (RVb + x)) := fun x hx => by
    rw [hRV x hx, hRT _ (rvI_lt h x), phiI_eq h hx]
  have eRT : ∀ x < m, phiI M.dual en m x = c.nmem (RTb + x) := fun x hx => by
    rw [hRT x hx, phiI_dual]
  have pNX := phi_permOn h
  have pRT := phi_permOn h'
  obtain ⟨c', t, e, ht, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ :=
    smP_exec (P := P) c hc r00 r01 r02 r03 r04 (fun i hi => by rw [hRV i hi]; exact rvI_lt h i)
      (permOn_congr pNX eNX) (permOn_congr pRT eRT) l1 l2 l3 w
  have lF : ∀ i < m, olab (fun i => c.nmem (RTb + c.nmem (RVb + i))) i = labI M en m i :=
    fun i hi => (olab_congr pNX eNX hi).symm
  have lV : ∀ i < m, olab (fun i => c.nmem (RTb + i)) i = labI M.dual en m i :=
    fun i hi => (olab_congr pRT eRT hi).symm
  refine ⟨c', t, e, ht, ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d => ?_, fun d => ?_⟩, k9, k10, k11, k12, k13, k14⟩
  all_goals have hd := ixOf_lt h d
  · -- RV
    show c'.nmem (β + 0 + ixOf en m d) = ixOf en m (M.rev d)
    rw [add_zero, k1 _ hd, hRV _ hd]
    unfold rvI; rw [en_ixOf h]
  · -- NF
    show c'.nmem (β + m + ixOf en m d) = 2 * m + 1 + fLab M.dual h' (M.tail d)
    rw [k2 _ hd, lV _ hd]
    have := fLab_face h' hd
    rw [en_ixOf h] at this
    change fLab M.dual h' (M.tail d) = labI M.dual en m (ixOf en m d) at this
    rw [this]; omega
  · -- NE
    show c'.nmem (β + 2 * m + ixOf en m d) = 3 * m + 1 + NegSSSP.eIx M (enEq h) d
    rw [k3 _ hd, hRV _ hd]
    unfold rvI NegSSSP.eIx; rw [en_ixOf h]; rfl
  · -- NG
    show c'.nmem (β + 3 * m + ixOf en m d) = m + 1 + NegSSSP.eIx M (enEq h) d
    rw [k4 _ hd, hRV _ hd]
    unfold rvI NegSSSP.eIx; rw [en_ixOf h]; rfl
  · -- NT
    show c'.nmem (β + 4 * m + ixOf en m d) = fLab M h (M.face d) + 1
    rw [k5 _ hd, lF _ hd]
    have := fLab_face h hd
    rw [en_ixOf h] at this
    rw [this]
  · -- NH
    show c'.nmem (β + 5 * m + ixOf en m d) = fLab M h (M.face (M.rev d)) + 1
    rw [k6 _ hd, hRV _ hd, lF _ (rvI_lt h _)]
    have := fLab_face h (rvI_lt h (ixOf en m d))
    rw [en_rvI h, en_ixOf h] at this
    rw [this]
  · -- IS
    show c'.nmem (β + 6 * m + ixOf en m d) = 0
    exact k7 _ (by omega)
  · -- ED
    show c'.nmem (β + 8 * m + (3 * m + 1 + NegSSSP.eIx M (enEq h) d)) = ixOf en m d ∨
      c'.nmem (β + 8 * m + (3 * m + 1 + NegSSSP.eIx M (enEq h) d)) = ixOf en m (M.rev d)
    obtain ⟨x', hx', h1, h2⟩ := k8 _ hd
    have ee : NegSSSP.eIx M (enEq h) d = min (ixOf en m d) (c.nmem (RVb + ixOf en m d)) := by
      unfold NegSSSP.eIx; rw [hRV _ hd]; unfold rvI; rw [en_ixOf h]; rfl
    rw [ee, h2]
    have e' : NegSSSP.eIx M (enEq h) (en x') = NegSSSP.eIx M (enEq h) d := by
      rw [ee, ← h1]; unfold NegSSSP.eIx; rw [hRV _ hx']; unfold rvI
      simp only [enEq_val, ixOf_en h hx']
    rcases NegSSSP.eIx_eq (M := M) (enEq h) e' with h3 | h3
    · left; rw [h3, ixOf_en h hx']
    · right; rw [h3, M.rev_rev, ixOf_en h hx']

end StEnc

end BKMNW

end PlanarFlow
