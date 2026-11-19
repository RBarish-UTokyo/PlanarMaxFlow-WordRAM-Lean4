module

public import PlanarFlow.STFlow.ProgRun

/-!
# The perturbed run on the machine: the loop of the steps

The program `pLoopS` runs the steps of the perturbed run (`lstep`) on the dynamic trees, the
state stored as in `PlanarFlow/STFlow/ProgStore.lean` (`LStored`), until a step stops. One
iteration (`pBodyS`):

1. the query `min2` at the node of `t` (`regMin2S`, threshold `kTh` in the real `r100`): the
   dart `e` of least key of the path of the cotree, which is the perturbed bottleneck `lbott`
   (`lbott_eq_of_key'`, for a perturbation with the properties `PertOK`), and its key `z`
   (`selS` of Klein's program, which orients it);
2. **the augmentation**: `add z` and `add2 (-z)` at the node of `t` (`aug_stored`);
3. **the test of the stop**: `add 1` at the node of the face `x` of `e`, the value of the node of
   the face `y` of its reverse, `add (-1)` at the node of `x` (`anc_test`): `y` is an ancestor of
   `x` in the dual tree exactly when the value is positive;
4. if so, the run stops (`r102 := 1`); otherwise **the pivot**: the sixteen operations of Klein's
   pivot with the amount `0` (`pivCoreS`), which give the face `y` the parent dart `e`, move the
   old parent dart `a` of `y` to the cotree with the keys `0` (on `a`) and `w a + w (rev a)` (on
   its reverse) (`pivotVal_key`), and write `TP[y] := e`.

**Registers.** `r100`: the node of `t`; `r101`: the node of `s` (the root of the cotree);
`r102 < r103 = 1`: the loop test; `r104`: the number of the last bottleneck; the real `r100`:
the threshold `kTh`.

* `PInv`: the invariant: after `i` steps, the state `ltraj i` is stored (`LStored`, with a bound
  `Lo ≥ kH0 - i kZ` at the nodes of the vertices), the steps before the last are pivots, and
  when the loop has stopped the last step stopped;
* `pBody_orun`: **one iteration** (counted at most `33` operations);
* `pLoop_orun`: **the loop**: it ends after `i ≤ m + 1` steps (`piv_le_card`), the last one
  stopping, counted at most `66 (m + 1)` operations and `2` further steps.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### The constants -/

variable (D F) in
/-- The bound of the keys of the darts of the path: `N Σ c + 2 lexR F ε`. -/
def kZ (N : ℤ) (c ε : D → ℤ) : ℤ := N * ∑ d, c d + 2 * lexR F ε

variable (D F) in
/-- The threshold of the query `min2`. -/
def kTh (N : ℤ) (c ε : D → ℤ) : ℤ := kZ D F N c ε + 1

variable (D F) in
/-- The initial value at the nodes of the vertices, high enough for `m + 2` steps. -/
def kH0 (N : ℤ) (c ε : D → ℤ) : ℤ := kTh D F N c ε + (Fintype.card D + 2) * kZ D F N c ε

/-! ### The steps of the run -/

section Steps

variable {M : CombMap D V F} {c ε : D → ℤ} {s t : V}

/-- A step whose bottleneck has its reverse's face above its face stops, and keeps the tree. -/
lemma lstep_stop {st : LSt M} (hne : (pathSet s t st.T).Nonempty)
    (ha : st.T.Anc (M.face (M.rev (lbott c ε s t st.g st.h st.T hne)))
      (M.face (lbott c ε s t st.g st.h st.T hne))) :
    (lstep M c ε s t st).2 = true ∧ (lstep M c ε s t st).1.T = st.T := by
  rw [lstep_of_ne hne]
  unfold stepE
  split_ifs with h
  · exact ⟨rfl, rfl⟩
  · exact absurd ha h

/-- Otherwise the step pivots the bottleneck into the tree. -/
lemma lstep_piv {st : LSt M} (hne : (pathSet s t st.T).Nonempty)
    (ha : ¬ st.T.Anc (M.face (M.rev (lbott c ε s t st.g st.h st.T hne)))
      (M.face (lbott c ε s t st.g st.h st.T hne))) :
    (lstep M c ε s t st).2 = false ∧ (lstep M c ε s t st).1.T =
      st.T.reparent _ (lbott c ε s t st.g st.h st.T hne) (st.T.ne_root_of_not_anc ha) rfl ha := by
  rw [lstep_of_ne hne]
  unfold stepE
  split_ifs with h
  · exact absurd h ha
  · exact ⟨rfl, rfl⟩

end Steps

/-! ### The program -/

/-- The glue after the selection of the bottleneck `e` (`r114`, its key the real `r110`): the
number of `e` into `r104`; the key `z` and `-z`, `1`, `-1`, `0` into the reals `r101 … r105`;
the nodes of the faces of the reverse of `e` and of `e` into `r105`, `r106`. -/
def glueA (nD : ℕ) : List Instr :=
  [.copyN 104 114, .copyR 101 110, .constR 102 0, .subR 102 102 110, .constR 103 1,
    .constR 104 (-1), .constR 105 0, .constN 105 (iNH nD), .addN 105 105 114, .readIn 105 105,
    .constN 106 (iNT nD), .addN 106 106 114, .readIn 106 106]

/-- **One step of the perturbed run**: the query, the augmentation, the test of the stop, the
pivot or the stop. -/
def pBodyS (B nD : ℕ) : Stmt :=
  .seq (regMin2S B 100 100) <| .seq (selS B nD) <| .seq (block (glueA nD)) <|
  .seq (regAddS B 100 101) <| .seq (regAdd2S B 100 102) <|
  .seq (regAddS B 106 103) <| .seq (regValS B false 105) <| .seq (.instr (.copyR 106 195)) <|
  .seq (regAddS B 106 104) <|
  .ifLtR 105 106 (.instr (.constN 102 1)) (.seq (.instr (.constR 110 0)) (pivCoreS B nD))

/-- **The loop of the steps**, while `r102 < r103`. -/
def pLoopS (B nD : ℕ) : Stmt := .whileLtN 102 103 (pBodyS B nD)

/-- The ghost state of the loop. -/
structure PG where
  /-- The number of steps made. -/
  i : ℕ
  /-- Whether the run has stopped. -/
  done : Bool
  /-- The bound of the values at the nodes of the vertices. -/
  Lo : ℝ
  /-- The operations counted so far. -/
  ops : ℕ

variable (M : CombMap D V F) (c ε : D → ℤ) (s t : V) (st₀ : LSt M) (N : ℤ) {nD : ℕ}
  (σ : D ≃ Fin nD) (n : ℕ) (ιF : F → ℕ) (ιG : D → ℕ) (ιV : V → ℕ) (ιE : D → ℕ) (B : ℕ)
  (Fo₀ : Forest) (c₀ : Config) (Wd : ℕ)

/-- **The invariant of the loop.** -/
structure PInv (x : PG) (hs : List EOp) (G : List VT) (cf : Config) : Prop where
  lcte : LCTE B n (runOpsE n Fo₀ hs).1 G cf
  wb : WordsBounded Wd cf
  st : LStored M n ιF ιG ιV ιE N c ε s x.Lo (runOpsE n Fo₀ hs).1
    (ltraj M c ε s t st₀ x.i)
  piv : ∀ j, (j + 1 < x.i ∨ (j < x.i ∧ x.done = false)) →
    (lstep M c ε s t (ltraj M c ε s t st₀ j)).2 = false
  fin : x.done = true → 1 ≤ x.i ∧
    (lstep M c ε s t (ltraj M c ε s t st₀ (x.i - 1))).2 = true ∧
    ∃ hne : (pathSet s t (ltraj M c ε s t st₀ (x.i - 1)).T).Nonempty,
      cf.nreg 104 = σ (lbott c ε s t (ltraj M c ε s t st₀ (x.i - 1)).g
        (ltraj M c ε s t st₀ (x.i - 1)).h (ltraj M c ε s t st₀ (x.i - 1)).T
        hne)
  lo : ((kH0 D F N c ε - x.i * kZ D F N c ε : ℤ) : ℝ) ≤ x.Lo
  ops : x.ops ≤ 33 * x.i
  kmem : KMem M.dual σ ιF (toDD (ltraj M c ε s t st₀ x.i).T) (wlen N c ε)
    (wlen N c ε) cf
  r100 : cf.nreg 100 = ιV t
  r101 : cf.nreg 101 = ιV s
  r102 : cf.nreg 102 = if x.done then 1 else 0
  r103 : cf.nreg 103 = 1
  q100 : cf.rreg 100 = (kTh D F N c ε : ℝ)
  fr : MvFr B n c₀ cf

/-- The measure of the loop. -/
def PG.μ (D : Type*) [Fintype D] (x : PG) : ℕ := if x.done then 0 else Fintype.card D + 2 - x.i

/-! ### One iteration -/

section Body

variable {M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd}

/-- Sequencing with a rewrite of the forest in between. -/
lemma ORun.seq' {P : Input} {W : ℕ} {s₁ s₂ : Stmt} {c c₁ c₂ : Config} {F F₁ : Forest}
    {G G₁ G₂ : List VT} {os₁ os₂ : List EOp} {m₁ g₁ m₂ g₂ : ℕ}
    (h₁ : ORun P W B n s₁ c F G c₁ os₁ G₁ m₁ g₁) (hF : (runOpsE n F os₁).1 = F₁)
    (h₂ : ORun P W B n s₂ c₁ F₁ G₁ c₂ os₂ G₂ m₂ g₂) :
    ORun P W B n (.seq s₁ s₂) c F G c₂ (os₁ ++ os₂) G₂ (m₁ + m₂) (g₁ + g₂) := by
  subst hF; exact h₁.seq h₂

/-- The flows after a step. -/
lemma lstep_gh {c ε : D → ℤ} {st : LSt M} (hne : (pathSet s t st.T).Nonempty) (d : D) :
    (lstep M c ε s t st).1.g d = st.g d +
        (c (lbott c ε s t st.g st.h st.T hne) - st.g (lbott c ε s t st.g st.h st.T hne)) *
          st.T.chi s t d ∧
      (lstep M c ε s t st).1.h d = st.h d +
        (ε (lbott c ε s t st.g st.h st.T hne) - st.h (lbott c ε s t st.g st.h st.T hne)) *
          st.T.chi s t d := by
  rw [lstep_of_ne hne]
  refine ⟨?_, ?_⟩ <;> simp [stepE_g, aug]

/-- The registers up to `r100` and the output are kept. -/
def P100 (c c' : Config) : Prop :=
  (∀ r, r ≤ 100 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output

lemma P100.trans {c c' c'' : Config} (h : P100 c c') (h' : P100 c' c'') : P100 c c'' :=
  ⟨fun r hr => ⟨(h'.1 r hr).1.trans (h.1 r hr).1, (h'.1 r hr).2.trans (h.1 r hr).2⟩,
    h'.2.trans h.2⟩

lemma RegFr.p100 {c c' : Config} (h : RegFr c c') : P100 c c' :=
  ⟨fun r hr => ⟨h.1 r (by omega), h.2.1 r (by omega)⟩, h.2.2⟩

lemma GFr.p100 {lo hi : ℕ} {c c' : Config} (h : GFr lo hi c c') (hlo : 101 ≤ lo) : P100 c c' :=
  ⟨fun r hr => h.1 r (by omega), h.2.2.2⟩

lemma LoFr.p100 {c c' : Config} (h : LoFr c c') : P100 c c' :=
  ⟨fun r hr => h.1 r (by omega), h.2⟩

lemma mvFr_step {c c' : Config} (h : MvFr B n c₀ c) (h1 : P100 c c')
    (h2 : MemFrame B n (DynTree.mem c) (DynTree.mem c')) : MvFr B n c₀ c' :=
  ⟨fun r hr => ⟨(h1.1 r hr.le).1.trans (h.1 r hr).1, (h1.1 r hr.le).2.trans (h.1 r hr).2⟩,
    h1.2.trans h.2.1, fun a ha => (h2 a ha).2.trans (h.2.2.1 a ha),
    fun a ha han => (h2 a ha).1.trans (h.2.2.2 a ha han)⟩

variable {P : Input}

/-- **One iteration of the loop**: one step of the perturbed run on the machine. -/
theorem pBody_orun (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hPO : PertOK M c ε s t d₀)
    (hI₀ : LInv c ε s t st₀) (hroot : st₀.T.root = M.face d₀)
    (hμ₀ : |M.div st₀.h s| ≤ lexR F ε) (hN : 2 * lexR F ε < N)
    (hL : Layout M.dual n ιF ιG ιV ιE) (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (x : PG) (hs : List EOp) (G : List VT) (cf : Config)
    (hI : PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd x hs G cf)
    (ht : cf.nreg 102 < cf.nreg 103) :
    ∃ x' c' os G' j h, ORun P Wd B n (pBodyS B nD) cf (runOpsE n Fo₀ hs).1 G c' os G' j h ∧
      PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd x' (hs ++ os) G' c' ∧
      x'.ops = x.ops + j ∧ 1 ≤ j ∧ h + 2 ≤ opCostE n ∧ PG.μ D x' < PG.μ D x := by
  classical
  have hdone : x.done = false := by
    cases hd : x.done
    · rfl
    · rw [hI.r102, hd, hI.r103] at ht; simp at ht
  have hε0 : ∀ d, 0 ≤ ε d := hPO.nonneg
  set st := ltraj M c ε s t st₀ x.i with hstd
  set Fo := (runOpsE n Fo₀ hs).1 with hFo
  have hIst : LInv c ε s t st := ltraj_inv hM hI₀ x.i
  have hpiv : ∀ j < x.i, (lstep M c ε s t (ltraj M c ε s t st₀ j)).2 = false :=
    fun j hj => hI.piv j (Or.inr ⟨hj, hdone⟩)
  have hile : x.i ≤ Fintype.card D := piv_le_card hPO hI₀ hroot hpiv
  have hμ := ltraj_mu hM hst hI₀ hε0 hμ₀ x.i
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  set e := lbott c ε s t st.g st.h st.T hne with he_def
  have he : st.T.chi s t e = 1 := lbott_mem c ε s t st.g st.h st.T hne
  obtain ⟨hz0, hzb⟩ := lkey_path_bound hM hst hIst hε0 hc hμ hN he
  set z := lkey N c ε st.g st.h e with hz
  have hzZ : z ≤ kZ D F N c ε := hzb
  have hZ0 : 0 ≤ kZ D F N c ε := hz0.trans hzZ
  have hThLo : ((kTh D F N c ε : ℤ) : ℝ) ≤ x.Lo := by
    have h1 : (kTh D F N c ε : ℤ) ≤ kH0 D F N c ε - x.i * kZ D F N c ε := by
      have : (x.i : ℤ) ≤ Fintype.card D := by exact_mod_cast hile
      unfold kH0; nlinarith
    exact le_trans (by exact_mod_cast h1) hI.lo
  have hzTh : z < kTh D F N c ε := by unfold kTh; omega
  -- the query
  have hlt := stored_min2_lt hM.dual hL hI.st hThLo t (d := e) he hzTh
  obtain ⟨d₁, h196, h195, hpar, hfb, hchi, hmin⟩ :=
    stored_min2_at hM.dual hL hI.st hThLo t hlt
  have hed : e = d₁ := lbott_eq_of_key' hM hst hIst hε0 (hPO.sep st.T) hN hchi hmin hne
  rw [← hed] at h196 h195 hpar hfb
  have hσe := (σ e).2
  obtain ⟨c₁, G₁, o₁, a196, a195, -, -, m₁, f₁⟩ := regMin2_orun (P := P) hWW hI.wb hI.lcte
    (ra := 100) (rz := 100) hI.r100 (hL.dual.f_lt t)
  obtain ⟨c₂, G₂, o₂, s114, s110, lf₂, sm₂⟩ := sel_orun (σ := σ) hWW hWa hP hL hK o₁.2.wb
    o₁.2.lcte (b := e) (by rw [a196, h196]) hpar hfb
  have hz₂ : c₂.rreg 110 = (z : ℝ) := by rw [s110, a195, h195]
  -- the glue
  obtain ⟨c₃, k₃, e₃, hk₃, g104, q101, q102, q103, q104, q105, g105, g106, hg₃⟩ :
      ∃ c' k, Exec P Wd (block (glueA nD)) c₂ c' k ∧ k = 13 ∧ c'.nreg 104 = σ e ∧
        c'.rreg 101 = (z : ℝ) ∧ c'.rreg 102 = ((-z : ℤ) : ℝ) ∧ c'.rreg 103 = ((1 : ℤ) : ℝ) ∧
        c'.rreg 104 = ((-1 : ℤ) : ℝ) ∧ c'.rreg 105 = 0 ∧
        c'.nreg 105 = ιF (M.face (M.rev e)) ∧ c'.nreg 106 = ιF (M.face e) ∧
        (∀ r, r ≠ 104 → r ≠ 105 → r ≠ 106 → c'.nreg r = c₂.nreg r) ∧
        (∀ r, (r < 101 ∨ 106 ≤ r) → c'.rreg r = c₂.rreg r) ∧ c'.nmem = c₂.nmem ∧
        c'.rmem = c₂.rmem ∧ c'.output = c₂.output := by
    have hc₂ := o₂.2.wb
    unfold glueA
    exec_block
    all_goals try (first
      | exact hP _
      | (offs_simp; omega)
      | (config_simp; rw [s114]; offs_simp; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; exact s114
    · config_simp; exact hz₂
    · config_simp; rw [hz₂]; push_cast; ring
    · config_simp
    · config_simp
    · config_simp; push_cast; rfl
    · config_simp; rw [s114, hK.nh]; rfl
    · config_simp; rw [s114, hK.nt]; rfl
    · refine ⟨fun r h1 h2 h3 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
      · config_simp
        simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
      · simp only [upd_out (lo := 101) (hi := 106) hr, Nat.reduceLeDiff,
          Nat.reduceLT, le_refl]
  obtain ⟨hn₃, hr₃, hnm₃, hrm₃, hout₃⟩ := hg₃
  have o₃ : ORun P Wd B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORun.glue e₃ o₂.2.lcte
    (fun a _ _ => by rw [hnm₃, hrm₃]; exact ⟨rfl, rfl⟩) (hn₃ 151 (by omega) (by omega) (by omega))
  -- the registers kept so far
  have k₃ : ∀ r, r < 101 → c₃.nreg r = cf.nreg r ∧ c₃.rreg r = cf.rreg r := fun r hr =>
    ⟨by rw [hn₃ r (by omega) (by omega) (by omega), (lf₂.1 r (by omega)).1, f₁.1 r (by omega)],
      by rw [hr₃ r (Or.inl hr), (lf₂.1 r (by omega)).2, f₁.2.1 r (by omega)]⟩
  have k₃' : ∀ r, r < 104 → c₃.nreg r = cf.nreg r := fun r hr => by
    rw [hn₃ r (by omega) (by omega) (by omega), (lf₂.1 r (by omega)).1, f₁.1 r (by omega)]
  have k114 : c₃.nreg 114 = σ e := by rw [hn₃ 114 (by omega) (by omega) (by omega), s114]
  have mf₃ : MemFrame B n (mem cf) (mem c₃) :=
    (m₁.trans B n sm₂).trans B n (fun a _ => by simp [DynTree.mem, hnm₃, hrm₃])
  -- the augmentation
  obtain ⟨c₄, G₄, o₄, m₄, f₄⟩ := regAdd_orun (P := P) hWW o₃.2.wb o₃.2.lcte (ra := 100)
    (rz := 101) (z := z) (by rw [(k₃ 100 (by omega)).1, hI.r100]) q101 (hL.dual.f_lt t)
  obtain ⟨c₅, G₅, o₅, m₅, f₅⟩ := regAdd2_orun (P := P) hWW o₄.2.wb o₄.2.lcte (ra := 100)
    (rz := 102) (z := -z) (by rw [f₄.1 100 (by omega), (k₃ 100 (by omega)).1, hI.r100])
    (by rw [f₄.2.1 102 (by omega), q102]) (hL.dual.f_lt t)
  set Fa := (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 with hFa
  have hSa := aug_stored hM hL hI.st t z
  have hanc := anc_test hL hSa (M.face e) (M.face (M.rev e))
  -- the test of the stop
  obtain ⟨c₆, G₆, o₆, m₆, f₆⟩ := regAdd_orun (P := P) hWW o₅.2.wb o₅.2.lcte (ra := 106)
    (rz := 103) (z := 1) (by rw [f₅.1 106 (by omega), f₄.1 106 (by omega), g106])
    (by rw [f₅.2.1 103 (by omega), f₄.2.1 103 (by omega), q103]) (hL.prim.f_lt _)
  obtain ⟨c₇, G₇, o₇, a7, m₇, f₇⟩ := regVal_orun (P := P) hWW false o₆.2.wb o₆.2.lcte
    (ra := 105) (by rw [f₆.1 105 (by omega), f₅.1 105 (by omega), f₄.1 105 (by omega), g105])
    (hL.prim.f_lt _)
  have e₈ := Exec.copyR (P := P) o₇.2.wb 106 195
  set c₈ := { c₇ with rreg := upd c₇.rreg 106 (c₇.rreg 195) } with hc₈
  have g₈ : GFr 106 107 c₇ c₈ := by rw [hc₈]; gfr_tac
  have o₈ := ORun.ofGFr e₈ o₇.2.lcte g₈ (by omega)
  obtain ⟨c₉, G₉, o₉, m₉, f₉⟩ := regAdd_orun (P := P) hWW o₈.2.wb o₈.2.lcte (ra := 106)
    (rz := 104) (z := -1)
    (by rw [show c₈.nreg 106 = c₇.nreg 106 from rfl, f₇.1 106 (by omega), f₆.1 106 (by omega),
      f₅.1 106 (by omega), f₄.1 106 (by omega), g106])
    (by rw [(g₈.1 104 (by omega)).2, f₇.2.1 104 (by omega), f₆.2.1 104 (by omega),
      f₅.2.1 104 (by omega), f₄.2.1 104 (by omega), q104]) (hL.prim.f_lt _)
  have hv₉ : c₉.rreg 106 = if st.T.Anc (M.face (M.rev e)) (M.face e) then 1 else 0 := by
    rw [f₉.2.1 106 (by omega), hc₈]
    config_simp
    rw [a7]
    exact hanc.1
  have hz₉ : c₉.rreg 105 = 0 := by
    rw [f₉.2.1 105 (by omega), (g₈.1 105 (by omega)).2, f₇.2.1 105 (by omega),
      f₆.2.1 105 (by omega), f₅.2.1 105 (by omega), f₄.2.1 105 (by omega), q105]
  have hF₉ : (runOpsE n Fa [.add (ιF (M.face e)) 1, .add (ιF (M.face e)) (-1)]).1 = Fa :=
    congrArg Prod.fst hanc.2
  have hl₉ : LCTE B n Fa G₉ c₉ := by
    have h : LCTE B n (runOpsE n Fa [.add (ιF (M.face e)) 1, .add (ιF (M.face e)) (-1)]).1
      G₉ c₉ := o₉.2.lcte
    rwa [hF₉] at h
  -- the frames so far
  have p₉ : P100 cf c₉ := (RegFr.p100 f₁).trans ((LoFr.p100 lf₂).trans (P100.trans
    ⟨fun r hr => ⟨hn₃ r (by omega) (by omega) (by omega), hr₃ r (Or.inl (by omega))⟩, hout₃⟩
    ((RegFr.p100 f₄).trans ((RegFr.p100 f₅).trans ((RegFr.p100 f₆).trans ((RegFr.p100 f₇).trans
      ((GFr.p100 g₈ (by omega)).trans (RegFr.p100 f₉))))))))
  have mf₉ : MemFrame B n (DynTree.mem cf) (DynTree.mem c₉) :=
    mf₃.trans B n (m₄.trans B n (m₅.trans B n (m₆.trans B n (m₇.trans B n
      (g₈.memFrame.trans B n m₉)))))
  have n₉ : ∀ r, r < 104 → c₉.nreg r = cf.nreg r := fun r hr => by
    rw [f₉.1 r (by omega), show c₈.nreg r = c₇.nreg r from rfl, f₇.1 r (by omega),
      f₆.1 r (by omega), f₅.1 r (by omega), f₄.1 r (by omega), k₃' r hr]
  have n104 : c₉.nreg 104 = σ e := by
    rw [f₉.1 104 (by omega), show c₈.nreg 104 = c₇.nreg 104 from rfl, f₇.1 104 (by omega),
      f₆.1 104 (by omega), f₅.1 104 (by omega), f₄.1 104 (by omega), g104]
  have n114 : c₉.nreg 114 = σ e := by
    rw [f₉.1 114 (by omega), show c₈.nreg 114 = c₇.nreg 114 from rfl, f₇.1 114 (by omega),
      f₆.1 114 (by omega), f₅.1 114 (by omega), f₄.1 114 (by omega), k114]
  have hk_o : ∀ d, lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h d =
      lkey N c ε st.g st.h d - z * st.T.chi s t d := fun d => lstep_key hne N d
  have hkey' : lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h =
      fun d => lkey N c ε st.g st.h d - z * st.T.chi s t d := funext hk_o
  have hzabs : |(z : ℝ)| ≤ (kZ D F N c ε : ℝ) := by
    rw [abs_of_nonneg (by exact_mod_cast hz0)]; exact_mod_cast hzZ
  have hlo' : ((kH0 D F N c ε - (x.i + 1 : ℕ) * kZ D F N c ε : ℤ) : ℝ) ≤ x.Lo - |(z : ℝ)| := by
    have := hI.lo
    push_cast at this ⊢
    linarith
  have hr102 : cf.nreg 102 = 0 := by rw [hI.r102, hdone]; rfl
  by_cases hA : st.T.Anc (M.face (M.rev e)) (M.face e)
  · -- the run stops
    have hstep := lstep_stop (c := c) (ε := ε) hne hA
    have e₁₀ := Exec.constN (P := P) o₉.2.wb 102 1 (by omega)
    set c₁₀ := { c₉ with nreg := upd c₉.nreg 102 1 } with hc₁₀
    have g₁₀ : GFr 102 103 c₉ c₁₀ := by rw [hc₁₀]; gfr_tac
    have o₁₀ := ORun.ofGFr e₁₀ hl₉ g₁₀ (by omega)
    have oB := ORun.ifLtR_true (a := 105) (b := 106)
      (e := .seq (.instr (.constR 110 0)) (pivCoreS B nD))
      (by rw [hz₉, hv₉, ite_eq_left hA]; norm_num) o₁₀
    have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq
      (ORun.seq' o₉ hF₉ oB))))))))
    refine ⟨⟨x.i + 1, true, x.Lo - |(z : ℝ)|, x.ops + 8⟩, c₁₀, _, G₉, _, _, o, ?_, rfl,
      by norm_num, ?_, ?_⟩
    · have hFend : (runOpsE n Fo₀ (hs ++ ([] ++ ([] ++ ([] ++ ([.add (ιV t) z] ++
          ([.add2 (ιV t) (-z)] ++ ([.add (ιF (M.face e)) 1] ++ ([] ++ ([] ++
          ([.add (ιF (M.face e)) (-1)] ++ []))))))))))).1 = Fa := by
        rw [runOpsE_fst_append]
        simp only [List.nil_append, List.append_nil, List.singleton_append]
        exact hF₉
      have p₁₀ : P100 cf c₁₀ := p₉.trans (GFr.p100 g₁₀ (by omega))
      have mf₁₀ : MemFrame B n (DynTree.mem cf) (DynTree.mem c₁₀) :=
        mf₉.trans B n g₁₀.memFrame
      refine ⟨?_, o.2.wb, ?_, fun j hj => hpiv j ?_, fun _ => ⟨by dsimp only; omega, ?_, ?_⟩,
        hlo', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runOpsE_fst_append]; exact o.2.lcte
      · unfold LStored
        rw [hFend]
        show Stored M.dual n ιF ιG ιV ιE (wlen N c ε) s (x.Lo - |(z : ℝ)|) Fa
          (toDD (lstep M c ε s t st).1.T)
          (lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h)
        rw [hstep.2, hkey']
        exact hSa
      · dsimp only at hj
        rcases hj with h | ⟨-, h'⟩
        · omega
        · exact absurd h' (by decide)
      · simpa using hstep.1
      · dsimp only
        simp only [Nat.add_sub_cancel]
        refine ⟨hne, ?_⟩
        rw [show c₁₀.nreg 104 = c₉.nreg 104 from (g₁₀.1 104 (by omega)).1, n104]
      · show x.ops + 8 ≤ 33 * (x.i + 1)
        have := hI.ops; omega
      · show KMem M.dual σ ιF (toDD (lstep M c ε s t st).1.T) _ _ c₁₀
        rw [hstep.2]
        exact hI.kmem.congr mf₁₀ hB hL
      · rw [(p₁₀.1 100 le_rfl).1]; exact hI.r100
      · rw [(g₁₀.1 101 (by omega)).1, n₉ 101 (by omega)]; exact hI.r101
      · rw [hc₁₀]; config_simp; rfl
      · rw [(g₁₀.1 103 (by omega)).1, n₉ 103 (by omega)]; exact hI.r103
      · rw [(p₁₀.1 100 le_rfl).2]; exact hI.q100
      · exact mvFr_step hI.fr p₁₀ mf₁₀
    · have : opCostE n ≥ 42220 := by unfold opCostE; omega
      omega
    · simp [PG.μ, hdone]; omega
  · -- the pivot
    have hstep := lstep_piv (c := c) (ε := ε) hne hA
    have hy : M.face (M.rev e) ≠ st.T.root := st.T.ne_root_of_not_anc hA
    obtain ⟨-, -, hoff, -⟩ := st.T.chi_spec hM s t
    have hbT : ¬ st.T.InT e := fun h => by rw [hoff e h] at he; exact absurd he (by norm_num)
    have e₁₀ := Exec.constR (P := P) o₉.2.wb 110 0
    set c₁₀ := { c₉ with rreg := upd c₉.rreg 110 ((0 : ℤ) : ℝ) } with hc₁₀
    have g₁₀ : GFr 110 111 c₉ c₁₀ := by rw [hc₁₀]; gfr_tac
    have o₁₀ := ORun.ofGFr e₁₀ hl₉ g₁₀ (by omega)
    have p₁₀ : P100 cf c₁₀ := p₉.trans (GFr.p100 g₁₀ (by omega))
    have mf₁₀ : MemFrame B n (DynTree.mem cf) (DynTree.mem c₁₀) := mf₉.trans B n g₁₀.memFrame
    obtain ⟨c₁₁, G₁₁, osP, o₁₁, -, -, -, hSt', hKM', lf₁₁, rm₁₁, nm₁₁⟩ :=
      pivCore_orun (σ := σ) (S := ∅) (ℓ := 0) hWW hWa hB hP hM.dual hL hK o₁₀.2.wb o₁₀.2.lcte
        hSa (hI.kmem.congr mf₁₀ hB hL)
        (by rw [show c₁₀.nreg 101 = c₉.nreg 101 from rfl, n₉ 101 (by omega)]; exact hI.r101)
        (b := e) (cv := 0) (by rw [show c₁₀.nreg 114 = c₉.nreg 114 from rfl, n114])
        (by rw [hc₁₀]; config_simp) hy hA hbT
    have oB := ORun.ifLtR_false (a := 105) (b := 106) (t := .instr (.constN 102 1))
      (by rw [hz₉, hv₉, ite_eq_right hA]; norm_num) (o₁₀.seq o₁₁)
    have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq
      (ORun.seq' o₉ hF₉ oB))))))))
    refine ⟨⟨x.i + 1, false, x.Lo - |(z : ℝ)|, x.ops + 33⟩, c₁₁, _, G₁₁, _, _, o, ?_, rfl,
      by norm_num, ?_, ?_⟩
    · have hFend : (runOpsE n Fo₀ (hs ++ ([] ++ ([] ++ ([] ++ ([.add (ιV t) z] ++
          ([.add2 (ιV t) (-z)] ++ ([.add (ιF (M.face e)) 1] ++ ([] ++ ([] ++
          ([.add (ιF (M.face e)) (-1)] ++ ([] ++ osP)))))))))))).1 = (runOpsE n Fa osP).1 := by
        rw [runOpsE_fst_append]
        simp only [List.nil_append, List.singleton_append]
        rw [show ∀ l : List EOp, EOp.add (ιV t) z :: EOp.add2 (ιV t) (-z) ::
          EOp.add (ιF (M.face e)) 1 :: EOp.add (ιF (M.face e)) (-1) :: l =
          [EOp.add (ιV t) z, EOp.add2 (ιV t) (-z)] ++
            ([EOp.add (ιF (M.face e)) 1, EOp.add (ιF (M.face e)) (-1)] ++ l) from fun _ => rfl,
          runOpsE_fst_append, runOpsE_fst_append, hF₉]
      have p₁₁ : P100 cf c₁₁ := p₁₀.trans (LoFr.p100 lf₁₁)
      have hT' : toDD (lstep M c ε s t st).1.T = (toDD st.T).reparent (M.dual.head e) e hy
          (dual_face_rev e) hA := by
        rw [hstep.2]; rfl
      have hval : pivotVal (toDD st.T) (wlen N c ε) (wlen N c ε)
          (fun d => lkey N c ε st.g st.h d - z * st.T.chi s t d) (M.dual.head e) 0 =
          lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h := by
        rw [← hkey']
        refine pivotVal_key hIst hy _ _ (fun d hd => ?_) (fun d hd => ?_)
        · rw [(lstep_gh hne d).1, hoff d hd]; ring
        · rw [(lstep_gh hne d).2, hoff d hd]; ring
      refine ⟨?_, o.2.wb, ?_, fun j hj => ?_, fun h => absurd h Bool.false_ne_true, hlo', ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runOpsE_fst_append]; exact o.2.lcte
      · unfold LStored
        rw [hFend]
        show Stored M.dual n ιF ιG ιV ιE (wlen N c ε) s (x.Lo - |(z : ℝ)|) _
          (toDD (lstep M c ε s t st).1.T)
          (lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h)
        rw [hT', ← hval]
        have := hSt'
        simp only [Int.cast_zero, abs_zero, sub_zero] at this
        exact this
      · dsimp only at hj
        rcases hj with h | ⟨h, -⟩
        · exact hpiv j (by omega)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
          · exact hpiv j h
          · exact hstep.1
      · show x.ops + 33 ≤ 33 * (x.i + 1)
        have := hI.ops; omega
      · show KMem M.dual σ ιF (toDD (lstep M c ε s t st).1.T) _ _ c₁₁
        rw [hT']; exact hKM'
      · rw [(p₁₁.1 100 le_rfl).1]; exact hI.r100
      · rw [(lf₁₁.1 101 (by omega)).1, show c₁₀.nreg 101 = c₉.nreg 101 from rfl,
          n₉ 101 (by omega)]; exact hI.r101
      · rw [(lf₁₁.1 102 (by omega)).1, show c₁₀.nreg 102 = c₉.nreg 102 from rfl,
          n₉ 102 (by omega), hr102]; rfl
      · rw [(lf₁₁.1 103 (by omega)).1, show c₁₀.nreg 103 = c₉.nreg 103 from rfl,
          n₉ 103 (by omega)]; exact hI.r103
      · rw [(p₁₁.1 100 le_rfl).2]; exact hI.q100
      · refine ⟨fun r hr => ?_, ?_, fun a ha => ?_, fun a ha han => ?_⟩
        · rw [(p₁₁.1 r hr.le).1, (p₁₁.1 r hr.le).2]; exact hI.fr.1 r hr
        · rw [p₁₁.2]; exact hI.fr.2.1
        · rw [rm₁₁ a ha]; exact ((mf₁₀ a ha).2).trans (hI.fr.2.2.1 a ha)
        · rw [nm₁₁ a ha (by have := hL.prim.f_lt (M.dual.head e); unfold aTP; omega)]
          exact ((mf₁₀ a ha).1).trans (hI.fr.2.2.2 a ha han)
    · have : opCostE n ≥ 42220 := by unfold opCostE; omega
      omega
    · simp [PG.μ, hdone]; omega

/-- **The loop of the steps on the machine**: from a state of the invariant (not stopped), the
loop runs until a step stops; it performs operations `os`, counted twice the operations of its
iterations (at most `33` per step) and `2` further steps. At the end the run has stopped after
`i ≤ m + 1` steps, and `lrun (fuel F)` from the initial state is the state after `i` steps. -/
theorem pLoop_orun (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hPO : PertOK M c ε s t d₀)
    (hI₀ : LInv c ε s t st₀) (hroot : st₀.T.root = M.face d₀)
    (hμ₀ : |M.div st₀.h s| ≤ lexR F ε) (hN : 2 * lexR F ε < N)
    (hL : Layout M.dual n ιF ιG ιV ιE) (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    {x : PG} {hs : List EOp} {G : List VT} {cf : Config}
    (hI : PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd x hs G cf)
    (hv : ValidOpsE n Fo₀ hs) :
    ∃ x' os c' G', ORun P Wd B n (pLoopS B nD) cf (runOpsE n Fo₀ hs).1 G c' os G'
        (2 * (x'.ops - x.ops)) 2 ∧
      PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd x' (hs ++ os) G' c' ∧
      x'.done = true ∧ x.ops ≤ x'.ops ∧ x'.i ≤ Fintype.card D + 1 ∧
      lrun M c ε s t (fuel F) st₀ =
        (ltraj M c ε s t st₀ x'.i, x'.i, true) := by
  obtain ⟨x', os, c', G', o, hI', ht', hcnt⟩ := ORun.whileLtN_abs (P := P) (W := Wd) (B := B)
    (n := n) (a := 102) (b := 103) (body := pBodyS B nD) Fo₀
    (PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd) PG.ops (PG.μ D)
    (fun x hs G c h _ => ⟨h.lcte, h.wb⟩)
    (fun x hs G c h _ ht => by
      obtain ⟨x', c', os, G', j, h', o, hI', hops, hj, hh, hμ⟩ := pBody_orun hWW hWa hB hP hM
        hc hst hPO hI₀ hroot hμ₀ hN hL hK x hs G c h ht
      exact ⟨x', c', os, G', j, h', o, hI', hops, hj, hh, hμ⟩) hI hv
  have hdone : x'.done = true := by
    by_contra h
    rw [hI'.r102, hI'.r103, ite_eq_right h] at ht'
    exact ht' (by norm_num)
  obtain ⟨h1, h2, -⟩ := hI'.fin hdone
  have hpiv : ∀ j < x'.i - 1,
      (lstep M c ε s t (ltraj M c ε s t st₀ j)).2 = false :=
    fun j hj => hI'.piv j (Or.inl (by omega))
  have hle := piv_le_card hPO hI₀ hroot hpiv
  have hlt := piv_lt_fuel (c := c) (ε := ε) hM hst hpiv
  have hrun := lrun_of_stop (x'.i - 1) st₀ hpiv h2 (fuel F) hlt
  rw [Nat.sub_add_cancel h1] at hrun
  exact ⟨x', os, c', G', o, hI', hdone, hcnt, by omega, hrun⟩

end Body

end STFlow

end PlanarFlow
