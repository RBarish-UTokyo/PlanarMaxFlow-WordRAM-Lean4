module

public import PlanarFlow.STFlow.ProgOut

/-!
# The perturbed single-source single-sink maximum flow on the machine

The program `pstProg` (`r151 := n`, the initialisation of the dynamic trees, `pstS`):

1. `inS` (Klein's initialisation, for the dual map): the dual tree `T₀` and its cotree `C₀`
   from the input (orders `KInit`), `T₀` with the perturbed lengths `w = N c + ε`, the cotree with
   the values `w d - cob (psum w) d`, which are the keys of the initial state
   `(cob (psum c), cob (psum ε), T₀)` (`init_key`), and `kH0` at the nodes of the vertices;
2. `setupI`: the nodes of `s` and `t` (the tails of the two darts of the array `GB` of the
   input), the loop registers, the threshold `kTh`;
3. `pLoopS`: the steps of the perturbed run until one stops (`PlanarFlow/STFlow/ProgLoop.lean`);
4. the flow into `OUT` (`PlanarFlow/STFlow/ProgOut.lean`).

* `pstS_orun`: **the program from the initialised structure**, counted at most `pstOps`
  operations and `pstExt` further steps, with `OUT[d] = RS[d] · g d`, `g` the flow of
  `lrun (fuel F)` from the initial state;
* `pcore_exec`: **the end-to-end theorem** for a given initial state.
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

/-! ### The program -/

/-- The setup of the loop: the nodes of `s` (`r101`) and `t` (`r100`), the tails of the darts
`GB[0]` and `GB[1]`; `r102 := 0`, `r103 := 1`; the threshold into the real `r100`. -/
def setupI (nD n : ℕ) : List Instr :=
  [.constN 130 (iGB nD n), .readIn 130 130, .constN 131 (iNF nD), .addN 131 131 130,
    .readIn 101 131, .constN 130 (iGB nD n + 1), .readIn 130 130, .constN 131 (iNF nD),
    .addN 131 131 130, .readIn 100 131, .constN 102 0, .constN 103 1, .constN 105 (aTH nD),
    .loadR 100 105]

/-- **The perturbed single-source single-sink maximum flow on the dynamic trees** (after
`r151 := n` and the initialisation of the structure). -/
def pstS (B nD n : ℕ) : Stmt :=
  .seq (inS B nD n 2) <| .seq (block (setupI nD n)) <| .seq (pLoopS B nD) <|
  .seq (cvS B nD n) <| .seq (lamS B nD) <| .seq (rdS B nD) <| .seq (.instr (.constR 110 1)) <|
  .seq (regAdd2S B 100 110) (wrS B nD)

/-- **The program.** -/
def pstProg (B nD n : ℕ) : Stmt :=
  .seq (.instr (.constN 151 n)) (.seq (initS B) (pstS B nD n))

/-- The bound of the counted operations of `pstS`. -/
def pstOps (nV nF nD : ℕ) : ℕ :=
  6 * (nV + nF) + 2 * nD + 66 * (nD + 1) + 4 * nF + 2 * nD + 7 * nD + 3

/-- The bound of the further steps of `pstS`. -/
def pstExt (nV nF nD : ℕ) : ℕ := 60 * (nV + nF) + 20 * nD + 42 + 14 + 2 + 42 * nF + 5 + 13 +
  12 * nD + 4 + 1 + 42 * nD + 4

/-! ### Lemmas -/

section Lemmas

variable {M : CombMap D V F}

/-- **The values of the initial cotree are the keys of the initial state.** -/
lemma init_key (N : ℤ) (c ε : D → ℤ) (T : DTree M) (d : D) :
    wlen N c ε d + (toDD T).psum (wlen N c ε) (M.dual.tail d) -
        (toDD T).psum (wlen N c ε) (M.dual.head d) =
      lkey N c ε (M.cob (T.psum c)) (M.cob (T.psum ε)) d := by
  have h : ∀ x, (toDD T).psum (wlen N c ε) x = N * T.psum c x + T.psum ε x := fun x => by
    have : wlen N c ε = (fun d => N * c d) + ε := rfl
    show T.psum (wlen N c ε) x = _
    rw [this, DTree.psum_add, DTree.psum_smul]
  rw [h, h]
  simp only [lkey, wlen, cob]
  change N * c d + ε d + (N * T.psum c (M.face d) + T.psum ε (M.face d)) -
    (N * T.psum c (M.face (M.rev d)) + T.psum ε (M.face (M.rev d))) = _
  ring

/-- A step that stops keeps the tree. -/
lemma lstep_T_of_stop {c ε : D → ℤ} {s t : V} {st : LSt M} (hne : (pathSet s t st.T).Nonempty)
    (h : (lstep M c ε s t st).2 = true) : (lstep M c ε s t st).1.T = st.T := by
  by_cases ha : st.T.Anc (M.face (M.rev (lbott c ε s t st.g st.h st.T hne)))
      (M.face (lbott c ε s t st.g st.h st.T hne))
  · exact (lstep_stop hne ha).2
  · rw [(lstep_piv hne ha).1] at h; exact absurd h (by simp)

variable {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ} {ιV : V → ℕ} {ιE : D → ℕ}

/-- **The capacities on the stored dual tree**: the operations of `cvS` store `T` with the
capacities `cap` instead of the perturbed lengths, and keep the cotree. -/
theorem conv_stored (hL : Layout M.dual n ιF ιG ιV ιE) {w : D → ℤ} {s : V} {Lo : ℝ}
    {Fo : Forest} {T : DTree M} {κ : D → ℤ}
    (hS : Stored M.dual n ιF ιG ιV ιE w s Lo Fo (toDD T) κ) {ts : List F} (hnd : ts.Nodup)
    (hts : ∀ y, y ∈ ts ↔ y ≠ T.root) (cap : D → ℤ) :
    ValidOpsE n Fo (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))) ∧
    Stored M.dual n ιF ιG ιV ιE cap s Lo (runOpsE n Fo (ts.flatMap fun y => pointOps ιF ιG
      (toDD T) y (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y))))).1
      (toDD T) κ := by
  classical
  have heq : (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))) =
      convOps ιF ιG (toDD T) (fun d => w (M.dual.rev d)) (fun d => cap (M.dual.rev d)) ts := by
    unfold convOps
    refine List.flatMap_congr fun y _ => ?_
    show _ = pointOps ιF ιG (toDD T) y (cap (M.rev (M.rev (T.par y))) -
      w (M.rev (M.rev (T.par y)))) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))
    rw [M.rev_rev]
  rw [heq]
  obtain ⟨hv, -, hR, hp, hag⟩ := conv_trep (C := toDD T) hL.prim hL.hv
    (fun d => cap (M.dual.rev d)) ts hS.tree hnd (fun y hy => (hts y).1 hy)
  refine ⟨hv, ⟨trep_congr_edges hR fun y hy => ?_, fun d hd => ?_, ?_, ?_⟩⟩
  · have hm : y ∈ ts := (hts y).2 hy
    have e1 : ∃ y' ∈ ts, (toDD T).par y = (toDD T).par y' ∨
        (toDD T).par y = M.dual.dual.rev ((toDD T).par y') := ⟨y, hm, Or.inl rfl⟩
    have e2 : ∃ y' ∈ ts, M.dual.dual.rev ((toDD T).par y) = (toDD T).par y' ∨
        M.dual.dual.rev ((toDD T).par y) = M.dual.dual.rev ((toDD T).par y') :=
      ⟨y, hm, Or.inr rfl⟩
    simp only [e1, e2, ite_true, and_self]
  · rw [hp]; exact hS.treeIso d hd
  · obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
    refine ⟨C, β, β₂, hroot, hoff, hRc.congr (fun x => hag _ fun d => (hL.gf d x).symm)
      (fun d => hag _ fun d' => (hL.ge d' d).symm), hIc.congr
      (fun d => hag _ fun d' => (hL.ge d' d).symm), hLo⟩
  · exact intF_runOpsE _ hS.int

end Lemmas

/-! ### The program from the initialised structure -/

section Main

variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {W B : ℕ}

/-- **The perturbed single-source single-sink maximum flow on the machine, from the initialised
structure.** The hypotheses: a plane map, nonnegative capacities `c`, a perturbation `ε` with the
properties `PertOK` (nonnegative, separating the darts of the path, at most `m + 1` steps),
`s ≠ t`, the dart `d₀` leaving `t` and `d₁` leaving `s` (`GB`), an initial dual
tree `T₀` rooted at the face of `d₀` whose state `(cob (psum c), cob (psum ε), T₀)` satisfies
the invariant `LInv` (a shortest-path tree for the perturbed lengths: `exists_linit`), a cotree
`C₀` of it rooted at `s` (`KInit`, with orders), `N > 2 lexR`, the real memory holding `w` in
`WT` and `PH`, `c` in `CP`, the restriction `rs` in `RS`, `kTh` and `kH0`. Then `pstS` makes an
amortised run counted at most `pstOps` operations and `pstExt` further steps, printing nothing,
and ends with `OUT[d] = rs d · g d`, `g` the flow of `lrun (fuel F)` from the initial state. -/
theorem pstS_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + 6 ≤ W)
    (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hM : M.IsPlane) {c ε : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t) {d₀ d₁ : D} (hd₀ : M.tail d₀ = t)
    (hPO : PertOK M c ε s t d₀)
    (hd₁ : M.tail d₁ = s) {T₀ : DTree M} (hroot : T₀.root = M.face d₀)
    (hI₀ : LInv c ε s t ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩)
    {N : ℤ} (hN : 2 * lexR F ε < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = s)
    {rs : D → ℝ} {cf : Config} (hcf : WordsBounded W cf) {G : List VT}
    (hS : LCTE B n (Forest.init n) G cf)
    (hwt : ∀ d, cf.rmem (aWT + σ d) = wlen N c ε d)
    (hph : ∀ d, cf.rmem (aPH nD + σ d) = wlen N c ε d)
    (hcp : ∀ d, cf.rmem (aCP nD + σ d) = c d) (hrs : ∀ d, cf.rmem (aRS nD + σ d) = rs d)
    (hth : cf.rmem (aTH nD) = kTh D F N c ε) (hh0 : cf.rmem (aH0 nD) = kH0 D F N c ε) :
    ∃ c' F' G' m', LRun P W B n (pstS B nD n) cf G c' F' G' m'
        (pstExt (Fintype.card V) (Fintype.card F) nD) ∧
      m' ≤ pstOps (Fintype.card V) (Fintype.card F) nD ∧
      (∀ d, c'.rmem (aOT nD + σ d) = rs d *
        (lrun M c ε s t (fuel F)
          ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩).1.g d) ∧
      c'.output = cf.output := by
  classical
  set w := wlen N c ε with hw
  set st₀ : LSt M := ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩ with hst₀
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hnD : Fintype.card D = nD := by simpa using Fintype.card_congr σ
  -- 1. the initialisation
  obtain ⟨c₁, G₁, os₁, o₁, -, -, hSt₁, hKM₁, r₁, out₁, nm₁, rm₁⟩ := in_orun (k := 2)
    (S := ∅) (ℓ := 0) hW (by omega) hB (by omega) hP hL hK hI hoff hcf hS hwt hph
    (H₀ := kH0 D F N c ε) hh0
  set F₁ := (runOpsE n (Forest.init n) os₁).1 with hF₁
  have hL₁ : LStored M n ιF ιG ιV ιE N c ε s (kH0 D F N c ε : ℝ) F₁ st₀ := by
    unfold LStored
    rw [← hCr]
    have : lkey N c ε st₀.g st₀.h = fun d => w d + (toDD T₀).psum w (M.dual.tail d) -
        (toDD T₀).psum w (M.dual.head d) := funext fun d => (init_key N c ε T₀ d).symm
    rw [this]; exact hSt₁
  -- 2. the setup
  have hg0 : P.data.getD (iGB nD n) 0 = σ d₁ := by simpa using hG 0 (by omega)
  have hg1 : P.data.getD (iGB nD n + 1) 0 = σ d₀ := by simpa using hG 1 (by omega)
  have hc₁ := o₁.2.wb
  have h0 := hσ d₀
  have h1 := hσ d₁
  have hth₁ : c₁.rmem (aTH nD) = kTh D F N c ε := by
    rw [rm₁ _ (Or.inl (by unfold aTH; omega)) (Or.inr (by unfold aTH aVL; omega)), hth]
  obtain ⟨c₂, k₂, e₂, hk₂, p100, p101, p102, p103, q100, n₂, r₂, mm₂, rm₂, out₂⟩ :
      ∃ c' k', Exec P W (block (setupI nD n)) c₁ c' k' ∧ k' = 14 ∧ c'.nreg 100 = ιV t ∧
      c'.nreg 101 = ιV s ∧ c'.nreg 102 = 0 ∧ c'.nreg 103 = 1 ∧
      c'.rreg 100 = (kTh D F N c ε : ℝ) ∧
      (∀ r, r ≠ 100 → r ≠ 101 → r ≠ 102 → r ≠ 103 → r ≠ 105 → r ≠ 130 → r ≠ 131 →
        c'.nreg r = c₁.nreg r) ∧ (∀ r, r ≠ 100 → c'.rreg r = c₁.rreg r) ∧
      c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
    unfold setupI
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (simp only [iGB]; omega)
      | (offs_simp'; omega)
      | (config_simp; rw [hg0]; offs_simp'; omega)
      | (config_simp; rw [hg1]; offs_simp'; omega))
    refine ⟨rfl, ?_, ?_, by config_simp, by config_simp, ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_,
      fun r h1 => ?_, rfl, rfl, rfl⟩
    · config_simp; rw [hg1, hK.nf]; exact congrArg ιV hd₀
    · config_simp; rw [hg0, hK.nf]; exact congrArg ιV hd₁
    · config_simp; rw [hth₁]
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, upd_other _ _ _ h4,
        upd_other _ _ _ h5, upd_other _ _ _ h6, upd_other _ _ _ h7]
    · config_simp; simp only [upd_other _ _ _ h1]
  have o₂ : ORun P W B n _ c₁ F₁ G₁ c₂ [] G₁ 0 k₂ := ORun.glue e₂ o₁.2.lcte
    (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩)
    (n₂ 151 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  have mf₂ : MemFrame B n (DynTree.mem c₁) (DynTree.mem c₂) := fun a _ => by
    simp [DynTree.mem, mm₂, rm₂]
  -- 3. the loop
  have hμ₀ : |M.div st₀.h s| ≤ lexR F ε := by
    have h0 : M.div st₀.h s = 0 := M.div_cob _ s
    rw [h0, abs_zero]
    unfold lexR
    have : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
    positivity
  have hP₀ : PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B F₁ c₂ W ⟨0, false, (kH0 D F N c ε : ℝ), 0⟩ []
      G₁ c₂ := by
    refine ⟨o₂.2.lcte, e₂.wb_right, hL₁, fun j hj => ?_, fun h => absurd h Bool.false_ne_true,
      by simp, le_refl _, hKM₁.congr mf₂ hB hL, p100, p101, by rw [p102]; rfl, p103, q100,
      MvFr.refl B n c₂⟩
    simp at hj
  obtain ⟨x', os₃, c₃, G₃, o₃, hI₃, hdone, -, hix, hrun⟩ := pLoop_orun hW (by omega) hB hP hM
    hc hst hPO hI₀ hroot hμ₀ hN hL hK hP₀ trivial
  set stf := ltraj M c ε s t st₀ x'.i with hstf
  obtain ⟨hi1, hstop, hne, h104⟩ := hI₃.fin hdone
  set stp := ltraj M c ε s t st₀ (x'.i - 1) with hstp
  have hsucc : stf = (lstep M c ε s t stp).1 := by
    rw [hstf, hstp, show x'.i = x'.i - 1 + 1 by omega]; rfl
  have hpiv : ∀ j < x'.i - 1, (lstep M c ε s t (ltraj M c ε s t st₀ j)).2 = false :=
    fun j hj => hI₃.piv j (Or.inl (by omega))
  have hTf : stf.T = stp.T := by rw [hsucc]; exact lstep_T_of_stop hne hstop
  have hrootf : stf.T.root = T₀.root := by
    rw [hTf]; exact ltraj_root hM hst hpiv (x'.i - 1) le_rfl
  set e := lbott c ε s t stp.g stp.h stp.T hne with he_def
  have he : stf.T.chi s t e = 1 := by rw [hTf]; exact lbott_mem c ε s t _ _ _ hne
  have hsat : stf.g e = c e := by
    rw [hsucc, (lstep_gh hne e).1, ← he_def, ← hTf, he]; ring
  have hIf : LInv c ε s t stf := ltraj_inv hM hI₀ x'.i
  -- the frame of the loop
  have hfr₃ := hI₃.fr
  have hcp₃ : ∀ d, c₃.rmem (aCP nD + σ d) = c d := fun d => by
    have := hσ d
    rw [hfr₃.2.2.1 _ (Or.inl (by unfold aCP; omega)), rm₂,
      rm₁ _ (Or.inl (by unfold aCP; omega)) (Or.inr (by unfold aCP aVL; omega)), hcp]
  have hrs₃ : ∀ d, c₃.rmem (aRS nD + σ d) = rs d := fun d => by
    have := hσ d
    rw [hfr₃.2.2.1 _ (Or.inl (by unfold aRS; omega)), rm₂,
      rm₁ _ (Or.inl (by unfold aRS; omega)) (Or.inr (by unfold aRS aVL; omega)), hrs]
  -- 4. the capacities on the dual tree
  have hSf : Stored M.dual n ιF ιG ιV ιE w s x'.Lo (runOpsE n F₁ ([] ++ os₃)).1 (toDD stf.T)
      (lkey N c ε stf.g stf.h) := hI₃.st
  obtain ⟨hvc, hSC⟩ := conv_stored hL hSf hI.oT.ynd (fun y => by
    rw [hI.oT.ymem y, hrootf]; rfl) c
  obtain ⟨c₄, G₄, o₄, fr₄⟩ := cv_orun (T₀ := T₀) (T := stf.T) hW hWa hB7 hB hP hL hK hI hrootf
    (cap := c) (w := w) o₃.2.wb o₃.2.lcte (fun y hy => hI₃.kmem.tp y hy) hcp₃
    (fun d => hI₃.kmem.wt d) hvc
  set FC := (runOpsE n (runOpsE n F₁ ([] ++ os₃)).1 (ts.flatMap fun y => pointOps ιF ιG
    (toDD stf.T) y (c (stf.T.par y) - w (stf.T.par y))
      (c (M.rev (stf.T.par y)) - w (M.rev (stf.T.par y))))).1 with hFC
  have hcp₄ : ∀ d, c₄.rmem (aCP nD + σ d) = c d := fun d => by
    have := hσ d; rw [(fr₄.2.2 _ (Or.inl (by unfold aCP; omega))).2, hcp₃]
  have hrs₄ : ∀ d, c₄.rmem (aRS nD + σ d) = rs d := fun d => by
    have := hσ d; rw [(fr₄.2.2 _ (Or.inl (by unfold aRS; omega))).2, hrs₃]
  -- 5. the value
  obtain ⟨c₅, G₅, o₅, l111, fr₅, l104⟩ := lam_orun hW hB7 hP hL hK o₄.2.wb o₄.2.lcte (e := e)
    (by rw [(fr₄.1 104 (by omega)).1]; exact h104) hcp₄
  -- 6. the second values before
  obtain ⟨c₆, G₆, o₆, a₆, r₆, out₆, nm₆, rm₆⟩ := rd_orun hW hB7 hP hL hK o₅.2.wb o₅.2.lcte
  -- 7. the addition
  have e₇ := Exec.constR (P := P) o₆.2.wb 110 1
  set c₇ := { c₆ with rreg := upd c₆.rreg 110 ((1 : ℤ) : ℝ) } with hc₇
  have g₇ : GFr 110 111 c₆ c₇ := by rw [hc₇]; gfr_tac
  have o₇ := ORun.ofGFr e₇ o₆.2.lcte g₇ (by omega)
  have t100 : c₇.nreg 100 = ιV t := by
    rw [show c₇.nreg 100 = c₆.nreg 100 from rfl, (r₆ 100 (by omega)).1, (fr₅.1 100 (by omega)).1,
      (fr₄.1 100 (by omega)).1]; exact hI₃.r100
  obtain ⟨c₈, G₈, o₈, m₈, f₈⟩ := regAdd2_orun (P := P) hW o₇.2.wb o₇.2.lcte (ra := 100)
    (rz := 110) (z := 1) t100 (by rw [hc₇]; config_simp) (hL.dual.f_lt t)
  -- 8. the flow
  obtain ⟨c₉, G₉, o₉, w₉, r₉, out₉, nm₉, rm₉⟩ := wr_orun hW hB7 hP hL hK o₈.2.wb o₈.2.lcte
  -- the values read by the last loop
  have hl₈ : c₈.rreg 111 = c e - pathSum FC n (ιF (M.face (M.rev e))) +
      pathSum FC n (ιF (M.face e)) := by
    rw [f₈.2.1 111 (by omega), show c₇.rreg 111 = c₆.rreg 111 from by
      rw [hc₇]; config_simp, (r₆ 111 (by omega)).2, l111]; rfl
  have hrs₈ : ∀ d, c₈.rmem (aRS nD + σ d) = rs d := fun d => by
    have := hσ d
    have h8 := (m₈ (aRS nD + σ d) (Or.inl (by unfold aRS; omega))).2
    have h5 := (fr₅.2.2 (aRS nD + σ d) (Or.inl (by unfold aRS; omega))).2
    simp only [DynTree.mem] at h8
    rw [h8, show c₇.rmem = c₆.rmem from rfl, rm₆ _ (Or.inl (by unfold aRS; omega))
      (Or.inl (by unfold aRS aAK; omega)), h5, hrs₄]
  have hak₈ : ∀ d, c₈.rmem (aAK nD + σ d) = FC.val2 (ιE d) := fun d => by
    have := hσ d
    have h8 := (m₈ (aAK nD + σ d) (Or.inl (by unfold aAK; omega))).2
    simp only [DynTree.mem] at h8
    rw [h8, show c₇.rmem = c₆.rmem from rfl, a₆ d]; rfl
  have hps : ∀ x, pathSum FC n (ιF x) = stf.T.psum c x := fun x =>
    lct_label (M := M.dual) hSC.tree hL.prim.f_lt hL.prim.e_lt hL.hv x
  have hval : ∀ d, wrVal (runOpsE n FC [.add2 (ιV t) 1]).1 n ιF ιV ιE M (c₈.rreg 111)
      (c₈.rmem (aRS nD + σ d)) (c₈.rmem (aAK nD + σ d)) d = rs d * stf.g d := by
    intro d
    have hχ := chi_read hM hL hSC t d
    have hg := lfinal_g hM hst hIf he hsat d
    have hp : (runOpsE n FC [.add2 (ιV t) 1]).1.par = FC.par := rfl
    have hsum : ∀ u, pathSum (runOpsE n FC [.add2 (ιV t) 1]).1 n u = pathSum FC n u := by
      intro u
      unfold pathSum
      rw [rootPath_congr (Fo := FC) (Fo' := (runOpsE n FC [.add2 (ιV t) 1]).1) hp]; rfl
    unfold wrVal
    rw [hrs₈, hak₈, hl₈, hp, hsum, hsum, hps, hps, hps, hps, hg]
    have hk : (if FC.par (ιE d) = ιV (M.tail d) then (1 : ℝ) else -1) *
        (((runOpsE n FC [.add2 (ιV t) 1]).1.val2 (ιE d) - FC.val2 (ιE d)) *
          (c e - stf.T.psum c (M.face (M.rev e)) + stf.T.psum c (M.face e))) =
        (stf.T.chi s t d : ℝ) *
          (c e - stf.T.psum c (M.face (M.rev e)) + stf.T.psum c (M.face e)) := by
      rw [hχ]; ring
    rw [hk]
    simp only [cob]
    push_cast
    ring
  -- the run
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq o₉)))))))
  have hops := hI₃.ops
  have hts := hI.oT.ylen
  refine ⟨c₉, _, G₉, _, o.2.mono (m' := pstOps (Fintype.card V) (Fintype.card F) nD) ?_ ?_,
    le_rfl, fun d => ?_, ?_⟩
  · unfold pstOps; omega
  · unfold pstExt; omega
  · rw [w₉ d]; exact (hval d).trans (by rw [hrun])
  · rw [out₉, f₈.2.2, g₇.2.2.2, out₆, fr₅.2.1, fr₄.2.1, hfr₃.2.1, out₂, out₁]

end Main

end STFlow

end PlanarFlow
