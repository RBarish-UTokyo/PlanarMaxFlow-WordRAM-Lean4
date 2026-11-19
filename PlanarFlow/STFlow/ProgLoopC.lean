module

public import PlanarFlow.STFlow.ProgLoop
public import PlanarFlow.STFlow.PivC

/-!
# The loop of the steps with bounded comparisons

The compare-bounded versions (`ORunC`) of `pBody_orun` and `pLoop_orun`
(`PlanarFlow/STFlow/ProgLoop.lean`), replayed with the same proofs. The invariant `PInvC` adds to
`PInv` the bound `P0 + i Δ` on the potential of the forest after `i` steps
(`PlanarFlow/DynTree/CmpPot.lean`): a step raises it by at most
`Δ ≥ 2 n kZ + n + 4 Kw` (`Kw` a bound of the lengths `|N c + ε|`): the augmentation by
`n · 2 |z|`, the test of the stop by `n` in between, the pivot by the four new values
(`pivot_pot`). With `P0 + (m + 2) Δ ≤ Vb`, every forest of the loop has values at most `Vb`, and
with `2 Vb ≤ H`, `|kTh| ≤ Vb`, `1 ≤ H` every comparison of the loop is within `H`.
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

/-- The four new values of a pivot with the amount `0` and `wt = φ = w`. -/
lemma pot_four {w : D → ℤ} {Kw : ℝ} (hK : ∀ d, |((w d : ℤ) : ℝ)| ≤ Kw) (rv : D → D) (a b : D) :
    (((|w a - w a - 0| + |w (rv a) + w a + 0| + |w b| + |w (rv b)| : ℤ)) : ℝ) ≤ 4 * Kw := by
  have h1 := hK (rv a)
  have h2 := hK a
  have h3 := hK b
  have h4 := hK (rv b)
  have h5 := abs_add_le ((w (rv a) : ℤ) : ℝ) ((w a : ℤ) : ℝ)
  push_cast
  simp only [sub_self, zero_sub, neg_zero, abs_zero, add_zero, zero_add]
  linarith

lemma pot_one_le (Fo : Forest) (n v : ℕ) (z : ℤ) {K : ℝ} (hz : |((z : ℤ) : ℝ)| ≤ K) :
    DynTree.pot n (runOpsE n Fo [.add v z]).1 ≤ DynTree.pot n Fo + n * K := by
  have h := pot_runOpsE_le n [.add v z] Fo
  simp only [amtSum_cons, amtSum_nil, EOp.amt, add_zero, Int.cast_abs] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma pot_aug_le (Fo : Forest) (n v : ℕ) (z : ℤ) {K : ℝ} (hz : |((z : ℤ) : ℝ)| ≤ K) :
    DynTree.pot n (runOpsE n Fo [.add v z, .add2 v (-z)]).1 ≤ DynTree.pot n Fo + n * (2 * K) := by
  have h := pot_runOpsE_le n [.add v z, .add2 v (-z)] Fo
  simp only [amtSum_cons, amtSum_nil, EOp.amt, add_zero, Int.cast_add, Int.cast_abs, abs_neg]
    at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

variable (M : CombMap D V F) (c ε : D → ℤ) (s t : V) (st₀ : LSt M) (N : ℤ) {nD : ℕ}
  (σ : D ≃ Fin nD) (n : ℕ) (ιF : F → ℕ) (ιG : D → ℕ) (ιV : V → ℕ) (ιE : D → ℕ) (B : ℕ)
  (Fo₀ : Forest) (c₀ : Config) (Wd : ℕ)

/-- **The invariant of the loop with the potential**: `PInv`, and the potential of the forest
after `i` steps at most `P0 + i Δ`. -/
def PInvC (P0 Δ : ℝ) (x : PG) (hs : List EOp) (G : List VT) (cf : Config) : Prop :=
  PInv M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd x hs G cf ∧
    DynTree.pot n (runOpsE n Fo₀ hs).1 ≤ P0 + x.i * Δ

section Body

variable {M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd}

variable {P : Input}

/-- **One iteration of the loop**: one step of the perturbed run on the machine. -/
theorem pBody_orunC (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hPO : PertOK M c ε s t d₀)
    (hI₀ : LInv c ε s t st₀) (hroot : st₀.T.root = M.face d₀)
    (hμ₀ : |M.div st₀.h s| ≤ lexR F ε) (hN : 2 * lexR F ε < N)
    (hL : Layout M.dual n ιF ιG ιV ιE) (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    {H : ℕ} {Kw P0 Δ Vb : ℝ} (hKw : ∀ d, |((wlen N c ε d : ℤ) : ℝ)| ≤ Kw)
    (hΔ : 2 * (n : ℝ) * (kZ D F N c ε : ℝ) + n + 4 * Kw ≤ Δ)
    (hVb : P0 + ((Fintype.card D : ℝ) + 2) * Δ ≤ Vb) (hH : 2 * Vb ≤ H)
    (hTh : |((kTh D F N c ε : ℤ) : ℝ)| ≤ Vb) (hH1 : 1 ≤ H)
    (x : PG) (hs : List EOp) (G : List VT) (cf : Config)
    (hIC : PInvC M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd P0 Δ x hs G cf)
    (ht : cf.nreg 102 < cf.nreg 103) :
    ∃ x' c' os G' j h, ORunC P Wd H B n (pBodyS B nD) cf (runOpsE n Fo₀ hs).1 G c' os G' j h ∧
      PInvC M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd P0 Δ x' (hs ++ os) G' c' ∧
      x'.ops = x.ops + j ∧ 1 ≤ j ∧ h + 2 ≤ opCostE n ∧ PG.μ D x' < PG.μ D x := by
  classical
  have hI := hIC.1
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
  -- the potential
  have hpot0 : DynTree.pot n Fo ≤ P0 + x.i * Δ := hIC.2
  have hiD : (x.i : ℝ) ≤ Fintype.card D := by exact_mod_cast hile
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpotN := DynTree.pot_nonneg n Fo
  have hμ := ltraj_mu hM hst hI₀ hε0 hμ₀ x.i
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  set e := lbott c ε s t st.g st.h st.T hne with he_def
  have he : st.T.chi s t e = 1 := lbott_mem c ε s t st.g st.h st.T hne
  obtain ⟨hz0, hzb⟩ := lkey_path_bound hM hst hIst hε0 hc hμ hN he
  set z := lkey N c ε st.g st.h e with hz
  have hzZ : z ≤ kZ D F N c ε := hzb
  have hZ0 : 0 ≤ kZ D F N c ε := hz0.trans hzZ
  have hZ0R : (0 : ℝ) ≤ kZ D F N c ε := by exact_mod_cast hZ0
  have hKw0 : 0 ≤ Kw := (abs_nonneg _).trans (hKw e)
  have hnZ : (0 : ℝ) ≤ n * kZ D F N c ε := mul_nonneg hnR hZ0R
  have hΔ0 : 0 ≤ Δ := by linarith only [hΔ, hnZ, hnR, hKw0]
  have hiΔ : (x.i : ℝ) * Δ ≤ Fintype.card D * Δ := mul_le_mul_of_nonneg_right hiD hΔ0
  have hstepV : P0 + x.i * Δ + Δ ≤ Vb := by linarith only [hiΔ, hVb, hΔ0]
  have hzR : |((z : ℤ) : ℝ)| ≤ kZ D F N c ε := by
    rw [abs_of_nonneg (by exact_mod_cast hz0)]; exact_mod_cast hzZ
  have hzR' : |((-z : ℤ) : ℝ)| ≤ kZ D F N c ε := by rw [Int.cast_neg, abs_neg]; exact hzR
  have hV₀ : VBnd Vb n Fo := vbnd_of_pot (by linarith only [hpot0, hstepV, hΔ0])
  have hpa := pot_aug_le Fo n (ιV t) z hzR
  have hV₄ : VBnd Vb n (runOpsE n Fo [.add (ιV t) z]).1 := vbnd_of_pot (by
    have h := pot_one_le Fo n (ιV t) z hzR
    linarith only [h, hpot0, hstepV, hΔ, hnZ, hnR, hKw0])
  have hV₅ : VBnd Vb n (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 :=
    vbnd_of_pot (by linarith only [hpa, hpot0, hstepV, hΔ, hnZ, hnR, hKw0])
  have hV₆ : ∀ u, VBnd Vb n (runOpsE n (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1
      [.add u 1]).1 := fun u => vbnd_of_pot (by
    have h := pot_one_le (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 n u 1
      (by norm_num : |((1 : ℤ) : ℝ)| ≤ 1)
    linarith only [h, hpa, hpot0, hstepV, hΔ, hnZ, hnR, hKw0])
  have hz100 : |(pathMin2 Fo n (ιV t)).1 - cf.rreg 100| ≤ H := by
    rw [hI.q100]
    have h1 := (pathMin_bound hV₀ (hL.dual.f_lt t)).2
    have h2 := abs_sub (pathMin2 Fo n (ιV t)).1 ((kTh D F N c ε : ℤ) : ℝ)
    linarith
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
  obtain ⟨c₁, G₁, o₁, a196, a195, -, -, m₁, f₁⟩ := regMin2_orunC (P := P) hWW hI.wb hI.lcte
    hV₀ hH (ra := 100) (rz := 100) hI.r100 (hL.dual.f_lt t) hz100
  obtain ⟨c₂, G₂, o₂, s114, s110, lf₂, sm₂⟩ := stSel_orunC (σ := σ) hWW hWa hP hL hK o₁.1.2.wb
    o₁.1.2.lcte (b := e) (by rw [a196, h196]) hpar hfb hV₀ hH
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
    have hc₂ := o₂.1.2.wb
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
  have o₃ : ORunC P Wd H B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORunC.glue e₃ o₂.1.2.lcte
    (fun a _ _ => by rw [hnm₃, hrm₃]; exact ⟨rfl, rfl⟩) (hn₃ 151 (by omega) (by omega) (by omega))
    rfl
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
  obtain ⟨c₄, G₄, o₄, m₄, f₄⟩ := regAdd_orunC (P := P) hWW o₃.1.2.wb o₃.1.2.lcte hV₀ hH (ra := 100)
    (rz := 101) (z := z) (by rw [(k₃ 100 (by omega)).1, hI.r100]) q101 (hL.dual.f_lt t)
  obtain ⟨c₅, G₅, o₅, m₅, f₅⟩ := regAdd2_orunC (P := P) hWW o₄.1.2.wb o₄.1.2.lcte hV₄ hH (ra := 100)
    (rz := 102) (z := -z) (by rw [f₄.1 100 (by omega), (k₃ 100 (by omega)).1, hI.r100])
    (by rw [f₄.2.1 102 (by omega), q102]) (hL.dual.f_lt t)
  set Fa := (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 with hFa
  have hSa := aug_stored hM hL hI.st t z
  have hanc := anc_test hL hSa (M.face e) (M.face (M.rev e))
  -- the test of the stop
  obtain ⟨c₆, G₆, o₆, m₆, f₆⟩ := regAdd_orunC (P := P) hWW o₅.1.2.wb o₅.1.2.lcte hV₅ hH (ra := 106)
    (rz := 103) (z := 1) (by rw [f₅.1 106 (by omega), f₄.1 106 (by omega), g106])
    (by rw [f₅.2.1 103 (by omega), f₄.2.1 103 (by omega), q103]) (hL.prim.f_lt _)
  obtain ⟨c₇, G₇, o₇, a7, m₇, f₇⟩ := regVal_orunC (P := P) hWW o₆.1.2.wb o₆.1.2.lcte (hV₆ _) hH false
    (ra := 105) (by rw [f₆.1 105 (by omega), f₅.1 105 (by omega), f₄.1 105 (by omega), g105])
    (hL.prim.f_lt _)
  have e₈ := Exec.copyR (P := P) o₇.1.2.wb 106 195
  set c₈ := { c₇ with rreg := upd c₇.rreg 106 (c₇.rreg 195) } with hc₈
  have g₈ : GFr 106 107 c₇ c₈ := by rw [hc₈]; gfr_tac
  have o₈ := ORunC.ofGFr (H := H) e₈ o₇.1.2.lcte g₈ (by omega) rfl
  obtain ⟨c₉, G₉, o₉, m₉, f₉⟩ := regAdd_orunC (P := P) hWW o₈.1.2.wb o₈.1.2.lcte (hV₆ _) hH (ra := 106)
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
      G₉ c₉ := o₉.1.2.lcte
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
    have e₁₀ := Exec.constN (P := P) o₉.1.2.wb 102 1 (by omega)
    set c₁₀ := { c₉ with nreg := upd c₉.nreg 102 1 } with hc₁₀
    have g₁₀ : GFr 102 103 c₉ c₁₀ := by rw [hc₁₀]; gfr_tac
    have o₁₀ := ORunC.ofGFr (H := H) e₁₀ hl₉ g₁₀ (by omega) rfl
    have oB := ORunC.ifLtR_true (a := 105) (b := 106)
      (e := .seq (.instr (.constR 110 0)) (pivCoreS B nD))
      (by rw [hz₉, hv₉, ite_eq_left hA]; norm_num; exact_mod_cast hH1)
      (by rw [hz₉, hv₉, ite_eq_left hA]; norm_num) o₁₀
    have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq
      (ORunC.seq' o₉ hF₉ oB))))))))
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
      refine ⟨⟨?_, o.1.2.wb, ?_, fun j hj => hpiv j ?_, fun _ => ⟨by dsimp only; omega, ?_, ?_⟩,
        hlo', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [runOpsE_fst_append]; exact o.1.2.lcte
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
      · rw [hFend]
        show DynTree.pot n Fa ≤ P0 + ((x.i + 1 : ℕ) : ℝ) * Δ
        push_cast
        linarith only [hpa, hpot0, hΔ, hnR, hKw0]
    · have : opCostE n ≥ 42220 := by unfold opCostE; omega
      omega
    · simp [PG.μ, hdone]; omega
  · -- the pivot
    have hstep := lstep_piv (c := c) (ε := ε) hne hA
    have hy : M.face (M.rev e) ≠ st.T.root := st.T.ne_root_of_not_anc hA
    obtain ⟨-, -, hoff, -⟩ := st.T.chi_spec hM s t
    have hbT : ¬ st.T.InT e := fun h => by rw [hoff e h] at he; exact absurd he (by norm_num)
    have e₁₀ := Exec.constR (P := P) o₉.1.2.wb 110 0
    set c₁₀ := { c₉ with rreg := upd c₉.rreg 110 ((0 : ℤ) : ℝ) } with hc₁₀
    have g₁₀ : GFr 110 111 c₉ c₁₀ := by rw [hc₁₀]; gfr_tac
    have o₁₀ := ORunC.ofGFr (H := H) e₁₀ hl₉ g₁₀ (by omega) rfl
    have p₁₀ : P100 cf c₁₀ := p₉.trans (GFr.p100 g₁₀ (by omega))
    have mf₁₀ : MemFrame B n (DynTree.mem cf) (DynTree.mem c₁₀) := mf₉.trans B n g₁₀.memFrame
    have hpotP := pot_four hKw (M.dual.rev) ((toDD st.T).par (M.dual.head e)) e
    obtain ⟨c₁₁, G₁₁, osP, o₁₁, -, -, -, hSt', hKM', lf₁₁, rm₁₁, nm₁₁, hpivP⟩ :=
      stPivCore_orunC (σ := σ) (S := ∅) (ℓ := 0) hWW hWa hB hP hM.dual hL hK o₁₀.1.2.wb o₁₀.1.2.lcte
        hSa (hI.kmem.congr mf₁₀ hB hL)
        (by rw [show c₁₀.nreg 101 = c₉.nreg 101 from rfl, n₉ 101 (by omega)]; exact hI.r101)
        (b := e) (cv := 0) (by rw [show c₁₀.nreg 114 = c₉.nreg 114 from rfl, n114])
        (by rw [hc₁₀]; config_simp) hy hA hbT rfl (Vb := Vb)
        (by show DynTree.pot n Fa + _ ≤ Vb
            linarith only [hpotP, hpa, hpot0, hΔ, hnR, hKw0, hstepV]) hH
    have hpivP' : DynTree.pot n (runOpsE n Fa osP).1 ≤ DynTree.pot n Fa + _ := hpivP
    have oB := ORunC.ifLtR_false (a := 105) (b := 106) (t := .instr (.constN 102 1))
      (by rw [hz₉, hv₉, ite_eq_right hA]; norm_num)
      (by rw [hz₉, hv₉, ite_eq_right hA]; norm_num) (o₁₀.seq o₁₁)
    have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq
      (ORunC.seq' o₉ hF₉ oB))))))))
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
      refine ⟨⟨?_, o.1.2.wb, ?_, fun j hj => ?_, fun h => absurd h Bool.false_ne_true, hlo', ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [runOpsE_fst_append]; exact o.1.2.lcte
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
      · rw [hFend]
        show DynTree.pot n (runOpsE n Fa osP).1 ≤ P0 + ((x.i + 1 : ℕ) : ℝ) * Δ
        push_cast
        linarith only [hpivP', hpotP, hpa, hpot0, hΔ, hnR, hKw0]
    · have : opCostE n ≥ 42220 := by unfold opCostE; omega
      omega
    · simp [PG.μ, hdone]; omega

/-- **The loop of the steps on the machine**: from a state of the invariant (not stopped), the
loop runs until a step stops; it performs operations `os`, counted twice the operations of its
iterations (at most `33` per step) and `2` further steps. At the end the run has stopped after
`i ≤ m + 1` steps, and `lrun (fuel F)` from the initial state is the state after `i` steps. -/
theorem pLoop_orunC (hWW : B + 16 * (n + 1) ≤ Wd) (hWa : 8 * nD + n ≤ Wd)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ Wd) (hM : M.IsPlane)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hPO : PertOK M c ε s t d₀)
    (hI₀ : LInv c ε s t st₀) (hroot : st₀.T.root = M.face d₀)
    (hμ₀ : |M.div st₀.h s| ≤ lexR F ε) (hN : 2 * lexR F ε < N)
    (hL : Layout M.dual n ιF ιG ιV ιE) (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    {H : ℕ} {Kw P0 Δ Vb : ℝ} (hKw : ∀ d, |((wlen N c ε d : ℤ) : ℝ)| ≤ Kw)
    (hΔ : 2 * (n : ℝ) * (kZ D F N c ε : ℝ) + n + 4 * Kw ≤ Δ)
    (hVb : P0 + ((Fintype.card D : ℝ) + 2) * Δ ≤ Vb) (hH : 2 * Vb ≤ H)
    (hTh : |((kTh D F N c ε : ℤ) : ℝ)| ≤ Vb) (hH1 : 1 ≤ H)
    {x : PG} {hs : List EOp} {G : List VT} {cf : Config}
    (hI : PInvC M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd P0 Δ x hs G cf)
    (hv : ValidOpsE n Fo₀ hs) :
    ∃ x' os c' G', ORunC P Wd H B n (pLoopS B nD) cf (runOpsE n Fo₀ hs).1 G c' os G'
        (2 * (x'.ops - x.ops)) 2 ∧
      PInvC M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd P0 Δ x' (hs ++ os) G' c' ∧
      x'.done = true ∧ x.ops ≤ x'.ops ∧ x'.i ≤ Fintype.card D + 1 ∧
      lrun M c ε s t (fuel F) st₀ =
        (ltraj M c ε s t st₀ x'.i, x'.i, true) := by
  obtain ⟨x', os, c', G', o, hI', ht', hcnt⟩ := ORunC.whileLtN_abs (P := P) (W := Wd) (H := H) (B := B)
    (n := n) (a := 102) (b := 103) (body := pBodyS B nD) Fo₀
    (PInvC M c ε s t st₀ N σ n ιF ιG ιV ιE B Fo₀ c₀ Wd P0 Δ) PG.ops (PG.μ D)
    (fun x hs G c h _ => ⟨h.1.lcte, h.1.wb⟩)
    (fun x hs G c h _ ht => by
      obtain ⟨x', c', os, G', j, h', o, hI', hops, hj, hh, hμ⟩ := pBody_orunC hWW hWa hB hP hM
        hc hst hPO hI₀ hroot hμ₀ hN hL hK hKw hΔ hVb hH hTh hH1 x hs G c h ht
      exact ⟨x', c', os, G', j, h', o, hI', hops, hj, hh, hμ⟩) hI hv
  have hdone : x'.done = true := by
    by_contra h
    rw [hI'.1.r102, hI'.1.r103, ite_eq_right h] at ht'
    exact ht' (by norm_num)
  obtain ⟨h1, h2, -⟩ := hI'.1.fin hdone
  have hpiv : ∀ j < x'.i - 1,
      (lstep M c ε s t (ltraj M c ε s t st₀ j)).2 = false :=
    fun j hj => hI'.1.piv j (Or.inl (by omega))
  have hle := piv_le_card hPO hI₀ hroot hpiv
  have hlt := piv_lt_fuel (c := c) (ε := ε) hM hst hpiv
  have hrun := lrun_of_stop (x'.i - 1) st₀ hpiv h2 (fuel F) hlt
  rw [Nat.sub_add_cancel h1] at hrun
  exact ⟨x', os, c', G', o, hI', hdone, hcnt, by omega, hrun⟩


end Body

end STFlow

end PlanarFlow
