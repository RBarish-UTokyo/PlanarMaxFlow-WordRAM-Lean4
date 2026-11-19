module

public import PlanarFlow.NegSSSP.Enc.FeLay

/-!
# The composed encoder, phase B: a search tree of the vertices, a cotree, the isolating weights

On the map with the sources copied (`M' = srcMap hf`, darts numbered by `σ = srcNum σ₀`, vertices
by `τ = srcVNum νv₀`, faces by `srcFNum τ₀`), from the words of phase A:

* `feB1_exec`: the search of all the vertices from the first root `u = tripSrc 0`
  (`vtSearch_exec`): **a tree `C₀ : DTree M'.dual` rooted at `u`** with its parent array at `PA`;
  then `PA[τ u] := PA[τ v]` (`v = tripDst 0`), so that the array is the list of the parent darts
  of a list `ts` of the non-root vertices (`feTs`), as `cotProg` reads it.
* `feB2_exec`: **a cotree `C₁` of `C₀`**, rooted at the face of `g' 0`, with its order `cs`
  (`cotProg_exec`, outputs at `O1`).
* `feB3_exec`: **the isolating weights `FN + treeW C₁`** at `WW` (`iwProg_treeW`):
  `treeW C₁` is an isolating weight with the exceptional face of `g' 0`, `|treeW C₁| ≤ FN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The list of the non-root nodes of an order has `card - 1` elements. -/
lemma orders_ylen_eq {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
    {N : CombMap D X Y} {C : STFlow.DTree N} {fs ys : List Y} (h : Orders C fs ys) :
    ys.length = Fintype.card Y - 1 := by
  rw [← List.toFinset_card_of_nodup h.ynd]
  have : ys.toFinset = univ.erase C.root := by
    ext y; simp [h.ymem y]
  rw [this, card_erase_of_mem (mem_univ _), card_univ]

/-- `r₁ := nmem[a] - o`, `r₂ := nmem[a] - o`. -/
def feLd2 (r₁ r₂ a o : ℕ) : Stmt :=
  block [.constN 2455 a, .loadN 2456 2455, .constN 2457 o, .subN r₁ 2456 2457,
    .subN r₂ 2456 2457]

theorem feLd2_natOnly (r₁ r₂ a o : ℕ) : natOnly (feLd2 r₁ r₂ a o) = true := by kernel_rfl

theorem feLd2_exec {r₁ r₂ a o : ℕ} (hr : r₁ ≠ r₂) (h1 : r₁ < 2450 ∨ 2459 < r₁)
    (h2 : r₂ < 2450 ∨ 2459 < r₂) (ha : a ≤ W) (ho : o ≤ W) (c : Config)
    (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (feLd2 r₁ r₂ a o) c c' k ∧ k = 5 ∧ c'.nmem = c.nmem ∧
      c'.nreg r₁ = c.nmem a - o ∧ c'.nreg r₂ = c.nmem a - o ∧
      (∀ r, r ≠ r₁ → r ≠ r₂ → (r < 2450 ∨ 2459 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold feLd2
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, rfl, ?_, ?_, fun r hr1 hr2 hr3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- The sizes of the map with the sources copied. -/
lemma fe_cards (p : FeP) (hD : p.nD = Fintype.card D) (hk : p.k = k)
    (hV : p.nV = Fintype.card V) (hF : p.nF = Fintype.card F) :
    Fintype.card (SrcD D k) = p.N ∧ Fintype.card (SrcV V k) = p.A ∧
      Fintype.card (SrcF F k) = p.FN := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_srcD]; simp only [FeP.N]; rw [hD, hk]; ring
  · rw [card_srcV]; simp only [FeP.A]; rw [hV, hk]
  · rw [card_srcF]; simp only [FeP.FN]; rw [hF, hk]

/-- The number of the first root and of the second root, of the boundary dart `g' 0`. -/
lemma fe_roots (hf : MSSP.FaceCycle M k g) :
    (srcVNum (k := k) νv₀ (tripSrc (srcMap hf) k (srcG hf) 0) : ℕ) = Fintype.card V ∧
      (srcVNum (k := k) νv₀ (tripDst (srcMap hf) k (srcG hf) 0) : ℕ) = Fintype.card V + 2 ∧
      (srcNum σ₀ (srcG hf (0 % k)) : ℕ) = Fintype.card D ∧
      (srcNum σ₀ (srcG hf 0) : ℕ) = Fintype.card D := by
  have hk := hf.two_le
  have h0 : (0 : ℕ) % k = 0 := Nat.zero_mod k
  have h1 : (0 + 1) % k = 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tripSrc; rw [h0, srcTail_srcG hf (by omega), srcVNum_inr]; simp
  · unfold tripDst; rw [h1, srcTail_srcG hf (by omega), srcVNum_inr]; simp
  · simp [srcG, srcNum_inr, kindIdx]
  · simp [srcG, srcNum_inr, kindIdx]

/-- The first root and the second root differ. -/
lemma fe_src_ne_dst (hf : MSSP.FaceCycle M k g) :
    tripSrc (srcMap hf) k (srcG hf) 0 ≠ tripDst (srcMap hf) k (srcG hf) 0 := by
  have hk := hf.two_le
  unfold tripSrc tripDst
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (show 0 + 1 < k by omega), srcTail_srcG hf (by omega),
    srcTail_srcG hf (by omega)]
  simp

/-! ### The search tree -/

/-- The registers of the search of the vertices. -/
def feVtRegs (p : FeP) : List (ℕ × ℕ) :=
  [(1500, p.N), (1501, p.A), (1502, p.β + 4 * p.N), (1504, p.ONE), (1505, p.ZV),
    (1506, p.ZV + p.A + 1), (1507, p.ZV + 2 * p.A + 1), (1508, p.ZV + 3 * p.A + 1),
    (1509, p.ZV + 4 * p.A + 1), (1400, p.A), (1401, p.nV), (1402, p.ZV + 2 * p.A + 1),
    (1403, p.ZV + 3 * p.A + 1), (1404, p.ZV + 4 * p.A + 1), (1405, p.β + 5 * p.N),
    (1406, p.ZV + 4 * p.A + 1 + p.N), (1407, p.ZV + 5 * p.A + 1 + p.N),
    (1408, p.ZV + 6 * p.A + 1 + p.N)]

/-- **Phase B1**: the search tree of the vertices, then the root word of its parent array. -/
def feB1Prog (p : FeP) : Stmt :=
  .seq (feSet (feVtRegs p)) (.seq (.seq osProg ctProg) (feCpyCell (p.PA + p.nV) (p.PA + p.nV + 2)))

theorem feB1Prog_natOnly (p : FeP) : natOnly (feB1Prog p) = true := by
  have h1 : natOnly osProg = true := by kernel_rfl
  have h2 : natOnly ctProg = true := by kernel_rfl
  simp only [feB1Prog, natOnly, feSet_natOnly, feCpyCell_natOnly, h1, h2, Bool.and_self]

set_option maxHeartbeats 2000000 in
/-- **Phase B1 on the machine.** -/
theorem feB1_exec (hf : MSSP.FaceCycle M k g) (hM : M.IsPlane) (p : FeP)
    (hD : p.nD = Fintype.card D) (hk : p.k = k) (hV : p.nV = Fintype.card V)
    (hF : p.nF = Fintype.card F) (hW : p.END ≤ W) (c : Config) (hc : WordsBounded W c)
    (hA : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE c.nmem)
    (hone : ∀ j < p.N, c.nmem (p.ONE + j) = 1) :
    ∃ c' t, Exec P W (feB1Prog p) c c' t ∧ t ≤ osCost p.N p.A + 35 * p.A + 19 * p.N + 34 ∧
      (∃ C₀ : STFlow.DTree (srcMap hf).dual, C₀.root = tripSrc (srcMap hf) k (srcG hf) 0 ∧
        (∀ y, y ≠ C₀.root → c'.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (C₀.par y)) ∧
        c'.nmem (p.PA + p.nV) = srcNum σ₀ (C₀.par (tripDst (srcMap hf) k (srcG hf) 0))) ∧
      (∀ a, a < p.ZV ∨ p.ZV + 7 * p.A + p.N + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  haveI : Nonempty (SrcD D k) := ⟨srcG hf 0⟩
  obtain ⟨cD, cV, cF⟩ := fe_cards p hD hk hV hF
  obtain ⟨ru, rv, -, -⟩ := fe_roots (σ₀ := σ₀) (νv₀ := νv₀) hf
  have hne := fe_src_ne_dst hf
  have hE := p.eqs
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ : p.β + 6 * p.N ≤ p.ONE ∧ p.ONE + p.N ≤ p.ZV ∧
      p.ZV + 7 * p.A + p.N + 2 ≤ W ∧ p.PA = p.ZV + 6 * p.A + 1 + p.N ∧ p.nV + 2 < p.A ∧
      p.N ≤ p.ONE ∧ 1 ≤ p.N := by
    have h2k := hf.two_le; have hsl := p.slot_le
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, -⟩ := hE
    obtain ⟨s1, -, -⟩ := hsl
    have hEND : p.ZV + 7 * p.A + p.N + 2 ≤ p.END := by
      have := p.eqs; clear * - this; omega
    refine ⟨by omega, by omega, by omega, e10, by omega, by omega, by omega⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feVtRegs p) (by
      intro q hq; simp only [feVtRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> clear * - l1 l2 l3 l5 l6 <;> omega)
      c hc
  have arr := fun d => (hA.arrays hf d)
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨C₀, hCr, hPA⟩, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    vtSearch_exec (P := P) (srcMap_isPlane hf hM) (srcNum σ₀) (srcVNum νv₀)
      (tripSrc (srcMap hf) k (srcG hf) 0) (Tb := p.β + 4 * p.N) (Kb := p.ONE)
      (HHb := p.β + 5 * p.N) (Z := p.ZV) c₁ e₁.wb_right
      (by rw [hn₁]; simp [feVtRegs, feSetV, cD]) (by rw [hn₁]; simp [feVtRegs, feSetV, cV])
      (by rw [hn₁]; simp [feVtRegs, feSetV]) (by rw [hn₁]; simp [feVtRegs, feSetV])
      (by rw [hn₁]; simp [feVtRegs, feSetV]) (by rw [hn₁]; simp [feVtRegs, feSetV, cV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV]) (by rw [hn₁]; simp [feVtRegs, feSetV, cV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV]) (by rw [hn₁]; simp [feVtRegs, feSetV, ru, hV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV]) (by rw [hn₁]; simp [feVtRegs, feSetV, cV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV]) (by rw [hn₁]; simp [feVtRegs, feSetV])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV, cD]) (by rw [hn₁]; simp [feVtRegs, feSetV, cV, cD])
      (by rw [hn₁]; simp [feVtRegs, feSetV, cV, cD])
      (fun d => by rw [hm₁]; exact (arr d).2.2.1)
      (fun d => by rw [hm₁]; exact hone _ (by have := (srcNum σ₀ d).2; omega))
      (fun d => by rw [hm₁]; exact (arr d).2.2.2.1)
      (by rw [cD]; clear * - l1 l2; omega) (by rw [cD]; clear * - l2; omega)
      (by rw [cD]; clear * - l1 l2; omega) (by rw [cD, cV]; clear * - l3; omega)
  rw [cD, cV] at hm₂
  have ePA : p.ZV + 6 * Fintype.card (SrcV V k) + 1 + Fintype.card (SrcD D k) = p.PA := by
    rw [cD, cV, l4]
  replace hPA : ∀ y, y ≠ C₀.root → c₂.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (C₀.par y) :=
    fun y hy => by rw [← ePA]; exact hPA y hy
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    feCpyCell_exec (P := P) (dst := p.PA + p.nV) (src := p.PA + p.nV + 2)
      (by clear * - l3 l4 l5; omega) (by clear * - l3 l4 l5; omega) c₂ e₂.wb_right
  have hvt : (srcVNum (k := k) νv₀ (tripDst (srcMap hf) k (srcG hf) 0) : ℕ) = p.nV + 2 := by
    rw [rv, hV]
  have hut : (srcVNum (k := k) νv₀ (tripSrc (srcMap hf) k (srcG hf) 0) : ℕ) = p.nV := by
    rw [ru, hV]
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), ?_, ⟨C₀, hCr, fun y hy => ?_, ?_⟩,
    fun a ha => ?_, by rw [hr₃, hr₂, hr₁], by rw [hrm₃, hrm₂, hrm₁], by rw [ho₃, ho₂, ho₁]⟩
  · simp [feVtRegs] at hk₁; rw [cD, cV] at hk₂; clear * - hk₁ hk₂ hk₃; omega
  · have hyu : (srcVNum νv₀ y : ℕ) ≠ p.nV := fun h => hy (by
      rw [hCr]; apply (srcVNum νv₀).injective; ext; rw [h, hut])
    rw [hm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact hPA y hy
  · have hvr : tripDst (srcMap hf) k (srcG hf) 0 ≠ C₀.root := by rw [hCr]; exact hne.symm
    rw [hm₃, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), Nat.add_assoc, ← hvt]
    exact hPA _ hvr
  · rw [hm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by clear * - ha l4 l5; omega)),
      hm₂ a ha, hm₁]

end NegSSSP

end PlanarFlow
