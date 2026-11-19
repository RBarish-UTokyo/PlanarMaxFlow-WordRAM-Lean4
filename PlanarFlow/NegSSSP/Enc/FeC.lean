module

public import PlanarFlow.NegSSSP.Enc.FeB3

/-!
# The composed encoder, phase C: the out-lists of the piece and the reach bits

On the map with the sources copied, from the words of phase A:

* `feOs`, **`feOs_exec`**: `osProg` on the tails `NT` and the flags `IS` of the piece in the slot
  writes the out-lists `OB`, `OE`, `OL` at `β + iOB`, `β + iOE`, `β + iOL` (`FeOut`: `OutMem` and
  the bounds the search reads); `FeOut.of`: they survive changes keeping (or clamping to
  `Bd ≥ N`) those words; `FeOut.kout`: **`Klein.KOut`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Relation Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

variable (S σ₀ νv₀) in
/-- **The out-lists of the piece in the slot**, with the bounds read by the search. -/
def FeOut (hf : MSSP.FaceCycle M k g) (p : FeP) (m : ℕ → ℕ) : Prop :=
  OutMem (srcMap hf) (srcPiece k S) (srcNum σ₀) (fun y => (srcVNum νv₀ y : ℕ)) m
      (p.β + iOB p.N p.NN p.k) (p.β + iOE p.N p.NN p.k) (p.β + iOL p.N p.NN p.k) ∧
    ∃ mm ≤ p.N, (∀ x < p.A, m (p.β + iOB p.N p.NN p.k + x) ≤ m (p.β + iOE p.N p.NN p.k + x) ∧
        m (p.β + iOE p.N p.NN p.k + x) ≤ mm) ∧
      (∀ e < mm, m (p.β + iOL p.N p.NN p.k + e) < p.N) ∧
      ∑ u ∈ range p.A, (m (p.β + iOE p.N p.NN p.k + u) - m (p.β + iOB p.N p.NN p.k + u)) ≤ mm

/-- **The out-lists survive** a change keeping (or clamping to `Bd ≥ N`) the words of
`[β + iOB, β + iOL + N)`. -/
theorem FeOut.of (hf : MSSP.FaceCycle M k g) {p : FeP} (cA : Fintype.card (SrcV V k) = p.A)
    {m m' : ℕ → ℕ} {Bd : ℕ} (hBd : p.N ≤ Bd) (h : FeOut S σ₀ νv₀ hf p m)
    (hk : ∀ x, p.β + iOB p.N p.NN p.k ≤ x → x < p.β + iOL p.N p.NN p.k + p.N →
      ClampAg m m' Bd x) :
    FeOut S σ₀ νv₀ hf p m' := by
  obtain ⟨hO, mm, hmm, hbe, hol, hdeg⟩ := h
  have hA : p.A ≤ p.NN := by have := p.eqs; omega
  have eB : ∀ x < p.A, m' (p.β + iOB p.N p.NN p.k + x) = m (p.β + iOB p.N p.NN p.k + x) :=
    fun x hx => (hk _ (by omega) (by unfold iOB iOL; omega)).eq rfl
      (by have := hbe x hx; omega)
  have eE : ∀ x < p.A, m' (p.β + iOE p.N p.NN p.k + x) = m (p.β + iOE p.N p.NN p.k + x) :=
    fun x hx => (hk _ (by unfold iOB iOE; omega) (by unfold iOE iOL; omega)).eq rfl
      (by have := hbe x hx; omega)
  have eL : ∀ e < mm, m' (p.β + iOL p.N p.NN p.k + e) = m (p.β + iOL p.N p.NN p.k + e) :=
    fun e he => (hk _ (by unfold iOB iOL; omega) (by omega)).eq rfl
      (by have := hol e he; omega)
  refine ⟨fun x => ?_, mm, hmm, fun x hx => by rw [eB x hx, eE x hx]; exact hbe x hx,
    fun e he => by rw [eL e he]; exact hol e he, ?_⟩
  · have hx : (srcVNum νv₀ x : ℕ) < p.A := by rw [← cA]; exact (srcVNum νv₀ x).2
    obtain ⟨ds, hnd, hmem, hl, hle, hds⟩ := hO x
    simp only at hl hle hds
    refine ⟨ds, hnd, hmem, ?_, ?_, fun i hi => ?_⟩
    · simp only; rw [eB _ hx, eE _ hx]; exact hl
    · simp only; rw [eE _ hx]; exact hle
    · simp only
      have h1 := (hbe _ hx).2
      rw [eB _ hx, eL _ (by omega)]; exact hds i hi
  · rw [Finset.sum_congr rfl fun u hu => by rw [eB u (by simpa using hu), eE u (by simpa using hu)]]
    exact hdeg

/-- **`Klein.KOut` from the out-lists in memory.** -/
theorem FeOut.kout (hf : MSSP.FaceCycle M k g) {p : FeP} (cD : Fintype.card (SrcD D k) = p.N)
    {m : ℕ → ℕ} (h : FeOut S σ₀ νv₀ hf p m) {Pk : Input}
    (hP : ∀ i < iOL p.N p.NN p.k + p.N, Pk.data.getD i 0 = m (p.β + i))
    (hA : p.A ≤ p.NN) (cA : Fintype.card (SrcV V k) = p.A) :
    KOut (srcMap hf) (srcPiece k S) (srcNum σ₀) (fun y => (srcVNum νv₀ y : ℕ)) p.NN p.k Pk := by
  have h1 := h.1
  rw [← cD] at h1 hP
  exact kout_of_outMem (M := srcMap hf) (S := srcPiece k S) (σ := srcNum σ₀)
    (ιv := fun y => (srcVNum νv₀ y : ℕ)) (n := p.NN) (k := p.k) (β := p.β) (mem := m) (P := Pk)
    (fun x => by have := (srcVNum νv₀ x).2; omega) hP h1

/-- The out-lists of `OutMem` as the inputs of the search (`bfsProg_reach`). -/
lemma outMem_snd {nD : ℕ} {σ : SrcD D k ≃ Fin nD} {ν : SrcV V k → ℕ}
    (hf : MSSP.FaceCycle M k g) {S' : Finset (SrcD D k)} {m : ℕ → ℕ} {OBb OEb OLb : ℕ}
    (hO : OutMem (srcMap hf) S' σ ν m OBb OEb OLb) :
    (∀ x i, m (OBb + ν x) ≤ i → i < m (OEb + ν x) →
      ∃ d ∈ S', (srcMap hf).tail d = x ∧ m (OLb + i) = σ d) ∧
    (∀ d ∈ S', ∃ i, m (OBb + ν ((srcMap hf).tail d)) ≤ i ∧ i < m (OEb + ν ((srcMap hf).tail d)) ∧
      m (OLb + i) = σ d) := by
  refine ⟨fun x i h1 h2 => ?_, fun d hd => ?_⟩
  · obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO x
    have hj : i - m (OBb + ν x) < ds.length := by omega
    have e := hds _ hj
    rw [show m (OBb + ν x) + (i - m (OBb + ν x)) = i by omega] at e
    obtain ⟨h3, h4⟩ := (hmem _).1 (List.getElem_mem hj)
    exact ⟨_, h3, h4, e⟩
  · obtain ⟨ds, -, hmem, hl, -, hds⟩ := hO ((srcMap hf).tail d)
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 ((hmem d).2 ⟨hd, rfl⟩)
    refine ⟨m (OBb + ν ((srcMap hf).tail d)) + j, by omega, by omega, ?_⟩
    rw [hds j hj, e]

/-! ### The out-lists on the machine -/

/-- The registers of `osProg` for the out-lists of the piece. -/
def feOsRegs (p : FeP) : List (ℕ × ℕ) :=
  [(1500, p.N), (1501, p.A), (1502, p.β + 4 * p.N), (1504, p.β + 6 * p.N), (1505, p.OS),
    (1506, p.OS + p.A + 1), (1507, p.β + iOB p.N p.NN p.k), (1508, p.β + iOE p.N p.NN p.k),
    (1509, p.β + iOL p.N p.NN p.k)]

/-- **The out-lists of the piece.** -/
def feOs (p : FeP) : Stmt := .seq (feSet (feOsRegs p)) osProg

theorem feOs_natOnly (p : FeP) : natOnly (feOs p) = true := by
  have h : natOnly osProg = true := by kernel_rfl
  simp only [feOs, natOnly, feSet_natOnly, h, Bool.and_self]

set_option maxHeartbeats 2000000 in
/-- **The out-lists of the piece on the machine.** -/
theorem feOs_exec (hf : MSSP.FaceCycle M k g) (p : FeP) (hD : p.nD = Fintype.card D)
    (hk : p.k = k) (hV : p.nV = Fintype.card V) (hF : p.nF = Fintype.card F) (hW : p.END ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hA : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ p.β p.SL p.N p.A p.AE c.nmem) :
    ∃ c' t, Exec P W (feOs p) c c' t ∧ t ≤ 9 + osCost p.N p.A ∧ FeOut S σ₀ νv₀ hf p c'.nmem ∧
      (∀ a, (a < p.OS ∨ p.OS + 2 * p.A + 1 ≤ a) →
        (a < p.β + iOB p.N p.NN p.k ∨ p.β + iOL p.N p.NN p.k + p.N ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, -⟩ := fe_cards p hD hk hV hF
  obtain ⟨l1, l2, l3, l4, l5⟩ : p.β + (8 * p.N + 3 * p.NN + p.k) + p.N ≤ p.SL ∧ p.SL ≤ p.OS ∧
      p.OS + 2 * p.A + 1 ≤ W ∧ p.A ≤ p.NN ∧ p.β + 6 * p.N + p.N ≤ p.β + (8 * p.N + p.NN + p.k) := by
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hW; omega
  have hN1 : 1 ≤ p.N := by rw [← cD]; exact Fintype.card_pos_iff.2 ⟨srcG hf 0⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feOsRegs p) (by
      intro q hq; simp only [feOsRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [iOB, iOE, iOL] <;> clear * - l1 l2 l3 l4 l5 <;> omega) c hc
  have arr := fun d => hA.arrays hf d
  have hT : ∀ d, (fun j => c₁.nmem (p.β + 4 * Fintype.card (SrcD D k) + j)) (srcNum σ₀ d) =
      (srcVNum νv₀ ((srcMap hf).tail d) : ℕ) := fun d => by
    simp only; rw [hm₁]; have := (arr d).2.2.1; rw [← cD] at this; exact this
  have hK : ∀ d, (fun j => c₁.nmem (p.β + 6 * Fintype.card (SrcD D k) + j)) (srcNum σ₀ d) =
      if d ∈ srcPiece k S then 1 else 0 := fun d => by
    simp only; rw [hm₁]; have := (arr d).2.2.2.2.1; rw [← cD] at this; exact this
  have hιv : ∀ x : SrcV V k, (srcVNum νv₀ x : ℕ) < p.A := fun x => by
    rw [← cV]; exact (srcVNum νv₀ x).2
  have hinj : Function.Injective fun x : SrcV V k => (srcVNum νv₀ x : ℕ) :=
    fun a b h => (srcVNum νv₀).injective (Fin.ext h)
  rw [← cD] at l1 l5 hN1
  have hL : OsLay (Fintype.card (SrcD D k)) p.A (p.β + 4 * Fintype.card (SrcD D k))
      (p.β + 6 * Fintype.card (SrcD D k)) p.OS (p.OS + p.A + 1)
      (p.β + iOB (Fintype.card (SrcD D k)) p.NN p.k) (p.β + iOE (Fintype.card (SrcD D k)) p.NN p.k)
      (p.β + iOL (Fintype.card (SrcD D k)) p.NN p.k) W
      (fun j => c₁.nmem (p.β + 4 * Fintype.card (SrcD D k) + j))
      (fun j => c₁.nmem (p.β + 6 * Fintype.card (SrcD D k) + j)) := by
    refine ⟨tlt_of_piece (srcNum σ₀) hιv hT, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals ((try simp only [iOB, iOE, iOL]); clear * - l1 l2 l3 l4 l5 hN1; omega)
  have hI : OsIn (Fintype.card (SrcD D k)) p.A (p.β + 4 * Fintype.card (SrcD D k))
      (p.β + 6 * Fintype.card (SrcD D k)) p.OS (p.OS + p.A + 1)
      (p.β + iOB (Fintype.card (SrcD D k)) p.NN p.k) (p.β + iOE (Fintype.card (SrcD D k)) p.NN p.k)
      (p.β + iOL (Fintype.card (SrcD D k)) p.NN p.k)
      (fun j => c₁.nmem (p.β + 4 * Fintype.card (SrcD D k) + j))
      (fun j => c₁.nmem (p.β + 6 * Fintype.card (SrcD D k) + j)) c₁ :=
    ⟨by rw [hn₁, cD]; simp [feOsRegs, feSetV], by rw [hn₁]; simp [feOsRegs, feSetV],
      by rw [hn₁, cD]; simp [feOsRegs, feSetV], by rw [hn₁, cD]; simp [feOsRegs, feSetV],
      by rw [hn₁]; simp [feOsRegs, feSetV], by rw [hn₁]; simp [feOsRegs, feSetV],
      by rw [hn₁, cD]; simp [feOsRegs, feSetV], by rw [hn₁, cD]; simp [feOsRegs, feSetV],
      by rw [hn₁, cD]; simp [feOsRegs, feSetV], fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hO, ⟨mm, hmm, hbe, hol, hdeg⟩, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    osProg_bfs (P := P) (Mp := srcMap hf) (S := srcPiece k S) (srcNum σ₀) hinj hιv hT hK hL c₁
      e₁.wb_right hI
  have hFO : FeOut S σ₀ νv₀ hf p c₂.nmem := by
    unfold FeOut; rw [← cD]; exact ⟨hO, mm, hmm, hbe, hol, hdeg⟩
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp [feOsRegs] at hk₁; rw [cD] at hk₂; omega,
    hFO, fun a h1 h2 => by rw [← cD] at h2; rw [hm₂ a h1 h2, hm₁],
    by rw [hr₂, hr₁], by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩

end NegSSSP

end PlanarFlow
