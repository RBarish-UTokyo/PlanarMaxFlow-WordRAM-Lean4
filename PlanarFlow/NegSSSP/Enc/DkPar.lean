module

public import PlanarFlow.NegSSSP.Enc.DkDist
public import PlanarFlow.NegSSSP.Enc.ParT

/-!
# The parent array of the initial tree `T`, the distances by Dijkstra

`dkpProg`: the registers of `dkProg` and `tpProg` (`feSet`), **Dijkstra in memory** (`dkProg`,
`O((n + mm) log n)`) instead of Bellman–Ford, the tight-dart pass (`tpProg`), then
`PA[pv] := pe`. **`dkpProg_parT`**: the conclusion of `ptProg_parT` (`PA[ιv y] = σ (parT …)` for
`y ≠ u`) from the out-lists of the piece in memory, within `dkpCost nD n mm` steps; memory
changed only in `[Db, Db + n) ∪ [Xb, Xb + 3n) ∪ [Pb, Pb + n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

variable {P : Input} {W : ℕ}

/-- **The parent array of `T` with Dijkstra.** -/
def dkpProg (nD Sb NTb NHb Lb Db Xb OBb OEb OLb Rb Pb n Inf u₀ pv pe : ℕ) : Stmt :=
  .seq (feSet [(2500, n), (2501, Db), (2502, Xb), (2504, OBb), (2505, OEb), (2506, OLb),
      (2507, NHb), (2508, Lb), (2509, Inf), (2510, u₀), (2300, nD), (2301, Sb), (2302, NTb),
      (2303, NHb), (2304, Lb), (2305, Rb), (2306, Db), (2307, Pb)])
    (.seq (.seq dkProg tpProg) (feStore pv pe))

theorem dkpProg_natOnly (nD Sb NTb NHb Lb Db Xb OBb OEb OLb Rb Pb n Inf u₀ pv pe : ℕ) :
    Klein.natOnly (dkpProg nD Sb NTb NHb Lb Db Xb OBb OEb OLb Rb Pb n Inf u₀ pv pe) = true := by
  have h : Klein.natOnly tpProg = true := by kernel_rfl
  simp only [dkpProg, Klein.natOnly, feSet_natOnly, dkProg_natOnly, h, feStore_natOnly,
    Bool.and_self]

/-- The cost of `dkpProg` (`n` nodes, `nD` darts, `mm` arcs in the out-lists). -/
def dkpCost (nD n mm : ℕ) : ℕ :=
  18 + ((17 * n + 13 * lg (2 * n) + 22 + n * (23 * lg (2 * n) + 21) +
    (13 * lg (2 * n) + 20) * mm) + (29 * nD + 5)) + 3

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

set_option maxHeartbeats 2000000 in
/-- **The parent array of the combined tree, the distances by Dijkstra.** -/
theorem dkpProg_parT {u v : V} {e : D} (C₀ : STFlow.DTree M.dual) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) {n : ℕ} (hιn : ∀ x, ιv x < n)
    (hsurj : ∀ y < n, ∃ x, ιv x = y) {nD : ℕ} (σ : D ≃ Fin nD)
    {Sb NTb NHb Lb Db Xb OBb OEb OLb Rb Pb Inf Lmax mm : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hU : MSSP.UniqTight (MSSP.pieceGraph M S ℓ))
    (hDk : DkLay n nD mm Db Xb OBb OEb OLb NHb Lb Inf Lmax W)
    (hTP : TPLay nD n Sb NTb NHb Lb Rb Db Pb W)
    (hXd : (Sb + nD ≤ Db ∨ Db + n ≤ Sb) ∧ (NTb + nD ≤ Db ∨ Db + n ≤ NTb) ∧
      (Rb + n ≤ Db ∨ Db + n ≤ Rb) ∧ (Sb + nD ≤ Xb ∨ Xb + 3 * n ≤ Sb) ∧
      (NTb + nD ≤ Xb ∨ Xb + 3 * n ≤ NTb) ∧ (Rb + n ≤ Xb ∨ Xb + 3 * n ≤ Rb) ∧
      (Pb + n ≤ Xb ∨ Xb + 3 * n ≤ Pb))
    (hRL : Fintype.card V * Lmax < Inf)
    (c : Config) (hc : WordsBounded W c)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (hrb : ∀ x, 0 < c.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x)
    (hPA : ∀ y, y ≠ u → c.nmem (Pb + ιv y) = σ (C₀.par y))
    (hOut1 : ∀ x i, c.nmem (OBb + ιv x) ≤ i → i < c.nmem (OEb + ιv x) →
      ∃ d ∈ S, M.tail d = x ∧ c.nmem (OLb + i) = σ d)
    (hOut2 : ∀ d ∈ S, ∃ i, c.nmem (OBb + ιv (M.tail d)) ≤ i ∧
      i < c.nmem (OEb + ιv (M.tail d)) ∧ c.nmem (OLb + i) = σ d)
    (hOBE : ∀ y < n, c.nmem (OBb + y) ≤ c.nmem (OEb + y) ∧ c.nmem (OEb + y) ≤ mm)
    (hdeg : ∑ y ∈ range n, (c.nmem (OEb + y) - c.nmem (OBb + y)) ≤ mm) :
    ∃ c' t, Exec P W (dkpProg nD Sb NTb NHb Lb Db Xb OBb OEb OLb Rb Pb n Inf (ιv u) (Pb + ιv v)
        (σ e)) c c' t ∧ t ≤ dkpCost nD n mm ∧
      (∀ y, y ≠ u → c'.nmem (Pb + ιv y) = σ (parT M S ℓ C₀ u v e y)) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → (a < Xb ∨ Xb + 3 * n ≤ a) → (a < Pb ∨ Pb + n ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := hXd
  have := hDk.wD; have := hDk.wX; have := hDk.wI; have := hDk.wOB; have := hDk.wOE
  have := hDk.wOL; have := hDk.wNH; have := hDk.wL
  have := hTP.wS; have := hTP.wT; have := hTP.wR; have := hTP.wP; have := hTP.dD
  have := hTP.dR
  have hu := hιn u; have hv := hιn v; have he := (σ e).2
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) [(2500, n), (2501, Db), (2502, Xb), (2504, OBb), (2505, OEb),
      (2506, OLb), (2507, NHb), (2508, Lb), (2509, Inf), (2510, ιv u), (2300, nD), (2301, Sb),
      (2302, NTb), (2303, NHb), (2304, Lb), (2305, Rb), (2306, Db), (2307, Pb)]
      (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega) c hc
  -- 1. the distances by Dijkstra
  obtain ⟨c₂, k₂, e₂, hk₂, hD₁, -, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ :=
    dkProg_dist (P := P) (M := M) (S := S) (ℓ := ℓ) (u := u) hinj hιn hsurj σ hpos hL hDk hRL c₁
      e₁.wb_right
      (fun x i h1 h2 => by rw [hm₁] at h1 h2 ⊢; exact hOut1 x i h1 h2)
      (fun d hd => by rw [hm₁]; exact hOut2 d hd)
      (fun y hy => by rw [hm₁]; exact hOBE y hy) (by rw [hm₁]; exact hdeg)
      (fun d => by rw [hm₁]; exact hNH d) (fun d hd => by rw [hm₁]; exact hLv d hd)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
  have hk2 : ∀ a, (a < Db ∨ Db + n ≤ a) → (a < Xb ∨ Xb + 3 * n ≤ a) → c₂.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [hm₂ a h1 h2, hm₁]
  have g : ∀ r, 2300 ≤ r → r ≤ 2307 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    hn₂ r (by omega)
  have hσn : ∀ d, (σ d : ℕ) < nD := fun d => (σ d).2
  have hfl₂ : ∀ d, 0 < c₂.nmem (Sb + σ d) ↔ d ∈ S := fun d => by
    have := hσn d; rw [hk2 _ (by omega) (by omega)]; exact hfl d
  have hNT₂ : ∀ d, c₂.nmem (NTb + σ d) = ιv (M.tail d) := fun d => by
    have := hσn d; rw [hk2 _ (by omega) (by omega)]; exact hNT d
  have hNH₂ : ∀ d, c₂.nmem (NHb + σ d) = ιv (M.head d) := fun d => by
    have := hσn d; have := hDk.dNH; rw [hk2 _ (by omega) (by omega)]; exact hNH d
  have hLv₂ : ∀ d ∈ S, c₂.nmem (Lb + σ d) = (ℓ d).toNat := fun d hd => by
    have := hσn d; have := hDk.dL; rw [hk2 _ (by omega) (by omega)]; exact hLv d hd
  have hrb₂ : ∀ x, 0 < c₂.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x := fun x => by
    have := hιn x; rw [hk2 _ (by omega) (by omega)]; exact hrb x
  -- 2. the tight darts
  obtain ⟨c₃, k₃, e₃, hk₃, hP₃, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    tpProg_tpar (P := P) hpos hU σ hinj hιn u hTP c₂ e₂.wb_right
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      hfl₂ hNT₂ hNH₂ hLv₂ hrb₂ hD₁
  -- the unreached vertices keep the parent words of `C₀`
  have hkeep : ∀ y, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u y →
      c₃.nmem (Pb + ιv y) = c.nmem (Pb + ιv y) := by
    intro y hy
    have := hιn y
    rw [tpProg_keep (P := P) σ hinj hιn u hTP c₂ e₂.wb_right
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((g _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      hfl₂ hNT₂ hNH₂ hrb₂ e₃ y hy, hk2 _ (by omega) (by omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, hm₄, -, hr₄, hrm₄, ho₄⟩ :=
    feStore_exec (P := P) (a := Pb + ιv v) (v := σ e) (by omega) (by omega) c₃ e₃.wb_right
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  refine ⟨c₄, k₁ + ((k₂ + k₃) + k₄), Exec.seq e₁ (Exec.seq (Exec.seq e₂ e₃) e₄), ?_,
    fun y hy => ?_, fun a h1 h2 h3 => ?_, by rw [hr₄, hr₃, hr₂, hr₁],
    by rw [hrm₄, hrm₃, hrm₂, hrm₁], by rw [ho₄, ho₃, ho₂, ho₁]⟩
  · simp at hk₁; unfold dkpCost; omega
  · refine parT_mem (C₀ := C₀) (u := u) (v := v) (e := e) σ ιv (mem := c₄.nmem) (PAb := Pb)
      (fun x a ha hxv => ?_) (fun y hy hyv hnone => ?_) ?_ y hy
    · rw [hm₄, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hxv (hinj (by omega)))]
      exact hP₃ x a ha
    · rw [hm₄, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hyv (hinj (by omega)))]
      have hnr : ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u y := fun hr => by
        obtain ⟨a, ha⟩ := Klein.tpar_isSome hnn hr hy
        rw [ha] at hnone; exact absurd hnone (by simp)
      rw [hkeep y hnr]; exact hPA y hy
    · rw [hm₄, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [hm₄, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm₃ a h3,
      hk2 a h1 h2]

end NegSSSP

end PlanarFlow
