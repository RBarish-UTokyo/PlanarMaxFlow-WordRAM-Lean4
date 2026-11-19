module

public import PlanarFlow.NegSSSP.Enc.EncUtil
public import PlanarFlow.NegSSSP.KEncNatB

/-!
# The parent array of the initial tree `T` on the machine (Bellman–Ford, `O(#V · #D)`)

`tree_compat` (`SrcTree.lean`) combines a search tree `C₀` of the vertices rooted at `u` with
the shortest-path tree of `u` and the dart `e` into `v` (`parT`). Here the combination is
computed **in place** in the parent array of `C₀` (as `vtSearch_exec` writes it):

* `tpProg_keep`: the tight-dart pass `tpProg` keeps the parent word of every vertex **not
  reached** from `u` (no tight dart enters it).
* `ptProg`: the registers of `bfProg` and `tpProg` set, **`spTreeProg` (Bellman–Ford, then the
  tight-dart pass)**, then `PA[ιv v] := σ e`. Natural words only (`ptProg_natOnly`).
* `ptProg_parT`: from `PA[ιv y] = σ (C₀.par y)` (`y ≠ u`), within
  `R (24 nD + 6) + 5 n + 29 nD + 17 + 20` steps (**`O(#V · #D)` by Bellman–Ford**, `R ≥ #V`
  rounds), `PA[ιv y] = σ (parT M S ℓ C₀ u v e y)` for every `y ≠ u` (via `parT_mem`).
* `ptProg_tree`: in the setting `MSSP.Hyp M k g S ℓ` (`u = tripSrc 0`, `v = tripDst 0`,
  `e = g (0 % k)`): **a tree `T : DTree M.dual` meeting `Klein.Compat`** (the last field of
  `Klein.KValNL`) with `PA[ιv y] = σ (T.par y)` for `y ≠ u` (the hypothesis `hPD` of
  `toProg_orders`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

/-- **The tight-dart pass keeps the parent words of the unreached vertices.** -/
theorem tpProg_keep {nD n Sb NTb NHb Lb Rb Db Pb : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιn : ∀ x, ιv x < n) (u : V)
    (hL : TPLay nD n Sb NTb NHb Lb Rb Db Pb W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 2300 = nD) (h01 : c.nreg 2301 = Sb) (h02 : c.nreg 2302 = NTb)
    (h03 : c.nreg 2303 = NHb) (h04 : c.nreg 2304 = Lb) (h05 : c.nreg 2305 = Rb)
    (h06 : c.nreg 2306 = Db) (h07 : c.nreg 2307 = Pb)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hrb : ∀ x, 0 < c.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x)
    {c' : Config} {t : ℕ} (ex : Exec P W tpProg c c' t) :
    ∀ y, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u y → c'.nmem (Pb + ιv y) = c.nmem (Pb + ιv y) := by
  have hσs : ∀ j < nD, ∃ d, (σ d : ℕ) = j := fun j hj => ⟨σ.symm ⟨j, hj⟩, by simp⟩
  have hNT' : ∀ j < nD, c.nmem (NTb + j) < n := fun j hj => by
    obtain ⟨d, rfl⟩ := hσs j hj; rw [hNT]; exact hιn _
  have hNH' : ∀ j < nD, c.nmem (NHb + j) < n := fun j hj => by
    obtain ⟨d, rfl⟩ := hσs j hj; rw [hNH]; exact hιn _
  obtain ⟨c₂, t₂, ex₂, -, hP, -⟩ :=
    tpProg_exec (P := P) hL c hc h00 h01 h02 h03 h04 h05 h06 h07 hNT' hNH'
  obtain ⟨rfl, -⟩ := ex.det ex₂
  intro y hy
  rw [hP _ (hιn y)]
  refine tpW_of_none fun j hj ht => ?_
  obtain ⟨d, rfl⟩ := hσs j hj
  obtain ⟨h1, h2, -⟩ := ht
  simp only [hNT, hNH] at h1 h2 ⊢
  have hd := (hfl d).1 h1
  have hr := (hrb _).1 h2
  have hr' : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.head d) :=
    MSSP.Reach.arc (G := MSSP.pieceGraph M S ℓ) (a := ⟨d, hd⟩) hr
  intro e
  exact hy (hinj e ▸ hr')

/-- **The parent array of `T`**: the registers of `bfProg` (`2400 … 2409`) and `tpProg`
(`2300 … 2307`), Bellman–Ford and the tight-dart pass, then `PA[pv] := pe`. -/
def ptProg (nD Sb NTb NHb Lb Db Rb Pb n R Inf u₀ pv pe : ℕ) : Stmt :=
  .seq (feSet [(2400, nD), (2401, Sb), (2402, NTb), (2403, NHb), (2404, Lb), (2405, Db),
      (2406, n), (2407, R), (2408, Inf), (2409, u₀), (2300, nD), (2301, Sb), (2302, NTb),
      (2303, NHb), (2304, Lb), (2305, Rb), (2306, Db), (2307, Pb)])
    (.seq spTreeProg (feStore pv pe))

theorem ptProg_natOnly (nD Sb NTb NHb Lb Db Rb Pb n R Inf u₀ pv pe : ℕ) :
    Klein.natOnly (ptProg nD Sb NTb NHb Lb Db Rb Pb n R Inf u₀ pv pe) = true := by
  simp only [ptProg, Klein.natOnly, feSet_natOnly, spTreeProg_natOnly, feStore_natOnly,
    Bool.and_self]

set_option maxHeartbeats 1000000 in
/-- **The parent array of the combined tree on the machine** (see the module docstring). -/
theorem ptProg_parT {u v : V} {e : D} (C₀ : STFlow.DTree M.dual) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) {n : ℕ} (hιn : ∀ x, ιv x < n) {nD : ℕ} (σ : D ≃ Fin nD)
    {Sb NTb NHb Lb Db Rb Pb Inf Lmax R : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hU : MSSP.UniqTight (MSSP.pieceGraph M S ℓ))
    (hLay : BFLay nD n Sb NTb NHb Lb Db Inf Lmax W)
    (hTP : TPLay nD n Sb NTb NHb Lb Rb Db Pb W) (hRb : Rb + n ≤ Db ∨ Db + n ≤ Rb)
    (hR : Fintype.card V ≤ R) (hRL : R * Lmax < Inf) (hRW : R ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (hrb : ∀ x, 0 < c.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x)
    (hPA : ∀ y, y ≠ u → c.nmem (Pb + ιv y) = σ (C₀.par y)) :
    ∃ c' t, Exec P W (ptProg nD Sb NTb NHb Lb Db Rb Pb n R Inf (ιv u) (Pb + ιv v) (σ e)) c c' t ∧
      t ≤ R * (24 * nD + 6) + 5 * n + 29 * nD + 17 + 21 ∧
      (∀ y, y ≠ u → c'.nmem (Pb + ιv y) = σ (parT M S ℓ C₀ u v e y)) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → (a < Pb ∨ Pb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.wD; have := hLay.wS; have := hLay.wT; have := hLay.wH; have := hLay.wL
  have := hLay.wI; have := hTP.wR; have := hTP.wP; have := hTP.dD; have := hTP.dR
  have hu := hιn u; have hv := hιn v; have he := (σ e).2
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) [(2400, nD), (2401, Sb), (2402, NTb), (2403, NHb), (2404, Lb), (2405, Db),
      (2406, n), (2407, R), (2408, Inf), (2409, ιv u), (2300, nD), (2301, Sb), (2302, NTb),
      (2303, NHb), (2304, Lb), (2305, Rb), (2306, Db), (2307, Pb)]
      (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega) c hc
  have hIn : BFIn M S ℓ σ ιv Sb NTb NHb Lb c₁ := ⟨fun d => by rw [hm₁]; exact hfl d,
    fun d => by rw [hm₁]; exact hNT d, fun d => by rw [hm₁]; exact hNH d,
    fun d hd => by rw [hm₁]; exact hLv d hd⟩
  have hrb₁ : ∀ x, 0 < c₁.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x := fun x => by
    rw [hm₁]; exact hrb x
  obtain ⟨c₂, k₂, e₂, hk₂, hP₂, hm₂, hr₂, hrm₂, ho₂⟩ :=
    spTreeProg_tpar (P := P) hinj hιn σ hpos hL hU hLay hTP hRb hR hRL hRW c₁ e₁.wb_right hIn hrb₁
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
      (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
  -- the unreached vertices keep the parent words of `C₀`
  have hkeep : ∀ y, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u y →
      c₂.nmem (Pb + ιv y) = c.nmem (Pb + ιv y) := by
    unfold spTreeProg at e₂
    obtain ⟨cb, kb, kt, eb, ht⟩ : ∃ cb kb kt, Exec P W bfProg c₁ cb kb ∧ Exec P W tpProg cb c₂ kt := by
      cases e₂ with
      | seq h1 h2 => exact ⟨_, _, _, h1, h2⟩
    obtain ⟨cb', kb', eb', -, -, -, hmb, hnb, -⟩ :=
      bfProg_dist (P := P) hinj hιn σ hpos hL hLay hR hRL hRW c₁ e₁.wb_right hIn
        (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
        (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
        (by rw [hn₁]; rfl) (by rw [hn₁]; rfl)
    obtain ⟨rfl, -⟩ := eb.det eb'
    have gb : ∀ r, 2300 ≤ r → r ≤ 2307 → cb.nreg r = c₁.nreg r := fun r h1 h2 =>
      hnb r (by omega)
    have hIb := hIn.frame hLay hmb
    intro y hy
    rw [tpProg_keep (P := P) σ hinj hιn u hTP cb eb.wb_right
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      ((gb _ (by omega) (by omega)).trans (by rw [hn₁]; rfl))
      hIb.fl hIb.nt hIb.nh
      (fun x => by rw [hmb _ (by have := hιn x; omega)]; exact hrb₁ x) ht y hy,
      hmb _ (by have := hιn y; omega), hm₁]
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, -, hr₃, hrm₃, ho₃⟩ :=
    feStore_exec (P := P) (a := Pb + ιv v) (v := σ e) (by omega) (by omega) c₂ e₂.wb_right
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), by simp at hk₁; omega,
    fun y hy => ?_, fun a h1 h2 => ?_, by rw [hr₃, hr₂, hr₁], by rw [hrm₃, hrm₂, hrm₁],
    by rw [ho₃, ho₂, ho₁]⟩
  · refine parT_mem (C₀ := C₀) (u := u) (v := v) (e := e) σ ιv (mem := c₃.nmem) (PAb := Pb)
      (fun x a ha hxv => ?_) (fun y hy hyv hnone => ?_) ?_ y hy
    · rw [hm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hxv (hinj (by omega)))]
      exact hP₂ x a ha
    · rw [hm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hyv (hinj (by omega)))]
      have hnr : ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u y := fun hr => by
        obtain ⟨a, ha⟩ := Klein.tpar_isSome hnn hr hy
        rw [ha] at hnone; exact absurd hnone (by simp)
      rw [hkeep y hnr]; exact hPA y hy
    · rw [hm₃, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [hm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by have := hιn v; omega)), hm₂ a h1 h2, hm₁]

/-- **The initial tree of Klein's encoding from the parent array**: in the setting of Klein's
algorithm (`MSSP.Hyp`), the array of `ptProg_parT` is that of a tree `T : DTree M.dual` meeting
`Klein.Compat` (the last field of `Klein.KValNL`). -/
theorem ptProg_tree {k : ℕ} {g : ℕ → D} (H : MSSP.Hyp M k g S ℓ) (C₀ : STFlow.DTree M.dual)
    (hC₀ : C₀.root = Klein.tripSrc M k g 0) {nD : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    {mem : ℕ → ℕ} {Pb : ℕ}
    (hPA : ∀ y, y ≠ Klein.tripSrc M k g 0 → mem (Pb + ιv y) =
      σ (parT M S ℓ C₀ (Klein.tripSrc M k g 0) (Klein.tripDst M k g 0) (g (0 % k)) y)) :
    ∃ T : STFlow.DTree M.dual,
      Klein.Compat T (Klein.tripSrc M k g 0) (Klein.tripDst M k g 0) (g (0 % k))
        (Klein.tpar (MSSP.pieceGraph M S ℓ) (Klein.tripSrc M k g 0)) ∧
      T.root = Klein.tripSrc M k g 0 ∧
      ∀ y, y ≠ T.root → mem (Pb + ιv y) = σ (T.par y) := by
  obtain ⟨T, hT, hpar⟩ := tree_compat_hyp H C₀ hC₀
  refine ⟨T, hT, hT.root, fun y hy => ?_⟩
  rw [hT.root] at hy
  rw [hPA y hy, hpar y hy]

end NegSSSP

end PlanarFlow
