module

public import PlanarFlow.BKMNW.StBnd
public import PlanarFlow.NegSSSP.Enc.DkDist

/-!
# Dijkstra in memory for a node numbering that is not onto

`NegSSSP.dkProg_dist` asks every node `y < n` to number a vertex (`hsurj`); the numberings of the
frame (`fLab + 1`, orbit labels) are injective but not onto. The hypothesis is used only to know
that the out-list of every node lists darts of the piece; here it is replaced by **empty out-lists
at the nodes numbering no vertex** (what the counting sort `osProg` gives):

* **`dkProg_dist'`**: the conclusion of `dkProg_dist` (distances of the reached vertices, `Inf`
  elsewhere, `O((n + mm) log n)` steps) with `hemp` in place of `hsurj`;
* **`osProg_emp`**: `osProg_bfs` and the emptiness `hemp` of the out-lists at the nodes numbering
  no vertex, so `osProg` then `dkProg` give the distances for any injective node numbering.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {P : Input} {W : ℕ}

section Run

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

set_option maxHeartbeats 1000000 in
/-- **`NegSSSP.dkProg_dist` for a node numbering that need not be onto** `[0, n)`: the nodes
`y < n` that number no vertex have empty out-lists (`OE[y] ≤ OB[y]`). -/
theorem dkProg_dist' {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {n : ℕ}
    (hιn : ∀ x, ιv x < n)  {nD : ℕ} (σ : D ≃ Fin nD)
    {mm Db Xb OBb OEb OLb NHb Lb Inf Lmax : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hLay : DkLay n nD mm Db Xb OBb OEb OLb NHb Lb Inf Lmax W)
    (hRL : Fintype.card V * Lmax < Inf)
    (c : Config) (hc : WordsBounded W c)
    (hOut1 : ∀ x i, c.nmem (OBb + ιv x) ≤ i → i < c.nmem (OEb + ιv x) →
      ∃ d ∈ S, M.tail d = x ∧ c.nmem (OLb + i) = σ d)
    (hOut2 : ∀ d ∈ S, ∃ i, c.nmem (OBb + ιv (M.tail d)) ≤ i ∧
      i < c.nmem (OEb + ιv (M.tail d)) ∧ c.nmem (OLb + i) = σ d)
    (hOBE : ∀ y < n, c.nmem (OBb + y) ≤ c.nmem (OEb + y) ∧ c.nmem (OEb + y) ≤ mm)
    (hdeg : ∑ y ∈ range n, (c.nmem (OEb + y) - c.nmem (OBb + y)) ≤ mm)
    (hemp : ∀ y < n, (∀ x, ιv x ≠ y) → c.nmem (OEb + y) ≤ c.nmem (OBb + y))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (h00 : c.nreg 2500 = n) (h01 : c.nreg 2501 = Db) (h02 : c.nreg 2502 = Xb)
    (h04 : c.nreg 2504 = OBb) (h05 : c.nreg 2505 = OEb) (h06 : c.nreg 2506 = OLb)
    (h07 : c.nreg 2507 = NHb) (h08 : c.nreg 2508 = Lb) (h09 : c.nreg 2509 = Inf)
    (h10 : c.nreg 2510 = ιv u) :
    ∃ c' t, Exec P W dkProg c c' t ∧
      t ≤ 17 * n + 13 * lg (2 * n) + 22 + n * (23 * lg (2 * n) + 21) +
        (13 * lg (2 * n) + 20) * mm ∧
      (∀ x, MSSP.Reach (MSSP.pieceGraph M S ℓ) u x →
        c'.nmem (Db + ιv x) = (MSSP.dist (MSSP.pieceGraph M S ℓ) u x).toNat) ∧
      (∀ x, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x → c'.nmem (Db + ιv x) = Inf) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → (a < Xb ∨ Xb + 3 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2500 ∨ 2548 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  set p := dkPOf n Db Xb OBb OEb OLb NHb Lb Inf (ιv u) c.nmem with hp
  have hn := hLay.n_pos
  have hD1 := hLay.wD
  have hX1 := hLay.wX
  have hdx := hLay.dDX
  have hI1 := hLay.wI
  have hOB := hLay.wOB
  have hOE := hLay.wOE
  have hOL := hLay.wOL
  have hNHw := hLay.wNH
  have hLw := hLay.wL
  have dOB := hLay.dOB
  have dOE := hLay.dOE
  have dOL := hLay.dOL
  have dNH := hLay.dNH
  have dL := hLay.dL
  -- the arcs of a node
  have harc : ∀ y < n, ∀ i, p.ob y ≤ i → i < p.oe y →
      ∃ d ∈ S, ∃ x, ιv x = y ∧ M.tail d = x ∧ p.ol i = σ d := by
    intro y hy i h1 h2
    by_cases hx : ∃ x, ιv x = y
    swap
    · have := hemp y hy (fun x e => hx ⟨x, e⟩)
      have h1' : c.nmem (OBb + y) ≤ i := h1
      have h2' : i < c.nmem (OEb + y) := h2
      omega
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨d, hd, ht, he⟩ := hOut1 x i h1 h2
    exact ⟨d, hd, x, rfl, ht, he⟩
  have hG : DkG p W := by
    refine ⟨hn, hιn u, hD1, hX1, hdx, by show Inf ≤ W; omega, fun y (hy : y < n) => (hOBE y hy).1,
      fun y (hy : y < n) => ⟨by show OBb + y ≤ W; omega, (dkPOf_out (a := OBb + y)).not.2 (by omega)⟩,
      fun y (hy : y < n) => ⟨by show OEb + y ≤ W; omega, (dkPOf_out (a := OEb + y)).not.2 (by omega)⟩,
      fun y (hy : y < n) i h1 h2 => ?_, fun y (hy : y < n) i h1 h2 => ?_,
      fun y (hy : y < n) i h1 h2 => ?_, fun y (hy : y < n) i h1 h2 => ?_,
      fun y (hy : y < n) i h1 h2 => ?_⟩
    · have := (hOBE y hy).2
      have h2' : i < c.nmem (OEb + y) := h2
      exact ⟨by show OLb + i ≤ W; omega, (dkPOf_out (a := OLb + i)).not.2 (by omega)⟩
    · obtain ⟨d, hd, x, -, -, he⟩ := harc y hy i h1 h2
      rw [he]
      have := (σ d).2
      exact ⟨by show NHb + _ ≤ W; omega, (dkPOf_out (a := NHb + σ d)).not.2 (by omega)⟩
    · obtain ⟨d, hd, x, -, -, he⟩ := harc y hy i h1 h2
      rw [he]
      have := (σ d).2
      exact ⟨by show Lb + _ ≤ W; omega, (dkPOf_out (a := Lb + σ d)).not.2 (by omega)⟩
    · obtain ⟨d, hd, x, -, -, he⟩ := harc y hy i h1 h2
      rw [he]
      show c.nmem (NHb + σ d) < n
      rw [hNH d]; exact hιn _
    · obtain ⟨d, hd, x, -, -, he⟩ := harc y hy i h1 h2
      rw [he]
      show Inf + c.nmem (Lb + σ d) ≤ W
      rw [hLv d hd]; have := hL d hd; omega
  have hM : DkMem p c.nmem := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨c', t, e, ht, hD, hfr, hreg, hrr, hrm, ho⟩ :=
    dkProg_exec (P := P) hG c hc hM h00 h01 h02 h04 h05 h06 h07 h08 h09 h10 (mm := mm) hdeg
  -- the walks of `DkReach`
  have hwalk : ∀ y L, DkReach p y L → ∃ x, ιv x = y ∧ ∃ l,
      MSSP.LWalk (MSSP.pieceGraph M S ℓ) u x l ∧ MSSP.wlen (MSSP.pieceGraph M S ℓ) l = L := by
    intro y L hr
    induction hr with
    | src => exact ⟨u, rfl, [], .nil _, by simp⟩
    | @step y' L i _ hy h1 h2 ih =>
      obtain ⟨x, rfl, l, hl, hw⟩ := ih
      obtain ⟨d, hd, hdt, he⟩ := hOut1 x i h1 h2
      have hl' : MSSP.LWalk (MSSP.pieceGraph M S ℓ) u (M.head d) (l ++ [⟨d, hd⟩]) :=
        hl.concat (show (MSSP.pieceGraph M S ℓ).src ⟨d, hd⟩ = x from hdt)
      refine ⟨M.head d, ?_, l ++ [⟨d, hd⟩], hl', ?_⟩
      · show ιv (M.head d) = c.nmem (NHb + c.nmem (OLb + i))
        rw [he, hNH]
      · show _ = ((L + c.nmem (Lb + c.nmem (OLb + i)) : ℕ) : ℤ)
        rw [he, hLv d hd, MSSP.wlen_append, hw]
        simp only [MSSP.wlen_cons, MSSP.wlen_nil, add_zero]
        have : (MSSP.pieceGraph M S ℓ).len ⟨d, hd⟩ = ℓ d := rfl
        rw [this]
        have := Int.toNat_of_nonneg (hpos d hd).le
        push_cast; omega
  -- every walk gives a `DkReach`
  have hreach : ∀ y x l, MSSP.LWalk (MSSP.pieceGraph M S ℓ) y x l → ∀ L, DkReach p (ιv y) L →
      DkReach p (ιv x) (L + (MSSP.wlen (MSSP.pieceGraph M S ℓ) l).toNat) := by
    intro y x l hl
    induction hl with
    | nil x => intro L h; simpa using h
    | @cons a z l _ ih =>
      intro L h
      obtain ⟨i, h1, h2, he⟩ := hOut2 a.1 a.2
      have hs := DkReach.step (p := p) (u := ιv (M.tail a.1)) (i := i) h (hιn _) h1 h2
      have e1 : p.nh (p.ol i) = ιv (M.head a.1) := by
        show c.nmem (NHb + c.nmem (OLb + i)) = _
        rw [he, hNH]
      have e2 : p.ln (p.ol i) = (ℓ a.1).toNat := by
        show c.nmem (Lb + c.nmem (OLb + i)) = _
        rw [he, hLv a.1 a.2]
      rw [e1, e2] at hs
      have := ih _ hs
      have hw := dk_wlen_nonneg (M := M) hpos l
      have ha := hpos a.1 a.2
      rw [MSSP.wlen_cons]
      have e3 : (MSSP.pieceGraph M S ℓ).len a = ℓ a.1 := rfl
      rw [e3]
      have e4 : (ℓ a.1 + MSSP.wlen (MSSP.pieceGraph M S ℓ) l).toNat =
          (ℓ a.1).toNat + (MSSP.wlen (MSSP.pieceGraph M S ℓ) l).toNat := by omega
      rw [e4, ← Nat.add_assoc]
      exact this
  -- the invariant of Bellman–Ford, for all walks
  have hBF : BFInv M S ℓ u ιv Db Inf (Fintype.card V) c'.nmem := by
    refine ⟨fun x hx => ?_, fun x l hl _ => ?_, fun x => (hD _ (hιn x)).1⟩
    · obtain ⟨x', hx', l, hl, hw⟩ := hwalk _ _ ((hD _ (hιn x)).2.1 hx)
      rw [hinj hx'] at hl
      exact ⟨l, hl, hw⟩
    · have : c'.nmem (Db + ιv x) ≤ 0 + (MSSP.wlen (MSSP.pieceGraph M S ℓ) l).toNat :=
        (hD _ (hιn x)).2.2 _ (hreach u x l hl 0 DkReach.src)
      have hw := dk_wlen_nonneg (M := M) hpos l
      omega
  obtain ⟨hd₁, hd₂⟩ := bfInv_dist hpos hL le_rfl hRL hBF
  refine ⟨c', t, e, ht, hd₁, hd₂, fun a h1 h2 => hfr a (dkPOf_out.not.2 (by omega)),
    hreg, hrr, hrm, ho⟩

end Run


section Out

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {N Tb Kb Ob Cb OBb OEb Db : ℕ} {T K : ℕ → ℕ}

/-- **The out-lists of `osProg` are empty at the nodes numbering no vertex**, besides
`osProg_bfs`: the hypotheses of `dkProg_dist'` on the out-lists. -/
theorem osProg_emp {Mp : CombMap D V F} {S : Finset D} {nD : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < N) (hT : ∀ d, T (σ d) = ιv (Mp.tail d))
    (hK : ∀ d, K (σ d) = if d ∈ S then 1 else 0)
    (hL : OsLay nD N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn nD N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost nD N ∧ OutMem Mp S σ ιv c'.nmem OBb OEb Db ∧
      (∃ mm ≤ nD, (∀ x < N, c'.nmem (OBb + x) ≤ c'.nmem (OEb + x) ∧ c'.nmem (OEb + x) ≤ mm) ∧
        (∀ e < mm, c'.nmem (Db + e) < nD) ∧
        ∑ u ∈ range N, (c'.nmem (OEb + u) - c'.nmem (OBb + u)) ≤ mm) ∧
      (∀ y < N, (∀ x, ιv x ≠ y) → c'.nmem (OEb + y) ≤ c'.nmem (OBb + y)) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + nD ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hOB, -, -, -, -, -, -⟩ := osProg_exec (P := P) hL c hc hI
  obtain ⟨c'', k', ex', hk', hO, hmm, hm, hn, hr, hrm, ho⟩ :=
    osProg_bfs (P := P) (Mp := Mp) (S := S) σ hinj hιv hT hK hL c hc hI
  obtain ⟨rfl, rfl⟩ := Exec.det ex ex'
  refine ⟨c', k, ex, hk, hO, hmm, fun y hy hne => ?_, hm, hn, hr, hrm, ho⟩
  rw [(hOB y hy).1, (hOB y hy).2, NegSSSP.length_pre_succ]
  have hb : (Monge.FR.blk (csList T id K (fun _ => 0) nD) y).map (fun a => a.2.1) = [] := by
    rw [blk_map_csList, List.filter_eq_nil_iff]
    intro i hi
    have hi' : i < nD := List.mem_range.1 hi
    have := hT (σ.symm ⟨i, hi'⟩)
    rw [Equiv.apply_symm_apply] at this
    simp only [decide_eq_true_eq, not_and]
    intro _ e
    exact hne _ (this ▸ e)
  have := congrArg List.length hb
  simp only [List.length_map, List.length_nil] at this
  omega

end Out

end NegSSSP

end PlanarFlow
