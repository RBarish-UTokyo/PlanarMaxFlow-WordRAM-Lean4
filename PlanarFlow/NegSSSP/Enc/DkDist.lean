module

public import PlanarFlow.NegSSSP.Enc.DkRun
public import PlanarFlow.NegSSSP.KEncNatB

/-!
# The distances from the first source by Dijkstra in memory (`O((n + m) log n)`)

**`dkProg_dist`**: the replacement of `bfProg_dist` (Bellman–Ford, `O(#V · #D)`). On a piece
`S` of a map `M` with lengths `ℓ > 0` on `S`, from the **out-lists** of the piece in memory
(`OB[ιv x] ≤ i < OE[ιv x]` lists the darts `d ∈ S` of tail `x` by `OL[i] = σ d`, as
`outMem_snd` gives them for the out-lists written by `osProg`), the heads `NH[σ d] = ιv (head d)`
and the lengths `L[σ d] = (ℓ d).toNat`, `dkProg` writes **`D[ιv x] = (dist G u x).toNat` for
every `x` reached from `u` and `D[ιv x] = Inf` otherwise** (`G = pieceGraph M S ℓ`; the same
postcondition as `bfProg_dist`), within
`17 n + 13 L + 22 + n (23 L + 21) + (13 L + 20) mm` steps (`L = lg (2n)`, `mm` the number of
arcs of the out-lists): **`O((n + mm) log n)`**. Natural words only (`dkProg_natOnly`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {P : Input} {W : ℕ}

/-- The parameters of `dkProg` read from the memory `m`. -/
def dkPOf (n Db Xb OBb OEb OLb NHb Lb Inf s : ℕ) (m : ℕ → ℕ) : DkP :=
  ⟨n, Db, Xb, OBb, OEb, OLb, NHb, Lb, Inf, s, fun y => m (OBb + y), fun y => m (OEb + y),
    fun i => m (OLb + i), fun a => m (NHb + a), fun a => m (Lb + a)⟩

lemma dkPOf_out {n Db Xb OBb OEb OLb NHb Lb Inf s : ℕ} {m : ℕ → ℕ} {a : ℕ} :
    DkOut (dkPOf n Db Xb OBb OEb OLb NHb Lb Inf s m) a ↔
      (Db ≤ a ∧ a < Db + n) ∨ (Xb ≤ a ∧ a < Xb + 3 * n) := Iff.rfl

/-- **The layout of `dkProg`** on the arrays of a piece: `n` nodes, `nD` darts, `mm` arcs in the
out-lists; the read arrays below `W` and apart from the written regions `[Db, Db + n)`,
`[Xb, Xb + 3n)`. -/
structure DkLay (n nD mm Db Xb OBb OEb OLb NHb Lb Inf Lmax W : ℕ) : Prop where
  n_pos : 1 ≤ n
  wD : Db + n ≤ W
  wX : Xb + 3 * n ≤ W
  dDX : Db + n ≤ Xb ∨ Xb + 3 * n ≤ Db
  wI : Inf + Lmax ≤ W
  wOB : OBb + n ≤ W
  wOE : OEb + n ≤ W
  wOL : OLb + mm ≤ W
  wNH : NHb + nD ≤ W
  wL : Lb + nD ≤ W
  dOB : (OBb + n ≤ Db ∨ Db + n ≤ OBb) ∧ (OBb + n ≤ Xb ∨ Xb + 3 * n ≤ OBb)
  dOE : (OEb + n ≤ Db ∨ Db + n ≤ OEb) ∧ (OEb + n ≤ Xb ∨ Xb + 3 * n ≤ OEb)
  dOL : (OLb + mm ≤ Db ∨ Db + n ≤ OLb) ∧ (OLb + mm ≤ Xb ∨ Xb + 3 * n ≤ OLb)
  dNH : (NHb + nD ≤ Db ∨ Db + n ≤ NHb) ∧ (NHb + nD ≤ Xb ∨ Xb + 3 * n ≤ NHb)
  dL : (Lb + nD ≤ Db ∨ Db + n ≤ Lb) ∧ (Lb + nD ≤ Xb ∨ Xb + 3 * n ≤ Lb)

section Math

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

lemma dk_wlen_nonneg (hpos : ∀ d ∈ S, 0 < ℓ d) (l : List {d // d ∈ S}) :
    0 ≤ MSSP.wlen (MSSP.pieceGraph M S ℓ) l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [MSSP.wlen_cons]
    have : (MSSP.pieceGraph M S ℓ).len a = ℓ a.1 := rfl
    have := hpos a.1 a.2
    omega

end Math

section Run

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

set_option maxHeartbeats 1000000 in
/-- **The distances from `u` by Dijkstra in memory** (see the module docstring). -/
theorem dkProg_dist {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {n : ℕ}
    (hιn : ∀ x, ιv x < n) (hsurj : ∀ y < n, ∃ x, ιv x = y) {nD : ℕ} (σ : D ≃ Fin nD)
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
    obtain ⟨x, rfl⟩ := hsurj y hy
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

end NegSSSP

end PlanarFlow
