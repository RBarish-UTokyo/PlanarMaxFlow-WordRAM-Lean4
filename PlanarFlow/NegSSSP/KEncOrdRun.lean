module

public import PlanarFlow.NegSSSP.KEncOrd

/-!
# The depth orders of the one-face encoding: the whole program

`toProg` (`PlanarFlow/NegSSSP/KEncOrd.lean`) from the parent darts of a rooted tree:

* `toOut_exec`: the outputs `HD`, `IV`, `IT` from the finished search.
* `toProg_exec`: **the whole program**: within `toCost n nD` steps, a queue `q` of the finished
  search (`TQ`) with `IV[i] = i + of`, `IT[i] = PD[q[i + 1]]`, `HD = [n, |q| - 1]`.
* `toProg_orders`: **the orders of a tree** `C` (any `DTree`, the spanning tree on `M.dual` or
  the cotree on `M`), from the parent darts `PD[τ y] = σ (C.par y)` and the faces of the darts
  `A[σ d] = of + τ (M.face d)`: the lists `fs` (all the nodes) and `ys` (all but the root, by
  nondecreasing depth) meet `Klein.Orders C fs ys`, with `IV[i] = of + τ fs[i]`,
  `IT[i] = σ (C.par ys[i])`, `HD = [|fs|, |ys|]` (the fields of `Klein.KInit` for one tree).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {n r : ℕ} {pn kf : ℕ → ℕ}
variable {P : Input} {W : ℕ} {nD Sb PDb Ab IVb ITb HDb of : ℕ}

/-- The two lengths. -/
theorem toOutHD_exec (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 1600 = n)
    (h15 : c.nreg 1615 = HDb) (h20 : c.nreg 1620 = 1) {t : ℕ} (h31 : c.nreg 1631 = t)
    (hw : HDb + 1 ≤ W) :
    ∃ c' k, Exec P W toOutHD c c' k ∧ k = 4 ∧ c'.nmem HDb = n ∧ c'.nmem (HDb + 1) = t - 1 ∧
      (∀ a, a ≠ HDb → a ≠ HDb + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 1622 → r ≠ 1634 → c'.nreg r = c.nreg r) ∧ c'.nreg 1634 = t - 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold toOutHD
  exec_block
  all_goals try ((try config_simp); (try simp only [h15, h20]); omega)
  refine ⟨rfl, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h00, h15, h20, upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h15, h20, h31, upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h15, h20, upd_apply]; split_ifs <;> omega
  · config_simp; simp only [upd_apply, h1, h2, ↓reduceIte]
  · config_simp; simp only [h20, h31]

/-- The nodes in the order of their numbers. -/
theorem toOutIV_exec (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 1600 = n)
    (h04 : c.nreg 1604 = of) (h13 : c.nreg 1613 = IVb) (h20 : c.nreg 1620 = 1)
    (hw : IVb + n ≤ W) (hwo : of + n ≤ W) :
    ∃ c' k, Exec P W toOutIV c c' k ∧ k ≤ 6 * n + 3 ∧
      ((∀ x < n, c'.nmem (IVb + x) = x + of) ∧
        (∀ a, (a < IVb ∨ IVb + n ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1621 ∨ 1623 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold toOutIV
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x < i, d.nmem (IVb + x) = x + of) ∧
      (∀ a, (a < IVb ∨ IVb + i ≤ a) → d.nmem a = c.nmem a) ∧
      (∀ r, r < 1621 ∨ 1623 < r → d.nreg r = c.nreg r) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1621) (bR := 1600)
    (body := block [.addN 1622 1621 1604, .addN 1623 1613 1621, .storeN 1623 1622,
      .addN 1621 1621 1620]) J (K := 4) (n := n) _ ‹_› (by config_simp)
    (by config_simp; exact h00) ⟨fun x hx => absurd hx (by omega), fun _ _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
    (fun i d hi hw' ha hb ⟨g, gm, gn, gr, grm, go⟩ => by
      have e04 : d.nreg 1604 = of := (gn 1604 (by omega)).trans h04
      have e13 : d.nreg 1613 = IVb := (gn 1613 (by omega)).trans h13
      have e20 : d.nreg 1620 = 1 := (gn 1620 (by omega)).trans h20
      exec_block
      all_goals try ((try config_simp); (try simp only [e04, e13, e20, ha]); omega)
      dsimp only [J]
      config_simp
      simp only [e04, e13, e20, ha]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun a h1 => ?_, fun r hr => ?_, gr, grm,
        go⟩
      · simp only [upd_apply]
        split_ifs with h
        · rw [show x = i by omega]
        · exact g x (by omega)
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact gm a (by omega)
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨_, g, gm, gn, gr, grm, go⟩
  exact ⟨by omega, g, gm, gn, gr, grm, go⟩

/-- The parent darts in the order of the queue: `IT[x] := PD[Q[x + 1]]`, `x < m`. -/
theorem toOutIT_exec (c : Config) (hc : WordsBounded W c) {Qb m nP : ℕ} {v : ℕ → ℕ}
    (h02 : c.nreg 1602 = PDb) (h12 : c.nreg 1612 = Qb) (h14 : c.nreg 1614 = ITb)
    (h20 : c.nreg 1620 = 1) (h34 : c.nreg 1634 = m)
    (hq : ∀ x < m, c.nmem (Qb + (x + 1)) = v x) (hv : ∀ x < m, v x < nP)
    (hQd : ITb + m ≤ Qb ∨ Qb + m + 1 ≤ ITb) (hPd : ITb + m ≤ PDb ∨ PDb + nP ≤ ITb)
    (hwQ : Qb + m + 1 ≤ W) (hwP : PDb + nP ≤ W) (hwI : ITb + m ≤ W) :
    ∃ c' k, Exec P W toOutIT c c' k ∧ k ≤ 10 * m + 3 ∧
      ((∀ x < m, c'.nmem (ITb + x) = c.nmem (PDb + v x)) ∧
        (∀ a, (a < ITb ∨ ITb + m ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1621 ∨ 1624 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold toOutIT
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x < i, d.nmem (ITb + x) = c.nmem (PDb + v x)) ∧
      (∀ a, (a < ITb ∨ ITb + i ≤ a) → d.nmem a = c.nmem a) ∧
      (∀ r, r < 1621 ∨ 1624 < r → d.nreg r = c.nreg r) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1621) (bR := 1634)
    (body := block [.addN 1622 1612 1621, .addN 1622 1622 1620, .loadN 1623 1622,
      .addN 1622 1602 1623, .loadN 1624 1622, .addN 1622 1614 1621, .storeN 1622 1624,
      .addN 1621 1621 1620]) J (K := 8) (n := m) _ ‹_› (by config_simp)
    (by config_simp; exact h34) ⟨fun x hx => absurd hx (by omega), fun _ _ => rfl,
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
    (fun i d hi hw' ha hb ⟨g, gm, gn, gr, grm, go⟩ => by
      have e02 : d.nreg 1602 = PDb := (gn 1602 (by omega)).trans h02
      have e12 : d.nreg 1612 = Qb := (gn 1612 (by omega)).trans h12
      have e14 : d.nreg 1614 = ITb := (gn 1614 (by omega)).trans h14
      have e20 : d.nreg 1620 = 1 := (gn 1620 (by omega)).trans h20
      have hvi := hv i hi
      have eq : d.nmem (Qb + i + 1) = v i := by
        rw [gm _ (by omega), Nat.add_assoc]; exact hq i hi
      have ep : d.nmem (PDb + v i) = c.nmem (PDb + v i) := gm _ (by omega)
      exec_block
      all_goals try ((try config_simp); (try simp only [e02, e12, e14, e20, ha, eq]); omega)
      dsimp only [J]
      config_simp
      simp only [e02, e12, e14, e20, ha, eq, ep]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun a h1 => ?_, fun r hr => ?_, gr, grm,
        go⟩
      · simp only [upd_apply]
        split_ifs with h
        · rw [show x = i by omega]
        · exact g x (by omega)
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact gm a (by omega)
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨_, g, gm, gn, gr, grm, go⟩
  exact ⟨by omega, g, gm, gn, gr, grm, go⟩

/-! ### The whole program -/

/-- The cost bound of `toProg`. -/
def toCost (n : ℕ) : ℕ := 111 * n + 54

set_option maxHeartbeats 1000000 in
/-- **The depth orders of a tree on the machine** (natural words only): from the parent darts
`PD[u] < nD` of the `n` nodes and the array `A` (by darts), the parents
`pn u = A[PD[u]] - of` (below `n` off the root `r`), `toProg` ends within `toCost n` steps
with, for a queue `q` of a finished search (`TQ n r pn kf q.length q`, `kf u = [u ≠ r]`),
`HD = [n, |q| - 1]`, `IV[x] = x + of` (`x < n`) and `IT[x] = PD[q[x + 1]]`
(`x + 1 < |q|`); the natural memory changes only in the scratch and the outputs, the natural
registers only in `1500 … 1520`, `1620 … 1634`; the real registers and memory are kept. -/
theorem toProg_exec (hL : ToLay n nD r Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n r Sb PDb Ab IVb ITb HDb of c)
    (hpd : ∀ u < n, c.nmem (PDb + u) < nD)
    (htlt : ∀ u < n, u ≠ r → c.nmem (Ab + c.nmem (PDb + u)) - of < n) :
    ∃ c' t, Exec P W toProg c c' t ∧ t ≤ toCost n ∧
      ∃ q : List ℕ, TQ n r (fun u => c.nmem (Ab + c.nmem (PDb + u)) - of)
          (fun u => (u - r) + (r - u)) q.length q ∧
        c'.nmem HDb = n ∧ c'.nmem (HDb + 1) = q.length - 1 ∧
        (∀ x < n, c'.nmem (IVb + x) = x + of) ∧
        (∀ x, x + 1 < q.length → c'.nmem (ITb + x) = c.nmem (PDb + q.getD (x + 1) 0)) ∧
        (∀ a, (a < Sb ∨ Sb + 8 * n + 1 ≤ a) → (a < IVb ∨ HDb + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1500 ∨ (1520 < r ∧ r < 1620) ∨ 1634 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hL.wS; have := hL.wP; have := hL.wH; have := hL.wo; have := hL.iv; have := hL.it
  have := hL.hO; have := hL.hOP; have := hL.hPD; have := hL.hA; have := hL.pos; have := hL.rlt
  set pn : ℕ → ℕ := fun u => c.nmem (Ab + c.nmem (PDb + u)) - of with hpn
  set kf : ℕ → ℕ := fun u => (u - r) + (r - u) with hkf
  -- 1. the parents and the flags
  obtain ⟨c₁, k₁, e₁, hk₁, P₁, m₁, n₁, r20₁, rr₁, rm₁, o₁⟩ := toPrep_exec (P := P) hL c hc hR hpd
  have hR₁ := hR.frame fun r h1 h2 => n₁ r (by omega)
  -- 2. the children lists
  obtain ⟨c₂, k₂, e₂, hk₂, ch₂, m₂, n₂, rr₂, rm₂, o₂⟩ := toSort_exec (P := P) (pn := pn)
    (kf := kf) hL c₁ e₁.wb_right hR₁ (fun u hu => P₁ u hu) fun u hu hk => htlt u hu (by
      intro e; apply hk; simp only [hkf, e, Nat.sub_self])
  have hR₂ := hR₁.frame fun r h1 h2 => n₂ r (by omega)
  have r20₂ : c₂.nreg 1620 = 1 := by rw [n₂ _ (by omega)]; exact r20₁
  -- 3. the search
  obtain ⟨c₃, k₃, e₃, hk₃, hR₃, r20₃, q, hq, r31₃, Q₃, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    toBfs_exec (P := P) hL c₂ e₂.wb_right hR₂ r20₂ ch₂ (by simp [hkf])
  have hqn := hq.length_le
  have hq0 := hq.pos
  -- 4. the lengths
  obtain ⟨c₄, k₄, e₄, hk₄, H0₄, H1₄, m₄, n₄, r34₄, rr₄, rm₄, o₄⟩ := toOutHD_exec (P := P) c₃
    e₃.wb_right hR₃.r00 hR₃.r15 r20₃ r31₃ (by omega)
  have hR₄ := hR₃.frame fun r h1 h2 => n₄ r (by omega) (by omega)
  have r20₄ : c₄.nreg 1620 = 1 := by rw [n₄ _ (by omega) (by omega)]; exact r20₃
  -- 5. the nodes
  obtain ⟨c₅, k₅, e₅, hk₅, IV₅, m₅, n₅, rr₅, rm₅, o₅⟩ := toOutIV_exec (P := P) c₄ e₄.wb_right
    hR₄.r00 hR₄.r04 hR₄.r13 r20₄ (by omega) (by omega)
  have hR₅ := hR₄.frame fun r h1 h2 => n₅ r (by omega)
  have r20₅ : c₅.nreg 1620 = 1 := by rw [n₅ _ (by omega)]; exact r20₄
  have r34₅ : c₅.nreg 1634 = q.length - 1 := by rw [n₅ _ (by omega)]; exact r34₄
  -- 6. the parent darts
  have hQ₅ : ∀ x < q.length - 1, c₅.nmem (Sb + 7 * n + 1 + (x + 1)) = q.getD (x + 1) 0 :=
    fun x hx => by
      rw [m₅ _ (by omega), m₄ _ (by omega) (by omega)]; exact Q₃ (x + 1) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, IT₆, m₆, n₆, rr₆, rm₆, o₆⟩ := toOutIT_exec (P := P) (PDb := PDb)
    (ITb := ITb) (nP := n) c₅ e₅.wb_right hR₅.r02 hR₅.r12 hR₅.r14 r20₅ r34₅ hQ₅
    (fun x hx => hq.lt _ (getD_mem (by omega))) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))), ?_, q, hq, ?_, ?_,
    fun x hx => ?_, fun x hx => ?_, fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold toCost; unfold osCost at hk₂; omega
  · rw [m₆ _ (by omega), m₅ _ (by omega)]; exact H0₄
  · rw [m₆ _ (by omega), m₅ _ (by omega)]; exact H1₄
  · rw [m₆ _ (by omega)]; exact IV₅ x hx
  · have hv : q.getD (x + 1) 0 < n := hq.lt _ (getD_mem hx)
    rw [IT₆ x (by omega), m₅ _ (by omega), m₄ _ (by omega) (by omega), m₃ _ (by omega),
      m₂ _ (by omega), m₁ _ (by omega)]
  · rw [m₆ _ (by omega), m₅ _ (by omega), m₄ _ (by omega) (by omega), m₃ _ (by omega),
      m₂ _ (by omega), m₁ _ (by omega)]
  · rw [n₆ r (by omega), n₅ r (by omega), n₄ r (by omega) (by omega), n₃ r (by omega),
      n₂ r (by omega), n₁ r (by omega)]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁]

/-! ### The orders of a tree -/

section Tree

open STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
  {M : CombMap D V F}

/-- **The depth orders of a tree on the machine**: for a tree `C` (a `DTree M`: the spanning
tree `T` on `M.dual`, or the cotree on `M`), its nodes numbered by `τ` (the root `τ C.root`)
and the darts by `σ`, from the parent darts `PD[τ y] = σ (C.par y)` (`y` off the root; any
dart number at the root) and the faces of the darts `A[σ d] = of + τ (M.face d)` (the array of
the nodes of the tails, `NT`, for `T`, or of the faces, `NF`, for the cotree, when the layout
numbers the nodes by `of + τ`), `toProg` ends within `toCost n` steps with lists `fs` (all the
nodes, by their numbers) and `ys` (all but the root, by nondecreasing depth) such that
`Klein.Orders C fs ys`, `IV[i] = of + τ fs[i]`, `IT[i] = σ (C.par ys[i])`,
`HD = [|fs|, |ys|]`: the fields `oT`, `iv`, `it`, `l0`, `l1` (or `oC`, `if_`, `ic`, `l2`, `l3`)
of `Klein.KInit` for the layout `of + τ`. -/
theorem toProg_orders (C : DTree M) {nD n : ℕ} (σ : D ≃ Fin nD) (τ : F ≃ Fin n)
    (hL : ToLay n nD (τ C.root) Sb PDb Ab IVb ITb HDb of W) (c : Config)
    (hc : WordsBounded W c) (hR : ToRegs n (τ C.root) Sb PDb Ab IVb ITb HDb of c)
    (hPD : ∀ y, y ≠ C.root → c.nmem (PDb + τ y) = σ (C.par y))
    (hPDr : c.nmem (PDb + τ C.root) < nD)
    (hA : ∀ d, c.nmem (Ab + σ d) = of + τ (M.face d)) :
    ∃ c' t, Exec P W toProg c c' t ∧ t ≤ toCost n ∧
      ∃ ys : List F, Klein.Orders C ((List.finRange n).map τ.symm) ys ∧
        (∀ i (h : i < ((List.finRange n).map τ.symm).length),
          c'.nmem (IVb + i) = of + τ ((List.finRange n).map τ.symm)[i]) ∧
        (∀ i (h : i < ys.length), c'.nmem (ITb + i) = σ (C.par ys[i])) ∧
        c'.nmem HDb = ((List.finRange n).map τ.symm).length ∧ c'.nmem (HDb + 1) = ys.length ∧
        (∀ a, (a < Sb ∨ Sb + 8 * n + 1 ≤ a) → (a < IVb ∨ HDb + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1500 ∨ (1520 < r ∧ r < 1620) ∨ 1634 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpar : ∀ y, y ≠ C.root →
      c.nmem (Ab + c.nmem (PDb + τ y)) - of = τ (C.up y) := fun y hy => by
    rw [hPD y hy, hA, C.up_of_ne hy]; omega
  have hpd : ∀ u < n, c.nmem (PDb + u) < nD := fun u hu => by
    have e : u = τ (τ.symm ⟨u, hu⟩) := by simp
    rw [e]
    by_cases hy : τ.symm ⟨u, hu⟩ = C.root
    · rw [hy]; exact hPDr
    · rw [hPD _ hy]; exact (σ _).2
  have htlt : ∀ u < n, u ≠ τ C.root → c.nmem (Ab + c.nmem (PDb + u)) - of < n := fun u hu hr => by
    have e : u = τ (τ.symm ⟨u, hu⟩) := by simp
    have hy : τ.symm ⟨u, hu⟩ ≠ C.root := fun h => hr (by rw [e, h])
    rw [e, hpar _ hy]; exact (τ _).2
  obtain ⟨c', t, ex, ht, q, hq, H0, H1, IV, IT, hm, hn, hr, hrm, ho⟩ :=
    toProg_exec (P := P) hL c hc hR hpd htlt
  have hT : TreeData C τ (τ C.root) (fun u => c.nmem (Ab + c.nmem (PDb + u)) - of)
      (fun u => (u - τ C.root) + (τ C.root - u)) :=
    ⟨rfl, hpar, fun y => ⟨fun h => τ.injective (Fin.ext (by omega)),
      fun h => by subst h; simp⟩⟩
  have hlen := hq.length_eq hT
  refine ⟨c', t, ex, ht, q.tail.map (tinv τ C.root), hq.orders hT, fun i hi => ?_,
    fun i hi => ?_, by rw [H0]; simp, by rw [H1]; simp, hm, hn, hr, hrm, ho⟩
  · simp only [List.getElem_map, List.getElem_finRange, Equiv.apply_symm_apply]
    rw [IV i (by simpa using hi)]
    (try simp only [Fin.val_cast])
    omega
  · have hi' : i + 1 < q.length := by simp at hi; omega
    have hv : q.getD (i + 1) 0 < n := hq.lt _ (getD_mem hi')
    obtain ⟨a, ha, -⟩ := hq.par
    have hk := (ha (i + 1) (by omega) hi').2.2.1
    simp only [List.getElem_map, List.getElem_tail]
    rw [← List.getD_eq_getElem _ 0 hi', IT i hi']
    set y := tinv τ C.root (q.getD (i + 1) 0) with hy
    have hτ : (τ y : ℕ) = q.getD (i + 1) 0 := tau_tinv τ C.root hv
    have hyr : y ≠ C.root := by
      intro h
      apply hk
      rw [← hτ, h]
      simp
    rw [← hτ, hPD y hyr]

end Tree

end NegSSSP

end PlanarFlow
