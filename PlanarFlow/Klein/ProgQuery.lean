module

public import PlanarFlow.Klein.ProgMove

/-!
# Klein's algorithm on the machine: the distances at the start of a move

**The targets in the input** (`KTgt`): after the four lengths `HD` (at `9 nD + 7 n + k + 4`,
`iXT`), the array `XN` of `t` words, the nodes `ιv (X i)` of the target vertices
`X 0, …, X (t-1)`, then the array `XR` of `t` words, their reach bits (`1` when `X i` is reached
from the roots, `0` otherwise; the targets are not roots, so by `SameReach` these do not depend on
the root).

* `qLoopS`: for `i = r104 < r105 = t`: the node `ιv (X i)` (`XN`), the query (`regQueryS`: the
  path sum into the real `r196`), stored into the real memory at `r106`; the reach bit (`XR`)
  stored into the natural memory at `r109`; then `r104`, `r106`, `r109` advanced.
* `qry_orun`: **the `t` answers of a move** as an `ORun` performing no operation, counted `t`
  operations and `14 t + 2` further steps: the real memory at `base + i` holds the path sum of
  the node of `X i`, the natural memory at `rbase + i` its reach bit; at the start of a move the
  path sums are the distances from its source at the vertices reached (`stored_label`, from
  `lct_label` and `MoveSpec.labels`).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-- The offset of the array `GB` (the boundary darts). -/
def iGB (nD n : ℕ) : ℕ := 8 * nD + n

/-- The offset of the array `XN` (the nodes of the targets), after the four lengths `HD`; the
reach bits `XR` follow at `iXT + t`. -/
def iXT (nD n k : ℕ) : ℕ := 9 * nD + 7 * n + k + 4

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The boundary darts in the input.** -/
def KBnd (k : ℕ) (g : ℕ → D) {nD : ℕ} (σ : D ≃ Fin nD) (n : ℕ) (P : Input) : Prop :=
  ∀ i < k, P.data.getD (iGB nD n + i) 0 = σ (g i)

open Classical in
/-- **The targets in the input**: the `t` vertices `X i`, none of them a root, by their nodes
(`XN`), and their reach bits from the first root (`XR`). -/
structure KTgt (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) (nD n : ℕ)
    (ιv : V → ℕ) (t : ℕ) (X : ℕ → V) (P : Input) : Prop where
  nr : ∀ i < t, ¬ IsRoot M k g (X i)
  xn : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i)
  xr : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 =
    if Reach (pieceGraph M S ℓ) (M.tail (g 0)) (X i) then 1 else 0

/-- The body of the query loop. -/
def qBodyS (B nD n k t : ℕ) : Stmt :=
  .seq (block [.constN 107 (iXT nD n k), .addN 107 107 104, .readIn 108 107]) <|
  .seq (regQueryS B 108) (block [.storeR 106 196, .constN 107 (iXT nD n k + t),
    .addN 107 107 104, .readIn 107 107, .storeN 109 107, .constN 107 1, .addN 106 106 107,
    .addN 109 109 107, .addN 104 104 107])

/-- **The query loop**: the path sums at the targets into the real memory, their reach bits into
the natural memory. -/
def qLoopS (B nD n k t : ℕ) : Stmt := .whileLtN 104 105 (qBodyS B nD n k t)

variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ}
  {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

section
variable {P : Input} {W B : ℕ}

/-- The invariant of the query loop. -/
structure QInv (B n t base rbase : ℕ) (X : ℕ → V) (xb : ℕ → ℕ) (ιv : V → ℕ) (W : ℕ)
    (F₀ : Forest) (c₀ : Config) (i : ℕ) (hs : List EOp) (G : List VT) (c : Config) : Prop where
  nil : hs = []
  lcte : LCTE B n F₀ G c
  wb : WordsBounded W c
  ile : i ≤ t
  r104 : c.nreg 104 = i
  r105 : c.nreg 105 = t
  r106 : c.nreg 106 = base + i
  r109 : c.nreg 109 = rbase + i
  done : ∀ i' < i, c.rmem (base + i') = pathSum F₀ n (ιv (X i')) ∧ c.nmem (rbase + i') = xb i'
  regs : ∀ r, r < 104 → c.nreg r = c₀.nreg r ∧ c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  nm : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < rbase ∨ rbase + i ≤ a) →
    c.nmem a = c₀.nmem a
  rm : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < base ∨ base + i ≤ a) →
    c.rmem a = c₀.rmem a

theorem qBody_orun (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (hbase : base + t ≤ B) (hrbase : rbase + t ≤ B) {F₀ : Forest} {c₀ : Config} (i : ℕ)
    (G : List VT) (c : Config) (h : QInv B n t base rbase X xb ιv W F₀ c₀ i [] G c)
    (ht : i < t) :
    ∃ c' G', ORun P W B n (qBodyS B nD n k t) c F₀ G c' [] G' 1 12 ∧
      QInv B n t base rbase X xb ιv W F₀ c₀ (i + 1) [] G' c' := by
  obtain ⟨-, hS₁, hc₁, hile, q104, q105, q106, q109, qdone, qregs, qout, qnm, qrm⟩ := h
  have hxi := hX i ht
  have hbi := hXb i ht
  -- the node of `X i`
  obtain ⟨c₂, k₂, e₂, hk₂, p108, g₂⟩ : ∃ c' k', Exec P W (block [.constN 107 (iXT nD n k),
      .addN 107 107 104, .readIn 108 107]) c c' k' ∧ k' = 3 ∧ c'.nreg 108 = ιv (X i) ∧
      GFr 107 109 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; simp only [q104]; omega))
    refine ⟨rfl, by config_simp; simp only [q104, hxi], by gfr_tac⟩
  have o₂ := ORun.ofGFr e₂ hS₁ g₂ (by omega)
  obtain ⟨c₃, G₃, o₃, -, -, -, s196, -, m₃, f₃⟩ := regQuery_orun (P := P) hW e₂.wb_right
    o₂.2.lcte p108 (hL.prim.f_lt _)
  have r106 : c₃.nreg 106 = base + i := by
    rw [f₃.1 106 (by omega), (g₂.1 106 (by omega)).1, q106]
  have r109 : c₃.nreg 109 = rbase + i := by
    rw [f₃.1 109 (by omega), (g₂.1 109 (by omega)).1, q109]
  have r104 : c₃.nreg 104 = i := by
    rw [f₃.1 104 (by omega), (g₂.1 104 (by omega)).1, q104]
  have hc₃ := o₃.2.wb
  obtain ⟨c₄, k₄, e₄, hk₄, t104, t106, t109, tm, tb, tr, tn, tregs, trr, tout⟩ : ∃ c' k',
      Exec P W (block [.storeR 106 196, .constN 107 (iXT nD n k + t), .addN 107 107 104,
        .readIn 107 107, .storeN 109 107, .constN 107 1, .addN 106 106 107, .addN 109 109 107,
        .addN 104 104 107]) c₃ c' k' ∧
      k' = 9 ∧ c'.nreg 104 = i + 1 ∧ c'.nreg 106 = base + i + 1 ∧
      c'.nreg 109 = rbase + i + 1 ∧
      c'.rmem (base + i) = pathSum F₀ n (ιv (X i)) ∧ c'.nmem (rbase + i) = xb i ∧
      (∀ a, a ≠ base + i → c'.rmem a = c₃.rmem a) ∧
      (∀ a, a ≠ rbase + i → c'.nmem a = c₃.nmem a) ∧
      (∀ r, r ≠ 104 → r ≠ 106 → r ≠ 107 → r ≠ 109 → c'.nreg r = c₃.nreg r) ∧
      c'.rreg = c₃.rreg ∧ c'.output = c₃.output := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; simp only [r104, r106, r109]; omega))
    refine ⟨rfl, by config_simp; rw [r104], by config_simp; rw [r106], by config_simp; rw [r109],
      ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl⟩
    · config_simp; rw [r106, upd_same]; exact s196
    · config_simp; rw [r109, upd_same, r104, hbi]
    · config_simp; rw [r106, upd_other _ _ _ ha]
    · config_simp; rw [r109, upd_other _ _ _ ha]
    · simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
        upd_other _ _ _ h4]
  have o₄ : ORun P W B n _ c₃ F₀ G₃ c₄ [] G₃ 0 k₄ := ORun.glue e₄ o₃.2.lcte
    (fun a ha _ => ⟨tn a (by omega), tr a (by omega)⟩)
    (tregs 151 (by omega) (by omega) (by omega) (by omega))
  refine ⟨c₄, G₃, (o₂.seq (o₃.seq o₄)).mono (by omega) (by omega), rfl, o₄.2.lcte, e₄.wb_right,
    by omega, t104, by rw [tregs 105 (by omega) (by omega) (by omega) (by omega),
      f₃.1 105 (by omega), (g₂.1 105 (by omega)).1, q105], by rw [t106]; ring,
    by rw [t109]; ring, fun i' hi' => ?_, fun r hr => ?_, ?_, fun a ha hb => ?_,
    fun a ha hb => ?_⟩
  · rcases Nat.lt_or_ge i' i with h | h
    · have h1 := (m₃ (base + i') (Or.inl (by omega))).2
      have h2 := (m₃ (rbase + i') (Or.inl (by omega))).1
      simp only [DynTree.mem] at h1 h2
      rw [tr (base + i') (by omega), h1, g₂.2.2.1, tn (rbase + i') (by omega), h2, g₂.2.1]
      exact qdone i' h
    · obtain rfl : i' = i := by omega
      exact ⟨tm, tb⟩
  · rw [tregs r (by omega) (by omega) (by omega) (by omega), trr, f₃.1 r (by omega),
      f₃.2.1 r (by omega), (g₂.1 r (by omega)).1, (g₂.1 r (by omega)).2]
    exact qregs r hr
  · rw [tout, f₃.2.2, g₂.2.2.2]; exact qout
  · have h1 := (m₃ a ha).1
    simp only [DynTree.mem] at h1
    rw [tn a (by omega), h1, g₂.2.1]; exact qnm a ha (by omega)
  · have h1 := (m₃ a ha).2
    simp only [DynTree.mem] at h1
    rw [tr a (by omega), h1, g₂.2.2.1]
    exact qrm a ha (by omega)

/-- **The `t` answers of a move**: the path sums at the targets into the real memory at
`base + i`, their reach bits into the natural memory at `rbase + i`. -/
theorem qry_orun (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (hbase : base + t ≤ B) (hrbase : rbase + t ≤ B) {c : Config} (hc : WordsBounded W c)
    {F₀ : Forest} {G : List VT} (hS : LCTE B n F₀ G c) (h104 : c.nreg 104 = 0)
    (h105 : c.nreg 105 = t) (h106 : c.nreg 106 = base) (h109 : c.nreg 109 = rbase) :
    ∃ c' G', ORun P W B n (qLoopS B nD n k t) c F₀ G c' [] G' t (14 * t + 2) ∧
      (∀ i < t, c'.rmem (base + i) = pathSum F₀ n (ιv (X i)) ∧ c'.nmem (rbase + i) = xb i) ∧
      (∀ r, r < 104 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < rbase ∨ rbase + t ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < base ∨ base + t ≤ a) →
        c'.rmem a = c.rmem a) ∧ c'.nreg 104 = t := by
  have hI₀ : QInv B n t base rbase X xb ιv W F₀ c 0 [] G c :=
    ⟨rfl, hS, hc, Nat.zero_le _, h104, h105, by rw [h106]; rfl, by rw [h109]; rfl,
      fun i' hi' => absurd hi' (by omega), fun _ _ => ⟨rfl, rfl⟩, rfl, fun _ _ _ => rfl,
      fun _ _ _ => rfl⟩
  obtain ⟨i, os, c', G', hrun, hI, ht, -, -⟩ := ORun.whileLtN (α := ℕ) (P := P) (W := W)
    (B := B) (n := n) (a := 104) (b := 105) (body := qBodyS B nD n k t) F₀
    (fun i hs G₁ c₁ => QInv B n t base rbase X xb ιv W F₀ c i hs G₁ c₁) (fun i => i)
    (fun i => 14 * (t - i)) (fun i hs G₁ c₁ h _ => by rw [h.nil]; exact ⟨h.lcte, h.wb⟩)
    (fun i hs G₁ c₁ h _ ht => by
      have hnil := h.nil
      subst hnil
      have hik : i < t := by rw [h.r104, h.r105] at ht; exact ht
      obtain ⟨c₂, G₂, o, h'⟩ := qBody_orun hW hWa hP hL hX hXb hbase hrbase i G₁ c₁ h hik
      exact ⟨i + 1, c₂, [], G₂, 1, 12, o, h', by ring, by omega⟩)
    (x := 0) (hs := []) hI₀ trivial
  have hos := hI.nil
  simp only [List.nil_append] at hos
  subst hos
  have hik : i = t := by
    have := hI.ile; rw [hI.r104, hI.r105] at ht; omega
  subst hik
  refine ⟨c', G', hrun.mono (by omega) (by omega), hI.done, hI.regs, hI.out, hI.nm, hI.rm,
    hI.r104⟩

/-- **The labels at the start of a move are the distances**: in a forest storing the data at the
start of a move of a trip, the path sum at the node of a vertex reached from the source is its
distance from the source (`lct_label`, `MoveSpec.labels`). -/
theorem stored_label {k : ℕ} {g : ℕ → D} (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ)
    (hL : Layout M n ιv ιg ιf ιe) {j : ℕ} {Rj : MoveData M S} (h : MoveSpec M k g S ℓ j Rj)
    {fe : F} {Lo : ℝ} {Fo : Forest} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe (tripφ S ℓ) fe Lo Fo (Rj.T 0) val) {x : V}
    (hx : Reach (pieceGraph M S ℓ) (tripSrc M k g j) x) :
    pathSum Fo n (ιv x) = dist (pieceGraph M S ℓ) (tripSrc M k g j) x := by
  rw [lct_label hS.tree hL.prim.f_lt hL.prim.e_lt hL.hv x]
  exact_mod_cast MoveSpec.labels H hR h hx

end

end Klein

end PlanarFlow
