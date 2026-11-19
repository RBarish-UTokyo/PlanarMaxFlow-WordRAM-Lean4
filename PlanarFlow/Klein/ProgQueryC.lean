module

public import PlanarFlow.Klein.ProgQueryMask
public import PlanarFlow.Klein.CmpRun

/-!
# The answers of a move on the machine, with bounded comparisons

`qBody_orunC`, `qry_orunC`, `qMask_orunC`: the proofs of `PlanarFlow/Klein/ProgQuery.lean` and
`PlanarFlow/Klein/ProgQueryMask.lean` replayed as runs whose real comparisons are bounded
(`DynTree.ORunC`), for a forest (unchanged by the queries) with values at most `V`, `2 V ≤ H`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ}
  {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

section
variable {P : Input} {W B H : ℕ}

theorem qBody_orunC (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (hbase : base + t ≤ B) (hrbase : rbase + t ≤ B) {F₀ : Forest} {c₀ : Config} (i : ℕ)
    (G : List VT) (c : Config) (h : QInv B n t base rbase X xb ιv W F₀ c₀ i [] G c)
    (ht : i < t) {V : ℝ} (hV : VBnd V n F₀) (hH : 2 * V ≤ H) :
    ∃ c' G', ORunC P W H B n (qBodyS B nD n k t) c F₀ G c' [] G' 1 12 ∧
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
  have o₂ := ORunC.ofGFr (H := H) e₂ hS₁ g₂ (by omega) (by rfl)
  obtain ⟨c₃, G₃, o₃, -, -, -, s196, -, m₃, f₃⟩ := regQuery_orunC (P := P) hW e₂.wb_right
    o₂.1.2.lcte hV hH p108 (hL.prim.f_lt _)
  have r106 : c₃.nreg 106 = base + i := by
    rw [f₃.1 106 (by omega), (g₂.1 106 (by omega)).1, q106]
  have r109 : c₃.nreg 109 = rbase + i := by
    rw [f₃.1 109 (by omega), (g₂.1 109 (by omega)).1, q109]
  have r104 : c₃.nreg 104 = i := by
    rw [f₃.1 104 (by omega), (g₂.1 104 (by omega)).1, q104]
  have hc₃ := o₃.1.2.wb
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
  have o₄ : ORunC P W H B n _ c₃ F₀ G₃ c₄ [] G₃ 0 k₄ := ORunC.glue (H := H) e₄ o₃.1.2.lcte
    (fun a ha _ => ⟨tn a (by omega), tr a (by omega)⟩)
    (tregs 151 (by omega) (by omega) (by omega) (by omega)) (by rfl)
  refine ⟨c₄, G₃, (o₂.seq (o₃.seq o₄)).mono (by omega) (by omega), rfl, o₄.1.2.lcte, e₄.wb_right,
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

theorem qry_orunC (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (hbase : base + t ≤ B) (hrbase : rbase + t ≤ B) {c : Config} (hc : WordsBounded W c)
    {F₀ : Forest} {G : List VT} (hS : LCTE B n F₀ G c) (h104 : c.nreg 104 = 0)
    (h105 : c.nreg 105 = t) (h106 : c.nreg 106 = base) (h109 : c.nreg 109 = rbase) {V : ℝ}
    (hV : VBnd V n F₀) (hH : 2 * V ≤ H) :
    ∃ c' G', ORunC P W H B n (qLoopS B nD n k t) c F₀ G c' [] G' t (14 * t + 2) ∧
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
  obtain ⟨i, os, c', G', hrun, hI, ht, -, -⟩ := ORunC.whileLtN (α := ℕ) (P := P) (W := W) (H := H)
    (B := B) (n := n) (a := 104) (b := 105) (body := qBodyS B nD n k t) F₀
    (fun i hs G₁ c₁ => QInv B n t base rbase X xb ιv W F₀ c i hs G₁ c₁) (fun i => i)
    (fun i => 14 * (t - i)) (fun i hs G₁ c₁ h _ => by rw [h.nil]; exact ⟨h.lcte, h.wb⟩)
    (fun i hs G₁ c₁ h _ ht => by
      have hnil := h.nil
      subst hnil
      have hik : i < t := by rw [h.r104, h.r105] at ht; exact ht
      obtain ⟨c₂, G₂, o, h'⟩ := qBody_orunC hW hWa hP hL hX hXb hbase hrbase i G₁ c₁ h hik hV hH
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

end

section
variable {P : Input} {W B H : ℕ}

theorem qMask_orunC (hW : B + 16 * (n + 1) ≤ W) {k t : ℕ} (hWa : iXT nD n k + 2 * t ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe) {X : ℕ → V} {xb : ℕ → ℕ}
    (hX : ∀ i < t, P.data.getD (iXT nD n k + i) 0 = ιv (X i))
    (hXb : ∀ i < t, P.data.getD (iXT nD n k + t + i) 0 = xb i) {base rbase : ℕ}
    (b : Bool) (hbase : b = true → base + t ≤ B) (hrbase : b = true → rbase + t ≤ B)
    {c : Config} (hc : WordsBounded W c)
    {F₀ : Forest} {G : List VT} (hS : LCTE B n F₀ G c) {V : ℝ} (hV : VBnd V n F₀)
    (hH : 2 * V ≤ H) (h104 : c.nreg 104 = 0)
    (h105 : c.nreg 105 = t) (h106 : c.nreg 106 = base) (h109 : c.nreg 109 = rbase)
    (h107 : c.nreg 107 = 0) (h108 : c.nreg 108 = if b then 1 else 0) {q : ℕ}
    (h82 : c.nreg 82 = q) (hq : q + 1 ≤ W) :
    ∃ c' G', ORunC P W H B n (qMaskS B nD n k t) c F₀ G c' [] G' (if b then t else 0)
        (14 * (if b then t else 0) + 5) ∧
      (b = true → ∀ i < t,
        c'.rmem (base + i) = pathSum F₀ n (ιv (X i)) ∧ c'.nmem (rbase + i) = xb i) ∧
      c'.nreg 82 = q + (if b then 1 else 0) ∧
      (∀ r, r < 104 → r ≠ 82 → r ≠ 92 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧
      c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (b = true → a < rbase ∨ rbase + t ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (b = true → a < base ∨ base + t ≤ a) →
        c'.rmem a = c.rmem a) := by
  cases b with
  | false =>
    have o : ORunC P W H B n (qMaskS B nD n k t) c F₀ G c [] G 0 (0 + 2) :=
      ORunC.ifLtN_false (by simp [h107, h108]) (ORunC.skip hc hS)
    refine ⟨c, G, o.mono (by simp) (by simp), fun h => absurd h (by simp), by simp [h82],
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | true =>
    obtain ⟨c₁, G₁, o₁, q₁, rg₁, out₁, nm₁, rm₁, -⟩ := qry_orunC (P := P) (k := k) (X := X)
      (xb := xb) hW hWa hP hL hX hXb (hbase rfl) (hrbase rfl) hc hS h104 h105 h106 h109 hV hH
    have hc₁ := o₁.1.2.wb
    have p82 : c₁.nreg 82 = q := by rw [(rg₁ 82 (by omega)).1, h82]
    obtain ⟨c₂, k₂, e₂, hk₂, s82, n₂, r₂, mm₂, rm₂, out₂⟩ : ∃ c' k', Exec P W
        (block [.constN 92 1, .addN 82 82 92]) c₁ c' k' ∧ k' = 2 ∧ c'.nreg 82 = q + 1 ∧
        (∀ r, r ≠ 82 → r ≠ 92 → c'.nreg r = c₁.nreg r) ∧ c'.rreg = c₁.rreg ∧
        c'.nmem = c₁.nmem ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
      exec_block
      · omega
      · config_simp; rw [p82]; omega
      · refine ⟨rfl, by config_simp; rw [p82], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
    have o₂ : ORunC P W H B n _ c₁ _ G₁ c₂ [] G₁ 0 k₂ := ORunC.glue (H := H) e₂ o₁.1.2.lcte
      (fun a _ _ => by rw [mm₂, rm₂]; exact ⟨rfl, rfl⟩) (n₂ 151 (by omega) (by omega)) (by rfl)
    have o := ORunC.ifLtN_true (e := .skip)
      (show c.nreg 107 < c.nreg 108 by simp [h107, h108]) (o₁.seq o₂)
    try simp only [List.nil_append] at o
    refine ⟨c₂, G₁, o.mono (by simp) (by simp; omega), fun _ i hi => ?_, by simp [s82],
      fun r hr h1 h2 => ?_, by rw [out₂, out₁], fun a ha hb => ?_, fun a ha hb => ?_⟩
    · rw [mm₂, rm₂]; exact q₁ i hi
    · rw [n₂ r h1 h2, r₂]; exact rg₁ r hr
    · rw [mm₂]; exact nm₁ a ha (hb rfl)
    · rw [rm₂]; exact rm₁ a ha (hb rfl)

end

end Klein

end PlanarFlow
