module

public import PlanarFlow.STFlow.ProgLoopC

/-!
# The initialisation of the dynamic trees with bounded comparisons

The compare-bounded versions (`ORunC`) of the realization lemmas of Klein's initialisation
(`PlanarFlow/Klein/ProgInit.lean`), replayed with the same proofs, for operations whose forests
have values at most `Vb` before each operation (`AllV`), `2 Vb ≤ H`: `stListLoop_orunC`
(`listLoop_orun`), the bodies, `stInT_orunC`, `stInC_orunC`, `stInV_orunC`, and
`stIn_orunC` (`in_orun`, with the operations `treeOpsL ++ cotOpsL` named).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap MSSP DynTree Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD}

section
variable {P : Input} {W B n : ℕ}

theorem stListLoop_orunC {α : Type*} {body : Stmt} {ra rb : ℕ} (xs : List α)
    (opsOf : α → List EOp) {F₀ : Forest} (hv : ValidOpsE n F₀ (xs.flatMap opsOf))
    {H : ℕ} {Vb : ℝ} (hAV : AllV Vb n F₀ (xs.flatMap opsOf))
    (Q : ℕ → Config → Prop) {mb hb : ℕ}
    (hbody : ∀ i (hi : i < xs.length) (c : Config) (G : List VT), Q i c → WordsBounded W c →
      LCTE B n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 G c → c.nreg ra = i →
      c.nreg rb = xs.length →
      ValidOpsE n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) →
      AllV Vb n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) →
      ∃ c' G', ORunC P W H B n body c (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 G c'
        (opsOf xs[i]) G' mb hb ∧ Q (i + 1) c' ∧ c'.nreg ra = i + 1 ∧ c'.nreg rb = xs.length)
    {c : Config} (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₀ G c) (hQ : Q 0 c)
    (h0 : c.nreg ra = 0) (hlen : c.nreg rb = xs.length) :
    ∃ c' G', ORunC P W H B n (.whileLtN ra rb body) c F₀ G c' (xs.flatMap opsOf) G'
        (mb * xs.length) ((hb + 2) * xs.length + 2) ∧ Q xs.length c' := by
  have hvi : ∀ i (hi : i < xs.length),
      ValidOpsE n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) := by
    intro i hi
    have e : xs.flatMap opsOf = ((xs.take i).flatMap opsOf ++ opsOf xs[i]) ++
        (xs.drop (i + 1)).flatMap opsOf := by
      rw [← flatMap_take_succ xs opsOf hi, ← List.flatMap_append, List.take_append_drop]
    rw [e] at hv
    exact ((validOpsE_append_iff n _ _ _).1 ((validOpsE_append_iff n _ _ _).1 hv).1).2
  have hai : ∀ i (hi : i < xs.length),
      AllV Vb n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) := by
    intro i hi
    have e : xs.flatMap opsOf = ((xs.take i).flatMap opsOf ++ opsOf xs[i]) ++
        (xs.drop (i + 1)).flatMap opsOf := by
      rw [← flatMap_take_succ xs opsOf hi, ← List.flatMap_append, List.take_append_drop]
    rw [e] at hAV
    exact AllV.right (AllV.left hAV)
  obtain ⟨i, os, c', G', hrun, ⟨hos, hile, hS', hc', hra, hrb, hQ'⟩, ht, -, -⟩ :=
    ORunC.whileLtN (α := ℕ) (P := P) (W := W) (H := H) (B := B) (n := n) (a := ra) (b := rb)
    (body := body) F₀
    (fun i hs G₁ c₁ => hs = (xs.take i).flatMap opsOf ∧ i ≤ xs.length ∧
      LCTE B n (runOpsE n F₀ hs).1 G₁ c₁ ∧ WordsBounded W c₁ ∧ c₁.nreg ra = i ∧
      c₁.nreg rb = xs.length ∧ Q i c₁) (fun i => mb * i) (fun i => (hb + 2) * (xs.length - i))
    (fun i hs G₁ c₁ h _ => ⟨h.2.2.1, h.2.2.2.1⟩)
    (fun i hs G₁ c₁ h _ ht => by
      obtain ⟨rfl, hile, hS₁, hc₁, hra, hrb, hQ₁⟩ := h
      have hi : i < xs.length := by rw [hra, hrb] at ht; exact ht
      obtain ⟨c₂, G₂, o, hQ₂, hra₂, hrb₂⟩ := hbody i hi c₁ G₁ hQ₁ hc₁ hS₁ hra hrb (hvi i hi) (hai i hi)
      refine ⟨i + 1, c₂, opsOf xs[i], G₂, mb, hb, o, ⟨(flatMap_take_succ xs opsOf hi).symm,
        hi, ?_, o.1.2.wb, hra₂, hrb₂, hQ₂⟩, by ring, ?_⟩
      · rw [runOpsE_fst_append]
        exact o.1.2.lcte
      · have : xs.length - i = xs.length - (i + 1) + 1 := by omega
        rw [this]; ring_nf; omega)
    (x := 0) (hs := []) ⟨by simp, Nat.zero_le _, hS, hc, h0, hlen, hQ⟩ trivial
  have hik : i = xs.length := by rw [hra, hrb] at ht; omega
  subst hik
  rw [List.take_length] at hos
  simp only [List.nil_append] at hos
  subst hos
  refine ⟨c', G', hrun.mono (by omega) (by simp), hQ'⟩


theorem stBodyNV_orunC (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W) {α : Type*}
    {off rz : ℕ} {xs : List α} {ιN : α → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = ιN xs[i])
    (hoff : off + xs.length ≤ W) {z : ℤ} {i : ℕ} (hi : i < xs.length) {c : Config}
    (hc : WordsBounded W c) {F : Forest} {G : List VT} (hS : LCTE B n F G c)
    (h120 : c.nreg 120 = i) (hz : c.rreg rz = z) (hrz : rz < 120)
    (hv : ValidOpsE n F [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z]) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n F [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z]) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (bodyNV B off rz) c F G c' [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z]
        G' 2 5 ∧ c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, p122, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122]) c c' k' ∧ k' = 3 ∧ c'.nreg 122 = ιN xs[i] ∧
      GFr 122 123 c c' := by
    exec_block
    · omega
    · config_simp; rw [h120]; omega
    · exact hP _
    · refine ⟨rfl, by config_simp; rw [h120, hxs i hi], by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hz₁ : c₁.rreg rz = z := by rw [(g₁.1 rz (by omega)).2, hz]
  have hops : [ROp.add 122 rz, ROp.add2 122 rz].map (ROp.eop c₁ fun _ => z) =
      [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z] := by
    simp [ROp.eop, p122]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orunC (P := P) hW (fun _ => z) hH
    [ROp.add 122 rz, ROp.add2 122 rz] e₁.wb_right o₁.1.2.lcte (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by norm_num, by omega, hz₁⟩) (by rw [hops]; exact hv)
    (by rw [hops]; exact hAV)
  rw [hops] at o₂
  have hc₂ := o₂.1.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  refine ⟨c₃, G₂, o.mono (by simp) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)


theorem stBodyDV_orunC (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hK : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)) {Y : Type*}
    {off oN aA : ℕ} {xs : List Y} {pd : Y → D} {ιE : D → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = σ (pd xs[i]))
    (hoff : off + xs.length ≤ W) (hN : ∀ d, P.data.getD (oN + σ d) 0 = ιE d)
    (hoN : oN + nD ≤ W) (haA : aA + nD ≤ W) {A : D → ℤ} (sw : Bool)
    {i : ℕ} (hi : i < xs.length) {c : Config} (hc : WordsBounded W c) {F : Forest}
    {G : List VT} (hS : LCTE B n F G c) (h120 : c.nreg 120 = i)
    (hA : ∀ d, c.rmem (aA + σ d) = A d)
    (hv : ValidOpsE n F (eopsDV sw (ιE (pd xs[i])) (A (pd xs[i])) (A (M.rev (pd xs[i])))))
    {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n F (eopsDV sw (ιE (pd xs[i])) (A (pd xs[i])) (A (M.rev (pd xs[i])))))
    (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (bodyDV B nD off oN aA (opsDV sw)) c F G c'
        (eopsDV sw (ιE (pd xs[i])) (A (pd xs[i])) (A (M.rev (pd xs[i])))) G' 2 17 ∧
      c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  set d := pd xs[i] with hd
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσd := hσ d
  have hσr := hσ (M.rev d)
  obtain ⟨c₁, k₁, e₁, hk₁, p123, p132, p133, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122, .constN 123 oN, .addN 123 123 122, .readIn 123 123,
      .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124, .constN 125 aA,
      .addN 125 125 122, .loadR 132 125, .constN 125 aA, .addN 125 125 124,
      .loadR 133 125]) c c' k' ∧ k' = 15 ∧ c'.nreg 123 = ιE d ∧ c'.rreg 132 = A d ∧
      c'.rreg 133 = A (M.rev d) ∧ GFr 122 134 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; rw [h120]; omega)
      | (config_simp; rw [h120, hxs i hi]; omega)
      | (config_simp; rw [h120, hxs i hi, hK]; omega)
      | (simp only [iRV]; omega)
      | (config_simp; rw [h120, hxs i hi]; simp only [iRV]; omega))
    refine ⟨rfl, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, hxs i hi, hN]
    · config_simp; rw [h120, hxs i hi, hA]
    · config_simp; rw [h120, hxs i hi, hK, hA]
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  set zr : ℕ → ℤ := fun r => if r = 132 then A d else A (M.rev d) with hzr
  have w132 : c₁.rreg 132 = zr 132 := by rw [p132]; simp [hzr]
  have w133 : c₁.rreg 133 = zr 133 := by rw [p133]; simp [hzr]
  have hops : (opsDV sw).map (ROp.eop c₁ zr) = eopsDV sw (ιE d) (A d) (A (M.rev d)) := by
    cases sw <;> simp [opsDV, eopsDV, ROp.eop, p123, hzr]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orunC (P := P) hW zr hH (opsDV sw) e₁.wb_right o₁.1.2.lcte
    (fun o ho => by
      cases sw <;> simp only [opsDV, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at ho <;>
        rcases ho with rfl | rfl
      · exact ⟨by norm_num, by norm_num, w132⟩
      · exact ⟨by norm_num, by norm_num, w133⟩
      · exact ⟨by norm_num, by norm_num, w133⟩
      · exact ⟨by norm_num, by norm_num, w132⟩) (by rw [hops]; exact hv)
    (by rw [hops]; exact hAV)
  rw [hops] at o₂
  have hc₂ := o₂.1.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  have hl : (opsDV sw).length = 2 := by cases sw <;> rfl
  refine ⟨c₃, G₂, o.mono (by omega) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)

/-- **The links of the edges of a list of darts**: the body `bodyLK` links the node of the edge
of the dart `d` of the element `i` below the node `F1 d` of one end, then the node `F1 (rev d)`
of the other end below it. -/

theorem stBodyLK_orunC (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hK : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)) {Y : Type*}
    {off oN oF : ℕ} {xs : List Y} {pd : Y → D} {ιE F1 : D → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = σ (pd xs[i]))
    (hoff : off + xs.length ≤ W) (hN : ∀ d, P.data.getD (oN + σ d) 0 = ιE d)
    (hoN : oN + nD ≤ W) (hF : ∀ d, P.data.getD (oF + σ d) 0 = F1 d) (hoF : oF + nD ≤ W)
    {i : ℕ} (hi : i < xs.length) {c : Config} (hc : WordsBounded W c) {F : Forest}
    {G : List VT} (hS : LCTE B n F G c) (h120 : c.nreg 120 = i)
    (hv : ValidOpsE n F [.link (ιE (pd xs[i])) (F1 (pd xs[i])),
      .link (F1 (M.rev (pd xs[i]))) (ιE (pd xs[i]))]) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n F [.link (ιE (pd xs[i])) (F1 (pd xs[i])),
      .link (F1 (M.rev (pd xs[i]))) (ιE (pd xs[i]))]) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (bodyLK B nD off oN oF) c F G c'
        [.link (ιE (pd xs[i])) (F1 (pd xs[i])), .link (F1 (M.rev (pd xs[i]))) (ιE (pd xs[i]))]
        G' 2 17 ∧ c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  set d := pd xs[i] with hd
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσd := hσ d
  have hσr := hσ (M.rev d)
  obtain ⟨c₁, k₁, e₁, hk₁, p123, p125, p126, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122, .constN 123 oN, .addN 123 123 122, .readIn 123 123,
      .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124, .constN 125 oF,
      .addN 125 125 122, .readIn 125 125, .constN 126 oF, .addN 126 126 124,
      .readIn 126 126]) c c' k' ∧ k' = 15 ∧ c'.nreg 123 = ιE d ∧ c'.nreg 125 = F1 d ∧
      c'.nreg 126 = F1 (M.rev d) ∧ GFr 122 127 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; rw [h120]; omega)
      | (config_simp; rw [h120, hxs i hi]; omega)
      | (config_simp; rw [h120, hxs i hi, hK]; omega)
      | (simp only [iRV]; omega)
      | (config_simp; rw [h120, hxs i hi]; simp only [iRV]; omega))
    refine ⟨rfl, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, hxs i hi, hN]
    · config_simp; rw [h120, hxs i hi, hF]
    · config_simp; rw [h120, hxs i hi, hK, hF]
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hops : [ROp.link 123 125, ROp.link 126 123].map (ROp.eop c₁ fun _ => 0) =
      [.link (ιE d) (F1 d), .link (F1 (M.rev d)) (ιE d)] := by
    simp [ROp.eop, p123, p125, p126]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orunC (P := P) hW (fun _ => 0) hH
    [ROp.link 123 125, ROp.link 126 123] e₁.wb_right o₁.1.2.lcte (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩) (by rw [hops]; exact hv)
    (by rw [hops]; exact hAV)
  rw [hops] at o₂
  have hc₂ := o₂.1.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  refine ⟨c₃, G₂, o.mono (by simp) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)

/-- **The parent darts of the spanning tree** into `TP`: for the dart `d = IT[r120]`,
`TP[NH[d]] := d`. -/

theorem stBodyVL_orunC (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W) {ιv : V → ℕ}
    (hlt : ∀ x, ιv x < n) (hNT : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d))
    (hNH : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)) (hWa : 6 * nD ≤ W)
    (hB : 3 * nD ≤ B) {d : D} {i : ℕ} (hd : (σ d : ℕ) = i) {c : Config}
    (hc : WordsBounded W c) {F : Forest} {G : List VT} (hS : LCTE B n F G c)
    (h120 : c.nreg 120 = i) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n F) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (bodyVL B nD) c F G c' [] G' 2 18 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aVL nD + i → c'.rmem a = c.rmem a) ∧
      c'.rmem (aVL nD + i) = c.rmem (aWT + i) + pathSum F n (ιv (M.tail d)) -
        pathSum F n (ιv (M.head d)) := by
  have hσd := (σ d).2
  obtain ⟨c₁, k₁, e₁, hk₁, p122, p123, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 (iNT nD),
      .addN 122 122 120, .readIn 122 122, .constN 123 (iNH nD), .addN 123 123 120,
      .readIn 123 123]) c c' k' ∧ k' = 6 ∧ c'.nreg 122 = ιv (M.tail d) ∧
      c'.nreg 123 = ιv (M.head d) ∧ GFr 122 124 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iNT, iNH]; omega)
      | (config_simp; rw [h120]; simp only [iNT, iNH]; omega))
    refine ⟨rfl, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, ← hd, hNT]
    · config_simp; rw [h120, ← hd, hNH]
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, -, -, -, s₂, -, m₂, f₂⟩ := regQuery_orunC (P := P) hW e₁.wb_right
    o₁.1.2.lcte hV hH p122 (hlt _)
  have e₃ := Exec.copyR (P := P) o₂.1.2.wb 134 196
  have g₃ : GFr 134 135 c₂ { c₂ with rreg := upd c₂.rreg 134 (c₂.rreg 196) } := by gfr_tac
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  obtain ⟨c₄, G₄, o₄, -, -, -, s₄, -, m₄, f₄⟩ := regQuery_orunC (P := P) hW e₃.wb_right
    o₃.1.2.lcte hV hH (v := ιv (M.head d))
    (by rw [(g₃.1 123 (by omega)).1, f₂.1 123 (by omega), p123]) (hlt _)
  have e₅ := Exec.copyR (P := P) o₄.1.2.wb 135 196
  have g₅ : GFr 135 136 c₄ { c₄ with rreg := upd c₄.rreg 135 (c₄.rreg 196) } := by gfr_tac
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) rfl
  set c₅ := { c₄ with rreg := upd c₄.rreg 135 (c₄.rreg 196) } with hc₅
  have hc₅w : WordsBounded W c₅ := e₅.wb_right
  have q120 : c₅.nreg 120 = i := by
    rw [(g₅.1 120 (by omega)).1, f₄.1 120 (by omega), (g₃.1 120 (by omega)).1,
      f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]
  have q134 : c₅.rreg 134 = pathSum F n (ιv (M.tail d)) := by
    rw [(g₅.1 134 (by omega)).2, f₄.2.1 134 (by omega)]; config_simp; exact s₂
  have q135 : c₅.rreg 135 = pathSum F n (ιv (M.head d)) := by
    rw [hc₅]; config_simp; exact s₄
  have hmem : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₅.nmem a = c.nmem a ∧
      c₅.rmem a = c.rmem a := fun a ha => by
    have h2 := m₂ a ha
    have h4 := m₄ a ha
    simp only [DynTree.mem] at h2 h4
    rw [hc₅]
    simp only
    rw [h4.1, h4.2, g₃.2.1, g₃.2.2.1, h2.1, h2.2, g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩
  have hw : c₅.rmem (aWT + i) = c.rmem (aWT + i) :=
    (hmem _ (Or.inl (by unfold aWT; omega))).2
  obtain ⟨c₆, k₆, e₆, hk₆, t120, tn, tr, tm, tnm, tout⟩ : ∃ c' k', Exec P W
      (block ([.constN 124 aWT, .addN 124 124 120, .loadR 136 124, .addR 136 136 134,
        .subR 136 136 135, .constN 125 (aVL nD), .addN 125 125 120, .storeR 125 136] ++ incI))
      c₅ c' k' ∧ k' = 10 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, r ≠ 120 → r ≠ 124 → r ≠ 125 → r ≠ 127 → c'.nreg r = c₅.nreg r) ∧
      (∀ r, r ≠ 136 → c'.rreg r = c₅.rreg r) ∧
      c'.rmem = upd c₅.rmem (aVL nD + i) (c.rmem (aWT + i) + pathSum F n (ιv (M.tail d)) -
        pathSum F n (ιv (M.head d))) ∧ c'.nmem = c₅.nmem ∧ c'.output = c₅.output := by
    unfold incI
    exec_block
    all_goals try (first
      | omega
      | (unfold aWT; omega)
      | (unfold aVL; omega)
      | (config_simp; rw [q120]; unfold aWT; omega)
      | (config_simp; rw [q120]; unfold aVL; omega)
      | (config_simp; rw [q120]; omega))
    refine ⟨rfl, by config_simp; rw [q120], fun r h1 h2 h3 h4 => ?_, fun r h1 => ?_, ?_, rfl,
      rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
        upd_other _ _ _ h4]
    · config_simp; simp only [upd_other _ _ _ h1]
    · config_simp; rw [q120, q134, q135, hw]
  have o₆ : ORunC P W H B n _ c₅ F G₄ c₆ [] G₄ 0 k₆ := ORunC.glue e₆ o₅.1.2.lcte
    (fun a ha _ => ⟨by rw [tnm], by rw [tm, upd_other _ _ _ (by unfold aVL; omega)]⟩)
    (tn 151 (by omega) (by omega) (by omega) (by omega)) rfl
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hreg : ∀ r, r < 120 → c₅.nreg r = c.nreg r ∧ c₅.rreg r = c.rreg r := fun r hr => by
    rw [(g₅.1 r (by omega)).1, (g₅.1 r (by omega)).2, f₄.1 r (by omega), f₄.2.1 r (by omega),
      (g₃.1 r (by omega)).1, (g₃.1 r (by omega)).2, f₂.1 r (by omega), f₂.2.1 r (by omega),
      (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]; exact ⟨rfl, rfl⟩
  refine ⟨c₆, G₄, o.mono (by omega) (by omega), t120, fun r hr => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha hne => ?_, ?_⟩
  · rw [tn r (by omega) (by omega) (by omega) (by omega)]
    rcases hr with hr | rfl
    · exact (hreg r hr).1
    · rw [(g₅.1 121 (by omega)).1, f₄.1 121 (by omega), (g₃.1 121 (by omega)).1,
        f₂.1 121 (by omega), (g₁.1 121 (by omega)).1]
  · rw [tr r (by omega)]; exact (hreg r hr).2
  · rw [tout, hc₅]; simp only; rw [f₄.2.2, g₃.2.2.2, f₂.2.2, g₁.2.2.2]
  · rw [tnm]; exact (hmem a ha).1
  · rw [tm, upd_other _ _ _ hne]; exact (hmem a ha).2
  · rw [tm, upd_same]


theorem stInT_orunC (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {φ : D → ℤ}
    (hv : ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) (hH : 2 * Vb ≤ H) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d) :
    ∃ c' G', ORunC P W H B n (inTS B nD n k) c (Forest.init n) G c' (treeOpsL T ιv ιg φ vs ts)
        G' (6 * Fintype.card V) (45 * Fintype.card V + 16) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a := by
  have hvl := hI.oT.flen
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [treeOpsL_eq T φ hI.oT] at hv hAV ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  have hAA := AllV.left (AllV.left hAV)
  have hAB := AllV.right (AllV.left hAV)
  have hAC := AllV.right hAV
  rw [runOpsE_fst_append] at hAC
  -- the values of the nodes of the vertices
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p110, g₁⟩ : ∃ c' k', Exec P W
      (block (.constR 110 0 :: ldI (iHD nD n k))) c c' k' ∧ k' = 4 ∧ c'.nreg 120 = 0 ∧
      c'.nreg 121 = vs.length ∧ c'.rreg 110 = ((0 : ℤ) : ℝ) ∧ GFr 110 122 c c' := by
    unfold ldI
    exec_block
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l0, by config_simp, by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, q₂⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) vs (fun y => [EOp.add (ιv y) 0, .add2 (ιv y) 0]) hvA hAA (fun _ c' => IFr B n c₁ c')
    (body := bodyNV B (iIV nD n k) 110) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyNV_orunC hW hP hI.iv (by unfold iIV; omega) hi hc' hS'
        h120 (z := 0) (by rw [hQ.2.1 110 (by omega), p110]) (by omega) hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.1.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.1.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have hph₃ : ∀ d, c₃.rmem (aPH nD + σ d) = φ d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, g₁.2.2.1, hph]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => eopsDV false (ιg (T.par y)) (φ (T.par y)) (φ (M.rev (T.par y))))
    hvB hAB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIT nD n k) (iNG nD) (aPH nD)
      (opsDV false)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyDV_orunC (aA := aPH nD) (A := φ) hW hP hK.rv
        hI.it (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega)
        (by unfold aPH; omega) false hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, hph₃]) hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l1]⟩)
    e₃.wb_right o₃.1.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l1])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.1.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) rfl
  obtain ⟨c₆, G₆, o₆, q₆⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => [EOp.link (ιg (T.par y)) (ιv (M.tail (T.par y))),
      .link (ιv (M.tail (M.rev (T.par y)))) (ιg (T.par y))])
    hvC hAC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIT nD n k) (iNG nD) (iNT nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyLK_orunC hW hP hK.rv hI.it
        (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega) hK.nt (by unfold iNT; omega)
        hi hc' hS' h120 hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l1]⟩)
    e₅.wb_right o₅.1.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l1])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr.1, hfr.2.1, hfr.2.2⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)



theorem stInC_orunC (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {val : D → ℤ} {H₀ : ℤ}
    {F₁ : Forest} (hv : ValidOpsE n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) (hH : 2 * Vb ≤ H) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₁ G c)
    (hvl : ∀ d, c.rmem (aVL nD + σ d) = val d) (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G', ORunC P W H B n (inCS B nD n k) c F₁ G c' (cotOpsL C ιf ιe val H₀ fs cs) G'
        (6 * Fintype.card F) (45 * Fintype.card F + 17) ∧ IFr0 B n c c' := by
  have hfl := hI.oC.flen
  have hcl := hI.oC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [cotOpsL_eq C val H₀ hI.oC] at hv hAV ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  have hAA := AllV.left (AllV.left hAV)
  have hAB := AllV.right (AllV.left hAV)
  have hAC := AllV.right hAV
  rw [runOpsE_fst_append] at hAC
  -- the values of the nodes of the faces
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p111, g₁⟩ : ∃ c' k', Exec P W
      (block ([.constN 122 (aH0 nD), .loadR 111 122] ++ ldI (iHD nD n k + 2))) c c' k' ∧
      k' = 5 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = fs.length ∧ c'.rreg 111 = (H₀ : ℝ) ∧
      GFr 111 123 c c' := by
    unfold ldI
    exec_block
    · unfold aH0; omega
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l2, by config_simp; exact hH0,
        by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, q₂⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) fs (fun y => [EOp.add (ιf y) H₀, .add2 (ιf y) H₀]) hvA hAA
    (fun _ c' => IFr B n c₁ c') (body := bodyNV B (iIF nD n k) 111) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyNV_orunC hW hP hI.if_ (by unfold iIF iIV; omega) hi hc'
        hS' h120 (z := H₀) (by rw [hQ.2.1 111 (by omega), p111]) (by omega) hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.1.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.1.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have hvl₃ : ∀ d, c₃.rmem (aVL nD + σ d) = val d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, g₁.2.2.1, hvl]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => eopsDV true (ιe (C.par y)) (val (C.par y)) (val (M.rev (C.par y))))
    hvB hAB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIC nD n k) (iNE nD) (aVL nD)
      (opsDV true)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyDV_orunC (aA := aVL nD) (A := val) hW hP hK.rv
        hI.ic (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega)
        (by unfold aVL; omega) true hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, hvl₃]) hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l3]⟩)
    e₃.wb_right o₃.1.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l3])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.1.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) rfl
  obtain ⟨c₆, G₆, o₆, q₆⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => [EOp.link (ιe (C.par y)) (ιf (M.face (C.par y))),
      .link (ιf (M.face (M.rev (C.par y)))) (ιe (C.par y))])
    hvC hAC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIC nD n k) (iNE nD) (iNF nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stBodyLK_orunC hW hP hK.rv hI.ic
        (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega) hK.nf (by unfold iNF; omega)
        hi hc' hS' h120 hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l3]⟩)
    e₅.wb_right o₅.1.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l3])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

theorem stInV_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 6 * nD ≤ W) (hB3 : 3 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) {ιv : V → ℕ} (hvn : ∀ x, ιv x < n)
    (hNT : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d))
    (hNH : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ}
    (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (inVS B nD) c Fo G c' [] G' (2 * nD) (20 * nD + 4) ∧
      (∀ d, c'.rmem (aVL nD + σ d) = c.rmem (aWT + σ d) + pathSum Fo n (ιv (M.tail d)) -
        pathSum Fo n (ιv (M.head d))) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ : ∃ c' k', Exec P W (block [.constN 120 0,
      .constN 121 nD]) c c' k' ∧ k' = 2 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = nD ∧
      GFr 120 122 c c' := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hlen : (List.range nD).length = nD := List.length_range
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n)
    (ra := 120) (rb := 121) (List.range nD) (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial) (by rw [flatMap_nil']; exact hV)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c₁.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c₁.rreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + i ≤ a) →
        c'.rmem a = c₁.rmem a) ∧
      ∀ d : D, (σ d : ℕ) < i → c'.rmem (aVL nD + σ d) = c₁.rmem (aWT + σ d) +
        pathSum Fo n (ιv (M.tail d)) - pathSum Fo n (ιv (M.head d)))
    (body := bodyVL B nD) (mb := 2) (hb := 18)
    (fun i hi c' G' hQ hc' hS' h120 h121 _ _ => by
      rw [flatMap_nil'] at hS' ⊢
      have hi' : i < nD := by rw [hlen] at hi; exact hi
      set d := σ.symm ⟨i, hi'⟩ with hd
      have hσd : (σ d : ℕ) = i := by rw [hd, Equiv.apply_symm_apply]
      obtain ⟨c₃, G₃, o, q120, qn, qr, qout, qnm, qrm, qv⟩ := stBodyVL_orunC hW hP hvn hNT hNH hWa
        (by omega) hσd hc' hS' h120 hV hH
      have hwt : c'.rmem (aWT + i) = c₁.rmem (aWT + i) :=
        hQ.2.2.2.2.1 _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aVL; omega))
      refine ⟨c₃, G₃, o, ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr,
        fun r hr => by rw [qr r hr]; exact hQ.2.1 r hr, by rw [qout]; exact hQ.2.2.1,
        fun a ha => by rw [qnm a ha]; exact hQ.2.2.2.1 a ha, fun a ha ha' => ?_,
        fun d' hd' => ?_⟩, q120, by rw [qn 121 (by omega), h121]⟩
      · rw [qrm a ha (by omega)]; exact hQ.2.2.2.2.1 a ha (by omega)
      · rcases Nat.lt_or_ge (σ d' : ℕ) i with h' | h'
        · rw [qrm _ (Or.inl (by unfold aVL; omega)) (by omega)]
          exact hQ.2.2.2.2.2 d' h'
        · have : d' = d := σ.injective (Fin.ext (by omega))
          subst this
          rw [hσd, qv, hwt]; rfl)
    e₁.wb_right o₁.1.2.lcte ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hlen])
  rw [flatMap_nil', hlen] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by omega) (by omega), fun d => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha ha' => ?_⟩
  · rw [q₆ d (by rw [hlen]; exact (σ d).2), g₁.2.2.1]
  · rw [q₁ r (by omega), q₂ r (by omega), (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [q₃, g₁.2.2.2]
  · rw [q₄ a ha, g₁.2.1]
  · rw [q₅ a ha (by rw [hlen]; exact ha'), g₁.2.2.1]



theorem stIn_orunC (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    {S : Finset D} {ℓ : D → ℤ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}
    (hL : Layout M n ιv ιg ιf ιe) (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual}
    {C : DTree M} {vs ts : List V} {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P)
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {wt φ : D → ℤ} {H₀ : ℤ} {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = wt d) (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d)
    (hH0 : c.rmem (aH0 nD) = H₀) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n (Forest.init n) (treeOpsL T ιv ιg φ vs ts ++
      cotOpsL C ιf ιe (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) H₀ fs cs))
    (hH : 2 * Vb ≤ H) :
    ∃ c' G' os, ORunC P W H B n (inS B nD n k) c (Forest.init n) G c' os G'
        (6 * (Fintype.card V + Fintype.card F) + 2 * nD)
        (60 * (Fintype.card V + Fintype.card F) + 20 * nD + 42) ∧
      os = treeOpsL T ιv ιg φ vs ts ++
        cotOpsL C ιf ιe (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) H₀ fs cs ∧
      os.length ≤ 6 * (Fintype.card V + Fintype.card F) ∧
      (runOpsE n (Forest.init n) os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ C.root H₀ (runOpsE n (Forest.init n) os).1 T
        (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) ∧
      KMem M σ ιv T wt φ c' ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  set val : D → ℤ := fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d) with hval
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨hlen, hv, ho, hSt⟩ := init_storedL hL hoff φ val H₀ hI.oT hI.oC
  obtain ⟨-, hvT, -, hRT, -, -, -⟩ := tree_storedL (ιf := ιf) (ιe := ιe) hL φ hI.oT
  obtain ⟨-, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  set F1 := (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 with hF1
  -- the spanning tree
  obtain ⟨c₁, G₁, o₁, r₁, out₁, m₁⟩ := stInT_orunC hW hWa hB hP hL hK hI hvT
    (AllV.left hAV) hH hc hS hph
  -- its parent darts
  obtain ⟨c₂, G₂, o₂', tp₂, r₂, out₂, rm₂, nm₂⟩ := inP_orun hW hWa hB hP hL hK hI o₁.1.2.wb
    o₁.1.2.lcte
  have o₂ := ORunC.of_noTestR (H := H) o₂' rfl
  -- the values of the darts
  obtain ⟨c₃, G₃, o₃, vl₃, r₃, out₃, nm₃, rm₃⟩ := stInV_orunC (P := P) (σ := σ) hW (by omega) hB3 hP
    hL.prim.f_lt hK.nt hK.nh o₂.1.2.wb o₂.1.2.lcte (AllV.left hAV).final hH
  have hvl : ∀ d, c₃.rmem (aVL nD + σ d) = ((val d : ℤ) : ℝ) := fun d => by
    have hd := hσ d
    rw [vl₃, rm₂, (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
    change (wt d : ℝ) + pathSum F1 n _ - pathSum F1 n _ = _
    rw [lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv,
      lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv]
    simp only [hval]; push_cast; ring
  have hH0₃ : c₃.rmem (aH0 nD) = H₀ := by
    rw [rm₃ _ (Or.inl (by unfold aH0; omega)) (Or.inr (by unfold aH0 aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aH0; omega))).2, hH0]
  -- the cotree
  obtain ⟨c₄, G₄, o₄, f₄⟩ := stInC_orunC hW hWa hB3 hP hL hK hI hvC
    (AllV.right hAV) hH o₃.1.2.wb o₃.1.2.lcte hvl hH0₃
  have o := o₁.seq (o₂.seq (o₃.seq o₄))
  simp only [List.nil_append] at o
  refine ⟨c₄, G₄, _, o.mono (by omega) (by omega), rfl, hlen, ho, hSt, ⟨fun x hx => ?_, fun d => ?_,
    fun d => ?_⟩, fun r hr => ?_, ?_, fun a ha han => ?_, fun a ha ha' => ?_⟩
  · have := hL.prim.f_lt x
    rw [(f₄.2.2 _ (Or.inl (by unfold aTP; omega))).1, nm₃ _ (Or.inl (by unfold aTP; omega))]
    exact tp₂ x hx
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aWT; omega))).2,
      rm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aPH; omega))).2,
      rm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aPH; omega))).2, hph]
  · rw [(f₄.1 r hr).1, (f₄.1 r hr).2, (r₃ r hr).1, (r₃ r hr).2, (r₂ r hr).1, (r₂ r hr).2]
    exact r₁ r hr
  · rw [f₄.2.1, out₃, out₂, out₁]
  · rw [(f₄.2.2 a ha).1, nm₃ a ha, nm₂ a han, (m₁ a ha).1]
  · rw [(f₄.2.2 a ha).2, rm₃ a ha ha', rm₂, (m₁ a ha).2]

end

end STFlow

end PlanarFlow
