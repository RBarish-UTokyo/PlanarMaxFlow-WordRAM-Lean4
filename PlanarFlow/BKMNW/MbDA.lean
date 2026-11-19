module

public import PlanarFlow.BKMNW.MbDP

/-!
# Miller's base, stage A, with the rotation on ranks

**`mbA_execS`**: `mbA_exec` (`MbBaseA.lean`, proof copied) with the extra conclusion that the
compacted rotation `SR[eRk (e i)] = eRk (σ (e i))` (written by `mcProg` at `Hb + 5n`) survives
stage A — `mbD` (`MbDP.lean`) needs it to decode the `up` codes of Miller's cycle.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Sem

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F} {P : Input} {W : ℕ}

open Classical in
set_option maxHeartbeats 1600000 in
/-- **Stage A, with the rotation on ranks** (`mbA_exec` plus `SR` at `Hb + 5n`): within
`75 n + 53 + 12 (Bz + 25 #N + 3 S + 15) + 21 #N + 1060 + encT #N + msT #N (#Q + #Face)` steps
(`S = Σ_N ex`), Miller's separator `R = sepC M e n Bz N σ … ex` is in the output form on the
memory cut at `Wr = Bz + 25 #N + 3 S + 14`, the work area `[0, Wr]` saved at `SVb`, the ranks
at `Hb` and the compacted reverses at `Hb + 4 n`; memory above `Wr` off `[Hb, Hb + 7 n)` and the
save area kept; `r5000 = n`, `r5004 = Hb`, `r5012 = #N`, `r5040 = Wr`, `r5045 = Wr + 1`,
`r5046 = SVb`; registers outside `mbU`, `4910 … 4916`, `5000 … 5049`, `5210`, `5211`,
`6220 … 6250` kept. -/
theorem mbA_execS (hloopM : ∀ d, M.head d ≠ M.tail d) (e : ℕ → D) {n b SGb Hb Bz SVb : ℕ}
    {B N : Finset D} {Hs : List (Finset V)} {σ τ : Perm D} {ex : D → ℕ}
    (hN : PMap M N Hs σ) (hne : N.Nonempty) (hret : ∀ x ∈ N, σ x = ret τ N x)
    (c : Config) (hc : WordsBounded W c) (hI : LvIn M c.nmem n b e B N Hs ex)
    (r40 : c.nreg 4840 = n) (r41 : c.nreg 4841 = b) (r43 : c.nreg 4843 = b + 2 * n)
    (s0 : c.nreg 5200 = SGb) (s1 : c.nreg 5201 = Hb) (s2 : c.nreg 5202 = Bz)
    (s3 : c.nreg 5203 = SVb) (hτB : Stable τ B)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i))
    (hBz : encB' n ≤ Bz)
    (lay : b + 4 * n ≤ Hb ∧ SGb + n ≤ Hb ∧ Bz + 25 * n + 3 * (∑ d ∈ N, ex d) + 15 ≤ Hb ∧
      Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * (∑ d ∈ N, ex d) + 16 ≤ W)
    (hS : ∑ j ∈ range n, c.nmem (b + 3 * n + j) ≤ W) :
    ∃ d t, Exec P W mbA c d t ∧
      t ≤ 75 * n + 53 + (12 * (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15) + 21 * #N + 1060 +
        encT #N + msT #N (Fintype.card (SVert σ N) + Fintype.card (psep M hN.stable hN.rev).Face)) ∧
      ∃ R, sepC M e n Bz N σ hN.stable hN.rev ex = some R ∧
        d.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, (mbCut (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14) d).nmem
          (d.nreg 640 + i) = (psep M hN.stable hN.rev).stCode (cNe e n N) (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ ((mbCut (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14) d).nmem
          (d.nreg 642 + (psep M hN.stable hN.rev).stFn (cNe e n N) G) ≠ d.nreg 643 ↔
            d.nreg 644 = 1)) ∧
      (∀ a ≤ Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14, d.nmem (SVb + a) = c.nmem a) ∧
      (∀ j < n, d.nmem (Hb + j) = eRk e n N (e j)) ∧
      (∀ i < n, e i ∈ N → d.nmem (Hb + 4 * n + eRk e n N (e i)) = eRk e n N (M.rev (e i))) ∧
      (∀ i < n, e i ∈ N → d.nmem (Hb + 5 * n + eRk e n N (e i)) = eRk e n N (σ (e i))) ∧
      (∀ a, Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 < a → ¬ (Hb ≤ a ∧ a < Hb + 7 * n) →
        ¬ (SVb ≤ a ∧ a < SVb + (Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15)) →
        d.nmem a = c.nmem a) ∧
      d.nreg 5000 = n ∧ d.nreg 5004 = Hb ∧ d.nreg 5012 = #N ∧
      d.nreg 5040 = Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 14 ∧
      d.nreg 5045 = Bz + 25 * #N + 3 * (∑ d ∈ N, ex d) + 15 ∧ d.nreg 5046 = SVb ∧
      (∀ x, mbU x = false → (x < 4910 ∨ (4916 < x ∧ x < 5000) ∨ (5049 < x ∧ x < 5210) ∨
        (5211 < x ∧ x < 6220) ∨ 6250 < x) → d.nreg x = c.nreg x) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ ∃ L, d.output = c.output ++ L := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  have hNn : #N ≤ n := card_le_of_lvIn hI
  set S := ∑ d ∈ N, ex d with hSdef
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, a8, am₁, an₁, ar₁, arm₁, ao₁⟩ :=
    mbP1_exec (P := P) c hc r40 r41 r43 s0 s1 (by omega)
  have hw₁ := e₁.wb_right
  have hsN : ∀ d ∈ N, ∃ i, i < n ∧ e i = d := fun d hd => hI.surj d (hI.sub hd)
  obtain ⟨c₂, t₂, e₂, ht₂, b12, b21, -, bRK, bC, bm₂, bn₂, br₂, brm₂, bo₂⟩ :=
    mcProg_exec (P := P) c₁ hw₁ (n := n) (NFb := b) (SGb := SGb) (RVb := b + 2 * n) (Hb := Hb)
      (EXb := b + 3 * n) (e := e) (B := B) (N := N) (τ := τ) (ι := M.rev) (ex := ex)
      a0 a1 a2 a3 a4 a8 hI.inj hI.mem (fun d hd => hI.surj d hd) hI.sub hτB
      (fun i hi => by rw [am₁]; exact hI.nf i hi)
      (fun i hi => by rw [am₁]; exact hSG i hi)
      (fun i hi => by rw [am₁]; exact hI.rv0 i hi)
      (fun i hi => by rw [am₁]; exact hI.ex i hi)
      ⟨by omega, by omega, by omega, by omega, by omega⟩ (by rw [am₁]; exact hS)
  have hw₂ := e₂.wb_right
  have k2 : ∀ x, (x < 5005 ∨ (5029 < x ∧ x < 6220) ∨ 6250 < x) → c₂.nreg x = c₁.nreg x := bn₂
  obtain ⟨c₃, t₃, e₃, ht₃, p09, p18, p19, p41, p46, pm₃, pn₃, pr₃, prm₃, po₃⟩ :=
    mbP2_exec (P := P) c₂ hw₂ (n := n) (Hb := Hb) (Bz := Bz) (SVb := SVb)
      (by rw [k2 _ (by omega), a0]) (by rw [k2 _ (by omega), a4])
      (by rw [k2 _ (by omega), an₁ _ (by omega), s2])
      (by rw [k2 _ (by omega), an₁ _ (by omega), s3]) (by omega) (by omega)
  have hw₃ := e₃.wb_right
  have hA : EncArr (psep M hN.stable hN.rev) (cNe e n N) (fun x => ex x.1) c₃.nmem
      (Hb + 4 * n) (Hb + 5 * n) (Hb + 6 * n) := by
    rw [pm₃]
    exact mc_encArr hN.stable hN.rev hsN hret bC
  obtain ⟨hl, hP, hm2⟩ := psep_run_conds hloopM hN hne
  obtain ⟨d, t₄, e₄, ht₄, R, hsep, h641, h640, hZ, -, hsv, hmem, h40, h45, hreg, hr₄, hrm₄, L,
    ho₄⟩ :=
    mbIn_exec (P := P) (W := W) (M := M) e n Bz hN.stable hN.rev ex hP hl hm2 c₃ hw₃
      (SVb := SVb) (CRb := Hb + 4 * n) (CSb := Hb + 5 * n) (CEb := Hb + 6 * n)
      (by rw [pn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        b12])
      (by rw [pn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        b21])
      p41 p46 p09 p18 p19 hA ((encB'_mono hNn).trans hBz)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have kk : ∀ x, (x < 5000 ∨ (5049 < x ∧ x < 5210) ∨ (5211 < x ∧ x < 6220) ∨ 6250 < x) →
      c₃.nreg x = c.nreg x := fun x hx => by
    rw [pn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k2 _ (by omega), an₁ _ (by omega)]
  have k3 : ∀ x, 5000 ≤ x → x ≤ 5004 → c₃.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [pn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k2 _ (by omega)]
  refine ⟨d, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, R, hsep, h641,
    h640, hZ, fun a ha => ?_, fun j hj => ?_, fun i hi hiN => ?_, fun i hi hiN => ?_,
    fun a h1 h2 h3 => ?_, ?_, ?_,
    ?_, h40, h45, by rw [hreg _ (by simp [mbU]) (by omega), p46], fun x hx1 hx2 => ?_,
    by rw [hr₄, pr₃, br₂, ar₁], by rw [hrm₄, prm₃, brm₂, arm₁], L, by rw [ho₄, po₃, bo₂, ao₁]⟩
  · rw [hsv a ha, pm₃, bm₂ _ (Or.inl (by omega)), am₁]
  · rw [hmem _ (by omega) (by omega), pm₃, bRK j hj]
  · rw [hmem _ (by have := eRk_lt (e := e) (n := n) hiN; omega)
      (by have := eRk_lt (e := e) (n := n) hiN; omega), pm₃, (bC i hi hiN).1]
  · rw [hmem _ (by have := eRk_lt (e := e) (n := n) hiN; omega)
      (by have := eRk_lt (e := e) (n := n) hiN; omega), pm₃, (bC i hi hiN).2.1, hret _ hiN]
  · rw [hmem a h1 h3, pm₃, bm₂ a (by omega), am₁]
  · rw [hreg _ (by simp [mbU]) (by omega), k3 _ (by omega) (by omega), a0]
  · rw [hreg _ (by simp [mbU]) (by omega), k3 _ (by omega) (by omega), a4]
  · rw [hreg _ (by simp [mbU]) (by omega),
      pn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b12]
  · rw [hreg x hx1 (by omega), kk x (by omega)]

end Sem

end BKMNW

end PlanarFlow
