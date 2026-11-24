module

public import PlanarFlow.BKMNW.LevelProg
public import Mathlib.Data.List.GetD

/-!
# One level of `scertD` with the bound on the number of pruned indices

`lvCut_exec'` / `lvProg_exec'`: `lvCut_exec` / `lvProg_exec` (`LevelProg.lean`, same programs,
same proofs) with two more conclusions: in kind `1` the number `r4828` of pruned indices written at
`IXb` is at most `n` (it is the length of the list `kpL … n`); in kind `2` the labels `LAB` are in
`(0, n]` (as `phCC_comp` gives them). The level loop
(`ScertProg.lean`) stores the pruned indices of the levels one after another and needs this bound
for the layout.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Sem

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}


set_option maxHeartbeats 1600000 in
open Classical in
/-- **A level at a cut-vertex hole on the machine** (the hole `Hs[J]` chosen by `hlProg`): the
outcome is `LvOut` of kind `1`, `2` or `3`. -/
theorem lvCut_exec' (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ} {n b nH A W₀ IXb J : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b nH A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r25 : c.nreg 4825 = IXb) (r72 : c.nreg 4872 = J)
    (r73 : c.nreg 4873 = 1) (hJ : J < Hs.length) (hHW : Hs.length + 1 ≤ W)
    (hnc : ¬ NoCut M N Hs)
    (hhole : (scChoiceE M sepF e n Hs A W₀).hole N = some (Hs.getD J ∅))
    (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hS : A + 2 * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) ≤ W) :
    ∃ c' t, Exec P W lvCut c c' t ∧ t ≤ 244 * n + 79 ∧
      (LvOut M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c.nmem c' n b IXb e ∧
        (c'.nreg 4900 = 1 → c'.nreg 4828 ≤ n) ∧
        (c'.nreg 4900 = 2 → ∀ i < n, 0 < c'.nmem (b + 13 * n + 1 + i) ∧
          c'.nmem (b + 13 * n + 1 + i) ≤ n)) ∧
      (∀ a, LvKept n b IXb a → c'.nmem a = c.nmem a) ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  set g := Hs.getD J ∅ with hg
  set ch := scChoiceE M sepF e n Hs A W₀ with hch
  have hgm : g ∈ Hs := by
    rw [hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, Option.getD_some]
    exact List.getElem_mem hJ
  have hsurjN : ∀ d ∈ N, ∃ i < n, e i = d := fun d hd => hI.surj d (hI.sub hd)
  set m₀ := c.nmem with hm₀
  have hEX : ∀ j < n, 1 + m₀ (b + 3 * n + j) ≤ ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    fun j hj => single_le_sum (f := fun j => 1 + m₀ (b + 3 * n + j)) (fun _ _ => Nat.zero_le _)
      (mem_range.2 hj)
  -- 1. the hole number
  obtain ⟨c₁, k₁, e₁, hk₁, g45, g84, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 4845 4872 4873, .copyN 4884 4845]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4845 = J + 1 ∧ c₁.nreg 4884 = J + 1 ∧
      (∀ x, x ≠ 4845 → x ≠ 4884 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [r72, r73]); omega)
    refine ⟨rfl, by config_simp; simp only [r72, r73], by config_simp; simp only [r72, r73],
      fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hw₁ := e₁.wb_right
  have hR₁ : LvRegs c₁ n b nH A W₀ := hR.of_frame fun x hx => by
    unfold LvFr at hx; exact gn₁ x (by omega) (by omega)
  -- 2. the labels of the components off `g`
  obtain ⟨c₂, k₂, e₂, hk₂, L1, L2, L3, L4, L5, L6, L7⟩ := phCC_comp (P := P) (M := M) (B := B)
    (N := N) hd hgm (n := n) (NFb := b) (THb := b + n) (RV0b := b + 2 * n) (J1 := J + 1)
    (GNb := b + 4 * n) (RVb := b + 5 * n) (TKb := b + 6 * n) (YFb := b + 7 * n)
    (LSb := b + 8 * n) (OFFb := b + 9 * n) (ADJb := b + 10 * n + 1) (LABb := b + 13 * n + 1)
    (Qb := b + 14 * n + 1) hI.mem hI.surj hI.inj hI.sub c₁ hw₁
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
    (by omega) ⟨by omega, by omega, by omega⟩ (by omega)
    (fun i hi => by rw [gm₁]; exact hI.rv0 i hi) (fun i hi => by rw [gm₁]; exact hI.nf i hi)
    (fun i hi => by rw [gm₁]; exact hI.th i hi J hJ) (fun i hi => by rw [gm₁]; exact hI.tk i hi)
    (fun i hi j hj => by rw [gm₁]; exact hI.key i hi j hj)
    hR₁.p0 hR₁.p1 hR₁.p2 hR₁.p3 g45 hR₁.p6 hR₁.p7 hR₁.p8 hR₁.p9 hR₁.p10 hR₁.r0 hR₁.r1 hR₁.r2
    hR₁.r3 hR₁.r4 hR₁.r5 hR₁.r6 hR₁.s0 hR₁.s1 hR₁.s2 hR₁.s3 hR₁.s4
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4853) ∨ 4865 < x) → c₂.nreg x = c₁.nreg x := L4
  have hmid : ∀ k < 10, phCC.wr (4417 + k) = false := by decide
  have hR₂ : LvRegs c₂ n b nH A W₀ := hR₁.of_frame fun x hx => by
    unfold LvFr at hx
    by_cases hm : 4416 < x ∧ x < 4427
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 10, x = 4417 + k := ⟨x - 4417, by omega, by omega⟩
      exact e₂.nreg_of_wr (hmid k hk)
    · exact f₂ x (by omega)
  have m₂ : ∀ a, (a < b + 4 * n ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n) ∨ b + 15 * n + 1 ≤ a) →
      c₂.nmem a = m₀ a := fun a ha => by rw [L3 a (by omega), gm₁]
  have hlabN : ∀ i < n, ∀ j < n, e i ∈ N → (c₂.nmem (b + 13 * n + 1 + i) =
      c₂.nmem (b + 13 * n + 1 + j) ↔ e j ∈ comp M N Hs g (e i)) := L1
  have hSm : ∑ j ∈ range n, (1 + c₂.nmem (b + 3 * n + j)) = ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    sum_congr rfl fun j hj => by rw [m₂ _ (by have := mem_range.1 hj; omega)]
  -- 3. the arrays of the scans
  obtain ⟨c₃, k₃, e₃, hk₃, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11⟩ := lpProg_exec (P := P) c₂ hw₂
    (n := n) (NFb := b) (THb := b + n) (EXb := b + 3 * n) (J1 := J + 1) (TGb := b + 15 * n + 2)
    (TG2b := b + 16 * n + 2) (VALb := b + 17 * n + 2) (SUMb := b + 18 * n + 2)
    hR₂.l0 hR₂.l1 hR₂.l2 hR₂.l3 (by rw [f₂ _ (by omega)]; exact g84) hR₂.l5 hR₂.l6 hR₂.l7 hR₂.l8
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ (by rw [hSm]; omega)
  have hw₃ := e₃.wb_right
  have hR₃ : LvRegs c₃ n b nH A W₀ := hR₂.of_frame fun x hx => by
    unfold LvFr at hx; exact P8 x (by omega)
  have m₃ : ∀ a, (a < b + 15 * n + 2 ∨ b + 19 * n + 3 ≤ a) → c₃.nmem a = c₂.nmem a :=
    fun a ha => P7 a (by omega)
  have eNF : ∀ i < n, c₂.nmem (b + i) = m₀ (b + i) := fun i hi => m₂ _ (by omega)
  have eEX : ∀ i < n, c₂.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => m₂ _ (by omega)
  have eTH : ∀ i < n, c₂.nmem (b + n + i) = m₀ (b + n + i) := fun i hi => m₂ _ (by omega)
  have hval : ∀ j < n, c₃.nmem (b + 17 * n + 2 + j) = if e j ∈ N then 1 + ex (e j) else 0 :=
    fun j hj => by
      rw [P4 j hj, eNF j hj, eEX j hj, lpV_eq, hI.ex j hj]
      by_cases h : e j ∈ N
      · simp [h, (hI.nf j hj).2 h]
      · have : ¬ m₀ (b + j) ≠ 0 := fun h' => h ((hI.nf j hj).1 h')
        simp [h, this]
  have htot : c₃.nreg 4891 = ∑ d ∈ N, (1 + ex d) := by
    rw [P6]
    exact sum_lpV hI.inj hsurjN (fun i hi => by rw [eNF i hi]; exact hI.nf i hi)
      (fun i hi => by rw [eEX i hi]; exact hI.ex i hi)
  have hvalS : ∑ j ∈ range n, c₃.nmem (b + 17 * n + 2 + j) ≤ ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) :=
    sum_le_sum fun j hj => by
      rw [P4 j (mem_range.1 hj), eEX j (mem_range.1 hj)]; exact lpV_le _ _
  -- 4. the weights of the components
  obtain ⟨c₄, k₄, e₄, hk₄, S1, S2, S3, S4, S5, S6⟩ := saProg_exec (P := P) c₃ hw₃
    (m := n) (nk := n + 1) (KEYb := b + 13 * n + 1) (VALb := b + 17 * n + 2) (st := 1)
    (Wb := b + 18 * n + 2) hR₃.a0 hR₃.a1 hR₃.a2 hR₃.a3 hR₃.a4
    (fun j hj => by rw [m₃ _ (by omega)]; have := (L2 j hj).2; omega)
    (fun k hk => P5 k (by omega)) (fun j hj => by omega) (fun j hj => by omega) (by omega)
    (by omega) (fun j hj => by omega) (by omega)
    (by simp only [one_mul]; omega)
  have hw₄ := e₄.wb_right
  have hR₄ : LvRegs c₄ n b nH A W₀ := hR₃.of_frame fun x hx => by
    unfold LvFr at hx; exact S3 x (by omega)
  have m₄ : ∀ a, (a < b + 18 * n + 2 ∨ b + 19 * n + 3 ≤ a) → c₄.nmem a = c₃.nmem a :=
    fun a ha => S2 a (by omega)
  have eLAB : ∀ i < n, c₄.nmem (b + 13 * n + 1 + i) = c₂.nmem (b + 13 * n + 1 + i) :=
    fun i hi => by rw [m₄ _ (by omega), m₃ _ (by omega)]
  have eNF4 : ∀ i < n, c₄.nmem (b + i) = m₀ (b + i) := fun i hi => by
    rw [m₄ _ (by omega), m₃ _ (by omega), eNF i hi]
  have eEX4 : ∀ i < n, c₄.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => by
    rw [m₄ _ (by omega), m₃ _ (by omega), eEX i hi]
  have hsumL : ∀ i < n, c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i)) =
      saF (fun j => c₄.nmem (b + 13 * n + 1 + j)) (fun j => if e j ∈ N then 1 + ex (e j) else 0) n
        (c₄.nmem (b + 13 * n + 1 + i)) := fun i hi => by
    rw [S1 _ (by rw [eLAB i hi]; have := (L2 i hi).2; omega)]
    exact saF_congr2 (fun j hj => by rw [m₃ _ (by omega), eLAB j hj])
      (fun j hj => by rw [one_mul, hval j hj]) _
  have hSUMle : ∀ k < n + 1, A + c₄.nmem (b + 18 * n + 2 + k) ≤ W := fun k hk => by
    rw [S1 k hk]
    have := saF_le (fun j => c₃.nmem (b + 13 * n + 1 + j)) (fun j => c₃.nmem (b + 17 * n + 2 + 1 * j)) n k
    simp only [one_mul] at this ⊢
    omega
  -- 5. the heavy scan
  obtain ⟨c₅, k₅, e₅, hk₅, H1, H2, H3, H4, H5, H6⟩ := hvScan_exec (P := P) c₄ hw₄
    (n := n) (NFb := b) (LABb := b + 13 * n + 1) (SUMb := b + 18 * n + 2) (A := A) (W₀ := W₀)
    (nl := n + 1) hR₄.h0 hR₄.h1 hR₄.h2 hR₄.h3 hR₄.h4 hR₄.h5
    (fun j hj => by rw [eLAB j hj]; have := (L2 j hj).2; omega) hSUMle (by omega) (by omega)
    (by omega) (by omega)
  have hw₅ := e₅.wb_right
  have hR₅ : LvRegs c₅ n b nH A W₀ := hR₄.of_frame fun x hx => by
    unfold LvFr at hx; exact H2 x (by omega)
  set Fh := ffS (fun i => hvP (c₄.nmem (b + i)) (c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i)))
    A W₀) n with hFh
  have hheavy : ch.heavy N g ex = if Fh.1 = 0 then none else some (e Fh.2) :=
    hvScan_heavy sepF hI.inj hsurjN ex A W₀ (lab := fun j => c₄.nmem (b + 13 * n + 1 + j))
      (sum := fun k => c₄.nmem (b + 18 * n + 2 + k)) (nf := fun i => c₄.nmem (b + i))
      (fun i hi j hj hiN => by
      rw [eLAB i hi, eLAB j hj]; exact hlabN i hi j hj hiN) hsumL
      (fun i hi => by rw [eNF4 i hi]; exact hI.nf i hi)
  have h88 : c₅.nreg 4788 = Fh.1 := congrArg Prod.fst H1
  have h89 : c₅.nreg 4789 = Fh.2 := congrArg Prod.snd H1
  have t73 : c₅.nreg 4873 = 1 := by
    rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
      gn₁ _ (by omega) (by omega), r73]
  have t25 : c₅.nreg 4825 = IXb := by
    rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
      gn₁ _ (by omega) (by omega), r25]
  have t91 : c₅.nreg 4891 = ∑ d ∈ N, (1 + ex d) := by
    rw [H2 _ (by omega), S3 _ (by omega), htot]
  have m₅ : ∀ a, LvKept n b IXb a → c₅.nmem a = m₀ a := fun a ha => by
    unfold LvKept at ha
    rw [H3, m₄ a (by omega), m₃ a (by omega), m₂ a (by omega)]
  have hFrs : ∀ x, LvFr x → c₅.nreg x = c.nreg x := fun x hx => by
    have hx' := hx
    unfold LvFr at hx'
    by_cases hm : 4416 < x ∧ x < 4427
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 10, x = 4417 + k := ⟨x - 4417, by omega, by omega⟩
      rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), e₂.nreg_of_wr (hmid k hk),
        gn₁ _ (by omega) (by omega)]
    · rw [H2 _ (by omega), S3 _ (by omega), P8 _ (by omega), f₂ _ (by omega),
        gn₁ _ (by omega) (by omega)]
  have hFhs := ffS_spec (fun i => hvP_le (c₄.nmem (b + i))
    (c₄.nmem (b + 18 * n + 2 + c₄.nmem (b + 13 * n + 1 + i))) A W₀) n
  have e5LAB : ∀ i < n, c₅.nmem (b + 13 * n + 1 + i) = c₂.nmem (b + 13 * n + 1 + i) :=
    fun i hi => by rw [H3, eLAB i hi]
  have e5NF : ∀ i < n, c₅.nmem (b + i) = m₀ (b + i) := fun i hi => by rw [H3, eNF4 i hi]
  have e5EX : ∀ i < n, c₅.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i) := fun i hi => by
    rw [H3, eEX4 i hi]
  have hlab5 : ∀ i < n, ∀ j < n, e i ∈ N → (c₅.nmem (b + 13 * n + 1 + i) =
      c₅.nmem (b + 13 * n + 1 + j) ↔ e j ∈ comp M N Hs g (e i)) := fun i hi j hj hiN => by
    rw [e5LAB i hi, e5LAB j hj]; exact hlabN i hi j hj hiN
  have hthg : ∀ i < n, (c₂.nmem (b + n + i) = J + 1 ↔ M.tail (e i) ∈ g) := fun i hi => by
    rw [eTH i hi]; exact hI.th i hi J hJ
  have hfrK : ∀ (c' : Config), (∀ a, LvKept n b IXb a → c'.nmem a = c₅.nmem a) →
      ∀ a, LvKept n b IXb a → c'.nmem a = m₀ a := fun c' h a ha => by rw [h a ha, m₅ a ha]
  by_cases hF0 : Fh.1 = 0
  · -- no heavy component: the cut
    have hlt : c₅.nreg 4788 < c₅.nreg 4873 := by rw [h88, t73, hF0]; omega
    obtain ⟨c₆, k₆, e₆, hk₆, B0, B1, B2, B3, B4, B5, B6, B7, B8⟩ := lvCutB_exec (P := P) c₅ hw₅
      hR₅ t73 (by omega) (fun j hj => by
        rw [H3, m₄ _ (by omega), P3 j hj]
        rw [tg2_eq]; split_ifs <;> omega)
    have hz : ch.heavy N g ex = none := by rw [hheavy, if_pos hF0]
    obtain ⟨hst, hbase⟩ := scStep_cut (τ := τ) hnc hhole hz
    set Fa := ffS (fun i => acP (c₅.nmem (b + 16 * n + 2 + i)) (c₅.nmem (b + 16 * n + 2 + i)) 1) n
      with hFa
    have hanc : ch.anchor N g = if Fa.1 = 0 then none else some (e Fa.2) := by
      rw [hFa, ffS_congr (p' := fun i => acP ((1 - phNe (c₂.nmem (b + n + i)) (J + 1)) *
          (c₂.nmem (b + i) / c₂.nmem (b + i))) ((1 - phNe (c₂.nmem (b + n + i)) (J + 1)) *
          (c₂.nmem (b + i) / c₂.nmem (b + i))) 1) (fun j hj => by rw [H3, m₄ _ (by omega), P3 j hj])]
      exact anchor_cut_ffS sepF hthg (fun i hi => by rw [eNF i hi]; exact hI.nf i hi)
    have h01 : c₆.nreg 4901 = Fa.1 := congrArg Prod.fst B1
    have h02 : c₆.nreg 4902 = Fa.2 := congrArg Prod.snd B1
    have hFas := ffS_spec (fun i => acP_le (c₅.nmem (b + 16 * n + 2 + i))
      (c₅.nmem (b + 16 * n + 2 + i)) 1) n
    refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + 1))))),
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_true hlt e₆))))), by omega,
      ⟨Or.inr (Or.inr (Or.inl ⟨B0, hst, g, fun i hi j hj hiN => by
        rw [B2]; exact hlab5 i hi j hj hiN, fun h => ?_, ?_, fun i hi => by rw [B2, e5NF i hi],
        fun i hi => by rw [B2, e5EX i hi]⟩)), fun h => absurd (B0.symm.trans h) (by decide),
        fun _ i hi => by rw [B2, e5LAB i hi]; exact L2 i hi⟩,
      hfrK c₆ (fun a _ => by rw [B2]), fun x hx => by rw [B3 x hx, hFrs x hx],
      by rw [B5 _ (Or.inr rfl), t25], by rw [B6, H4, S4, P9, L5, gr₁],
      by rw [B7, H5, S5, P10, L6, grm₁], by rw [B8, H6, S6, P11, L7, go₁]⟩
    · rw [h02]; rw [h01] at h
      rcases hFas with ⟨h', -⟩ | ⟨-, h', -⟩
      · exact absurd h' h
      · exact h'
    · rw [hbase, hanc, h01, h02]
      split_ifs <;> rfl
  · -- a heavy component
    have hnlt : ¬ c₅.nreg 4788 < c₅.nreg 4873 := by rw [h88, t73]; omega
    obtain ⟨hFh1, hz, hpz, -⟩ : Fh.1 = 1 ∧ Fh.2 < n ∧ _ ∧ _ := by
      rcases hFhs with ⟨h, -⟩ | h
      · exact absurd h hF0
      · exact h
    have hzN : e Fh.2 ∈ N := by
      rw [hvP_eq] at hpz
      split_ifs at hpz with h
      · exact (hI.nf _ hz).1 (by rw [← eNF4 _ hz]; exact h.1)
    have hheavy' : ch.heavy N g ex = some (e Fh.2) := by rw [hheavy, if_neg hF0]
    obtain ⟨c₆, k₆, e₆, hk₆, R1, R2, R3, R4, R5, R6, R7⟩ := lvPrune_exec (P := P) c₅ hw₅ hR₅
      (IXb := IXb) (z := Fh.2) (tot := ∑ d ∈ N, (1 + ex d)) t25 h89 t91 t73 hz ⟨l1, l2⟩
      (fun j hj => by rw [e5LAB j hj]; exact (L2 j hj).2)
      (fun i hi => by
        rw [e5EX i hi, ← sum_lpV hI.inj hsurjN hI.nf hI.ex]
        have h1 := hEX i hi
        have h2 : ∑ j ∈ range n, lpV (m₀ (b + j)) (m₀ (b + 3 * n + j)) ≤
            ∑ j ∈ range n, (1 + m₀ (b + 3 * n + j)) := sum_le_sum fun j _ => lpV_le _ _
        omega)
    set z := Fh.2 with hzdef
    set LZ := c₅.nmem (b + 13 * n + 1 + z) with hLZ
    set Fa := ffS (fun i => acP (c₅.nmem (b + 15 * n + 2 + i)) (c₅.nmem (b + 13 * n + 1 + i)) LZ) n
      with hFa
    have hanc : ch.anchor (comp M N Hs g (e z)) g = if Fa.1 = 0 then none else some (e Fa.2) :=
      acScan_anchor sepF (M := M) (e := e) (n := n) (Hs := Hs) (N := N) (g := g) A W₀
        (lab := fun j => c₅.nmem (b + 13 * n + 1 + j)) (tg := fun i => c₅.nmem (b + 15 * n + 2 + i))
        hz hzN hlab5 (fun i hi => by
        rw [H3, m₄ _ (by omega), P2 i hi, tg_ne]; exact hthg i hi)
    have hkp := kpScan_comp (M := M) (Hs := Hs) (g := g) (lab := fun j => c₅.nmem (b + 13 * n + 1 + j))
      hsurjN hz hzN hlab5 (nf := fun i => c₅.nmem (b + i)) (fun i hi => by rw [e5NF i hi]; exact hI.nf i hi)
    have hsub : comp M N Hs g (e z) ⊆ N := fun d hd => (mem_comp.1 hd).1
    have hrest : ∀ (c' : Config), c'.nreg 4900 = 3 → scStep ch Hs (N, τ, ex) = none →
        scBase ch Hs (N, τ, ex) = none → (∀ i < n, c'.nmem (b + i) = m₀ (b + i)) →
        (∀ i < n, c'.nmem (b + 3 * n + i) = m₀ (b + 3 * n + i)) →
        LvOut M ch Hs (N, τ, ex) m₀ c' n b IXb e := fun c' h1 h2 h3 h4 h5 =>
      Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩))
    refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + 2))))),
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ifLtN_false hnlt e₆))))), by omega, ⟨?_, ?_, ?_⟩,
      ?_, fun x hx => by rw [R2 x hx, hFrs x hx], R3, by rw [R5, H4, S4, P9, L5, gr₁],
      by rw [R6, H5, S5, P10, L6, grm₁], by rw [R7, H6, S6, P11, L7, go₁]⟩
    · rcases R1 with ⟨ha0, k3, hm⟩ | ⟨ha0, KO⟩
      · obtain ⟨h2, h3⟩ := scStep_noAnchor (τ := τ) hnc hhole hheavy'
          (by rw [hanc, if_pos ha0])
        exact hrest c₆ k3 h2 h3 (fun i hi => by rw [hm, e5NF i hi])
          (fun i hi => by rw [hm, e5EX i hi])
      · have hFas := ffS_spec (fun i => acP_le (c₅.nmem (b + 15 * n + 2 + i))
          (c₅.nmem (b + 13 * n + 1 + i)) LZ) n
        obtain ⟨-, ha, -, -⟩ : Fa.1 = 1 ∧ Fa.2 < n ∧ _ ∧ _ := by
          rcases hFas with ⟨h, -⟩ | h
          · exact absurd h ha0
          · exact h
        have hanc' : ch.anchor (comp M N Hs g (e z)) g = some (e Fa.2) := by
          rw [hanc, if_neg ha0]
        obtain ⟨hK1, hK2, hK3⟩ := hkp
        rcases KO with ⟨hl0, k3, hm⟩ | ⟨hl0, k1', k02, k28, kNF, kEX, kIX, km⟩
        · have hnK : ¬ (comp M N Hs g (e z)).card < N.card := by
            rw [comp_card_lt_iff, ← hK3, List.length_eq_zero_iff.1 hl0]
            simp
          obtain ⟨h2, h3⟩ := scStep_noShrink (τ := τ) hnc hhole hheavy' hanc' hnK
          exact hrest c₆ k3 h2 h3 (fun i hi => by rw [hm _ (by omega) (by omega), e5NF i hi])
            (fun i hi => by rw [hm _ (by omega) (by omega), e5EX i hi])
        · have hK : (comp M N Hs g (e z)).card < N.card := by
            rw [comp_card_lt_iff, ← hK3]
            obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hl0)
            exact ⟨e x, mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩⟩
          refine Or.inr (Or.inl ⟨k1', comp M N Hs g (e z), Fa.2, ha, k02,
            scStep_prune hnc hhole hheavy' hanc' hK, fun i hi => ?_, fun i hi => ?_,
            by rw [k28]; omega, fun k hk => ?_, ?_⟩)
          · rw [kNF i hi]; exact hK1 i hi
          · by_cases hia : i = Fa.2
            · subst hia
              have hSUMz : c₅.nmem (b + 18 * n + 2 + LZ) = ∑ d ∈ comp M N Hs g (e z), (1 + ex d) := by
                rw [hLZ, H3, hsumL z hz]
                exact saF_comp (M := M) hI.inj hsurjN (lab := fun j => c₄.nmem (b + 13 * n + 1 + j))
                  (fun i hi j hj hiN => by rw [eLAB i hi, eLAB j hj]; exact hlabN i hi j hj hiN)
                  (fun j _ => rfl) hz hzN
              rw [kEX, e5EX _ hi, hSUMz, hI.ex _ hi]
              unfold exP
              simp only [↓reduceIte]
              have := sum_sdiff hsub (f := fun d => 1 + ex d)
              omega
            · rw [km _ (by omega) (by omega) (by omega) (by omega), e5EX i hi, hI.ex i hi]
              unfold exP
              rw [if_neg (fun h => hia (hI.inj _ hi _ ha h))]
              simp
          · rw [k28] at hk
            rw [kIX k hk]; exact hK2 k hk
          · rw [k28, image_range_getElem (fun k hk => kIX k hk)]
            exact hK3
    · rcases R1 with ⟨-, k3, -⟩ | ⟨-, ⟨-, k3, -⟩ | ⟨-, -, -, k28, -⟩⟩
      · intro h; rw [k3] at h; exact absurd h (by decide)
      · intro h; rw [k3] at h; exact absurd h (by decide)
      · intro _; rw [k28]; exact (List.length_filter_le _ _).trans (by simp)
    · rcases R1 with ⟨-, k3, -⟩ | ⟨-, ⟨-, k3, -⟩ | ⟨-, k1', -⟩⟩
      · intro h; rw [k3] at h; exact absurd h (by decide)
      · intro h; rw [k3] at h; exact absurd h (by decide)
      · intro h; rw [k1'] at h; exact absurd h (by decide)
    · have hFa2 : Fa.2 ≤ n := (ffS_le (p := fun i => acP (c₅.nmem (b + 15 * n + 2 + i))
        (c₅.nmem (b + 13 * n + 1 + i)) LZ) (fun i => acP_le _ _ _) n).2
      exact hfrK c₆ fun a ha => by
        unfold LvKept at ha
        rcases R1 with ⟨-, -, hm⟩ | ⟨-, ⟨-, -, hm⟩ | ⟨-, -, -, -, -, -, -, km⟩⟩
        · rw [hm]
        · exact hm a (by omega) (by omega)
        · exact km a (by omega) (by omega) (by omega) (by omega)

open Classical in
/-- **One level of `scertD` on the machine** (the choices `scChoiceE`, any separator `sepF`):
within `|Hs| · (160 n + 36) + 244 n + 89` steps the outcome `LvOut` (kind `0`: `NoCut`; `1`: the
prune `scStep … = some …` with the new flags, weights and the record at `IXb`; `2`: the cut base;
`3`: failure); the kept memory `LvKept`, the fixed registers `LvFr` and `IXb` in `4825` kept. -/
theorem lvProg_exec' (sepF : SepFn M) {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ} {n b A W₀ IXb : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (r25 : c.nreg 4825 = IXb) (hHW : Hs.length + 1 ≤ W)
    (lay : b + 20 * n + 3 ≤ IXb ∧ IXb + n + 1 ≤ W)
    (hS : A + 2 * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j)) ≤ W) :
    ∃ c' t, Exec P W lvProg c c' t ∧ t ≤ Hs.length * (160 * n + 36) + 244 * n + 89 ∧
      (LvOut M (scChoiceE M sepF e n Hs A W₀) Hs (N, τ, ex) c.nmem c' n b IXb e ∧
        (c'.nreg 4900 = 1 → c'.nreg 4828 ≤ n) ∧
        (c'.nreg 4900 = 2 → ∀ i < n, 0 < c'.nmem (b + 13 * n + 1 + i) ∧
          c'.nmem (b + 13 * n + 1 + i) ≤ n)) ∧
      (∀ a, LvKept n b IXb a → c'.nmem a = c.nmem a) ∧
      (∀ x, LvFr x → c'.nreg x = c.nreg x) ∧ c'.nreg 4825 = IXb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2⟩ := lay
  obtain ⟨c₁, k₁, e₁, hk₁, Hres, Hmem, Hregs, Hr, Hrm, Ho⟩ := hlProg_exec (P := P) (M := M)
    (B := B) (N := N) hd (n := n) (NFb := b) (THb := b + n) (RV0b := b + 2 * n)
    (GNb := b + 4 * n) (RVb := b + 5 * n) (TKb := b + 6 * n) (YFb := b + 7 * n)
    (LSb := b + 8 * n) (OFFb := b + 9 * n) (ADJb := b + 10 * n + 1) (LABb := b + 13 * n + 1)
    (Qb := b + 14 * n + 1) hI.mem hI.surj hI.inj hI.sub c hc
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
    (by omega) ⟨by omega, by omega, by omega⟩ (by omega) hHW hI.rv0 hI.nf hI.th hI.tk hI.key
    hR.p0 hR.p1 hR.p2 hR.p3 hR.p6 hR.p7 hR.p8 hR.p9 hR.p10 hR.r0 hR.r1 hR.r2 hR.r3 hR.r4 hR.r5
    hR.r6 hR.s0 hR.s1 hR.s2 hR.s3 hR.s4 hR.u0 hR.u1 hR.u2 hR.v4
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, g73, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.constN 4873 1]) c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg 4873 = 1 ∧
      (∀ x, x ≠ 4873 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1]
  have hw₂ := e₂.wb_right
  have f₂ : ∀ x, LvFr x → c₂.nreg x = c.nreg x := fun x hx => by
    unfold LvFr at hx
    rw [gn₂ x (by omega), Hregs x ⟨by unfold HlFr; omega, by omega, by omega⟩]
  have t25 : c₂.nreg 4825 = IXb := by
    rw [gn₂ _ (by omega), Hregs _ ⟨by unfold HlFr; omega, by omega, by omega⟩, r25]
  have m₂ : ∀ a, (a < b + 4 * n ∨ (b + 6 * n ≤ a ∧ a < b + 7 * n) ∨ b + 15 * n + 1 ≤ a) →
      c₂.nmem a = c.nmem a := fun a ha => by rw [gm₂, Hmem a (by omega)]
  have hkept : ∀ a, LvKept n b IXb a → c₂.nmem a = c.nmem a := fun a ha => by
    unfold LvKept at ha; exact m₂ a (by omega)
  rcases hl_hole sepF e n A W₀ Hres with ⟨h0, hnc, -⟩ | ⟨h1, hJ, hnc, -, hhole⟩
  · have hlt : c₂.nreg 4871 < c₂.nreg 4873 := by rw [gn₂ _ (by omega), h0, g73]; omega
    obtain ⟨c₃, k₃, e₃, hk₃, b00, bn, bm, br, brm, bo⟩ : ∃ c₃ k₃,
        Exec P W (block [.constN 4900 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4900 = 0 ∧
        (∀ x, x ≠ 4900 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
      exec_block
      all_goals try ((try config_simp); omega)
      refine ⟨rfl, by config_simp, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
      simp only [Config.nreg_mk, upd_other _ _ _ h1]
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true hlt e₃)), by omega,
      ⟨Or.inl ⟨b00, hnc, fun i hi => by rw [bm, m₂ _ (by omega)],
        fun i hi => by rw [bm, m₂ _ (by omega)]⟩, fun h => absurd (b00.symm.trans h) (by decide),
        fun h => absurd (b00.symm.trans h) (by decide)⟩, fun a ha => by rw [bm, hkept a ha],
      fun x hx => ?_, by rw [bn _ (by omega), t25], by rw [br, gr₂, Hr], by rw [brm, grm₂, Hrm],
      by rw [bo, go₂, Ho]⟩
    have hx' := hx; unfold LvFr at hx'
    rw [bn x (by omega), f₂ x hx]
  · have hnlt : ¬ c₂.nreg 4871 < c₂.nreg 4873 := by rw [gn₂ _ (by omega), h1, g73]; omega
    have hR₂ : LvRegs c₂ n b Hs.length A W₀ := hR.of_frame f₂
    have hI₂ : LvIn M c₂.nmem n b e B N Hs ex := hI.congr fun a ha => m₂ a (by omega)
    have hS₂ : A + 2 * ∑ j ∈ range n, (1 + c₂.nmem (b + 3 * n + j)) ≤ W := by
      rw [sum_congr rfl fun j hj => by rw [m₂ _ (by have := mem_range.1 hj; omega)]]; exact hS
    obtain ⟨c₃, k₃, e₃, hk₃, ⟨C1, C1', C1''⟩, C2, C3, C4, C5, C6, C7⟩ := lvCut_exec' (P := P) (τ := τ) sepF hd
      c₂ hw₂ hR₂ hI₂ t25 (by rw [gn₂ _ (by omega)]) g73 hJ hHW hnc hhole ⟨l1, l2⟩ hS₂
    refine ⟨c₃, k₁ + (k₂ + (k₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hnlt e₃)), by omega,
      ⟨C1.congr (fun i hi => m₂ _ (by omega)) (fun i hi => m₂ _ (by omega)), C1', C1''⟩,
      fun a ha => by rw [C2 a ha, hkept a ha], fun x hx => by rw [C3 x hx, f₂ x hx], C4,
      by rw [C5, gr₂, Hr], by rw [C6, grm₂, Hrm], by rw [C7, go₂, Ho]⟩

end Sem

end BKMNW

end PlanarFlow
