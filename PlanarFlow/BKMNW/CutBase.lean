module

public import PlanarFlow.BKMNW.BackProg

/-!
# The cut base of `scertD` on the machine

When the level loop `slProg` stops at kind `2` (no heavy component off the cut-vertex hole `g`)
with an anchor `a₁`, the base of `scertD` is `cutCert M Hs N g (e a₁)`: the one-vertex path at
`tail (e a₁)` and the items `N.image (comp M N Hs g)` (the components off the hole). Here one scan
writes the items as labels and the flags of the new hole of that path, the inputs of the backward
pass `bpProg`:

* `ITEM[i] = lpV NF[i] LAB[i]` (`[e i ∈ N] (LAB[i] + 1)`), **`cut_itemRep`**: these labels represent
  `N.image (comp M N Hs g)`;
* `NH[i] = 1 - phNe TK[i] TK[a₁]` (`[TK[i] = TK[a₁]]`), **`mem_newHole_singleton`**,
  **`cut_nh`**: `NH[i] ≠ 0 ↔ tail (e i) ∈ newHole Hs (cutCert …).1.mverts`;
* `cbBodyC`, **`cbProg`** (registers `4950 = n`, `4951 = NFb`, `4952 = LABb`, `4953 = TKb`,
  `4954 = TK[a₁]`, `4955 = ITEMb`, `4956 = NHb`; written `4957 … 4963` and, for `bpProg`,
  `4944 := n + 2`, `4943 := NHb`, `4502 := ITEMb`), **`cbProg_exec`** (`22 n + 10` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Pure facts -/

section Pure

open Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The items of the cut on labels**: with labels exact on the components off `g` for the darts
of `N` and the flags of `N`, the labels `lpV nf lab` represent `N.image (comp M N Hs g)`. -/
theorem cut_itemRep {e : ℕ → D} {n : ℕ} {N : Finset D} {Hs : List (Finset V)} {g : Finset V}
    (hsurjN : ∀ d ∈ N, ∃ i < n, e i = d) {nf lab : ℕ → ℕ}
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N))
    (hlab : ∀ i < n, ∀ j < n, e i ∈ N → (lab i = lab j ↔ e j ∈ comp M N Hs g (e i))) :
    ItemRep e n (N.image (comp M N Hs g)) fun i => lpV (nf i) (lab i) := by
  have hit : ∀ i < n, lpV (nf i) (lab i) = if e i ∈ N then lab i + 1 else 0 := fun i hi => by
    rw [lpV_eq]
    by_cases h : e i ∈ N
    · simp [h, (hnf i hi).2 h]; omega
    · have : ¬ nf i ≠ 0 := fun h' => h ((hnf i hi).1 h')
      simp [h, this]
  have hcls : ∀ i < n, e i ∈ N →
      clsL e n (fun i => lpV (nf i) (lab i)) (lab i + 1) = comp M N Hs g (e i) := by
    intro i hi hiN
    ext d
    rw [mem_clsL]
    constructor
    · rintro ⟨j, hj, hl, rfl⟩
      rw [hit j hj] at hl
      by_cases hjN : e j ∈ N
      · rw [if_pos hjN] at hl
        exact (hlab i hi j hj hiN).1 (by omega)
      · rw [if_neg hjN] at hl; omega
    · intro hd
      have hdN : d ∈ N := (mem_comp.1 hd).1
      obtain ⟨j, hj, rfl⟩ := hsurjN d hdN
      refine ⟨j, hj, ?_, rfl⟩
      rw [hit j hj, if_pos hdN, ← (hlab i hi j hj hiN).2 hd]
  unfold ItemRep
  ext X
  rw [mem_erase, mem_labItems, mem_image]
  constructor
  · rintro ⟨hX, x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hsurjN x hx
    refine ⟨i, hi, by rw [hit i hi, if_pos hx]; omega, ?_⟩
    rw [hit i hi, if_pos hx, hcls i hi hx]
  · rintro ⟨i, hi, hl, rfl⟩
    have hiN : e i ∈ N := by
      by_contra h; rw [hit i hi, if_neg h] at hl; exact hl rfl
    rw [hit i hi, if_pos hiN, hcls i hi hiN]
    exact ⟨ne_empty_of_mem (self_mem_comp hiN), e i, hiN, rfl⟩

/-- The new hole of a one-vertex path: the vertex and the holes through it. -/
lemma mem_newHole_singleton {Hs : List (Finset V)} {u v : V} :
    u ∈ newHole Hs {v} ↔ HRel Hs u v := by
  rw [mem_newHole, HRel, mem_singleton]
  constructor
  · rintro (h | ⟨H, hH, hd, hu⟩)
    · exact Or.inl h
    · refine Or.inr ⟨H, hH, hu, ?_⟩
      by_contra hv
      exact hd (disjoint_singleton_right.2 hv)
  · rintro (h | ⟨H, hH, hu, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, hH, fun h => (disjoint_singleton_right.1 h) hv, hu⟩

/-- **The flags of the new hole of the cut path** from the class keys. -/
theorem cut_nh {e : ℕ → D} {n : ℕ} {N : Finset D} {Hs : List (Finset V)} {g : Finset V}
    {tk : ℕ → ℕ} {a : ℕ} (ha : a < n)
    (hkey : ∀ i < n, ∀ j < n, (tk i = tk j ↔ HRel Hs (M.tail (e i)) (M.tail (e j)))) :
    ∀ i < n, (1 - phNe (tk i) (tk a) ≠ 0 ↔
      M.tail (e i) ∈ newHole Hs (cutCert M Hs N g (e a)).1.mverts) := by
  intro i hi
  have hm : (cutCert M Hs N g (e a)).1.mverts = {M.tail (e a)} := by
    show (SPath.point (M' := M) (e a) (M.tail (e a))).toH.mverts = _
    rw [SPath.toH_mverts, SPath.point_verts]
  rw [hm, mem_newHole_singleton, ← hkey i hi a ha, tg_ne]

end Pure

/-! ### The program -/

/-- One index (`4957 = i`, `4958 = 1`). -/
def cbBodyC : Stmt :=
  block [.addN 4960 4951 4957, .loadN 4960 4960, .divN 4960 4960 4960,
    .addN 4961 4952 4957, .loadN 4961 4961, .addN 4961 4961 4958, .mulN 4961 4961 4960,
    .addN 4962 4953 4957, .loadN 4962 4962, .subN 4963 4962 4954, .subN 4962 4954 4962,
    .addN 4962 4963 4962, .divN 4962 4962 4962, .subN 4962 4958 4962,
    .addN 4963 4955 4957, .storeN 4963 4961,
    .addN 4963 4956 4957, .storeN 4963 4962,
    .addN 4957 4957 4958]

/-- **The cut base**: the item labels and the new-hole flags; then the registers of `bpProg`. -/
def cbProg : Stmt :=
  .seq (block [.constN 4958 1, .constN 4957 0])
    (.seq (.whileLtN 4957 4950 cbBodyC)
      (block [.addN 4944 4950 4958, .addN 4944 4944 4958, .copyN 4943 4956, .copyN 4502 4955]))

section Exec

variable {P : Input} {W : ℕ}

theorem cbBodyC_exec (c : Config) (hc : WordsBounded W c) {NFb LABb TKb TKa ITEMb NHb i : ℕ}
    (r1 : c.nreg 4951 = NFb) (r2 : c.nreg 4952 = LABb) (r3 : c.nreg 4953 = TKb)
    (r4 : c.nreg 4954 = TKa) (r5 : c.nreg 4955 = ITEMb) (r6 : c.nreg 4956 = NHb)
    (r7 : c.nreg 4957 = i) (r8 : c.nreg 4958 = 1)
    (w1 : NFb + i ≤ W) (w2 : LABb + i ≤ W) (w3 : TKb + i ≤ W) (w4 : ITEMb + i ≤ W)
    (w5 : NHb + i ≤ W) (w6 : i + 1 ≤ W) (w7 : c.nmem (LABb + i) + 1 ≤ W) :
    ∃ c' t, Exec P W cbBodyC c c' t ∧ t = 19 ∧ c'.nreg 4957 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (ITEMb + i) (lpV (c.nmem (NFb + i)) (c.nmem (LABb + i))))
        (NHb + i) (1 - phNe (c.nmem (TKb + i)) TKa) ∧
      (∀ x, (x < 4957 ∨ (4957 < x ∧ x < 4960) ∨ 4963 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have htk := hc.2 (TKb + i)
  have hJ := hc.1 4954
  rw [r4] at hJ
  have hne : (c.nmem (TKb + i) - TKa + (TKa - c.nmem (TKb + i))) /
      (c.nmem (TKb + i) - TKa + (TKa - c.nmem (TKb + i))) = phNe (c.nmem (TKb + i)) TKa := rfl
  have hv : (c.nmem (LABb + i) + 1) * (c.nmem (NFb + i) / c.nmem (NFb + i)) =
      lpV (c.nmem (NFb + i)) (c.nmem (LABb + i)) := rfl
  have hv1 := lpV_le (c.nmem (NFb + i)) (c.nmem (LABb + i))
  have hne1 : phNe (c.nmem (TKb + i)) TKa ≤ 1 := by rw [phNe_eq]; split_ifs <;> omega
  have ha1 : c.nmem (NFb + i) / c.nmem (NFb + i) ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have hW1 : 1 ≤ W := by omega
  unfold cbBodyC
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4, r5, r6, r7, r8, hne, hv]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r7, r8]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, hne, hv]
  · obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4957 ∧ x ≠ 4960 ∧ x ≠ 4961 ∧ x ≠ 4962 ∧ x ≠ 4963 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]

/-- **The cut base on the machine**: within `22 n + 10` steps `ITEM[i] = lpV NF[i] LAB[i]`,
`NH[i] = 1 - phNe TK[i] TKa`; `r4944 = n + 2`, `r4943 = NHb`, `r4502 = ITEMb`; memory outside
`ITEM`, `NH` kept, registers outside `4957 … 4963`, `4943`, `4944`, `4502` kept. -/
theorem cbProg_exec (c : Config) (hc : WordsBounded W c) {n NFb LABb TKb TKa ITEMb NHb : ℕ}
    (r0 : c.nreg 4950 = n) (r1 : c.nreg 4951 = NFb) (r2 : c.nreg 4952 = LABb)
    (r3 : c.nreg 4953 = TKb) (r4 : c.nreg 4954 = TKa) (r5 : c.nreg 4955 = ITEMb)
    (r6 : c.nreg 4956 = NHb)
    (lay : NFb + n ≤ W ∧ LABb + n ≤ W ∧ TKb + n ≤ W ∧ ITEMb + n ≤ NHb ∧ NHb + n ≤ W ∧
      n + 2 ≤ W)
    (hlab : ∀ i < n, c.nmem (LABb + i) + 1 ≤ W)
    (hdis : ∀ i < n, (NFb + i < ITEMb ∨ NHb + n ≤ NFb + i) ∧
      (LABb + i < ITEMb ∨ NHb + n ≤ LABb + i) ∧ (TKb + i < ITEMb ∨ NHb + n ≤ TKb + i)) :
    ∃ c' t, Exec P W cbProg c c' t ∧ t ≤ 22 * n + 10 ∧
      (∀ i < n, c'.nmem (ITEMb + i) = lpV (c.nmem (NFb + i)) (c.nmem (LABb + i))) ∧
      (∀ i < n, c'.nmem (NHb + i) = 1 - phNe (c.nmem (TKb + i)) TKa) ∧
      c'.nreg 4944 = n + 2 ∧ c'.nreg 4943 = NHb ∧ c'.nreg 4502 = ITEMb ∧
      (∀ a, (a < ITEMb ∨ NHb + n ≤ a ∨ (ITEMb + n ≤ a ∧ a < NHb)) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 4943 → x ≠ 4944 → x ≠ 4502 → (x < 4957 ∨ 4963 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  unfold cbProg
  obtain ⟨c₁, k₁, e₁, hk₁, g58, g57, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4958 1, .constN 4957 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4958 = 1 ∧ c₁.nreg 4957 = 0 ∧
      (∀ x, x ≠ 4957 → x ≠ 4958 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, by config_simp, by config_simp, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2]
  have hw₁ := e₁.wb_right
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4957 ∨ (4957 < x ∧ x < 4960) ∨ 4963 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (ITEMb + j) = lpV (m₀ (NFb + j)) (m₀ (LABb + j))) ∧
    (∀ j < i, c'.nmem (NHb + j) = 1 - phNe (m₀ (TKb + j)) TKa) ∧
    (∀ a, ¬ (ITEMb ≤ a ∧ a < ITEMb + i) → ¬ (NHb ≤ a ∧ a < NHb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h57, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P)
    (a := 4957) (b := 4950) (body := cbBodyC) J (lo := 0) (hi := n) (B := 19) c₁ hw₁ g57
    (by rw [gn₁ _ (by omega) (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h57 h50 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have f : ∀ x, (x < 4957 ∨ (4957 < x ∧ x < 4960) ∨ 4963 < x) → c'.nreg x = c₁.nreg x := j1
      have q : ∀ x, (x < 4957 ∨ 4963 < x) → x ≠ 4958 → c'.nreg x = c.nreg x := fun x hx h =>
        by rw [f x (by omega), gn₁ x (by omega) h]
      have e1 : c'.nmem (NFb + i) = m₀ (NFb + i) := j4 _
        (by have := hdis i hhi; omega) (by have := hdis i hhi; omega)
      have e2 : c'.nmem (LABb + i) = m₀ (LABb + i) := j4 _
        (by have := hdis i hhi; omega) (by have := hdis i hhi; omega)
      have e3 : c'.nmem (TKb + i) = m₀ (TKb + i) := j4 _
        (by have := hdis i hhi; omega) (by have := hdis i hhi; omega)
      obtain ⟨c'', t, ex, ht, h57', hm', hn', hr', hrm', ho'⟩ :=
        cbBodyC_exec (P := P) (i := i) c' hw (by rw [q _ (by omega) (by omega), r1])
        (by rw [q _ (by omega) (by omega), r2]) (by rw [q _ (by omega) (by omega), r3])
        (by rw [q _ (by omega) (by omega), r4]) (by rw [q _ (by omega) (by omega), r5])
        (by rw [q _ (by omega) (by omega), r6]) h57 (by rw [f _ (by omega), g58])
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [e2]; exact hlab i hhi)
      rw [e1, e2, e3] at hm'
      refine ⟨c'', t, ex, ht.le, h57', by rw [hn' _ (by omega)]; exact h50,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun j hj => ?_,
        fun a h1 h2 => ?_, by rw [hr', j5], by rw [hrm', j6], by rw [ho', j7]⟩
      · rw [hm', upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j4 a (by omega) (by omega))
  obtain ⟨c₃, k₃, e₃, hk₃, h44, h43, h02, gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4944 4950 4958, .addN 4944 4944 4958, .copyN 4943 4956,
        .copyN 4502 4955]) c₂ c₃ k₃ ∧ k₃ = 4 ∧ c₃.nreg 4944 = n + 2 ∧ c₃.nreg 4943 = NHb ∧
      c₃.nreg 4502 = ITEMb ∧
      (∀ x, x ≠ 4943 → x ≠ 4944 → x ≠ 4502 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have q50 : c₂.nreg 4950 = n := by rw [j1 _ (by omega), gn₁ _ (by omega) (by omega), r0]
    have q58 : c₂.nreg 4958 = 1 := by rw [j1 _ (by omega), g58]
    have q56 : c₂.nreg 4956 = NHb := by rw [j1 _ (by omega), gn₁ _ (by omega) (by omega), r6]
    have q55 : c₂.nreg 4955 = ITEMb := by rw [j1 _ (by omega), gn₁ _ (by omega) (by omega), r5]
    exec_block
    all_goals try (config_simp; (try simp only [q50, q58, q56, q55]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [q50, q58, q56, q55]
    · config_simp; simp only [q50, q58, q56, q55]
    · config_simp; simp only [q50, q58, q56, q55]
    · simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi => by rw [gm₃, j2 i hi],
    fun i hi => by rw [gm₃, j3 i hi], h44, h43, h02,
    fun a ha => by rw [gm₃, j4 a (by omega) (by omega)],
    fun x h1 h2 h3 hx => by rw [gn₃ x h1 h2 h3, j1 x (by omega), gn₁ x (by omega) (by omega)],
    by rw [gr₃, j5, gr₁], by rw [grm₃, j6, grm₁], by rw [go₃, j7, go₁]⟩

end Exec

/-! ### The cut branch of `scertD`: the base and the backward pass -/

/-- The registers of `cbProg` from those of the level (`TKa := TK[r4902]`). -/
def scPrep : Stmt :=
  block [.copyN 4950 4840, .copyN 4951 4841, .copyN 4952 4849, .copyN 4953 4422,
    .addN 4963 4422 4902, .loadN 4954 4963]

/-- **The cut branch**: the items and flags of the cut, then the records applied backwards. -/
def scCut : Stmt := .seq scPrep (.seq cbProg bpProg)

section Cut

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

theorem scPrep_exec (c : Config) (hc : WordsBounded W c) {n b nH A W₀ a : ℕ}
    (hR : LvRegs c n b nH A W₀) (r02 : c.nreg 4902 = a) (w : b + 6 * n + a ≤ W) :
    ∃ c' t, Exec P W scPrep c c' t ∧ t = 6 ∧ c'.nreg 4950 = n ∧ c'.nreg 4951 = b ∧
      c'.nreg 4952 = b + 13 * n + 1 ∧ c'.nreg 4953 = b + 6 * n ∧
      c'.nreg 4954 = c.nmem (b + 6 * n + a) ∧
      (∀ x, (x < 4950 ∨ (4954 < x ∧ x < 4963) ∨ 4963 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h0 := hR.p0
  have h1 := hR.p1
  have h9 := hR.p9
  have h22 := hR.r2
  unfold scPrep
  exec_block
  all_goals try (config_simp; (try simp only [h0, h1, h9, h22, r02]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [h0, h1, h9, h22, r02])
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ : x ≠ 4950 ∧ x ≠ 4951 ∧ x ≠ 4952 ∧ x ≠ 4953 ∧ x ≠ 4954 ∧
      x ≠ 4963 := by omega
  simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
    upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6]

open Classical in
/-- **The cut branch of `scertD` on the machine**: after the level loop at a state `s` of kind
`2` (labels of the components off `g` in `LAB`, in `(0, n]`; anchor index `a₁ = r4902`) with
the records `rs` of `scIter ch Hs ℓ s₀ = some (s, rs)` stored (`RecOK`), within
`ℓ (7 n + 40) + 22 n + 22` steps the labels at `ITEMb` represent
`applyPr Hs ρ rs (s.1.image (comp M s.1 Hs g))` for the cut path `ρ = (cutCert M Hs s.1 g (e a₁)).1`. -/
theorem scCut_exec {ch : ScChoice M} {Hs : List (Finset V)} {ℓ : ℕ} {s₀ s : ScSt D}
    {rs : List (ScRec D)} (hiter : scIter ch Hs ℓ s₀ = some (s, rs)) {e : ℕ → D}
    {B : Finset D} {g : Finset V} {n b A W₀ a₁ RECb IX0 top ITEMb NHb : ℕ}
    (c : Config) (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hIn : LvIn M c.nmem n b e B s.1 Hs s.2.2) (r02 : c.nreg 4902 = a₁) (ha₁ : a₁ < n)
    (hlabN : ∀ i < n, ∀ j < n, e i ∈ s.1 → (c.nmem (b + 13 * n + 1 + i) =
      c.nmem (b + 13 * n + 1 + j) ↔ e j ∈ comp M s.1 Hs g (e i)))
    (hpos : ∀ i < n, 0 < c.nmem (b + 13 * n + 1 + i) ∧ c.nmem (b + 13 * n + 1 + i) ≤ n)
    (r33 : c.nreg 4933 = ℓ) (r36 : c.nreg 4936 = RECb) (r55 : c.nreg 4955 = ITEMb)
    (r56 : c.nreg 4956 = NHb) (hrec : RecOK c.nmem RECb IX0 top n e rs)
    (lay : b + 20 * n + 3 ≤ ITEMb ∧ ITEMb + n ≤ NHb ∧ NHb + n ≤ W ∧
      (RECb + 3 * ℓ ≤ ITEMb ∨ NHb + n ≤ RECb) ∧ (top ≤ ITEMb ∨ NHb + n ≤ IX0) ∧ top ≤ W ∧
      RECb + 3 * ℓ ≤ W ∧ n + 2 + ℓ ≤ W) :
    ∃ c' t, Exec P W scCut c c' t ∧ t ≤ ℓ * (7 * n + 40) + 22 * n + 22 ∧
      ItemRep e n (applyPr Hs (cutCert M Hs s.1 g (e a₁)).1 rs (s.1.image (comp M s.1 Hs g)))
        (fun i => c'.nmem (ITEMb + i)) ∧
      (∀ a, (a < ITEMb ∨ NHb + n ≤ a ∨ (ITEMb + n ≤ a ∧ a < NHb)) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4500 ∨ (4511 < x ∧ x < 4940) ∨ (4947 < x ∧ x < 4950) ∨ 4963 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lay
  have hlen : rs.length = ℓ := (scIter_depth ch Hs ℓ s₀ s rs hiter).2
  have hsurjN : ∀ d ∈ s.1, ∃ i < n, e i = d := fun d hd => hIn.surj d (hIn.sub hd)
  obtain ⟨c₁, k₁, e₁, hk₁, p50, p51, p52, p53, p54, pn₁, pm₁, pr₁, prm₁, po₁⟩ :=
    scPrep_exec (P := P) c hc hR r02 (by omega)
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, C1, C2, C44, C43, C02, Cm, Cn, Cr, Crm, Co⟩ := cbProg_exec (P := P) c₁ hw₁
    p50 p51 p52 p53 p54 (by rw [pn₁ _ (by omega)]; exact r55) (by rw [pn₁ _ (by omega)]; exact r56)
    ⟨by omega, by omega, by omega, l2, l3, by omega⟩
    (fun i hi => by rw [pm₁]; have := (hpos i hi).2; omega)
    (fun i hi => ⟨by omega, by omega, by omega⟩)
  rw [pm₁] at C1 C2
  have hw₂ := e₂.wb_right
  have m₂ : ∀ a, (a < ITEMb ∨ NHb + n ≤ a ∨ (ITEMb + n ≤ a ∧ a < NHb)) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [Cm a ha, pm₁]
  have hrep : ItemRep e n (s.1.image (comp M s.1 Hs g)) fun i => c₂.nmem (ITEMb + i) := by
    have h := cut_itemRep (M := M) (g := g) hsurjN (nf := fun i => c.nmem (b + i))
      (lab := fun i => c.nmem (b + 13 * n + 1 + i)) hIn.nf hlabN
    unfold ItemRep at h ⊢
    rw [h]
    exact labItems_congr fun i hi => (C1 i hi).symm
  have hNH : ∀ i < n, (c₂.nmem (NHb + i) ≠ 0 ↔
      M.tail (e i) ∈ newHole Hs (cutCert M Hs s.1 g (e a₁)).1.mverts) := fun i hi => by
    rw [C2 i hi]
    exact cut_nh (N := s.1) (g := g) (tk := fun i => c.nmem (b + 6 * n + i)) ha₁ hIn.key i hi
  have hsub : ∀ X ∈ s.1.image (comp M s.1 Hs g), X ⊆ s.1 := by
    intro X hX
    obtain ⟨x, -, rfl⟩ := mem_image.1 hX
    exact fun d hd => (mem_comp.1 hd).1
  have q : ∀ x, x ≠ 4943 → x ≠ 4944 → x ≠ 4502 → (x < 4950 ∨ 4963 < x) →
      c₂.nreg x = c.nreg x := fun x h1 h2 h3 hx => by
    rw [Cn x h1 h2 h3 (by omega), pn₁ x (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, B1, -, B4, Bn, B5, B6, B7⟩ := bpProg_exec (P := P) hiter
    (ρ := (cutCert M Hs s.1 g (e a₁)).1) hIn.inj c₂ hw₂
    (by rw [q _ (by omega) (by omega) (by omega) (by omega)]; exact r33)
    (by rw [q _ (by omega) (by omega) (by omega) (by omega)]; exact r36) C43 C44 C02
    (hrec.congr le_rfl (fun a h1 h2 => m₂ a (by omega)) (fun a h1 h2 => m₂ a (by omega)))
    hNH hrep hsub (by omega) (fun i hi => by
      rw [C1 i hi]; have := lpV_le (c.nmem (b + i)) (c.nmem (b + 13 * n + 1 + i))
      have := (hpos i hi).2; omega)
    ⟨by omega, by omega, Or.inr (by omega), by omega, by omega, l6, l7, by omega, by omega⟩
  have hcost : k₁ + (k₂ + k₃) ≤ ℓ * (7 * n + 40) + 22 * n + 22 := by omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), hcost, B1, fun a ha => ?_,
    fun x hx => ?_, by rw [B5, Cr, pr₁], by rw [B6, Crm, prm₁], by rw [B7, Co, po₁]⟩
  · rw [B4 a (by omega), m₂ a ha]
  · rw [Bn x (by unfold BpFr; omega), q x (by omega) (by omega) (by omega) (by omega)]

end Cut

end BKMNW

end PlanarFlow
