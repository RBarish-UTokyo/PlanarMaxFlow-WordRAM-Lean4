module

public import PlanarFlow.BKMNW.SmOut

/-!
# One step of `smD` on the machine: the whole program

* `smT` (the tag of the left child, `smNode` of the five sums of `smO`, at `Ob + 3 n + k`, and
  `0` at `Ob + 3 n + k + 1`), `smT_exec`;
* `smHBody`, `smH` (the hole flags `HM[j] = smCVf (j + 1) t1 t2 up` at `Ob + 3 n + j`, `j < k`),
  `smH_exec`;
* **`smStep := smI ; smA ; smDsp ; smO ; smT ; smH`**, **`smStep_exec`** (within
  `252 n + 19 k + 78` steps: the outputs of the four parts in the final memory).

Registers: inputs `5300 = n`, `5301 = PFb`, `5302 = RVb`, `5303 = THb`, `5304 = KRb`,
`5305 = VTb`, `5306 = Ob`, `5307 = k`; written `5308 … 5440`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The bases `5308 = Ob + n`, `5309 = Ob + 2 n`, `5440 = Ob + 3 n`. -/
def smI : Stmt := block [.addN 5308 5306 5300, .addN 5309 5308 5300, .addN 5440 5309 5300]

/-- The tag of the left child and the tag `0` of the right child. -/
def smT : Stmt :=
  block [.subN 5423 5378 5310, .subN 5420 5378 5423, .subN 5423 5379 5310, .subN 5421 5379 5423,
    .subN 5423 5377 5310, .subN 5422 5377 5423,
    .subN 5424 5376 5311, .subN 5423 5424 5310, .subN 5424 5424 5423,
    .subN 5423 5380 5310, .subN 5425 5380 5423,
    .subN 5426 5310 5421, .addN 5426 5426 5420, .addN 5426 5426 5425, .subN 5423 5426 5310,
    .subN 5426 5426 5423,
    .subN 5423 5310 5422, .subN 5427 5424 5423, .subN 5423 5310 5426, .subN 5427 5427 5423,
    .addN 5428 5440 5307, .storeN 5428 5427, .addN 5428 5428 5310, .storeN 5428 5313]

/-- One hole flag. -/
def smHBody : Stmt :=
  block [.addN 5431 5430 5310,
    .subN 5433 5431 5370, .subN 5432 5370 5431, .addN 5433 5433 5432, .subN 5432 5310 5433,
    .subN 5433 5431 5371, .subN 5434 5371 5431, .addN 5433 5433 5434, .subN 5434 5310 5433,
    .subN 5433 5310 5434, .subN 5434 5366 5433, .addN 5432 5432 5434,
    .subN 5433 5432 5310, .subN 5432 5432 5433,
    .addN 5433 5440 5430, .storeN 5433 5432, .addN 5430 5430 5310]

/-- **The hole flags.** -/
def smH : Stmt := .seq (block [.constN 5430 0]) (.whileLtN 5430 5307 smHBody)

/-- **One step of `smD`.** -/
def smStep : Stmt := .seq smI (.seq smA (.seq smDsp (.seq smO (.seq smT smH))))

section Fin

variable {P : Input} {W : ℕ}

theorem smI_exec (c : Config) (hc : WordsBounded W c) {n Ob : ℕ} (r0 : c.nreg 5300 = n)
    (r6 : c.nreg 5306 = Ob) (w : Ob + 3 * n ≤ W) :
    ∃ c' t, Exec P W smI c c' t ∧ t = 3 ∧ c'.nreg 5308 = Ob + n ∧ c'.nreg 5309 = Ob + 2 * n ∧
      c'.nreg 5440 = Ob + 3 * n ∧
      (∀ x, (x < 5308 ∨ (5309 < x ∧ x < 5440) ∨ 5440 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smI
  exec_block
  all_goals try (config_simp; (try simp only [r0, r6]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r0, r6]); first | done | omega)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smT_exec (c : Config) (hc : WordsBounded W c) {T3 k : ℕ} (hW : 3 ≤ W)
    (r07 : c.nreg 5307 = k) (r10 : c.nreg 5310 = 1) (r11 : c.nreg 5311 = 2)
    (r12 : c.nreg 5440 = T3) (r13 : c.nreg 5313 = 0) (w : T3 + k + 1 ≤ W) :
    ∃ c' t, Exec P W smT c c' t ∧ t = 24 ∧
      c'.nmem = upd (upd c.nmem (T3 + k) (smNode (c.nreg 5376) (c.nreg 5380)
        (smSg (c.nreg 5378)) (smSg (c.nreg 5379)) (smSg (c.nreg 5377)))) (T3 + k + 1) 0 ∧
      (∀ x, (x < 5420 ∨ 5428 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smT
  exec_block
  all_goals try (config_simp; (try simp only [r07, r10, r11, r12, r13]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r07, r10, r11, r12, r13]
  · config_simp; simp (disch := omega) only [upd_other]

theorem smHBody_exec (c : Config) (hc : WordsBounded W c) {T3 j : ℕ} (hW : 2 ≤ W)
    (r10 : c.nreg 5310 = 1) (r12 : c.nreg 5440 = T3) (r30 : c.nreg 5430 = j)
    (hup : c.nreg 5366 ≤ 1) (w1 : T3 + j ≤ W) (w2 : j + 1 ≤ W) :
    ∃ c' t, Exec P W smHBody c c' t ∧ t = 17 ∧ c'.nreg 5430 = j + 1 ∧
      c'.nmem = upd c.nmem (T3 + j) (smCVf (j + 1) (c.nreg 5370) (c.nreg 5371) (c.nreg 5366)) ∧
      (∀ x, (x < 5430 ∨ 5434 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := hc.1 5370; have b2 := hc.1 5371
  unfold smHBody
  exec_block
  all_goals try (config_simp; (try simp only [r10, r12, r30]); omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r12, r30]
  · config_simp; simp only [r10, r12, r30]
  · config_simp; simp (disch := omega) only [upd_other]

/-- **The hole flags**: within `19 k + 3` steps, `HM[j] = smCVf (j + 1) t1 t2 up` at
`T3 + j` (`j < k`); memory outside `[T3, T3 + k)` kept. -/
theorem smH_exec (c : Config) (hc : WordsBounded W c) {T3 k : ℕ} (hW : 2 ≤ W)
    (r07 : c.nreg 5307 = k) (r10 : c.nreg 5310 = 1) (r12 : c.nreg 5440 = T3)
    (hup : c.nreg 5366 ≤ 1) (w1 : T3 + k ≤ W) (w2 : k + 1 ≤ W) :
    ∃ c' t, Exec P W smH c c' t ∧ t ≤ 19 * k + 3 ∧
      (∀ j < k, c'.nmem (T3 + j) =
        smCVf (j + 1) (c.nreg 5370) (c.nreg 5371) (c.nreg 5366)) ∧
      (∀ a, (a < T3 ∨ T3 + k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5430 ∨ 5434 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smH
  obtain ⟨c₁, k₁, e₁, hk₁, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5430 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 5430 = 0 ∧
      (∀ x, x ≠ 5430 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 5430 → c₁.nreg x = c.nreg x := gn₁
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5430 ∨ 5434 < x) → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (T3 + j) = smCVf (j + 1) (c.nreg 5370) (c.nreg 5371) (c.nreg 5366)) ∧
    (∀ a, (a < T3 ∨ T3 + k ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5430) (b := 5307) (body := smHBody) J (B := 17) c₁ hw₁ g30
    (by rw [q _ (by omega), r07]) (Nat.zero_le k)
    ⟨fun x hx => q x (by omega), fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁],
      gr₁, grm₁, go₁⟩
    (fun i c' hlo hhi hw h30 h07 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      obtain ⟨c'', t, ex, ht, b30, bm, bn, br, brm, bo⟩ :=
        smHBody_exec (P := P) c' hw (T3 := T3) (j := i) hW (by rw [j1 _ (by omega), r10])
          (by rw [j1 _ (by omega), r12]) h30 (by rw [j1 _ (by omega)]; exact hup) (by omega)
          (by omega)
      rw [j1 _ (by omega), j1 _ (by omega), j1 _ (by omega)] at bm
      refine ⟨c'', t, ex, by omega, b30, by rw [bn _ (by omega)]; exact h07,
        fun x hx => by rw [bn x (by omega), j1 x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [br, j4], by rw [brm, j5], by rw [bo, j6]⟩
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [bm, upd_other _ _ _ (by omega)]; exact j3 a ha)
  exact ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j1, j4, j5, j6⟩

/-- **The classification and the choice of one step**: the output of the scan (`SmAOut`, at a
configuration `cA`), the node bit `nd`, and the words `s` of the split in the three cases. -/
def SmChoice (m : ℕ → ℕ) (PFb RVb THb KRb VTb n nd : ℕ) (s : SmSV) : Prop :=
  ∃ cA : Config, SmAOut m PFb RVb THb KRb VTb n cA ∧
    nd = smNode (cA.nreg 5315) (cA.nreg 5316) (cA.nreg 5317) (cA.nreg 5323) (cA.nreg 5327) ∧
    s.up ≤ 1 ∧ s.lpm ≤ 1 ∧
    (nd ≠ 0 → cA.nreg 5317 = 1 → s = ⟨cA.nreg 5318, cA.nreg 5319, 1, 0, cA.nreg 5320,
      cA.nreg 5321, 0, cA.nreg 5322⟩) ∧
    (nd ≠ 0 → cA.nreg 5317 = 0 → cA.nreg 5323 = 1 → s = ⟨cA.nreg 5324, 0, 0, 1, cA.nreg 5325,
      0, cA.nreg 5326, 0⟩) ∧
    (nd ≠ 0 → cA.nreg 5317 = 0 → cA.nreg 5323 = 0 → s = ⟨cA.nreg 5328, cA.nreg 5329,
      1 - cA.nreg 5332, 0, cA.nreg 5330, cA.nreg 5331, 0, cA.nreg 5333⟩)

lemma smSel_eq {c : Config} {a a' up lpm v1 v2 t1 t2 : ℕ} (h : SmSel c a a' up lpm v1 v2 t1 t2) :
    (⟨c.nreg 5364, c.nreg 5365, c.nreg 5366, c.nreg 5367, c.nreg 5368, c.nreg 5369, c.nreg 5370,
      c.nreg 5371⟩ : SmSV) = ⟨a, a', up, lpm, v1, v2, t1, t2⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

set_option maxHeartbeats 1600000 in
/-- **One step of `smD` on the machine** (see the module docstring): within
`252 n + 19 k + 78` steps, the node bit `5360`, the words `s` of the split (`SmChoice`), and in
memory `LP`, `PD`, `CV` (`Ob`, `Ob + n`, `Ob + 2 n`), the hole flags (`Ob + 3 n + j`), the tags
(`Ob + 3 n + k`, `Ob + 3 n + k + 1`); memory outside `[Ob, Ob + 3 n + k + 2)` and registers
outside `5308 … 5440` kept. -/
theorem smStep_exec (c : Config) (hc : WordsBounded W c) {n PFb RVb THb KRb VTb Ob k : ℕ}
    (r0 : c.nreg 5300 = n) (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb)
    (r3 : c.nreg 5303 = THb) (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb)
    (r6 : c.nreg 5306 = Ob) (r7 : c.nreg 5307 = k) (hW : 3 ≤ W)
    (w1 : PFb + n ≤ Ob) (w2 : RVb + n ≤ Ob) (w3 : THb + n ≤ Ob) (w4 : KRb + n ≤ Ob)
    (w5 : VTb + n ≤ Ob) (w6 : Ob + 3 * n + k + 2 ≤ W) (w7 : n + 1 ≤ W)
    (hrv : ∀ i < n, c.nmem (RVb + i) < n) :
    ∃ c' t, Exec P W smStep c c' t ∧ t ≤ 252 * n + 19 * k + 78 ∧
      ∃ s : SmSV, SmChoice c.nmem PFb RVb THb KRb VTb n (c'.nreg 5360) s ∧
      (∀ j < n, c'.nmem (Ob + j) = smLPw (smW c.nmem PFb RVb THb KRb VTb j) s j) ∧
      (∀ j < n, c'.nmem (Ob + n + j) = smPDw s j) ∧
      (∀ j < n, c'.nmem (Ob + 2 * n + j) = smCVw (smW c.nmem PFb RVb THb KRb VTb j) s) ∧
      (∀ j < k, c'.nmem (Ob + 3 * n + j) = smCVf (j + 1) s.t1 s.t2 s.up) ∧
      c'.nmem (Ob + 3 * n + k) = smNode
        (∑ j ∈ range n, smLPw (smW c.nmem PFb RVb THb KRb VTb j) s j)
        (∑ j ∈ range n, smJ2w (smW c.nmem PFb RVb THb KRb VTb j) s j)
        (smSg (∑ j ∈ range n, smX2w (smW c.nmem PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smY2w (smW c.nmem PFb RVb THb KRb VTb j) s j))
        (smSg (∑ j ∈ range n, smB2w (smW c.nmem PFb RVb THb KRb VTb j) s j)) ∧
      c'.nmem (Ob + 3 * n + k + 1) = 0 ∧
      (∀ a, (a < Ob ∨ Ob + 3 * n + k + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5308 ∨ 5440 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, i08, i09, i12, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    smI_exec (P := P) c hc r0 r6 (by omega)
  have hw₁ := e₁.wb_right
  have q₁ : ∀ x, (x < 5308 ∨ (5309 < x ∧ x < 5440) ∨ 5440 < x) → c₁.nreg x = c.nreg x := n₁
  obtain ⟨c₂, t₂, e₂, ht₂, hA, a10, a11, a13, a14, n₂, m₂, rr₂, rm₂, o₂⟩ :=
    smA_exec (P := P) c₁ hw₁ (n := n) (PFb := PFb) (RVb := RVb) (THb := THb) (KRb := KRb)
      (VTb := VTb) (by rw [q₁ _ (by omega), r0]) (by rw [q₁ _ (by omega), r1])
      (by rw [q₁ _ (by omega), r2]) (by rw [q₁ _ (by omega), r3]) (by rw [q₁ _ (by omega), r4])
      (by rw [q₁ _ (by omega), r5]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) w7 (by rw [m₁]; exact hrv)
  have hw₂ := e₂.wb_right
  have q₂ : ∀ x, (x < 5310 ∨ 5353 < x) → c₂.nreg x = c₁.nreg x := n₂
  rw [m₁] at hA
  obtain ⟨c₃, t₃, e₃, ht₃, d60, d66, d67, dX, dY, dB, n₃, m₃, rr₃, rm₃, o₃⟩ :=
    smDsp_exec (P := P) c₂ hw₂ hW a10 a11 a13 hA.fx.1 hA.fy.1
  have hw₃ := e₃.wb_right
  have q₃ : ∀ x, (x < 5360 ∨ 5375 < x) → c₃.nreg x = c₂.nreg x := n₃
  have s₃ : ∀ x, (x < 5310 ∨ (5375 < x)) → x ≠ 5308 → x ≠ 5309 → x ≠ 5440 →
      c₃.nreg x = c.nreg x := fun x hx h1 h2 h3 => by
    rw [q₃ _ (by omega), q₂ _ (by omega), q₁ _ (by omega)]
  have hm₃ : c₃.nmem = c.nmem := by rw [m₃, m₂, m₁]
  obtain ⟨c₄, t₄, e₄, ht₄, hO, n₄, rr₄, rm₄, o₄⟩ :=
    smO_exec (P := P) c₃ hw₃ (n := n) (PFb := PFb) (RVb := RVb) (THb := THb) (KRb := KRb)
      (VTb := VTb) (Ob := Ob) (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r0])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r1])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r2])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r3])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r4])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r5])
      (by rw [s₃ _ (by omega) (by omega) (by omega) (by omega), r6])
      (by rw [q₃ _ (by omega), q₂ _ (by omega), i08])
      (by rw [q₃ _ (by omega), q₂ _ (by omega), i09])
      (by rw [q₃ _ (by omega), a10]) (by rw [q₃ _ (by omega), a11]) d66 (by omega)
      w1 w2 w3 w4 w5 (by omega) w7 (by rw [hm₃]; exact hrv)
  have hw₄ := e₄.wb_right
  have q₄ : ∀ x, (x < 5314 ∨ (5353 < x ∧ x < 5376) ∨ 5399 < x) → c₄.nreg x = c₃.nreg x := n₄
  rw [hm₃] at hO
  set s : SmSV := ⟨c₃.nreg 5364, c₃.nreg 5365, c₃.nreg 5366, c₃.nreg 5367, c₃.nreg 5368,
    c₃.nreg 5369, c₃.nreg 5370, c₃.nreg 5371⟩ with hs
  obtain ⟨c₅, t₅, e₅, ht₅, mT, n₅, rr₅, rm₅, o₅⟩ :=
    smT_exec (P := P) c₄ hw₄ (T3 := Ob + 3 * n) (k := k) hW
      (by rw [q₄ _ (by omega), s₃ _ (by omega) (by omega) (by omega) (by omega), r7])
      (by rw [q₄ _ (by omega), q₃ _ (by omega), a10])
      (by rw [q₄ _ (by omega), q₃ _ (by omega), a11])
      (by rw [q₄ _ (by omega), q₃ _ (by omega), q₂ _ (by omega)]; exact i12)
      (by rw [q₄ _ (by omega), q₃ _ (by omega), a13]) (by omega)
  have hw₅ := e₅.wb_right
  have q₅ : ∀ x, (x < 5420 ∨ 5428 < x) → c₅.nreg x = c₄.nreg x := n₅
  obtain ⟨c₆, t₆, e₆, ht₆, hH, hHm, n₆, rr₆, rm₆, o₆⟩ :=
    smH_exec (P := P) c₅ hw₅ (T3 := Ob + 3 * n) (k := k) (by omega)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega) (by omega) (by omega) (by omega),
        r7])
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega), a10])
      (by rw [q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega), q₂ _ (by omega)]; exact i12)
      (by rw [q₅ _ (by omega), q₄ _ (by omega)]; exact d66) (by omega) (by omega)
  have q₆ : ∀ x, (x < 5430 ∨ 5434 < x) → c₆.nreg x = c₅.nreg x := n₆
  have hsel : ∀ x, 5364 ≤ x → x ≤ 5371 → c₅.nreg x = c₃.nreg x := fun x h1 h2 => by
    rw [q₅ _ (by omega), q₄ _ (by omega)]
  have hv : ∀ x, 5364 ≤ x → x ≤ 5371 → c₆.nreg x = c₃.nreg x := fun x h1 h2 => by
    rw [q₆ _ (by omega), hsel x h1 h2]
  have hmem : ∀ a, (a < Ob + 3 * n ∨ Ob + 3 * n + k + 2 ≤ a) → c₆.nmem a = c₄.nmem a :=
    fun a ha => by
      rw [hHm a (by omega), mT, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, s,
    ⟨c₂, hA, ?_, d66, d67, fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, fun a ha => ?_,
    fun x hx => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), d60]
  · have e60 : c₃.nreg 5360 ≠ 0 := by
      rw [show c₃.nreg 5360 = c₆.nreg 5360 by rw [q₆ _ (by omega), q₅ _ (by omega),
        q₄ _ (by omega)]]; exact h1
    exact smSel_eq (dX e60 h2)
  · have e60 : c₃.nreg 5360 ≠ 0 := by
      rw [show c₃.nreg 5360 = c₆.nreg 5360 by rw [q₆ _ (by omega), q₅ _ (by omega),
        q₄ _ (by omega)]]; exact h1
    exact smSel_eq (dY e60 h2 h3)
  · have e60 : c₃.nreg 5360 ≠ 0 := by
      rw [show c₃.nreg 5360 = c₆.nreg 5360 by rw [q₆ _ (by omega), q₅ _ (by omega),
        q₄ _ (by omega)]]; exact h1
    exact smSel_eq (dB e60 h2 h3)
  · rw [hmem _ (by omega)]; exact hO.lp j hj
  · rw [hmem _ (by omega), show Ob + n + j = Ob + n + j from rfl]; exact hO.pd j hj
  · rw [hmem _ (by omega)]; exact hO.cv j hj
  · rw [hH j hj, hsel 5370 (by omega) (by omega), hsel 5371 (by omega) (by omega),
      hsel 5366 (by omega) (by omega)]
  · rw [hHm _ (by omega), mT, upd_other _ _ _ (by omega), upd_same,
      show c₄.nreg 5376 = _ from hO.sl, show c₄.nreg 5380 = _ from hO.sj,
      show c₄.nreg 5378 = _ from hO.sx, show c₄.nreg 5379 = _ from hO.sy,
      show c₄.nreg 5377 = _ from hO.sb]
  · rw [hHm _ (by omega), mT, upd_same]
  · rcases ha with ha | ha
    · rw [hmem _ (by omega), hO.mem a (Or.inl ha)]
    · rw [hmem _ (by omega), hO.mem a (Or.inr (by omega))]
  · rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega), q₂ _ (by omega),
      q₁ _ (by omega)]


end Fin

end BKMNW

end PlanarFlow
