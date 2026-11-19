module

public import PlanarFlow.BKMNW.NcFzC

/-!
# The pendant frame writer `pfP`: stage 2

`pfS2 = dvG ; dvP ; dvR ; RF ; lkG ; lkProg ; pfB1 ; pfB2` (**`pfS2_exec`**, `67 m + 80` steps),
from the result of stage 1 (`St1`):

* `dvP` on the fake frame at `S + 8`: `LAB[i] = olab SG i + 1`, `DV[v] = Σ_{olab j = v} X0[j]`,
  `DG[v] = #{j : olab j = v}`;
* `RF[i] = LAB[i] ∸ i` (`1` exactly at the representatives `olab i = i` of the vertices);
* `lkProg`: `n = cnt RF m` vertices, `CI[r] = cnt RF r` (the number of the vertex of the
  representative `r`), `IX[cnt RF r] = r`;
* the registers of the pendant frame (`Rg2`), its header `mem[d'] = m' = m + 2n`,
  `mem[d' + 3] = Z' = m Z`, and the saved base `mem[S + 6] = FL'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

variable {P : Input} {W : ℕ}

lemma permOn_congr {f g : ℕ → ℕ} {m : ℕ} (h : PermOn f m) (e : ∀ i < m, f i = g i) :
    PermOn g m :=
  ⟨fun i hi => e i hi ▸ h.lt i hi, fun i hi j hj h' => h.inj i hi j hj (by rw [e i hi, e j hj, h'])⟩

lemma cnt_congr {F G : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, F j = G j) : cnt F i = cnt G i := by
  unfold cnt
  rw [Finset.filter_congr (fun j hj => by rw [h j (Finset.mem_range.1 hj)])]

lemma cnt_le (F : ℕ → ℕ) (i : ℕ) : cnt F i ≤ i := by
  unfold cnt; exact (card_le_card (filter_subset _ _)).trans (by simp)

/-- The flow array of the fake frame (`F1` on the darts touching `Del`, `Z` elsewhere). -/
def x0F (mem : ℕ → ℕ) (F1b DFb RVb Z t : ℕ) : ℕ :=
  mem (F1b + t) * qF mem DFb RVb t + Z - Z * qF mem DFb RVb t

lemma x0F_le {mem : ℕ → ℕ} {F1b DFb RVb Z t : ℕ} (h : mem (F1b + t) ≤ 2 * Z) :
    x0F mem F1b DFb RVb Z t ≤ 2 * Z := by
  unfold x0F
  have h1 := qF_le_one mem DFb RVb t
  interval_cases (qF mem DFb RVb t) <;> simp <;> omega

/-- The representative flags. -/
noncomputable def rfF (sg : ℕ → ℕ) (i : ℕ) : ℕ := (olab sg i + 1) - i

/-- **The layout registers of the pendant frame** (stage 2). -/
structure Rg2 (c : Config) (m n d' : ℕ) : Prop where
  r31 : c.nreg 9931 = n
  r78 : c.nreg 9978 = m + n
  r73 : c.nreg 9973 = m + 2 * n
  r74 : c.nreg 9974 = d' + 4 + (m + 2 * n)
  r75 : c.nreg 9975 = d' + 4 + 2 * (m + 2 * n)
  r76 : c.nreg 9976 = d' + 4 + 3 * (m + 2 * n)
  r77 : c.nreg 9977 = d' + 4 + 6 * (m + 2 * n)
  r79 : c.nreg 9979 = d' + 4 + 7 * (m + 2 * n)
  r80 : c.nreg 9980 = d' + 4 + (m + 2 * n) + m
  r81 : c.nreg 9981 = d' + 4 + (m + 2 * n) + (m + n)
  r82 : c.nreg 9982 = d' + 4 + 2 * (m + 2 * n) + m
  r83 : c.nreg 9983 = d' + 4 + 2 * (m + 2 * n) + (m + n)
  r84 : c.nreg 9984 = d' + 4 + 3 * (m + 2 * n) + m
  r85 : c.nreg 9985 = d' + 4 + 3 * (m + 2 * n) + (m + n)
  r86 : c.nreg 9986 = d' + 4 + 6 * (m + 2 * n) + m
  r87 : c.nreg 9987 = d' + 4 + 6 * (m + 2 * n) + (m + n)

lemma Rg2.keepLp {c c' : Config} {m n d' : ℕ} (h : Rg2 c m n d')
    (hk : ∀ r, ¬ LpScr r → c'.nreg r = c.nreg r) : Rg2 c' m n d' := by
  obtain ⟨a31, a78, a73, a74, a75, a76, a77, a79, a80, a81, a82, a83, a84, a85, a86, a87⟩ := h
  have q : ∀ r, (r = 9931 ∨ (9973 ≤ r ∧ r ≤ 9987)) → c'.nreg r = c.nreg r := fun r h1 =>
    hk r (by unfold LpScr; omega)
  exact ⟨by rw [q _ (by omega), a31], by rw [q _ (by omega), a78],
    by rw [q _ (by omega), a73], by rw [q _ (by omega), a74],
    by rw [q _ (by omega), a75], by rw [q _ (by omega), a76],
    by rw [q _ (by omega), a77], by rw [q _ (by omega), a79],
    by rw [q _ (by omega), a80], by rw [q _ (by omega), a81],
    by rw [q _ (by omega), a82], by rw [q _ (by omega), a83],
    by rw [q _ (by omega), a84], by rw [q _ (by omega), a85],
    by rw [q _ (by omega), a86], by rw [q _ (by omega), a87]⟩

lemma Rg2.ofB1 {c₈ c₉ : Config} {m n d' : ℕ}
    (q : ∀ r, r ≠ 9940 → r ≠ 9941 → c₉.nreg r = c₈.nreg r)
    (b31 : c₈.nreg 9931 = n) (b78 : c₈.nreg 9978 = m + n)
    (b73 : c₈.nreg 9973 = m + 2 * n) (b74 : c₈.nreg 9974 = d' + 4 + (m + 2 * n))
    (b75 : c₈.nreg 9975 = d' + 4 + 2 * (m + 2 * n)) (b76 : c₈.nreg 9976 = d' + 4 + 3 * (m + 2 * n))
    (b77 : c₈.nreg 9977 = d' + 4 + 6 * (m + 2 * n)) (b79 : c₈.nreg 9979 = d' + 4 + 7 * (m + 2 * n))
    (b80 : c₈.nreg 9980 = d' + 4 + (m + 2 * n) + m)
    (b81 : c₈.nreg 9981 = d' + 4 + (m + 2 * n) + (m + n))
    (b82 : c₈.nreg 9982 = d' + 4 + 2 * (m + 2 * n) + m)
    (b83 : c₈.nreg 9983 = d' + 4 + 2 * (m + 2 * n) + (m + n))
    (b84 : c₈.nreg 9984 = d' + 4 + 3 * (m + 2 * n) + m)
    (b85 : c₈.nreg 9985 = d' + 4 + 3 * (m + 2 * n) + (m + n))
    (b86 : c₈.nreg 9986 = d' + 4 + 6 * (m + 2 * n) + m)
    (b87 : c₈.nreg 9987 = d' + 4 + 6 * (m + 2 * n) + (m + n)) : Rg2 c₉ m n d' :=
  ⟨by rw [q _ (by omega) (by omega), b31], by rw [q _ (by omega) (by omega), b78],
    by rw [q _ (by omega) (by omega), b73], by rw [q _ (by omega) (by omega), b74],
    by rw [q _ (by omega) (by omega), b75], by rw [q _ (by omega) (by omega), b76],
    by rw [q _ (by omega) (by omega), b77], by rw [q _ (by omega) (by omega), b79],
    by rw [q _ (by omega) (by omega), b80], by rw [q _ (by omega) (by omega), b81],
    by rw [q _ (by omega) (by omega), b82], by rw [q _ (by omega) (by omega), b83],
    by rw [q _ (by omega) (by omega), b84], by rw [q _ (by omega) (by omega), b85],
    by rw [q _ (by omega) (by omega), b86], by rw [q _ (by omega) (by omega), b87]⟩

lemma ne_of_inRg1 {r : ℕ} (hr : InRg1 r) : r ≠ 9940 ∧ r ≠ 9941 ∧ r ≠ 3004 ∧ r ≠ 8430 ∧
    ¬ (6300 ≤ r ∧ r ≤ 6303) ∧ (r < 7350 ∨ 7352 < r) ∧ (r < 7400 ∨ 7405 < r) ∧
    (r < 8431 ∨ 8447 < r) ∧ (r < 6304 ∨ 6309 < r) ∧ r ≠ 9931 ∧ ¬ (9973 ≤ r ∧ r ≤ 9987) := by
  unfold InRg1 at hr; omega

/-- The registers written by `pfP` outside its register band `9920 … 9999`: `dvP`'s and `lkProg`'s. -/
def ExtScr (r : ℕ) : Prop :=
  (7350 ≤ r ∧ r ≤ 7352) ∨ (7400 ≤ r ∧ r ≤ 7405) ∨ (8430 ≤ r ∧ r ≤ 8447) ∨
    (6300 ≤ r ∧ r ≤ 6309) ∨ (9920 ≤ r ∧ r ≤ 9999)

/-- **The result of stages 1–2** (relative to the start configuration `c`). -/
structure St2 (c c' : Config) (d m Z S F1b DFb CPb n : ℕ) : Prop where
  rg : Rg1 c' d m Z S F1b DFb CPb
  rg2 : Rg2 c' m n (S + 12 + 16 * m)
  r04 : c'.nreg 3004 = d
  reg : ∀ r, ¬ ExtScr r → c'.nreg r = c.nreg r
  low : ∀ a, a < S → c'.nmem a = c.nmem a
  sv0 : c'.nmem S = d
  sv1 : c'.nmem (S + 1) = c.nreg 3006
  sv2 : c'.nmem (S + 2) = m
  sv3 : c'.nmem (S + 3) = Z
  sv4 : c'.nmem (S + 4) = m * Z
  sv5 : c'.nmem (S + 5) = S + 12 + 13 * m
  sv6 : c'.nmem (S + 6) = S + 12 + 16 * m + 4 + 6 * (m + 2 * n)
  hd0 : c'.nmem (S + 12 + 16 * m) = m + 2 * n
  hd3 : c'.nmem (S + 12 + 16 * m + 3) = m * Z
  q : ∀ t < m, c'.nmem (S + 12 + 13 * m + t) = qF c.nmem DFb (d + 4 + m) t
  x0 : ∀ t < m, c'.nmem (S + 12 + 6 * m + t) = x0F c.nmem F1b DFb (d + 4 + m) Z t
  lab : ∀ i < m, c'.nmem (S + 12 + 7 * m + i) = olab (sgF d m c.nmem) i + 1
  dv : ∀ v < m, c'.nmem (S + 12 + 8 * m + v) =
    dvS (olab (sgF d m c.nmem)) (fun j => x0F c.nmem F1b DFb (d + 4 + m) Z j) m v
  dg : ∀ v < m, c'.nmem (S + 12 + 9 * m + v) = dvC (olab (sgF d m c.nmem)) m v
  nv : n = cnt (rfF (sgF d m c.nmem)) m
  ci : ∀ i < m, 0 < rfF (sgF d m c.nmem) i →
    c'.nmem (S + 12 + 11 * m + i) = cnt (rfF (sgF d m c.nmem)) i ∧
    c'.nmem (S + 12 + 12 * m + cnt (rfF (sgF d m c.nmem)) i) = i
  rr : c'.rreg = c.rreg
  rm : c'.rmem = c.rmem
  out : c'.output = c.output

lemma St1.x0' {c c' : Config} {d m Z S F1b DFb CPb : ℕ} (h : St1 c c' d m Z S F1b DFb CPb)
    {t : ℕ} (ht : t < m) :
    c'.nmem (S + 12 + 6 * m + t) = x0F c.nmem F1b DFb (d + 4 + m) Z t := h.x0 t ht

set_option maxHeartbeats 1600000 in
/-- **Stage 2 of `pfP`.** -/
theorem pfS2_exec (c c₁ : Config) (hW : 1 ≤ W) {d m Z S F1b DFb CPb : ℕ}
    (hI : PfIn c W d m Z S F1b DFb CPb) (h1 : St1 c c₁ d m Z S F1b DFb CPb)
    (hc₁ : WordsBounded W c₁) :
    ∃ c' k n, Exec P W pfS2 c₁ c' k ∧ k ≤ 67 * m + 80 ∧ n ≤ m ∧
      St2 c c' d m Z S F1b DFb CPb n := by
  have R1 := h1.rg
  have m0 := hI.m0
  have wS := hI.wS
  have wZ := hI.wZ
  set sgo := sgF d m c.nmem with hsgo
  have hp : PermOn sgo m := hI.sgp
  -- dvG
  obtain ⟨c₂, k₂, e₂, hk₂, a04, a30, g₂, m₂, rr₂, rm₂, o₂⟩ := dvG_exec (P := P) c₁ hc₁
  have hsg2 : ∀ i < m, sgF (S + 8) m c₂.nmem i = sgo i := fun i hi => by
    simp only [sgF, hsgo, m₂]
    rw [show S + 8 + 4 + 2 * m + i = S + 12 + 2 * m + i by omega, h1.sg0 i hi]
    congr 1; omega
  have hX2 : ∀ j < m, c₂.nmem (S + 8 + 6 * m + 4 + j) = x0F c.nmem F1b DFb (d + 4 + m) Z j :=
    fun j hj => by
      rw [m₂, show S + 8 + 6 * m + 4 + j = S + 12 + 6 * m + j by omega]; exact h1.x0 j hj
  have hsum : ∑ j ∈ range m, c₂.nmem (S + 8 + 6 * m + 4 + j) ≤ W := by
    have : ∑ j ∈ range m, c₂.nmem (S + 8 + 6 * m + 4 + j) ≤ ∑ j ∈ range m, 2 * Z :=
      sum_le_sum fun j hj => by
        rw [hX2 j (mem_range.1 hj)]
        exact x0F_le (by have := hI.f1 j (mem_range.1 hj); exact this)
    simp only [sum_const, card_range, smul_eq_mul] at this
    have : m * (2 * Z) ≤ 2 * (m * Z) := by ring_nf; omega
    omega
  obtain ⟨c₃, k₃, e₃, hk₃, l₃, d₃, f₃, g₃, rr₃, rm₃, o₃⟩ := dvP_exec (P := P) (W := W) c₂
    e₂.wb_right (d := S + 8) (A := S + 12 + 7 * m) (m := m) (by rw [a04, R1.r59])
    (by rw [a30, R1.r62]) (by rw [m₂]; exact h1.h0)
    (permOn_congr hp fun i hi => (hsg2 i hi).symm) (by omega) (by omega) (by omega) hsum
  have hk3 : ∀ r, InRg1 r → c₃.nreg r = c₁.nreg r := fun r hr => by
    have h := ne_of_inRg1 hr
    rw [g₃ r h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1, g₂ r h.2.2.1 h.2.2.2.1]
  have R3 := R1.keep hk3
  -- dvR
  obtain ⟨c₄, k₄, e₄, hk₄, b04, g₄, m₄, rr₄, rm₄, o₄⟩ := dvR_exec (P := P) c₃ e₃.wb_right
  have R4 := R3.keep fun r hr => g₄ r (ne_of_inRg1 hr).2.2.1
  have hw₄ := e₄.wb_right
  have hlab4 : ∀ i < m, c₄.nmem (S + 12 + 7 * m + i) = olab sgo i + 1 := fun i hi => by
    rw [m₄, l₃ i hi, olab_congr hsg2 (permOn_congr hp fun i hi => (hsg2 i hi).symm) hi]
  -- RF
  obtain ⟨c₅, k₅, e₅, hk₅, L₅⟩ := lp_exec (P := P) (xr := 9962) (yr := 9972) (or := 9965)
    (kr := 9972) (k2r := 9972) (rr := 9972) (bnd := 9930) (body := bRf)
    (O := S + 12 + 10 * m) (n := m) (B := 8 * m + 4)
    (val := fun t => c₄.nmem (S + 12 + 7 * m + t) - t) c₄ hw₄
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun c' hw hm' a23 a24 a25 a26 a27 a29 g => by
      obtain ⟨c'', k, ex, hk, hP⟩ := lRf_exec (P := P) c' hw hW (bnd := 9930) (n := m)
        (X := S + 12 + 7 * m) (O := S + 12 + 10 * m)
        (by rw [g _ (by omega), R4.r30]) (by unfold PfScr; omega) (by rw [a23, R4.r62])
        (by rw [a25, R4.r65]) (by omega) (by omega) (by omega) (fun t ht j hj => by omega)
      rw [hm'] at hP
      exact ⟨c'', k, ex, hk, hP⟩)
  have R5 := R4.keepLp L₅.reg
  have hw₅ := e₅.wb_right
  have hrf5 : ∀ i < m, c₅.nmem (S + 12 + 10 * m + i) = rfF sgo i := fun i hi => by
    rw [L₅.val i hi, hlab4 i hi]; rfl
  -- lkProg
  obtain ⟨c₆, k₆, e₆, hk₆, a00, a01, a02, a03, g₆, m₆, rr₆, rm₆, o₆⟩ := lkG_exec (P := P) c₅ hw₅
  have R6 := R5.keep fun r hr => g₆ r (ne_of_inRg1 hr).2.2.2.2.1
  obtain ⟨c₇, k₇, e₇, hk₇, n7, ci7, f₇, g₇, rr₇, rm₇, o₇⟩ := lkProg_exec (P := P) c₆ e₆.wb_right
    (m := m) (Fb := S + 12 + 10 * m) (CIb := S + 12 + 11 * m) (IXb := S + 12 + 12 * m)
    (by rw [a00, R5.r30]) (by rw [a01, R5.r65]) (by rw [a02, R5.r66]) (by rw [a03, R5.r67])
    (by omega) (by omega) (by omega) (by omega)
  have hcnt : ∀ i, i ≤ m → cnt (fun j => c₆.nmem (S + 12 + 10 * m + j)) i = cnt (rfF sgo) i :=
    fun i hi => cnt_congr fun j hj => by rw [m₆, hrf5 j (by omega)]
  set n := cnt (rfF sgo) m with hn
  have hnm : n ≤ m := cnt_le _ _
  have wB1 : S + 12 + 16 * m + 3 ≤ W := by clear * - wS; omega
  have wB2 : S + 6 ≤ W := by clear * - wS; omega
  have wB0 : S + 12 + 16 * m + 4 + 7 * (m + 2 * n) ≤ W := by clear * - wS hnm; omega
  have R7 := R6.keep fun r hr => g₇ r (ne_of_inRg1 hr).2.2.2.2.2.2.2.2.1
  -- pfB1, pfB2
  obtain ⟨c₈, k₈, e₈, hk₈, b31, b78, b73, b74, b75, b76, b77, b79, b80, b81, b82, b83, b84, b85,
    b86, b87, g₈, m₈, rr₈, rm₈, o₈⟩ := pfB1_exec (P := P) c₇ e₇.wb_right (m := m) (n := n)
    (d' := S + 12 + 16 * m) R7.r30 (by rw [n7, hcnt m le_rfl]) R7.r71 wB0
  have R8 := R7.keep fun r hr => g₈ r (ne_of_inRg1 hr).2.2.2.2.2.2.2.2.2.1
    (ne_of_inRg1 hr).1 (ne_of_inRg1 hr).2.2.2.2.2.2.2.2.2.2
  obtain ⟨c₉, k₉, e₉, hk₉, m₉, g₉, rr₉, rm₉, o₉⟩ := pfB2_exec (P := P) c₈ e₈.wb_right
    (d' := S + 12 + 16 * m) (m' := m + 2 * n) (Z' := m * Z) (S := S)
    (F := S + 12 + 16 * m + 4 + 6 * (m + 2 * n)) R8.r71 b73 R8.r52 R8.r58 b77 wB1 wB2
  have R9 := R8.keep fun r hr => g₉ r (ne_of_inRg1 hr).1 (ne_of_inRg1 hr).2.1
  have RR9 : Rg2 c₉ m n (S + 12 + 16 * m) := Rg2.ofB1 g₉ b31 b78 b73 b74 b75 b76 b77 b79 b80 b81
    b82 b83 b84 b85 b86 b87
  clear b31 b78 b73 b74 b75 b76 b79 b80 b81 b82 b83 b84 b85 b86 b87
  -- memory of `c₉` from `c₁`
  have M9 : ∀ a, (a < S + 12 + 7 * m ∨ S + 12 + 13 * m ≤ a) → a ≠ S + 12 + 16 * m →
      a ≠ S + 12 + 16 * m + 3 → a ≠ S + 6 → c₉.nmem a = c₁.nmem a := fun a h1 h2 h3 h4 => by
    rw [m₉, upd_other _ _ _ h4, upd_other _ _ _ h3, upd_other _ _ _ h2, m₈,
      f₇ a (by omega), m₆, L₅.mem _ (by omega), m₄, f₃ a (by omega), m₂]
  -- the arrays in `[S + 12 + 7m, S + 12 + 13m)`, from the run
  have M9' : ∀ a, S + 12 + 7 * m ≤ a → a < S + 12 + 13 * m → c₉.nmem a = c₇.nmem a := fun a h1 h2 => by
    rw [m₉, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), m₈]
  refine ⟨c₉, k₂ + (k₃ + k₄) + (k₅ + (k₆ + k₇ + (k₈ + k₉))), n,
    (e₂.seq (e₃.seq e₄)).seq (e₅.seq ((e₆.seq e₇).seq (e₈.seq e₉))), by omega, hnm,
    ⟨R9, RR9, ?_, fun r hr => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun t ht => ?_, fun t ht => ?_, fun i hi => ?_, fun v hv => ?_, fun v hv => ?_, rfl,
    fun i hi hr => ?_, ?_, ?_, ?_⟩⟩
  · rw [g₉ _ (by omega) (by omega), g₈ _ (by omega) (by omega) (by omega),
      g₇ _ (by omega), g₆ _ (by omega), L₅.reg _ (by unfold LpScr; omega), b04]
    exact R3.r50
  · unfold ExtScr at hr
    rw [g₉ _ (by omega) (by omega), g₈ _ (by omega) (by omega) (by omega),
      g₇ _ (by omega), g₆ _ (by omega), L₅.reg _ (by unfold LpScr; omega)]
    by_cases h34 : r = 3004
    · subst h34; rw [b04, R3.r50, hI.r04]
    · rw [g₄ _ h34, g₃ _ (by omega) (by omega) (by omega), g₂ _ (by omega) (by omega),
        h1.reg _ (by omega)]
  · rw [M9 a (by omega) (by omega) (by omega) (by omega), h1.low a ha]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv0]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv1]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv2]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv3]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv4]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.sv5]
  · rw [m₉, upd_same]
  · rw [m₉, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
  · rw [m₉, upd_other _ _ _ (by omega), upd_same]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.q t ht]
  · rw [M9 _ (by omega) (by omega) (by omega) (by omega), h1.x0 t ht]; rfl
  · rw [M9' _ (by omega) (by omega), f₇ _ (by omega), m₆, L₅.mem _ (by omega), hlab4 i hi]
  · rw [M9' _ (by omega) (by omega), f₇ _ (by omega), m₆, L₅.mem _ (by omega), m₄,
      show S + 12 + 8 * m + v = S + 12 + 7 * m + m + v by ring, (d₃ v hv).1]
    refine dvS_congr v (fun j hj => ?_) (fun j hj => hX2 j hj)
    exact olab_congr hsg2 (permOn_congr hp fun i hi => (hsg2 i hi).symm) hj
  · rw [M9' _ (by omega) (by omega), f₇ _ (by omega), m₆, L₅.mem _ (by omega), m₄,
      show S + 12 + 9 * m + v = S + 12 + 7 * m + m + m + v by ring, (d₃ v hv).2]
    exact dvC_congr v fun j hj => olab_congr hsg2 (permOn_congr hp fun i hi => (hsg2 i hi).symm) hj
  · have hF : 0 < c₆.nmem (S + 12 + 10 * m + i) := by rw [m₆, hrf5 i hi]; exact hr
    obtain ⟨u1, u2⟩ := ci7 i hi hF
    rw [hcnt i (by omega)] at u1 u2
    exact ⟨by rw [M9' _ (by omega) (by omega), u1],
      by rw [M9' _ (by have := cnt_le (rfF (sgF d m c.nmem)) i; omega)
        (by have := cnt_le (rfF (sgF d m c.nmem)) i; omega),
        u2]⟩
  · rw [rr₉, rr₈, rr₇, rr₆, L₅.rr, rr₄, rr₃, rr₂, h1.rr]
  · rw [rm₉, rm₈, rm₇, rm₆, L₅.rm, rm₄, rm₃, rm₂, h1.rm]
  · rw [o₉, o₈, o₇, o₆, L₅.out, o₄, o₃, o₂, h1.out]

end NcFz

end BKMNW

end PlanarFlow
