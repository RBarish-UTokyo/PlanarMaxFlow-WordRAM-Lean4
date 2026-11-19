module

public import PlanarFlow.BKMNW.NcHd
public import PlanarFlow.BKMNW.NcT1

/-!
# The frame block of the heads of `c2sP`/`s2cP`

* **`HdRegs`**: the registers after `hdF` (the frame's `d`, `m`, `Z`, `b`, the frame arrays, the
  bases above `b`, `ib`, `2Z`); **`hdF_exec`** (`hdF` within 67 steps);
* **`stR_le_pR`**: the scratch of `stCallZ` at a call with at most `m` vertices and faces fits in
  `stRm m = 4·10⁹ m² + 9` words.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **The registers of the head** after `hdF`. -/
structure HdRegs (c : Config) (d b m Z : ℕ) : Prop where
  r31 : c.nreg 9831 = d
  r32 : c.nreg 9832 = m
  r33 : c.nreg 9833 = Z
  r34 : c.nreg 9834 = b
  r74 : c.nreg 9874 = d + 4 + m
  r75 : c.nreg 9875 = d + 4 + 2 * m
  r78 : c.nreg 9878 = d + 4 + 3 * m
  r77 : c.nreg 9877 = d + 4 + 5 * m
  r76 : c.nreg 9876 = d + 4 + 6 * m
  r35 : c.nreg 9835 = b + m
  r36 : c.nreg 9836 = b + 2 * m
  r37 : c.nreg 9837 = b + 3 * m
  r38 : c.nreg 9838 = b + 4 * m
  r39 : c.nreg 9839 = b + 5 * m + 1
  r40 : c.nreg 9840 = b + 6 * m + 1
  r41 : c.nreg 9841 = b + 14 * m + 5
  r42 : c.nreg 9842 = b + 16 * m + 9
  r43 : c.nreg 9843 = b + 17 * m + 9
  r44 : c.nreg 9844 = b + 18 * m + 9
  r45 : c.nreg 9845 = b + 19 * m + 9
  r46 : c.nreg 9846 = b + 20 * m + 9
  r47 : c.nreg 9847 = b + 21 * m + 9
  r48 : c.nreg 9848 = b + 22 * m + 10
  r49 : c.nreg 9849 = b + 23 * m + 10
  r50 : c.nreg 9850 = b + 24 * m + 10
  r51 : c.nreg 9851 = b + 24 * m + 10 + stRm m
  r52 : c.nreg 9852 = b + 24 * m + 10 + stRm m + m
  r53 : c.nreg 9853 = b + 24 * m + 10 + stRm m + 2 * m
  r54 : c.nreg 9854 = b + 24 * m + 10 + stRm m + 3 * m
  r55 : c.nreg 9855 = b + 24 * m + 10 + stRm m + 4 * m
  r13 : c.nreg 9813 = wzQ m Z + 339 * m + 128
  r16 : c.nreg 9816 = 2 * Z
  r18 : c.nreg 9818 = m
  r19 : c.nreg 9819 = d

/-- `HdRegs` is kept by a run keeping the registers `9813 … 9819`, `9831 … 9855`,
`9874 … 9878`. -/
lemma HdRegs.congr {c c' : Config} {d b m Z : ℕ} (h : HdRegs c d b m Z)
    (hk : ∀ r, (9813 ≤ r ∧ r ≤ 9819) ∨ (9831 ≤ r ∧ r ≤ 9855) ∨ (9874 ≤ r ∧ r ≤ 9878) →
      c'.nreg r = c.nreg r) :
    HdRegs c' d b m Z := by
  constructor <;> rw [hk _ (by omega)]
  exacts [h.r31, h.r32, h.r33, h.r34, h.r74, h.r75, h.r78, h.r77, h.r76, h.r35, h.r36, h.r37,
    h.r38, h.r39, h.r40, h.r41, h.r42, h.r43, h.r44, h.r45, h.r46, h.r47, h.r48, h.r49, h.r50,
    h.r51, h.r52, h.r53, h.r54, h.r55, h.r13, h.r16, h.r18, h.r19]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The frame block of the head.** -/
theorem hdF_exec (c : Config) (hc : WordsBounded W c) {d b m Z : ℕ}
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = b + 5) (hm : c.nmem d = m)
    (hZ : c.nmem (d + 3) = Z) (hb : d + 4 + 7 * m ≤ b)
    (w1 : b + 28 * m + 10 + stRm m ≤ W) (w2 : 2 * Z ≤ W) (w3 : wzQ m Z + 339 * m + 128 ≤ W)
    (w4 : 4000000000 ≤ W) :
    ∃ c' k, Exec P W hdF c c' k ∧ k = 67 ∧ HdRegs c' d b m Z ∧
      (∀ r, r < 9813 ∨ (9819 < r ∧ r < 9830) ∨ 9879 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have v1 : d + 3 ≤ W := by omega
  have v2 : 5 ≤ W := by omega
  have v3 : 339 ≤ W := by omega
  have v4 : d + 4 + 6 * m ≤ W := by omega
  have v5 : b + 16 * m + 9 ≤ W := by omega
  have v6 : 8 ≤ W := by omega
  have v7 : b + 24 * m + 10 ≤ W := by omega
  have v8 : b + 24 * m + 10 + stRm m + 4 * m ≤ W := by omega
  obtain ⟨c₁, k₁, e₁, hk₁, a31, a32, a33, a34, a18, a19, a16, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    hdA_exec (P := P) c hc r04 r06 hm hZ v1 w2 v2
  obtain ⟨c₂, k₂, e₂, hk₂, a13, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    hdQ_exec (P := P) c₁ e₁.wb_right a32 a33 w3 v3
  have q₂ : ∀ r, r ≠ 9860 → r ≠ 9862 → r ≠ 9863 → r ≠ 9813 → c₂.nreg r = c₁.nreg r := f₂
  obtain ⟨c₃, k₃, e₃, hk₃, b74, b75, b78, b77, b76, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    hdB1_exec (P := P) c₂ e₂.wb_right (d := d) (m := m)
      (by rw [q₂ 9831 (by decide) (by decide) (by decide) (by decide)]; exact a31)
      (by rw [q₂ 9832 (by decide) (by decide) (by decide) (by decide)]; exact a32) v4
  obtain ⟨c₄, k₄, e₄, hk₄, b35, b36, b37, b38, b39, b40, b41, b42, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    hdB2_exec (P := P) c₃ e₃.wb_right (b := b) (m := m)
      (by rw [f₃ 9832 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        q₂ 9832 (by decide) (by decide) (by decide) (by decide)]; exact a32)
      (by rw [f₃ 9834 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        q₂ 9834 (by decide) (by decide) (by decide) (by decide)]; exact a34) v5 v6
  have p32 : c₄.nreg 9832 = m := by
    rw [f₄ 9832 (by decide) (by decide) (by decide),
      f₃ 9832 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      q₂ 9832 (by decide) (by decide) (by decide) (by decide)]; exact a32
  obtain ⟨c₅, k₅, e₅, hk₅, b43, b44, b45, b46, b47, b48, b49, b50, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    hdB3_exec (P := P) c₄ e₄.wb_right (b := b) (m := m) p32 b42 v7
  obtain ⟨c₆, k₆, e₆, hk₆, b51, b52, b53, b54, b55, f₆, m₆, rr₆, rm₆, o₆⟩ :=
    hdB4_exec (P := P) c₅ e₅.wb_right (p := b + 24 * m + 10) (m := m)
      (by rw [f₅ 9832 (by decide) (by decide)]; exact p32) b50 v8 w4
  -- the registers through the later blocks
  have k6 : ∀ r, ¬ (9851 ≤ r ∧ r ≤ 9855) → r ≠ 9860 → r ≠ 9864 → c₆.nreg r = c₅.nreg r := f₆
  have k5 : ∀ r, ¬ (9843 ≤ r ∧ r ≤ 9850) → r ≠ 9860 → c₅.nreg r = c₄.nreg r := f₅
  have k4 : ∀ r, ¬ (9835 ≤ r ∧ r ≤ 9842) → r ≠ 9860 → r ≠ 9864 → c₄.nreg r = c₃.nreg r := f₄
  have k3 : ∀ r, r ≠ 9860 → r ≠ 9874 → r ≠ 9875 → r ≠ 9876 → r ≠ 9877 → r ≠ 9878 →
      c₃.nreg r = c₂.nreg r := f₃
  have t3 : ∀ r, (r < 9835 ∨ 9878 < r) → r ≠ 9860 → r ≠ 9862 → r ≠ 9863 → r ≠ 9864 →
      c₆.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [k6 r (by omega) h2 h5, k5 r (by omega) h2, k4 r (by omega) h2 h5,
      k3 r h2 (by omega) (by omega) (by omega) (by omega) (by omega)]
  have t4 : ∀ r, (9874 ≤ r ∧ r ≤ 9878) → c₆.nreg r = c₃.nreg r := fun r h1 => by
    rw [k6 r (by omega) (by omega) (by omega), k5 r (by omega) (by omega),
      k4 r (by omega) (by omega) (by omega)]
  have t5 : ∀ r, (9835 ≤ r ∧ r ≤ 9842) → c₆.nreg r = c₄.nreg r := fun r h1 => by
    rw [k6 r (by omega) (by omega) (by omega), k5 r (by omega) (by omega)]
  have t6 : ∀ r, (9843 ≤ r ∧ r ≤ 9850) → c₆.nreg r = c₅.nreg r := fun r h1 => by
    rw [k6 r (by omega) (by omega) (by omega)]
  have t2 : ∀ r, r < 9813 ∨ (9813 < r ∧ r < 9835) ∨ 9878 < r → r ≠ 9860 → r ≠ 9862 →
      r ≠ 9863 → r ≠ 9864 → c₆.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 => by
    rw [t3 r (by omega) h2 h3 h4 h5, q₂ r h2 h3 h4 (by omega)]
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))), e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆)))),
    by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [t2 9831 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a31
  · rw [t2 9832 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a32
  · rw [t2 9833 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a33
  · rw [t2 9834 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a34
  · rw [t4 9874 (by decide)]; exact b74
  · rw [t4 9875 (by decide)]; exact b75
  · rw [t4 9878 (by decide)]; exact b78
  · rw [t4 9877 (by decide)]; exact b77
  · rw [t4 9876 (by decide)]; exact b76
  · rw [t5 9835 (by decide)]; exact b35
  · rw [t5 9836 (by decide)]; exact b36
  · rw [t5 9837 (by decide)]; exact b37
  · rw [t5 9838 (by decide)]; exact b38
  · rw [t5 9839 (by decide)]; exact b39
  · rw [t5 9840 (by decide)]; exact b40
  · rw [t5 9841 (by decide)]; exact b41
  · rw [t5 9842 (by decide)]; exact b42
  · rw [t6 9843 (by decide)]; exact b43
  · rw [t6 9844 (by decide)]; exact b44
  · rw [t6 9845 (by decide)]; exact b45
  · rw [t6 9846 (by decide)]; exact b46
  · rw [t6 9847 (by decide)]; exact b47
  · rw [t6 9848 (by decide)]; exact b48
  · rw [t6 9849 (by decide)]; exact b49
  · rw [t6 9850 (by decide)]; exact b50
  · exact b51
  · exact b52
  · exact b53
  · exact b54
  · exact b55
  · rw [t3 9813 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a13
  · rw [t2 9816 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a16
  · rw [t2 9818 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a18
  · rw [t2 9819 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a19
  · clear e₁ e₂ e₃ e₄ e₅ e₆
    rw [t2 r (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact f₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁]

universe w

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall STFlow

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- `pcoreB` with `4 m + 1` nodes is at most `3·10⁸ m²` when the map has at most `m` vertices and
faces. -/
lemma pcoreB_le_sq (V' F' : Type*) [Fintype V'] [Fintype F'] {m : ℕ} (hm : 1 ≤ m)
    (hV : Fintype.card V' ≤ m) (hF : Fintype.card F' ≤ m) :
    pcoreB V' F' m (4 * m + 1) ≤ 300000000 * (m * m) := by
  have hl := Nat.log_le_self 2 (4 * m + 1)
  have h1 : STFlow.pstOps (Fintype.card V') (Fintype.card F') m ≤ 93 * m + 69 := by
    unfold STFlow.pstOps; omega
  have h2 : DynTree.opCostE (4 * m + 1) ≤ 1246400 * m + 353820 := by
    unfold DynTree.opCostE; omega
  have h4 : STFlow.pstExt (Fintype.card V') (Fintype.card F') m ≤ 236 * m + 85 := by
    unfold STFlow.pstExt; omega
  have h3 := Nat.mul_le_mul h1 h2
  have e : (93 * m + 69) * (1246400 * m + 353820) =
      115915200 * (m * m) + 118906860 * m + 24413580 := by ring
  have hmm : m ≤ m * m := Nat.le_mul_of_pos_left m (by omega)
  have hmm1 : 1 ≤ m * m := le_trans hm hmm
  unfold pcoreB
  omega

/-- **The scratch of `stCallZ` fits in `stRm m`** at a call whose piece map has at most `m`
vertices and faces. -/
theorem stR_le_pR {x : MfDrv.MCall M} {m : ℕ} (hm : 1 ≤ m)
    (hV : Fintype.card (SVert x.2.2 (pdarts M x.1.piece x.2.1)) ≤ m)
    (hF : Fintype.card (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) ≤ m) :
    stR x m ≤ stRm m := by
  have h := pcoreB_le_sq _ _ hm hV hF
  show 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
    (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ≤
      4000000000 * (m * m) + 9
  omega

end NcStep

end BKMNW

end PlanarFlow
