module

public import PlanarFlow.BKMNW.FrImC

/-!
# The FR image, part D: the three stages

* `fiPre = fiPar ; fiR` (`fiPre_exec`, `8 b² + 12 b + 80` steps): the parameters and the
  registers `r7600 … r7613` of `frCall`;
* `fiNat = fiZ ; fiO ; fiS ; fiOff ; fiDst` (`fiNat_exec`): the image zeroed, the offsets
  and the heads of the arcs tail by tail (the natural part of the image), the sorted indices
  kept at `SIb`;
* `fiRes = fiMat ; fiPr ; fiLn` (`fiRes_exec`): the residues of the matrix, the prices and the
  lengths.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-- The parameters and the registers of `frCall`. -/
def fiPre : Stmt := .seq fiPar fiR

/-- The natural part of the image. -/
def fiNat : Stmt := .seq fiZ (.seq fiO (.seq fiS (.seq fiOff fiDst)))

/-- The residues. -/
def fiRes : Stmt := .seq fiMat (.seq fiPr fiLn)

section Stages

variable {P : Input} {W : ℕ}

lemma fLv_le (b : ℕ) : fLv b ≤ b + 1 := by
  have := Nat.log_le_self 2 b; unfold fLv; omega

theorem fiPre_exec (c : Config) (hc : WordsBounded W c) {b r mE K L A : ℕ}
    (r00 : c.nreg 8100 = b) (r03 : c.nreg 8103 = r) (r04 : c.nreg 8104 = mE)
    (r08 : c.nreg 8108 = K) (r09 : c.nreg 8109 = L) (r10 : c.nreg 8110 = A)
    (hW1 : fW b (b * b + b + b + 1 + mE + mE + b + b) + 1 ≤ W)
    (hW2 : 2 * (6 * ((b + 2) * L)) + 1 ≤ W)
    (hA : A + (b * b + b + b + 1 + mE + mE) ≤ W) :
    ∃ c' t, Exec P W fiPre c c' t ∧ t ≤ 8 * (b * b) + 12 * b + 80 ∧
      c'.nreg 8112 = 1 ∧ c'.nreg 8113 = b * b ∧ c'.nreg 8114 = b * b + b ∧
      c'.nreg 8115 = b * b + b + b + 1 + mE ∧ c'.nreg 8116 = b * b + b + b + 1 + mE + mE ∧
      c'.nreg 8124 = 2 * (6 * ((b + 2) * L)) + 1 ∧
      c'.nreg 8125 = 2 * (6 * ((b + 2) * L)) + 1 - K % (2 * (6 * ((b + 2) * L)) + 1) ∧
      c'.nreg 8126 = A + (b * b + b + b + 1 + mE + mE) ∧
      c'.nreg 7600 = b ∧ c'.nreg 7601 = b ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = b * b ∧
      c'.nreg 7604 = b * b + b ∧ c'.nreg 7605 = b * b + b + b + 1 + mE ∧ c'.nreg 7606 = r ∧
      c'.nreg 7607 = b * b + b + b + 1 + mE + mE ∧
      c'.nreg 7608 = b * b + b + b + 1 + mE + mE + b ∧
      c'.nreg 7609 = b * b + b + b + 1 + mE + mE + b + b ∧
      c'.nreg 7610 = 2 * (6 * ((b + 2) * L)) + 1 ∧ c'.nreg 7611 = 6 * ((b + 2) * L) ∧
      c'.nreg 7612 = fW b (b * b + b + b + 1 + mE + mE + b + b) + 1 ∧ c'.nreg 7613 = A ∧
      (∀ r', (r' < 2966 ∨ 2971 < r') → (r' < 7600 ∨ 7613 < r') → (r' < 8112 ∨ 8140 < r') →
        c'.nreg r' = c.nreg r') ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set wb := b * b + b + b + 1 + mE + mE + b + b with hwb
  have hfW := hW1
  unfold fW at hfW
  have hbl : b * fLv b ≤ b * b + b := by
    have := Nat.mul_le_mul_left b (fLv_le b); rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have hT : Nat.log 2 (b * fLv b) + 1 ≤ b * b + b + 1 := by
    have := Nat.log_le_self 2 (b * fLv b); omega
  have hP2 : fP2 b ≤ W := by
    have : fP2 b * 16 ≤ W := by omega
    omega
  -- fiA
  obtain ⟨c₁, t₁, e₁, ht₁, a12, a13, a14, a15, a16, a17, a18, a26, ak, am, ar, arm, ao⟩ :=
    fiA_exec (P := P) c hc r00 r04 r10 (by omega) hA
  -- fiL1
  obtain ⟨c₂, t₂, e₂, ht₂, b19, b66, b67, bk, bm, br, brm, bo⟩ :=
    fiL1_exec (P := P) c₁ e₁.wb_right (by rw [ak _ (by omega) (by omega), r00]) (by omega)
  have k2 : ∀ r', (r' < 2966 ∨ 2971 < r') → (r' < 8112 ∨ 8119 < r') → r' ≠ 8126 →
      c₂.nreg r' = c.nreg r' := fun r' h1 h2 h3 => by
    rw [bk r' h1 (by omega), ak r' (by omega) h3]
  -- fiL2
  obtain ⟨c₃, t₃, e₃, ht₃, d20, dk, dm, dr, drm, do'⟩ :=
    fiL2_exec (P := P) c₂ e₂.wb_right (by rw [k2 _ (by omega) (by omega) (by omega), r00]) b19
      b66 b67 (by omega)
  -- fiP
  obtain ⟨c₄, t₄, e₄, ht₄, f21, fk, fm, fr, frm, fo⟩ :=
    fiP_exec (P := P) c₃ e₃.wb_right (by rw [dk _ (by omega) (by omega), bk _ (by omega)
      (by omega), a12]) d20 hP2
  have k4 : ∀ r', r' ≠ 8121 → r' ≠ 8140 → (r' < 2966 ∨ 2971 < r') → r' ≠ 8120 →
      c₄.nreg r' = c₂.nreg r' := fun r' h1 h2 h3 h4 => by
    rw [fk r' h1 h2, dk r' h3 h4]
  -- fiW
  obtain ⟨c₅, t₅, e₅, ht₅, g22, gk, gm, gr, grm, go⟩ :=
    fiW_exec (P := P) (wb := wb) c₄ e₄.wb_right
      (by rw [k4 _ (by omega) (by omega) (by omega) (by omega),
        k2 _ (by omega) (by omega) (by omega), r00])
      (by rw [k4 _ (by omega) (by omega) (by omega) (by omega),
        bk _ (by omega) (by omega), a18])
      (by rw [k4 _ (by omega) (by omega) (by omega) (by omega), b19]) f21 (by omega)
  -- fiM
  obtain ⟨c₆, t₆, e₆, ht₆, h23, h24, h25, hk, hm, hr, hrm, ho⟩ :=
    fiM_exec (P := P) c₅ e₅.wb_right
      (by rw [gk _ (by omega) (by omega), k4 _ (by omega) (by omega) (by omega) (by omega),
        k2 _ (by omega) (by omega) (by omega), r00])
      (by rw [gk _ (by omega) (by omega), k4 _ (by omega) (by omega) (by omega) (by omega),
        k2 _ (by omega) (by omega) (by omega), r08])
      (by rw [gk _ (by omega) (by omega), k4 _ (by omega) (by omega) (by omega) (by omega),
        k2 _ (by omega) (by omega) (by omega), r09])
      (by rw [gk _ (by omega) (by omega), k4 _ (by omega) (by omega) (by omega) (by omega),
        bk _ (by omega) (by omega), a12]) hW2 (by omega)
  -- the registers of `c₆` read through the stages
  have q6 : ∀ r', (8112 ≤ r' ∧ r' ≤ 8118 ∨ r' = 8126) → c₆.nreg r' = c₁.nreg r' :=
    fun r' h => by
      rw [hk _ (by omega) (by omega), gk _ (by omega) (by omega), fk _ (by omega) (by omega),
        dk _ (by omega) (by omega), bk _ (by omega) (by omega)]
  have q6c : ∀ r', (r' < 2966 ∨ 2971 < r') → (r' < 8112 ∨ 8140 < r') → c₆.nreg r' = c.nreg r' :=
    fun r' h1 h2 => by
      rw [hk _ (by omega) (by omega), gk _ (by omega) (by omega),
        k4 _ (by omega) (by omega) h1 (by omega), k2 _ h1 (by omega) (by omega)]
  -- fiR
  obtain ⟨c₇, t₇, e₇, ht₇, s00, s01, s02, s03, s04, s05, s06, s07, s08, s09, s10, s11, s12, s13,
      sk, sm, sr, srm, so⟩ :=
    fiR_exec (P := P) c₆ e₆.wb_right (by rw [q6 _ (by omega), a12]) (Wp := fW b wb)
      (by rw [hk _ (by omega) (by omega), g22]) hW1
  have hcost : t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))) + t₇ ≤ 8 * (b * b) + 12 * b + 80 := by
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ hbl hT
    omega
  refine ⟨c₇, _, (e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆))))).seq e₇, hcost, ?_, ?_, ?_,
    ?_, ?_, by rw [sk _ (by omega), h24], by rw [sk _ (by omega), h25], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s12,
    ?_, fun r' h1 h2 h3 => ?_, by rw [sm, hm, gm, fm, dm, bm, am],
    by rw [sr, hr, gr, fr, dr, br, ar], by rw [srm, hrm, grm, frm, drm, brm, arm],
    by rw [so, ho, go, fo, do', bo, ao]⟩
  · rw [sk _ (by omega), q6 _ (by omega), a12]
  · rw [sk _ (by omega), q6 _ (by omega), a13]
  · rw [sk _ (by omega), q6 _ (by omega), a14]
  · rw [sk _ (by omega), q6 _ (by omega), a15]
  · rw [sk _ (by omega), q6 _ (by omega), a16]
  · rw [sk _ (by omega), q6 _ (by omega), a26]
  · rw [s00, q6c _ (by omega) (by omega), r00]
  · rw [s01, q6c _ (by omega) (by omega), r00]
  · exact s02
  · rw [s03, q6 _ (by omega), a13]
  · rw [s04, q6 _ (by omega), a14]
  · rw [s05, q6 _ (by omega), a15]
  · rw [s06, q6c _ (by omega) (by omega), r03]
  · rw [s07, q6 _ (by omega), a16]
  · rw [s08, q6 _ (by omega), a17]
  · rw [s09, q6 _ (by omega), a18]
  · rw [s10, h24]
  · rw [s11, h23]
  · rw [s13, q6c _ (by omega) (by omega), r10]
  · rw [sk r' h2, q6c r' h1 h3]

/-- The sorted indices are indices of arcs. -/
theorem fiL_eq (ET : ℕ → ℕ) (n : ℕ) :
    fiL ET n = (List.range n).map fun a => (ET a, a, (0 : ℤ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fiL, csList, one_ne_zero, ↓reduceIte, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, id] at ih ⊢
    rw [ih]

theorem length_pre_fiL_b {ET : ℕ → ℕ} {b mE : ℕ} (h : ∀ a < mE, ET a < b) :
    (pre (fiL ET mE) b).length = mE := by
  rw [length_pre_eq, fiL_eq, List.filter_eq_self.2, List.length_map, List.length_range]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  simpa using h i (List.mem_range.1 hi)

theorem fiL_idx_lt {ET : ℕ → ℕ} {b mE e : ℕ} (he : e < (pre (fiL ET mE) b).length) :
    ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1 < mE := by
  rw [List.getD_eq_getElem _ _ he]
  have hm := (mem_pre.1 (List.getElem_mem he)).1
  generalize (pre (fiL ET mE) b)[e] = x at hm ⊢
  rw [fiL_eq] at hm
  obtain ⟨i, hi, hi'⟩ := List.mem_map.1 hm
  rw [← hi']
  exact List.mem_range.1 hi

theorem fiNat_exec (c : Config) (hc : WordsBounded W c) {b mE ETb EHb A S : ℕ} {ET : ℕ → ℕ}
    (r00 : c.nreg 8100 = b) (r04 : c.nreg 8104 = mE) (r05 : c.nreg 8105 = ETb)
    (r06 : c.nreg 8106 = EHb) (r10 : c.nreg 8110 = A) (r11 : c.nreg 8111 = S)
    (r12 : c.nreg 8112 = 1) (r14 : c.nreg 8114 = b * b + b)
    (r16 : c.nreg 8116 = b * b + b + b + 1 + mE + mE)
    (het : ∀ a < mE, c.nmem (ETb + a) = ET a) (hlt : ∀ a < mE, ET a < b)
    (hET : ETb + mE ≤ A) (hEH : EHb + mE ≤ A)
    (hAS : A + ((b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE + mE)) ≤ S)
    (hW : S + mE + mE + 4 * b + 2 ≤ W) :
    ∃ c' t, Exec P W fiNat c c' t ∧
      t ≤ 10 * (b * b + b + b + 1 + mE + mE) + 50 * mE + 46 * b + 80 ∧
      (∀ a < b * b + b, c'.nmem (A + a) = 0) ∧
      (∀ x < b, c'.nmem (A + (b * b + b) + x) = (pre (fiL ET mE) x).length) ∧
      c'.nmem (A + (b * b + b) + b) = mE ∧
      (∀ e < mE, c'.nmem (A + (b * b + b) + b + 1 + e) =
        c.nmem (EHb + ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1)) ∧
      (∀ a, b * b + b + b + 1 + mE ≤ a → a < b * b + b + b + 1 + mE + mE → c'.nmem (A + a) = 0) ∧
      (∀ i < b * b + b + b + 1 + mE + mE,
        c'.nmem (A + (b * b + b + b + 1 + mE + mE) + i) = 0) ∧
      (∀ e < mE, c'.nmem (S + mE + b + 1 + b + b + b + e) =
        ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1) ∧
      c'.nreg 8142 = S + mE + b + 1 + b + b + b ∧
      (∀ a, (a < A ∨ A + ((b * b + b + b + 1 + mE + mE) + (b * b + b + b + 1 + mE + mE)) ≤ a) →
        (a < S ∨ S + mE + mE + 4 * b + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 1520 < r) → (r < 4910 ∨ 4916 < r) → (r < 5030 ∨ 5035 < r) →
        r ≠ 7861 → r ≠ 7865 → (r < 7873 ∨ 7875 < r) → (r < 8140 ∨ 8147 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set sb := b * b + b + b + 1 + mE + mE with hsb
  set ob := b * b + b with hob
  have hLm := length_pre_fiL_b hlt
  -- zero the image
  obtain ⟨c₁, t₁, e₁, ht₁, az, ak, an, ar, arm, ao⟩ :=
    fiZ_exec (P := P) c hc r16 r10 (by omega)
  have n1 : ∀ r, (r < 5030 ∨ 5035 < r) → c₁.nreg r = c.nreg r := an
  -- the flags
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bk, bn, br, brm, bo⟩ :=
    fiO_exec (P := P) c₁ e₁.wb_right (by rw [n1 _ (by omega), r04])
      (by rw [n1 _ (by omega), r11]) (by omega)
  have n2 : ∀ r, (r < 5030 ∨ 5035 < r) → r ≠ 7861 → r ≠ 7865 → (r < 7873 ∨ 7875 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [bn r h2 h3 (by omega), n1 r h1]
  -- the counting sort
  obtain ⟨c₃, t₃, e₃, ht₃, d41, d42, dOB, dSI, dk, dn, dr, drm, do'⟩ :=
    fiS_exec (P := P) (ET := ET) c₂ e₂.wb_right (by rw [n2 _ (by omega) (by omega) (by omega)
      (by omega), r00]) (by rw [n2 _ (by omega) (by omega) (by omega) (by omega), r04])
      (by rw [n2 _ (by omega) (by omega) (by omega) (by omega), r05])
      (by rw [n2 _ (by omega) (by omega) (by omega) (by omega), r11])
      (by rw [n2 _ (by omega) (by omega) (by omega) (by omega), r12])
      (fun a ha => by rw [bk _ (Or.inl (by omega)), ak _ (Or.inl (by omega)), het a ha]) b1
      hlt (by omega) (by omega)
  have n3 : ∀ r, (r < 1500 ∨ 1520 < r) → (r < 5030 ∨ 5035 < r) → r ≠ 7861 → r ≠ 7865 →
      (r < 7873 ∨ 7875 < r) → r ≠ 8141 → r ≠ 8142 → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [dn r h1 h6 h7, n2 r h2 h3 h4 h5]
  -- the offsets
  obtain ⟨c₄, t₄, e₄, ht₄, fOB, fmE, fk, fn, fr, frm, fo⟩ :=
    fiOff_exec (P := P) (OBb := S + mE + b + 1 + b) c₃ e₃.wb_right
      (by rw [n3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        r00])
      (by rw [n3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        r04])
      (by rw [n3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        r10])
      (by rw [n3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        r14]) d41 (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have n4 : ∀ r, (r < 1500 ∨ 1520 < r) → (r < 4910 ∨ 4916 < r) → (r < 5030 ∨ 5035 < r) →
      r ≠ 7861 → r ≠ 7865 → (r < 7873 ∨ 7875 < r) → r ≠ 8141 → r ≠ 8142 → r ≠ 8143 →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    rw [fn r h2 h9, n3 r h1 h3 h4 h5 h6 h7 h8]
  -- the heads
  have hSI4 : ∀ e < mE, c₄.nmem (S + mE + b + 1 + b + b + b + e) =
      ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1 := fun e he => by
    rw [fk _ (Or.inr (by omega)), dSI e (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, gD, gk, gn, g42, gr, grm, go⟩ :=
    fiDst_exec (P := P) (SIb := S + mE + b + 1 + b + b + b) c₄ e₄.wb_right
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r00])
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r04])
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r10])
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r14])
      (by rw [fn _ (by omega) (by omega), d42])
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r06])
      (by rw [n4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), r12])
      (Or.inr (by omega))
      (fun e he => by
        rw [hSI4 e he]
        have := fiL_idx_lt (ET := ET) (b := b) (mE := mE) (e := e) (by omega)
        exact ⟨by omega, Or.inl (by omega)⟩) (by omega) (by omega)
  -- the memory of `c₅` read back through the stages
  have m5 : ∀ a, (a < A ∨ A + (sb + sb) ≤ a) → (a < S ∨ S + mE + mE + 4 * b + 2 ≤ a) →
      c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [gk a (by omega), fk a (by omega), dk a (by omega), bk a (by omega), ak a h1]
  have mz : ∀ a, a < sb + sb → (a < ob ∨ ob + b + 1 + mE ≤ a) → c₅.nmem (A + a) = 0 :=
    fun a h1 h2 => by
      rw [gk _ (by omega), fk _ (by omega), dk _ (Or.inl (by omega)), bk _ (Or.inl (by omega)),
        az a h1]
  refine ⟨c₅, _, e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))), ?_, fun a ha => mz a (by omega)
    (Or.inl ha), fun x hx => ?_, ?_, fun e he => ?_, fun a h1 h2 => mz a (by omega) (Or.inr h1),
    fun i hi => ?_, fun e he => ?_, ?_, m5, fun r h1 h2 h3 h4 h5 h6 h7 => ?_,
    by rw [gr, fr, dr, br, ar], by rw [grm, frm, drm, brm, arm], by rw [go, fo, do', bo, ao]⟩
  · have : osCost mE b = 29 * mE + 32 * b + 26 := rfl
    rw [hsb]
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ this
    omega
  · rw [gk _ (by omega), fOB x hx, dOB x hx]
  · rw [gk _ (by omega), fmE]
  · rw [gD e he, hSI4 e he]
    have := fiL_idx_lt (ET := ET) (b := b) (mE := mE) (e := e) (by omega)
    rw [fk _ (Or.inl (by omega)), dk _ (Or.inl (by omega)), bk _ (Or.inl (by omega)),
      ak _ (Or.inl (by omega))]
  · have := mz (sb + i) (by omega) (Or.inr (by omega))
    rwa [← Nat.add_assoc] at this
  · rw [gk _ (by omega), hSI4 e he]
  · exact g42
  · rw [gn r h7, n4 r h1 h2 h3 h4 h5 h6 (by omega) (by omega) (by omega)]

theorem fiRes_exec (c : Config) (hc : WordsBounded W c) {b mE DMb PRb ELb As lb Kp Mo SIb : ℕ}
    (r00 : c.nreg 8100 = b) (r01 : c.nreg 8101 = DMb) (r02 : c.nreg 8102 = PRb)
    (r04 : c.nreg 8104 = mE) (r07 : c.nreg 8107 = ELb) (r12 : c.nreg 8112 = 1)
    (r13 : c.nreg 8113 = b * b) (r15 : c.nreg 8115 = lb) (r24 : c.nreg 8124 = Mo)
    (r25 : c.nreg 8125 = Kp) (r26 : c.nreg 8126 = As) (r42 : c.nreg 8142 = SIb)
    (hlb : b * b + b ≤ lb) (hDM : DMb + b * b ≤ As) (hPR : PRb + b ≤ As) (hEL : ELb + mE ≤ As)
    (hSI : As + lb + mE ≤ SIb) (hSIW : SIb + mE ≤ W)
    (hSIv : ∀ e < mE, c.nmem (SIb + e) < mE)
    (hPRv : ∀ x < b, c.nmem (PRb + x) + Kp ≤ W)
    (hELv : ∀ e < mE, c.nmem (ELb + c.nmem (SIb + e)) + Kp ≤ W)
    (hW1 : As + lb + mE ≤ W) (hW2 : b * b + b + mE + 1 ≤ W) :
    ∃ c' t, Exec P W fiRes c c' t ∧ t ≤ 7 * (b * b) + 9 * b + 11 * mE + 15 ∧
      (∀ i < b * b, c'.nmem (As + i) = c.nmem (DMb + i)) ∧
      (∀ x < b, c'.nmem (As + b * b + x) = (c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ e < mE, c'.nmem (As + lb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ a, a < As ∨ (As + b * b + b ≤ a ∧ a < As + lb) ∨ As + lb + mE ≤ a →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4910 ∨ 4916 < r) → (r < 8140 ∨ 8149 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the matrix
  obtain ⟨c₁, t₁, e₁, ht₁, aM, ak, an, ar, arm, ao⟩ :=
    fiMat_exec (P := P) c hc r13 r01 r26 (Or.inl hDM) (by omega) (by omega) (by omega)
  have n1 : ∀ r, (r < 4910 ∨ 4916 < r) → c₁.nreg r = c.nreg r := an
  -- the prices
  obtain ⟨c₂, t₂, e₂, ht₂, bP, bk, bn, br, brm, bo⟩ :=
    fiPr_exec (P := P) (pb := b * b) c₁ e₁.wb_right (by rw [n1 _ (by omega), r00])
      (by rw [n1 _ (by omega), r26]) (by rw [n1 _ (by omega), r13]) (by rw [n1 _ (by omega), r02])
      (by rw [n1 _ (by omega), r25]) (by rw [n1 _ (by omega), r24])
      (by rw [n1 _ (by omega), r12]) (Or.inl (by omega))
      (fun x hx => by rw [ak _ (Or.inl (by omega))]; exact hPRv x hx) (by omega) (by omega)
      (by omega)
  have n2 : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 8140 ∨ 8148 < r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [bn r (by omega) (by omega) (by omega) (by omega), n1 r h1]
  -- the lengths
  have m2 : ∀ a, (a < As ∨ As + b * b + b ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [bk a (by omega), ak a (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, dL, dk, dn, dr, drm, do'⟩ :=
    fiLn_exec (P := P) c₂ e₂.wb_right (by rw [n2 _ (by omega) (by omega), r04])
      (by rw [n2 _ (by omega) (by omega), r26]) (by rw [n2 _ (by omega) (by omega), r15])
      (by rw [bn _ (by omega) (by omega) (by omega) (by omega), an _ (by omega), r42])
      (by rw [n2 _ (by omega) (by omega), r07]) (by rw [n2 _ (by omega) (by omega), r25])
      (by rw [n2 _ (by omega) (by omega), r24]) (by rw [n2 _ (by omega) (by omega), r12])
      (Or.inr (by omega))
      (fun e he => by
        have h1 := hSIv e he
        rw [m2 (SIb + e) (Or.inr (by omega)), m2 (ELb + c.nmem (SIb + e)) (Or.inl (by omega))]
        exact ⟨by omega, hELv e he, Or.inl (by omega)⟩) (by omega) (by omega) (by omega)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, fun i hi => ?_, fun x hx => ?_, fun e he => ?_,
    fun a ha => ?_, fun r h1 h2 => ?_, by rw [dr, br, ar], by rw [drm, brm, arm],
    by rw [do', bo, ao]⟩
  · rw [dk _ (by omega), bk _ (by omega), aM i hi]
  · rw [dk _ (by omega), bP x hx, ak _ (Or.inl (by omega))]
  · have h1 := hSIv e he
    rw [dL e he, m2 (SIb + e) (Or.inr (by omega)), m2 (ELb + c.nmem (SIb + e)) (Or.inl (by omega))]
  · rw [dk _ (by omega), bk _ (by omega), ak _ (by omega)]
  · rw [dn r (by omega), n2 r h1 (by omega)]

end Stages

end MsCall

end BKMNW

end PlanarFlow
