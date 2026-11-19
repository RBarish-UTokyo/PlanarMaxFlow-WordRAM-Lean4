module

public import PlanarFlow.BKMNW.S7Od2

/-!
# Stage 7 of `sepL` (III), machine part (III): the weights of the classes

From the positions `P1` (`n` darts, `P1[i] ≤ n`), the hole labels `HP` (`≤ k`), the hole flags
`HT` (`k + 1` cells, `≤ 1`) and `K`, from `B0 = P1b + n`:

`odB = odSB ; zfill W1 ; ONE := 1 ; saProg (W1[P1[i]] += 1) ; zfill OW ; (OW[HP[i]] := P1[i]) ;
KO ; VH ; zfill W2 ; saProg (W2[KO[j]] += VH[j]) ; WT`

* `W1` at `B0` (`n + 1`), `ONE` at `B0 + n + 1`, `OW` at `B0 + n + 2` (`k + 1`), `KO` at
  `B0 + n + k + 3`, `VH` at `B0 + n + 2 k + 3`, `W2` at `B0 + n + 3 k + 3` (`n + 1`), `WT` at
  `B0 + 2 n + 3 k + 4` (`mC = r6306` cells);
* **`odB_exec`**: `WT[q] = #{i < n | P1[i] = q + 1} + saF KO VH k (q + 1)` with
  `KO[j] = own (j + 1)`, `VH[j] = vhV K HT[j+1] (own (j + 1))`, `own h = svF HP P1 n h 0` (the
  owner of the hole `h`).

Registers `7100 = n`, `7101 = HPb`, `7104 = HTb`, `7105 = k + 1`, `7143 = K`, `7180 = P1b`,
`6306 = mC`, `6521 = 1`; written `7154`, `7156 … 7159`, `7176 … 7179`, `7184 … 7189`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The bases of the weights. -/
def odSB : Stmt :=
  block [.subN 7154 7105 6521, .addN 7156 7180 7100, .addN 7178 7156 6521,
    .addN 7188 7100 6521, .addN 7157 7156 7188, .addN 7158 7157 6521, .addN 7176 7158 6521,
    .addN 7159 7158 7105, .addN 7184 7159 7154, .addN 7185 7184 7154, .addN 7179 7185 6521,
    .addN 7186 7185 7188, .addN 7177 7104 6521, .constN 7189 1]

/-- `ONE := 1`. -/
def odOne : Stmt := block [.storeN 7157 7189]

/-- The registers of the first scatter-add. -/
def odSa1 : Stmt :=
  block [.copyN 4630 7100, .copyN 4631 7180, .copyN 4632 7157, .constN 4633 0, .copyN 4634 7156]

/-- The registers of the scatter of the owners. -/
def odSv2 : Stmt := block [.copyN 7160 7100, .copyN 7161 7101, .copyN 7162 7180, .copyN 7163 7158]

/-- The registers of the second scatter-add. -/
def odSa2 : Stmt :=
  block [.copyN 4630 7154, .copyN 4631 7159, .copyN 4632 7184, .constN 4633 1, .copyN 4634 7185]

/-- **The weights of the classes.** -/
def odB : Stmt :=
  .seq odSB (.seq (zfill 7188 7156) (.seq odOne (.seq (.seq odSa1 saProg)
    (.seq (zfill 7105 7158) (.seq (.seq odSv2 svProg) (.seq (mapRunS vbKO 7154 7159)
      (.seq (mapRunS vbVH 7154 7184) (.seq (zfill 7188 7185) (.seq (.seq odSa2 saProg)
        (mapRunS vbWT 6306 7186))))))))))

/-- The registers of the weights. -/
structure OdRegsB (c : Config) (n k HPb HTb K P1b mC : ℕ) : Prop where
  r00 : c.nreg 7100 = n
  r01 : c.nreg 7101 = HPb
  r04 : c.nreg 7104 = HTb
  r05 : c.nreg 7105 = k + 1
  r43 : c.nreg 7143 = K
  r80 : c.nreg 7180 = P1b
  r06 : c.nreg 6306 = mC
  r21 : c.nreg 6521 = 1
  r54 : c.nreg 7154 = k
  r56 : c.nreg 7156 = P1b + n
  r57 : c.nreg 7157 = P1b + 2 * n + 1
  r58 : c.nreg 7158 = P1b + 2 * n + 2
  r59 : c.nreg 7159 = P1b + 2 * n + k + 3
  r76 : c.nreg 7176 = P1b + 2 * n + 2 + 1
  r77 : c.nreg 7177 = HTb + 1
  r78 : c.nreg 7178 = P1b + n + 1
  r79 : c.nreg 7179 = P1b + 2 * n + 3 * k + 3 + 1
  r84 : c.nreg 7184 = P1b + 2 * n + 2 * k + 3
  r85 : c.nreg 7185 = P1b + 2 * n + 3 * k + 3
  r86 : c.nreg 7186 = P1b + 3 * n + 3 * k + 4
  r88 : c.nreg 7188 = n + 1
  r89 : c.nreg 7189 = 1

/-- The registers `OdRegsB` reads. -/
def odBReg (x : ℕ) : Prop :=
  x = 7100 ∨ x = 7101 ∨ x = 7104 ∨ x = 7105 ∨ x = 7143 ∨ x = 7180 ∨ x = 6306 ∨ x = 6521 ∨
    x = 7154 ∨ (7156 ≤ x ∧ x ≤ 7159) ∨ (7176 ≤ x ∧ x ≤ 7179) ∨ (7184 ≤ x ∧ x ≤ 7189)

lemma OdRegsB.congr {c c' : Config} {n k HPb HTb K P1b mC : ℕ}
    (h : OdRegsB c n k HPb HTb K P1b mC) (e : ∀ x, odBReg x → c'.nreg x = c.nreg x) :
    OdRegsB c' n k HPb HTb K P1b mC := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rwa [e _ (by unfold odBReg; omega)]

section Exec

variable {P : Input} {W : ℕ}

theorem odSB_exec (c : Config) (hc : WordsBounded W c) {n k HPb HTb K P1b mC : ℕ}
    (r00 : c.nreg 7100 = n) (r01 : c.nreg 7101 = HPb) (r04 : c.nreg 7104 = HTb)
    (r05 : c.nreg 7105 = k + 1) (r43 : c.nreg 7143 = K) (r80 : c.nreg 7180 = P1b)
    (r06 : c.nreg 6306 = mC) (r21 : c.nreg 6521 = 1)
    (w : P1b + 3 * n + 3 * k + 5 ≤ W) (w' : HTb + 1 ≤ W) :
    ∃ c' t, Exec P W odSB c c' t ∧ t = 14 ∧ OdRegsB c' n k HPb HTb K P1b mC ∧
      c'.nmem = c.nmem ∧
      (∀ x, x ≠ 7154 → (x < 7156 ∨ 7159 < x) → (x < 7176 ∨ 7179 < x) → (x < 7184 ∨ 7189 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold odSB
  exec_block
  all_goals try (config_simp; (try simp only [r00, r01, r04, r05, r43, r80, r06, r21]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, rfl, fun x h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r01, r04, r05, r43, r80, r06, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r01, r04, r05, r43, r80, r06, r21]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

theorem odOne_exec (c : Config) (hc : WordsBounded W c) {a : ℕ} (r57 : c.nreg 7157 = a)
    (r89 : c.nreg 7189 = 1) (w : a ≤ W) :
    ∃ c' t, Exec P W odOne c c' t ∧ t = 1 ∧ c'.nmem = upd c.nmem a 1 ∧ c'.nreg = c.nreg ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold odOne
  exec_block
  all_goals try (config_simp; (try simp only [r57, r89]); omega)
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  config_simp; simp only [r57, r89]

theorem cp5_exec (c : Config) (hc : WordsBounded W c) {b0 b1 b2 b4 v0 v1 v2 v4 s : ℕ}
    (hb : b0 < 4630 ∨ 4634 < b0) (hb1 : b1 < 4630 ∨ 4634 < b1) (hb2 : b2 < 4630 ∨ 4634 < b2)
    (hb4 : b4 < 4630 ∨ 4634 < b4)
    (q0 : c.nreg b0 = v0) (q1 : c.nreg b1 = v1) (q2 : c.nreg b2 = v2) (q4 : c.nreg b4 = v4)
    (hs : s ≤ W) :
    ∃ c' t, Exec P W (block [.copyN 4630 b0, .copyN 4631 b1, .copyN 4632 b2, .constN 4633 s,
        .copyN 4634 b4]) c c' t ∧
      t = 5 ∧ c'.nreg 4630 = v0 ∧ c'.nreg 4631 = v1 ∧ c'.nreg 4632 = v2 ∧ c'.nreg 4633 = s ∧
      c'.nreg 4634 = v4 ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 4630 ∨ 4634 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp (disch := omega) only [upd_other, upd_same, q0, q1, q2, q4]

lemma svF_le {key val : ℕ → ℕ} {m B : ℕ} (hv : ∀ j < m, val j ≤ B) (x : ℕ) {old : ℕ}
    (ho : old ≤ B) : svF key val m x old ≤ B := by
  rcases svF_spec key val m x old with ⟨-, h⟩ | ⟨j, hj, -, h, -⟩
  · rw [h]; exact ho
  · rw [h]; exact hv j hj

lemma saF_congr7 {key key' val val' : ℕ → ℕ} {m : ℕ} (hk : ∀ j < m, key j = key' j)
    (hv : ∀ j < m, val j = val' j) (x : ℕ) : saF key val m x = saF key' val' m x := by
  unfold saF
  rw [filter_congr (fun j hj => by rw [hk j (mem_range.1 hj)])]
  exact sum_congr rfl fun j hj => hv j (mem_range.1 (mem_filter.1 hj).1)

set_option maxHeartbeats 8000000 in
/-- **The weights of the classes** (see the module docstring). -/
theorem odB_exec (c : Config) (hc : WordsBounded W c) {n k HPb HTb K P1b mC : ℕ}
    {p1 hp ht : ℕ → ℕ}
    (r00 : c.nreg 7100 = n) (r01 : c.nreg 7101 = HPb) (r04 : c.nreg 7104 = HTb)
    (r05 : c.nreg 7105 = k + 1) (r43 : c.nreg 7143 = K) (r80 : c.nreg 7180 = P1b)
    (r06 : c.nreg 6306 = mC) (r21 : c.nreg 6521 = 1)
    (hp1 : ∀ i < n, c.nmem (P1b + i) = p1 i) (hhp : ∀ i < n, c.nmem (HPb + i) = hp i)
    (hht : ∀ h < k + 1, c.nmem (HTb + h) = ht h)
    (hp1n : ∀ i < n, p1 i ≤ n) (hhpk : ∀ i < n, hp i ≤ k) (hht1 : ∀ h < k + 1, ht h ≤ 1)
    (hmC : mC ≤ n)
    (hsum : ∑ j ∈ range k, vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0) ≤ W)
    (hwt : ∀ q < mC, ((range n).filter fun i => p1 i = q + 1).card +
      saF (fun j => svF hp p1 n (j + 1) 0) (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0))
        k (q + 1) ≤ W)
    (lay : HPb + n ≤ P1b ∧ HTb + k + 1 ≤ P1b ∧ P1b + 4 * n + 3 * k + 5 ≤ W) :
    ∃ c' t, Exec P W odB c c' t ∧ t ≤ 45 * n + 40 * k + 90 ∧
      OdRegsB c' n k HPb HTb K P1b mC ∧
      (∀ q < mC, c'.nmem (P1b + 3 * n + 3 * k + 4 + q) =
        ((range n).filter fun i => p1 i = q + 1).card +
          saF (fun j => svF hp p1 n (j + 1) 0)
            (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0)) k (q + 1)) ∧
      (∀ a, (a < P1b + n ∨ P1b + 4 * n + 3 * k + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4630 ∨ (4639 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7154) ∨
        x = 7155 ∨ (7167 < x ∧ x < 7176) ∨ (7179 < x ∧ x < 7184) ∨ 7189 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  set m₀ := c.nmem with hm₀
  have hW1 : 1 ≤ W := by have := hc.1 6521; rw [r21] at this; exact this
  unfold odB
  obtain ⟨c₁, t₁, e₁, ht₁, R1, m1, n1, rr1, rm1, o1⟩ := odSB_exec (P := P) c hc r00 r01 r04 r05
    r43 r80 r06 r21 (by omega) (by omega)
  have gv : ∀ c' : Config, (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c₁.nreg x) →
      OdRegsB c' n k HPb HTb K P1b mC := fun c' h => R1.congr fun x hx =>
    h x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  -- `W1 := 0`, `ONE := 1`
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := zfill_exec (P := P) c₁ e₁.wb_right
    (bnd := 7188) (ob := 7156) (m := n + 1) (Ob := P1b + n) R1.r88 R1.r21 R1.r56 (by omega)
    (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega)
    (by omega)
  have R2 := gv c₂ fn2
  obtain ⟨c₃, t₃, e₃, ht₃, m3, n3, rr3, rm3, o3⟩ := odOne_exec (P := P) c₂ e₂.wb_right R2.r57
    R2.r89 (by omega)
  have R3 : OdRegsB c₃ n k HPb HTb K P1b mC := R2.congr fun x _ => by rw [n3]
  have M3 : ∀ a, (a < P1b + n ∨ P1b + 2 * n + 1 < a) → c₃.nmem a = m₀ a := fun a ha => by
    rw [m3, upd_other _ _ _ (by omega), fm2 a (by omega), m1]
  -- `W1[P1[i]] += 1`
  obtain ⟨c₄, t₄, e₄, ht₄, s0, s1, s2, s3, s4, sm4, sn4, sr4, srm4, so4⟩ := cp5_exec (P := P) c₃
    e₃.wb_right (b0 := 7100) (b1 := 7180) (b2 := 7157) (b4 := 7156) (s := 0) (by omega) (by omega)
    (by omega) (by omega) R3.r00 R3.r80 R3.r57 R3.r56 (by omega)
  have R4 : OdRegsB c₄ n k HPb HTb K P1b mC := R3.congr fun x hx =>
    sn4 x (by unfold odBReg at hx; omega)
  obtain ⟨c₅, t₅, e₅, ht₅, g5, gm5, gn5, gr5, grm5, go5⟩ := saProg_exec (P := P) c₄ e₄.wb_right
    (m := n) (nk := n + 1) (KEYb := P1b) (VALb := P1b + 2 * n + 1) (st := 0) (Wb := P1b + n)
    s0 s1 s2 s3 s4 (fun j hj => by rw [sm4, M3 _ (by omega), hp1 j hj]; have := hp1n j hj; omega)
    (fun k hk => by rw [sm4, m3, upd_other _ _ _ (by omega)]; exact f2 k hk)
    (fun j hj => by omega) (fun j hj => by omega) (by omega) (by omega) (fun j hj => by omega)
    (by omega)
    (by
      have e : ∀ j ∈ range n, c₄.nmem (P1b + 2 * n + 1 + 0 * j) = 1 := fun j _ => by
        rw [sm4, zero_mul, add_zero, m3, upd_same]
      rw [sum_congr rfl e]; simp; omega)
  have R5 : OdRegsB c₅ n k HPb HTb K P1b mC := R4.congr fun x hx =>
    gn5 x (by unfold odBReg at hx; omega)
  have W15 : ∀ q < mC, c₅.nmem (P1b + n + (q + 1)) =
      ((range n).filter fun i => p1 i = q + 1).card := fun q hq => by
    rw [g5 _ (by omega)]
    rw [saF_congr7 (key' := p1) (val' := fun _ => 1)
      (fun j hj => by rw [sm4, M3 _ (by omega), hp1 j hj])
      (fun j hj => by rw [sm4, zero_mul, add_zero, m3, upd_same]), saF_one]
  -- `OW := 0`, `OW[HP[i]] := P1[i]`
  obtain ⟨c₆, t₆, e₆, ht₆, f6, fm6, fn6, fr6, frm6, fo6⟩ := zfill_exec (P := P) c₅ e₅.wb_right
    (bnd := 7105) (ob := 7158) (m := k + 1) (Ob := P1b + 2 * n + 2) R5.r05 R5.r21 R5.r58
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
  have R6 : OdRegsB c₆ n k HPb HTb K P1b mC := R5.congr fun x hx =>
    fn6 x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  obtain ⟨c₇, t₇, e₇, ht₇, s0', s1', s2', s3', sm7, sn7, sr7, srm7, so7⟩ := cp4_exec (P := P) c₆
    e₆.wb_right (a0 := 7160) (a1 := 7161) (a2 := 7162) (a3 := 7163) (b0 := 7100) (b1 := 7101)
    (b2 := 7180) (b3 := 7158) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ R6.r00 R6.r01 R6.r80 R6.r58
  have R7 : OdRegsB c₇ n k HPb HTb K P1b mC := R6.congr fun x hx =>
    sn7 x (by unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
  have M7 : ∀ a, (a < P1b + n ∨ P1b + 2 * n + k + 3 ≤ a) → c₇.nmem a = m₀ a := fun a ha => by
    rw [sm7, fm6 a (by omega), gm5 a (by omega), sm4, M3 a (by omega)]
  obtain ⟨c₈, t₈, e₈, ht₈, g8, gm8, gn8, gr8, grm8, go8⟩ := svProg_exec (P := P) c₇ e₇.wb_right
    (m := n) (nk := k + 1) (KEYb := HPb) (VALb := P1b) (Tb := P1b + 2 * n + 2) s0' s1' s2' s3'
    (fun j hj => by rw [M7 _ (by omega), hhp j hj]; have := hhpk j hj; omega)
    (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega) (by omega)
  have R8 : OdRegsB c₈ n k HPb HTb K P1b mC := R7.congr fun x hx =>
    gn8 x (by unfold odBReg at hx; omega)
  have OW8 : ∀ h < k + 1, c₈.nmem (P1b + 2 * n + 2 + h) = svF hp p1 n h 0 := fun h hh => by
    rw [g8 h hh, show c₇.nmem (P1b + 2 * n + 2 + h) = 0 by rw [sm7]; exact f6 h hh]
    exact svF_congr (fun j hj => by rw [M7 _ (by omega), hhp j hj])
      (fun j hj => by rw [M7 _ (by omega), hp1 j hj]) _ _
  have own_le : ∀ h, svF hp p1 n h 0 ≤ n := fun h => svF_le hp1n h (Nat.zero_le _)
  have OW8' : ∀ j < k, c₈.nmem (P1b + 2 * n + 2 + 1 + j) = svF hp p1 n (j + 1) 0 := by
    intro j hj
    have := OW8 (j + 1) (by omega)
    rwa [show P1b + 2 * n + 2 + (j + 1) = P1b + 2 * n + 2 + 1 + j by omega] at this
  -- `KO`, `VH`
  obtain ⟨c₉, t₉, e₉, ht₉, f9, fm9, fn9, fr9, frm9, fo9⟩ := mapRun_exec (P := P) c₈ e₈.wb_right
    (vb := vbKO) (bnd := 7154) (ob := 7159) (m := k) (Ob := P1b + 2 * n + k + 3) (B := 2)
    (fun j => svF hp p1 n (j + 1) 0) R8.r54 R8.r21 R8.r59 (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have g := R8.congr (c' := c') fun x hx =>
        hr x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
          (by unfold odBReg at hx; omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbKO_exec (P := P) c' hw
        (OWb := P1b + 2 * n + 2) (o := svF hp p1 n (j + 1) 0) h20 g.r76
        (by rw [hm _ (by omega)]; exact OW8' j hj) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R9 : OdRegsB c₉ n k HPb HTb K P1b mC := R8.congr fun x hx =>
    fn9 x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  have HT9 : ∀ h < k + 1, c₉.nmem (HTb + h) = ht h := fun h hh => by
    rw [fm9 _ (by omega), gm8 _ (by omega), M7 _ (by omega)]; exact hht h hh
  have HT9' : ∀ j < k, c₉.nmem (HTb + 1 + j) = ht (j + 1) := by
    intro j hj
    have := HT9 (j + 1) (by omega)
    rwa [show HTb + (j + 1) = HTb + 1 + j by omega] at this
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, f10, fm10, fn10, fr10, frm10, fo10⟩ := mapRun_exec (P := P) c₉
    e₉.wb_right (vb := vbVH) (bnd := 7154) (ob := 7184) (m := k) (Ob := P1b + 2 * n + 2 * k + 3)
    (B := 8) (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0)) R9.r54 R9.r21 R9.r84
    (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun j hj c' hw h20 hr hm => by
      have g := R9.congr (c' := c') fun x hx =>
        hr x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
          (by unfold odBReg at hx; omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbVH_exec (P := P) c' hw
        (OWb := P1b + 2 * n + 2) (HTb := HTb) (K := K) (o := svF hp p1 n (j + 1) 0)
        (t := ht (j + 1)) h20 g.r76 g.r77 g.r43 g.r21
        (by rw [hm _ (by omega), fm9 _ (by omega)]; exact OW8' j hj)
        (by rw [hm _ (by omega)]; exact HT9' j hj)
        (hht1 (j + 1) (by omega)) (by omega) (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R10 : OdRegsB c₁₀ n k HPb HTb K P1b mC := R9.congr fun x hx =>
    fn10 x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  -- `W2 := 0`, `W2[KO[j]] += VH[j]`
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, f11, fm11, fn11, fr11, frm11, fo11⟩ := zfill_exec (P := P) c₁₀
    e₁₀.wb_right (bnd := 7188) (ob := 7185) (m := n + 1) (Ob := P1b + 2 * n + 3 * k + 3)
    R10.r88 R10.r21 R10.r85 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have R11 : OdRegsB c₁₁ n k HPb HTb K P1b mC := R10.congr fun x hx =>
    fn11 x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  obtain ⟨c₁₂, t₁₂, e₁₂, ht₁₂, u0, u1, u2, u3, u4, um12, un12, ur12, urm12, uo12⟩ := cp5_exec
    (P := P) c₁₁ e₁₁.wb_right (b0 := 7154) (b1 := 7159) (b2 := 7184) (b4 := 7185) (s := 1)
    (by omega) (by omega) (by omega) (by omega) R11.r54 R11.r59 R11.r84 R11.r85 hW1
  have R12 : OdRegsB c₁₂ n k HPb HTb K P1b mC := R11.congr fun x hx =>
    un12 x (by unfold odBReg at hx; omega)
  have KO12 : ∀ j < k, c₁₂.nmem (P1b + 2 * n + k + 3 + j) = svF hp p1 n (j + 1) 0 :=
    fun j hj => by rw [um12, fm11 _ (by omega), fm10 _ (by omega)]; exact f9 j hj
  have VH12 : ∀ j < k, c₁₂.nmem (P1b + 2 * n + 2 * k + 3 + 1 * j) =
      vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0) :=
    fun j hj => by rw [um12, one_mul, fm11 _ (by omega)]; exact f10 j hj
  obtain ⟨c₁₃, t₁₃, e₁₃, ht₁₃, g13, gm13, gn13, gr13, grm13, go13⟩ := saProg_exec (P := P) c₁₂
    e₁₂.wb_right (m := k) (nk := n + 1) (KEYb := P1b + 2 * n + k + 3)
    (VALb := P1b + 2 * n + 2 * k + 3) (st := 1) (Wb := P1b + 2 * n + 3 * k + 3) u0 u1 u2 u3 u4
    (fun j hj => by rw [KO12 j hj]; have := own_le (j + 1); omega)
    (fun k' hk' => by rw [um12]; exact f11 k' hk') (fun j hj => by omega) (fun j hj => by omega)
    (by omega) (by omega) (fun j hj => by omega) (by omega)
    (by rw [sum_congr rfl fun j hj => VH12 j (mem_range.1 hj)]; exact hsum)
  have R13 : OdRegsB c₁₃ n k HPb HTb K P1b mC := R12.congr fun x hx =>
    gn13 x (by unfold odBReg at hx; omega)
  have W213 : ∀ q < mC, c₁₃.nmem (P1b + 2 * n + 3 * k + 3 + (q + 1)) =
      saF (fun j => svF hp p1 n (j + 1) 0) (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0))
        k (q + 1) := fun q hq => by
    rw [g13 _ (by omega)]
    exact saF_congr7 (fun j hj => KO12 j hj) (fun j hj => VH12 j hj) _
  have W113 : ∀ q < mC, c₁₃.nmem (P1b + n + (q + 1)) =
      ((range n).filter fun i => p1 i = q + 1).card := fun q hq => by
    rw [gm13 _ (by omega), um12, fm11 _ (by omega), fm10 _ (by omega), fm9 _ (by omega),
      gm8 _ (by omega), sm7, fm6 _ (by omega)]
    exact W15 q hq
  have W113' : ∀ q < mC, c₁₃.nmem (P1b + n + 1 + q) =
      ((range n).filter fun i => p1 i = q + 1).card := by
    intro q hq
    have := W113 q hq
    rwa [show P1b + n + (q + 1) = P1b + n + 1 + q by omega] at this
  have W213' : ∀ q < mC, c₁₃.nmem (P1b + 2 * n + 3 * k + 3 + 1 + q) =
      saF (fun j => svF hp p1 n (j + 1) 0) (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0))
        k (q + 1) := by
    intro q hq
    have := W213 q hq
    rwa [show P1b + 2 * n + 3 * k + 3 + (q + 1) = P1b + 2 * n + 3 * k + 3 + 1 + q by omega]
      at this
  -- `WT`
  obtain ⟨c₁₄, t₁₄, e₁₄, ht₁₄, f14, fm14, fn14, fr14, frm14, fo14⟩ := mapRun_exec (P := P) c₁₃
    e₁₃.wb_right (vb := vbWT) (bnd := 6306) (ob := 7186) (m := mC)
    (Ob := P1b + 3 * n + 3 * k + 4) (B := 5)
    (fun q => ((range n).filter fun i => p1 i = q + 1).card +
      saF (fun j => svF hp p1 n (j + 1) 0) (fun j => vhV K (ht (j + 1)) (svF hp p1 n (j + 1) 0))
        k (q + 1)) R13.r06 R13.r21 R13.r86 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun q hq c' hw h20 hr hm => by
      have g := R13.congr (c' := c') fun x hx =>
        hr x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
          (by unfold odBReg at hx; omega)
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbWT_exec (P := P) c' hw
        (W1b := P1b + n) (W2b := P1b + 2 * n + 3 * k + 3) h20 g.r78 g.r79
        (by rw [hm _ (by omega)]; exact W113' q hq)
        (by rw [hm _ (by omega)]; exact W213' q hq) (by omega) (by omega) (hwt q hq)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have R14 : OdRegsB c₁₄ n k HPb HTb K P1b mC := R13.congr fun x hx =>
    fn14 x (by unfold vscr; unfold odBReg at hx; omega) (by unfold odBReg at hx; omega)
      (by unfold odBReg at hx; omega)
  refine ⟨c₁₄, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq (.seq e₄ e₅) (.seq e₆
    (.seq (.seq e₇ e₈) (.seq e₉ (.seq e₁₀ (.seq e₁₁ (.seq (.seq e₁₂ e₁₃) e₁₄))))))))),
    by omega, R14, f14, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [fm14 a (by omega), gm13 a (by omega), um12, fm11 a (by omega), fm10 a (by omega),
      fm9 a (by omega), gm8 a (by omega), M7 a (by omega)]
  · rw [fn14 x (by unfold vscr; omega) (by omega) (by omega), gn13 x (by omega),
      un12 x (by omega), fn11 x (by unfold vscr; omega) (by omega) (by omega),
      fn10 x (by unfold vscr; omega) (by omega) (by omega),
      fn9 x (by unfold vscr; omega) (by omega) (by omega), gn8 x (by omega),
      sn7 x (by omega) (by omega) (by omega) (by omega),
      fn6 x (by unfold vscr; omega) (by omega) (by omega), gn5 x (by omega), sn4 x (by omega),
      n3, fn2 x (by unfold vscr; omega) (by omega) (by omega),
      n1 x (by omega) (by omega) (by omega) (by omega)]
  · rw [fr14, gr13, ur12, fr11, fr10, fr9, gr8, sr7, fr6, gr5, sr4, rr3, fr2, rr1]
  · rw [frm14, grm13, urm12, frm11, frm10, frm9, grm8, srm7, frm6, grm5, srm4, rm3, frm2, rm1]
  · rw [fo14, go13, uo12, fo11, fo10, fo9, go8, so7, fo6, go5, so4, o3, fo2, o1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
