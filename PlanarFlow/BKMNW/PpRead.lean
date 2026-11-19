module

public import PlanarFlow.BKMNW.PpEnc

/-!
# Value blocks of the preprocessing: reading the input, flags, gathers

All blocks read the index `x` (or `i`) from the counter `8740` and leave their value in `8744`
(`VBPost`, scratch `pscr`):

* `vbW k`: the input word `5 x + k` (`tl`, `rv`, `nx`, `cp` for `k = 3, 4, 6, 7`);
* `vbSG`: `nx (rv x)` (the rotation); `vbNL`: the flag `tl (rv x) ≠ tl x`;
* `vbTS`, `vbTT`: the flags `bp (tl x) ≠ 0`, `bn (tl x) ≠ 0`;
* `vbEq`: the flag `A[x] = x + 1` (`A` at `r8727`); `vbPred`: `A[x] - 1`; `vbMul`: `A[x] · B[x]`
  (`B` at `r8729`); `vbZero`: `0`;
* `vbVal`: the validity flag of the slot (`decB ; itFlag`);
* `vbMod`: `A[i] % r8703`; `vbG1`: `POS[A[SRT[i]]]`; `vbG2`: `A[SRT[i]]` (`SRT` at `r8725`,
  `POS` at `r8726`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Feas

variable {P : Input} {W : ℕ}

/-- The input word `5 x + k`. -/
def vbW (k : ℕ) : Stmt :=
  block [.constN 8755 5, .mulN 8755 8740 8755, .constN 8756 k, .addN 8755 8755 8756,
    .readIn 8744 8755]

theorem vbW_exec {d : List ℕ} (hP : P.data = d) (c : Config) (hc : WordsBounded W c) {x k : ℕ}
    (hx : c.nreg 8740 = x) (hw : x * 5 + k + 5 ≤ W) (hword : word d (x * 5 + k) ≤ W) :
    ∃ c' t, Exec P W (vbW k) c c' t ∧ VBPost c (word d (x * 5 + k)) 5 c' t := by
  unfold vbW
  exec_block
  · omega
  · config_simp; rw [hx]; omega
  · omega
  · config_simp; rw [hx]; omega
  · config_simp; rw [hx, hP]; exact hword
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, hP]; rfl
  · vbframe

/-- The rotation `nx (rv x)`. -/
def vbSG : Stmt :=
  block [.constN 8755 5, .mulN 8755 8740 8755, .constN 8756 4, .addN 8755 8755 8756,
    .readIn 8757 8755, .constN 8755 5, .mulN 8755 8757 8755, .constN 8756 6,
    .addN 8755 8755 8756, .readIn 8744 8755]

theorem vbSG_exec {d : List ℕ} (hP : P.data = d) (c : Config) (hc : WordsBounded W c) {x : ℕ}
    (hx : c.nreg 8740 = x) (hrv : rv d x * 5 + 11 ≤ W) (hw : x * 5 + 9 ≤ W)
    (h1 : rv d x ≤ W) (h2 : nx d (rv d x) ≤ W) :
    ∃ c' t, Exec P W vbSG c c' t ∧ VBPost c (nx d (rv d x)) 10 c' t := by
  have e1 : word d (x * 5 + 4) = rv d x := by unfold rv; congr 1
  have e2 : word d (rv d x * 5 + 6) = nx d (rv d x) := rfl
  unfold vbSG
  exec_block
  · omega
  · config_simp; rw [hx]; omega
  · omega
  · config_simp; rw [hx]; omega
  · config_simp; rw [hx, hP, show d.getD (x * 5 + 4) 0 = rv d x from e1]; exact h1
  · omega
  · config_simp; rw [hx, hP]; rw [show d.getD (x * 5 + 4) 0 = rv d x from e1]; omega
  · omega
  · config_simp; rw [hx, hP]; rw [show d.getD (x * 5 + 4) 0 = rv d x from e1]; omega
  · config_simp; rw [hx, hP]; rw [show d.getD (x * 5 + 4) 0 = rv d x from e1]; exact h2
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, hP]; rw [show d.getD (x * 5 + 4) 0 = rv d x from e1]; rfl
  · vbframe

/-- `1 - ((a - b) + (b - a))` is the flag of `a = b`. -/
lemma eqf_eq (a b : ℕ) : 1 - ((a - b) + (b - a)) = fl (a = b) := by
  unfold fl; split_ifs with h <;> omega

/-- `1 - (1 - ((a - b) + (b - a)))` is the flag of `a ≠ b`. -/
lemma nef_eq (a b : ℕ) : 1 - (1 - ((a - b) + (b - a))) = fl (a ≠ b) := by
  unfold fl; split_ifs with h <;> omega

/-- `1 - (1 - a)` is the flag of `a ≠ 0`. -/
lemma nzf_eq (a : ℕ) : 1 - (1 - a) = fl (a ≠ 0) := by
  unfold fl; split_ifs with h <;> omega

/-- The flag of `tl (rv x) ≠ tl x`. -/
def vbNL : Stmt :=
  block [.constN 8755 5, .mulN 8755 8740 8755, .constN 8756 3, .addN 8756 8755 8756,
    .readIn 8757 8756, .constN 8756 4, .addN 8756 8755 8756, .readIn 8758 8756,
    .constN 8755 5, .mulN 8755 8758 8755, .constN 8756 3, .addN 8756 8755 8756,
    .readIn 8758 8756, .subN 8755 8757 8758, .subN 8756 8758 8757, .addN 8755 8755 8756,
    .subN 8755 8704 8755, .subN 8744 8704 8755]

theorem vbNL_exec {d : List ℕ} (hP : P.data = d) (c : Config) (hc : WordsBounded W c) {x : ℕ}
    (hx : c.nreg 8740 = x) (h04 : c.nreg 8704 = 1) (hrv : rv d x * 5 + 8 ≤ W)
    (hw : x * 5 + 8 ≤ W) (h1 : tl d x ≤ W) (h2 : rv d x ≤ W) (h3 : tl d (rv d x) ≤ W) :
    ∃ c' t, Exec P W vbNL c c' t ∧ VBPost c (fl (tl d (rv d x) ≠ tl d x)) 18 c' t := by
  have e1 : d.getD (x * 5 + 3) 0 = tl d x := rfl
  have e2 : d.getD (x * 5 + 4) 0 = rv d x := by
    show word d (x * 5 + 4) = word d (x * 5 + 3 + 1); congr 1
  have e3 : d.getD (rv d x * 5 + 3) 0 = tl d (rv d x) := rfl
  unfold vbNL
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hx]; omega)
  all_goals try (config_simp; rw [hx, hP, e1]; omega)
  all_goals try (config_simp; rw [hx, hP, e2]; omega)
  all_goals try (config_simp; rw [hx, hP, e2, e3]; omega)
  all_goals try (config_simp; rw [hx, hP, e1, e2, e3]; omega)
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, hP, e1, e2, e3, h04]; unfold fl; split_ifs <;> omega
  · vbframe

/-- The flag of `bp (tl x) ≠ 0` (`o = 0`) or `bn (tl x) ≠ 0` (`o = 1`). -/
def vbTF (o : ℕ) : Stmt :=
  block [.constN 8755 5, .mulN 8755 8740 8755, .constN 8756 3, .addN 8756 8755 8756,
    .readIn 8757 8756, .constN 8758 5, .mulN 8758 8700 8758, .constN 8756 (3 + o),
    .addN 8758 8758 8756, .addN 8758 8758 8757, .addN 8758 8758 8757, .readIn 8759 8758,
    .subN 8759 8704 8759, .subN 8744 8704 8759]

theorem vbTF_exec {d : List ℕ} (hP : P.data = d) (c : Config) (hc : WordsBounded W c) {x o : ℕ}
    (ho : o ≤ 1) (hx : c.nreg 8740 = x) (h00 : c.nreg 8700 = nd d) (h04 : c.nreg 8704 = 1)
    (hw : x * 5 + 8 ≤ W) (hw2 : nd d * 5 + 4 + 2 * tl d x ≤ W) (h1 : tl d x ≤ W)
    (h2 : word d (tl d x * 2 + (nd d * 5 + 3) + o) ≤ W) :
    ∃ c' t, Exec P W (vbTF o) c c' t ∧
      VBPost c (fl (word d (tl d x * 2 + (nd d * 5 + 3) + o) ≠ 0)) 14 c' t := by
  have e1 : d.getD (x * 5 + 3) 0 = tl d x := rfl
  have e2 : nd d * 5 + (3 + o) + tl d x + tl d x = tl d x * 2 + (nd d * 5 + 3) + o := by ring
  unfold vbTF
  exec_block
  all_goals try omega
  all_goals try (config_simp; rw [hx]; omega)
  all_goals try (config_simp; rw [hx, hP, e1]; omega)
  all_goals try (config_simp; rw [h00]; omega)
  all_goals try (config_simp; rw [hx, hP, e1, h00]; omega)
  all_goals try (config_simp; rw [hx, hP, e1, h00, e2]; exact h2)
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, hP, e1, h00, e2, h04, nzf_eq]; rfl
  · vbframe

/-- The flag of `A[x] = x + 1`, `A` at `r8727`. -/
def vbEq : Stmt :=
  block [.addN 8755 8727 8740, .loadN 8757 8755, .addN 8758 8740 8704, .subN 8755 8757 8758,
    .subN 8756 8758 8757, .addN 8755 8755 8756, .subN 8744 8704 8755]

theorem vbEq_exec (c : Config) (hc : WordsBounded W c) {x Ab : ℕ}
    (hx : c.nreg 8740 = x) (h04 : c.nreg 8704 = 1) (h27 : c.nreg 8727 = Ab)
    (hw : Ab + x + 1 ≤ W) :
    ∃ c' t, Exec P W vbEq c c' t ∧ VBPost c (fl (c.nmem (Ab + x) = x + 1)) 7 c' t := by
  have hm := hc.2 (Ab + x)
  unfold vbEq
  exec_block
  all_goals try (config_simp; rw [hx, h27]; omega)
  all_goals try (config_simp; rw [hx, h04]; omega)
  all_goals try (config_simp; rw [hx, h04, h27]; omega)
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h04, h27, eqf_eq]
  · vbframe

/-- `A[x] - 1`, `A` at `r8727`. -/
def vbPred : Stmt := block [.addN 8755 8727 8740, .loadN 8757 8755, .subN 8744 8757 8704]

theorem vbPred_exec (c : Config) (hc : WordsBounded W c) {x Ab : ℕ}
    (hx : c.nreg 8740 = x) (h04 : c.nreg 8704 = 1) (h27 : c.nreg 8727 = Ab) (hw : Ab + x ≤ W) :
    ∃ c' t, Exec P W vbPred c c' t ∧ VBPost c (c.nmem (Ab + x) - 1) 3 c' t := by
  unfold vbPred
  exec_block
  · config_simp; rw [hx, h27]; omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h04, h27]
  · vbframe

/-- `A[x] · B[x]`, `A` at `r8727`, `B` at `r8729`. -/
def vbMul : Stmt :=
  block [.addN 8755 8727 8740, .loadN 8757 8755, .addN 8755 8729 8740, .loadN 8758 8755,
    .mulN 8744 8757 8758]

theorem vbMul_exec (c : Config) (hc : WordsBounded W c) {x Ab Bb : ℕ}
    (hx : c.nreg 8740 = x) (h27 : c.nreg 8727 = Ab) (h29 : c.nreg 8729 = Bb) (hw : Ab + x ≤ W)
    (hw' : Bb + x ≤ W) (hv : c.nmem (Ab + x) * c.nmem (Bb + x) ≤ W) :
    ∃ c' t, Exec P W vbMul c c' t ∧ VBPost c (c.nmem (Ab + x) * c.nmem (Bb + x)) 5 c' t := by
  unfold vbMul
  exec_block
  · config_simp; rw [hx, h27]; omega
  · config_simp; rw [hx, h29]; omega
  · config_simp; rw [hx, h27, h29]; exact hv
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h27, h29]
  · vbframe

/-- `0`. -/
def vbZero : Stmt := block [.constN 8744 0]

theorem vbZero_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W vbZero c c' t ∧ VBPost c 0 1 c' t := by
  unfold vbZero
  exec_block
  · omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · vbframe

/-- `A[i] % r8703`, `A` at `r8728`. -/
def vbMod : Stmt := block [.addN 8755 8728 8740, .loadN 8757 8755, .modN 8744 8757 8703]

theorem vbMod_exec (c : Config) (hc : WordsBounded W c) {i Ab G : ℕ}
    (hx : c.nreg 8740 = i) (h28 : c.nreg 8728 = Ab) (h03 : c.nreg 8703 = G) (hw : Ab + i ≤ W) :
    ∃ c' t, Exec P W vbMod c c' t ∧ VBPost c (c.nmem (Ab + i) % G) 3 c' t := by
  unfold vbMod
  exec_block
  · config_simp; rw [hx, h28]; omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h28, h03]
  · vbframe

/-- `A[SRT[i]]`, `A` at `r8727`, `SRT` at `r8725`. -/
def vbG2 : Stmt := block [.addN 8755 8725 8740, .loadN 8757 8755, .addN 8755 8727 8757,
  .loadN 8744 8755]

theorem vbG2_exec (c : Config) (hc : WordsBounded W c) {i Ab Sb : ℕ}
    (hx : c.nreg 8740 = i) (h25 : c.nreg 8725 = Sb) (h27 : c.nreg 8727 = Ab) (hw : Sb + i ≤ W)
    (hw' : Ab + c.nmem (Sb + i) ≤ W) :
    ∃ c' t, Exec P W vbG2 c c' t ∧ VBPost c (c.nmem (Ab + c.nmem (Sb + i))) 4 c' t := by
  unfold vbG2
  exec_block
  · config_simp; rw [hx, h25]; omega
  · config_simp; rw [hx, h25, h27]; omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h25, h27]
  · vbframe

/-- `POS[A[SRT[i]]]`, `POS` at `r8726`. -/
def vbG1 : Stmt := block [.addN 8755 8725 8740, .loadN 8757 8755, .addN 8755 8727 8757,
  .loadN 8758 8755, .addN 8755 8726 8758, .loadN 8744 8755]

theorem vbG1_exec (c : Config) (hc : WordsBounded W c) {i Ab Sb Pb : ℕ}
    (hx : c.nreg 8740 = i) (h25 : c.nreg 8725 = Sb) (h27 : c.nreg 8727 = Ab)
    (h26 : c.nreg 8726 = Pb) (hw : Sb + i ≤ W) (hw' : Ab + c.nmem (Sb + i) ≤ W)
    (hw'' : Pb + c.nmem (Ab + c.nmem (Sb + i)) ≤ W) :
    ∃ c' t, Exec P W vbG1 c c' t ∧
      VBPost c (c.nmem (Pb + c.nmem (Ab + c.nmem (Sb + i)))) 6 c' t := by
  unfold vbG1
  exec_block
  · config_simp; rw [hx, h25]; omega
  · config_simp; rw [hx, h25, h27]; omega
  · config_simp; rw [hx, h25, h27, h26]; omega
  refine ⟨by omega, ?_, fun y hy => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [hx, h25, h27, h26]
  · vbframe

/-- The validity flag of the slot `r8740`. -/
def vbVal : Stmt := .seq decB (.seq itFlag (block [.copyN 8744 8758]))

theorem vbVal_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (c : Config) (hc : WordsBounded W c)
    {K BIG s KYb NLb CVb CFb KM : ℕ} (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s)
    (hs7 : s < 7 * n) (hA : ItArrs M vn K c KYb NLb CVb CFb KM)
    (hW : NLb + CVb + CFb + 7 * n ≤ W) :
    ∃ c' k, Exec P W vbVal c c' k ∧ VBPost c (fl (ValidS M s)) 14 c' k := by
  unfold vbVal
  refine vb_dec (B := 7) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  obtain ⟨c₂, k₂, e₂, hk₂, f58, fr2, m2, rr2, rm2, o2⟩ := itFlag_exec M vn c₁ hc₁ hK₁ hs₁ hs7
    ⟨hd.q, hd.x1, hd.x2⟩ hA₁ hW
  obtain ⟨c₃, k₃, e₃, hk₃, v3, fr3, m3, rr3, rm3, o3⟩ := MfDrv.cpy_exec (P := P) (r := 8744) (a := 8758)
    c₂ e₂.wb_right
  refine ⟨c₃, k₂ + k₃, .seq e₂ e₃, by omega, by rw [v3, f58], fun x hx => ?_, by rw [m3, m2],
    by rw [rr3, rr2], by rw [rm3, rm2], by rw [o3, o2]⟩
  unfold pscr at hx
  rw [fr3 x (by omega), fr2 x (by omega) (by omega)]

end Pp

end BKMNW

end PlanarFlow
