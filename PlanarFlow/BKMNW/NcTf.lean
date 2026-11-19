module

public import PlanarFlow.BKMNW.NcLoop
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The terminal-flag program of `c2sP`

`c2sP` needs, for every dart `i < m` of the frame, the flag `[tail ∈ πj.verts]` of the part `j`
of the separator (the source set of the s-t flow call) and the flag `[tail ∈ H]` of the hole. On
the machine a vertex of the piece map is a label (`dvP`: `LAB[i] = olab i + 1 ∈ [1, m]`, two darts
having the same label iff they have the same tail, `Lay.vert_eq_iff`), and a part of the separator
is given by its darts (`SegsOut`) and the dart of its first vertex. The program **`tfP`** (bases
and sizes in registers, natural words only):

1. `VM[v] := 0` for `v ≤ m` (scratch, `m + 1` words);
2. `VM[LAB[s]] := 1` (the first vertex), then `VM[LAB[L[t]]] := 1`, `VM[LAB[RV[L[t]]]] := 1` for
   `t < K` (the tail and the head of every dart of the list);
3. `F[i] := VM[LAB[i]]` for `i < m`.

**`tfP_exec`**: within `5 (m + 1) + 15 K + 9 m + 25` steps,
`F[i] = [LAB[s] = LAB[i] ∨ ∃ t < K, LAB[L[t]] = LAB[i] ∨ LAB[RV[L[t]]] = LAB[i]]` (`tfHit`);
memory changed only in `[Vb, Vb + m] ∪ [Fb, Fb + m)`, registers only `9706 … 9712`.

Registers: inputs `9700` (`m`), `9701` (`LAB` base), `9702` (`L` base), `9703` (`K`), `9704`
(`VM` base), `9705` (`F` base), `9713` (`RV` base), `9714` (`s`); scratch `9706 … 9712`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- Constants: `r9706 = 1`, `r9711 = 0`, `r9707 = 0`, `r9712 = m + 1`. -/
def tfInit : Stmt := block [.constN 9706 1, .constN 9711 0, .constN 9707 0, .addN 9712 9700 9706]

/-- `VM[r9707] := 0`, `r9707 += 1`. -/
def tfZ : Stmt := block [.addN 9708 9704 9707, .storeN 9708 9711, .addN 9707 9707 9706]

/-- `VM[LAB[s]] := 1`, `r9707 := 0`. -/
def tfS : Stmt :=
  block [.addN 9708 9701 9714, .loadN 9708 9708, .addN 9708 9704 9708, .storeN 9708 9706,
    .constN 9707 0]

/-- `VM[LAB[L[t]]] := 1`, `VM[LAB[RV[L[t]]]] := 1`, `t = r9707`, `r9707 += 1`. -/
def tfM : Stmt :=
  block [.addN 9708 9702 9707, .loadN 9708 9708, .addN 9709 9713 9708, .loadN 9709 9709,
    .addN 9708 9701 9708, .loadN 9708 9708, .addN 9708 9704 9708, .storeN 9708 9706,
    .addN 9709 9701 9709, .loadN 9709 9709, .addN 9709 9704 9709, .storeN 9709 9706,
    .addN 9707 9707 9706]

/-- `r9707 := 0`. -/
def tfR : Stmt := block [.constN 9707 0]

/-- `F[i] := VM[LAB[i]]`, `i = r9707`, `r9707 += 1`. -/
def tfG : Stmt :=
  block [.addN 9708 9701 9707, .loadN 9708 9708, .addN 9708 9704 9708, .loadN 9708 9708,
    .addN 9709 9705 9707, .storeN 9709 9708, .addN 9707 9707 9706]

/-- **The terminal-flag program.** -/
def tfP : Stmt :=
  .seq tfInit (.seq (.whileLtN 9707 9712 tfZ) (.seq tfS (.seq (.whileLtN 9707 9703 tfM)
    (.seq tfR (.whileLtN 9707 9700 tfG)))))

/-- The registers written by `tfP`. -/
def TfScr (r : ℕ) : Prop := 9706 ≤ r ∧ r ≤ 9712

/-! ### The blocks -/

theorem tfInit_exec (c : Config) (hc : WordsBounded W c) {m : ℕ} (r00 : c.nreg 9700 = m)
    (w : m + 1 ≤ W) :
    ∃ c' k, Exec P W tfInit c c' k ∧ k = 4 ∧ c'.nreg 9706 = 1 ∧ c'.nreg 9711 = 0 ∧
      c'.nreg 9707 = 0 ∧ c'.nreg 9712 = m + 1 ∧
      (∀ r, ¬ TfScr r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfInit
  exec_block
  all_goals try ((try config_simp); (try simp only [r00]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r00]
  · unfold TfScr at hr; simp only [upd_apply]; split_ifs <;> omega

theorem tfZ_exec (c : Config) (hc : WordsBounded W c) {Vb e : ℕ} (r04 : c.nreg 9704 = Vb)
    (r07 : c.nreg 9707 = e) (r06 : c.nreg 9706 = 1) (r11 : c.nreg 9711 = 0)
    (w1 : Vb + e ≤ W) (w2 : e + 1 ≤ W) :
    ∃ c' k, Exec P W tfZ c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (Vb + e) 0 ∧
      c'.nreg 9707 = e + 1 ∧ (∀ r, r ≠ 9707 → r ≠ 9708 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfZ
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r06, r07, r11]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r04, r07, r11]
  · config_simp; simp only [r06, r07]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem tfS_exec (c : Config) (hc : WordsBounded W c) {LABb Vb s : ℕ}
    (r01 : c.nreg 9701 = LABb) (r04 : c.nreg 9704 = Vb) (r14 : c.nreg 9714 = s)
    (r06 : c.nreg 9706 = 1) (w1 : LABb + s ≤ W) (w2 : Vb + c.nmem (LABb + s) ≤ W) :
    ∃ c' k, Exec P W tfS c c' k ∧ k = 5 ∧
      c'.nmem = upd c.nmem (Vb + c.nmem (LABb + s)) 1 ∧ c'.nreg 9707 = 0 ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfS
  exec_block
  all_goals try ((try config_simp); (try simp only [r01, r04, r06, r14]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r01, r04, r06, r14]
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem tfM_exec (c : Config) (hc : WordsBounded W c) {LABb Lb Vb RVb t : ℕ}
    (r01 : c.nreg 9701 = LABb) (r02 : c.nreg 9702 = Lb) (r04 : c.nreg 9704 = Vb)
    (r13 : c.nreg 9713 = RVb) (r07 : c.nreg 9707 = t) (r06 : c.nreg 9706 = 1)
    (w1 : Lb + t ≤ W) (w2 : RVb + c.nmem (Lb + t) ≤ W) (w3 : LABb + c.nmem (Lb + t) ≤ W)
    (w4 : LABb + c.nmem (RVb + c.nmem (Lb + t)) ≤ W)
    (w5 : Vb + c.nmem (LABb + c.nmem (Lb + t)) ≤ W)
    (w6 : Vb + c.nmem (LABb + c.nmem (RVb + c.nmem (Lb + t))) ≤ W)
    (d1 : Vb + c.nmem (LABb + c.nmem (Lb + t)) ≠ LABb + c.nmem (RVb + c.nmem (Lb + t)))
    (w7 : t + 1 ≤ W) :
    ∃ c' k, Exec P W tfM c c' k ∧ k = 13 ∧
      c'.nmem = upd (upd c.nmem (Vb + c.nmem (LABb + c.nmem (Lb + t))) 1)
        (Vb + c.nmem (LABb + c.nmem (RVb + c.nmem (Lb + t)))) 1 ∧ c'.nreg 9707 = t + 1 ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfM
  exec_block
  all_goals try ((try config_simp); (try simp only [r01, r02, r04, r06, r07, r13, upd_apply]); (try split_ifs) <;> omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r01, r02, r04, r06, r07, r13, upd_apply]
    split_ifs <;> first | omega | rfl
  · config_simp; simp only [r06, r07]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem tfR_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W tfR c c' k ∧ k = 1 ∧ c'.nreg 9707 = 0 ∧
      (∀ r, r ≠ 9707 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfR
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem tfG_exec (c : Config) (hc : WordsBounded W c) {LABb Vb Fb e : ℕ}
    (r01 : c.nreg 9701 = LABb) (r04 : c.nreg 9704 = Vb) (r05 : c.nreg 9705 = Fb)
    (r07 : c.nreg 9707 = e) (r06 : c.nreg 9706 = 1) (w1 : LABb + e ≤ W)
    (w2 : Vb + c.nmem (LABb + e) ≤ W) (w3 : Fb + e ≤ W) (w4 : e + 1 ≤ W) :
    ∃ c' k, Exec P W tfG c c' k ∧ k = 7 ∧
      c'.nmem = upd c.nmem (Fb + e) (c.nmem (Vb + c.nmem (LABb + e))) ∧ c'.nreg 9707 = e + 1 ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tfG
  exec_block
  all_goals try ((try config_simp); (try simp only [r01, r04, r05, r06, r07]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r01, r04, r05, r07]
  · config_simp; simp only [r06, r07]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end NcStep

end BKMNW

end PlanarFlow
