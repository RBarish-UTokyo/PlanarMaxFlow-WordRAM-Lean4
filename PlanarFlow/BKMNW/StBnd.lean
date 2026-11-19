module

public import PlanarFlow.BKMNW.StResM

/-!
# The terminal darts of the s-t flow on the machine (`KBnd`)

The input of `STFlow.pcore_exec` holds the dart `d₁` leaving the source and the dart `d₀` leaving
the sink (`Klein.KBnd 2`, at `iGB nD n`, `+ 1`). The machine's choice: **the dart of greatest index
whose tail is in `X`** (resp. `Y`), from the flags `XT`, `YT` by dart index:

* `lastF f n z` (the greatest `i < n` with `0 < f i`, `z` if none), `lastF_spec`;
* `gbProg` (one pass, natural words only, `gbProg_natOnly`), **`gbProg_exec`**: within
  `14 nD + 10` steps, `G[0] = lastF XT nD 0`, `G[1] = lastF YT nD 0` at `Gb`, `Gb + 1`;
* **`lastF_map`**: on a map numbered by `σ` with `XT (σ d) = [tail d ∈ X]` and some tail in `X`,
  `lastF XT nD 0 = σ d₁` for a dart `d₁` with tail in `X` (the same for `Y`, `d₀`);
* `kBnd_of`: the two words give `Klein.KBnd 2 (d₁, d₀)` of an input whose words are the memory
  at the input base (`gbProg` with `Gb = ib + iGB nD n`).

Registers: natural `7850 … 7853` (inputs `nD`, `Xb`, `Yb`, `Gb`), `7854 … 7859` (scratch).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-- The greatest `i < n` with `0 < f i` (`z` if there is none). -/
def lastF (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, z => z
  | i + 1, z => if 0 < f i then i else lastF f i z

theorem lastF_spec (f : ℕ → ℕ) (z : ℕ) : ∀ n, (∃ j < n, 0 < f j) →
    0 < f (lastF f n z) ∧ lastF f n z < n
  | 0, ⟨j, hj, _⟩ => absurd hj (by omega)
  | n + 1, ⟨j, hj, hf⟩ => by
    simp only [lastF]
    split_ifs with h
    · exact ⟨h, by omega⟩
    · have hjn : j < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
        · exact h'
        · exact absurd hf h
      obtain ⟨a, b⟩ := lastF_spec f z n ⟨j, hjn, hf⟩
      exact ⟨a, by omega⟩

lemma lastF_le (f : ℕ → ℕ) (z : ℕ) : ∀ n, lastF f n z < n ∨ lastF f n z = z
  | 0 => Or.inr rfl
  | n + 1 => by
    simp only [lastF]
    split_ifs
    · left; omega
    · rcases lastF_le f z n with h | h
      · left; omega
      · right; exact h

/-! ### The program -/

def gbBody : Stmt :=
  .seq (block [.addN 7859 7851 7856, .loadN 7859 7859]) <|
  .seq (.ifLtN 7855 7859 (block [.copyN 7857 7856]) .skip) <|
  .seq (block [.addN 7859 7852 7856, .loadN 7859 7859]) <|
  .seq (.ifLtN 7855 7859 (block [.copyN 7858 7856]) .skip) (block [.addN 7856 7856 7854])

/-- **The terminal darts**: the greatest dart indices with a flag, stored at `Gb`, `Gb + 1`. -/
def gbProg : Stmt :=
  .seq (block [.constN 7854 1, .constN 7855 0, .constN 7856 0, .constN 7857 0, .constN 7858 0]) <|
  .seq (.whileLtN 7856 7850 gbBody) (block [.storeN 7853 7857, .addN 7859 7853 7854,
    .storeN 7859 7858])

theorem gbProg_natOnly : Klein.natOnly gbProg = true := by kernel_rfl

/-- An `if` copying the counter into `t` when the word in `7859` is positive. -/
theorem gbIf_exec {t : ℕ} (c : Config) (hc : WordsBounded W c) (h55 : c.nreg 7855 = 0) :
    ∃ c' k, Exec P W (.ifLtN 7855 7859 (block [.copyN t 7856]) .skip) c c' k ∧ k ≤ 2 ∧
      (c'.nreg t = (if 0 < c.nreg 7859 then c.nreg 7856 else c.nreg t) ∧
        (∀ r, r ≠ t → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : 0 < c.nreg 7859
  · refine spec_ifLtN_true (by rw [h55]; exact h) ?_
    exec_block
    config_simp
    simp only [h, ↓reduceIte]
    sr_fin
  · refine spec_ifLtN_false (by rw [h55]; exact h) ?_
    refine spec_skip hc ?_
    simp only [h, ↓reduceIte]
    sr_fin

theorem gbProg_exec {nD Xb Yb Gb : ℕ} {XT YT : ℕ → ℕ} (hX : Xb + nD ≤ W) (hY : Yb + nD ≤ W)
    (hG : Gb + 1 ≤ W) (hnW : nD ≤ W) (c : Config) (hc : WordsBounded W c)
    (h50 : c.nreg 7850 = nD) (h51 : c.nreg 7851 = Xb) (h52 : c.nreg 7852 = Yb)
    (h53 : c.nreg 7853 = Gb) (mX : ∀ i < nD, c.nmem (Xb + i) = XT i)
    (mY : ∀ i < nD, c.nmem (Yb + i) = YT i) :
    ∃ c' t, Exec P W gbProg c c' t ∧ t ≤ 14 * nD + 10 ∧
      (c'.nmem = upd (upd c.nmem Gb (lastF XT nD 0)) (Gb + 1) (lastF YT nD 0) ∧
        (∀ r, r < 7854 ∨ 7860 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold gbProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 7857 = lastF XT i 0 ∧ c'.nreg 7858 = lastF YT i 0 ∧ c'.nreg 7854 = 1 ∧
      c'.nreg 7855 = 0 ∧ (∀ r, r < 7854 ∨ 7860 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 7856) (bR := 7850) (body := gbBody) J (K := 12)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact h50) ?_
    (fun i c₁ hi hw ha hb ⟨g57, g58, g54, g55, gn, gnm, gr, grm, go⟩ => by
      have e51 : c₁.nreg 7851 = Xb := (gn _ (by omega)).trans h51
      have e52 : c₁.nreg 7852 = Yb := (gn _ (by omega)).trans h52
      have xx : c₁.nmem (Xb + i) = XT i := by rw [gnm]; exact mX i hi
      have xy : c₁.nmem (Yb + i) = YT i := by rw [gnm]; exact mY i hi
      unfold gbBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e51, ha]); omega)
      refine spec_seq ?_
      refine spec_use (gbIf_exec (P := P) (t := 7857) _ ‹_› (by config_simp; exact g55)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a57, an, anm, ar, arm, ao⟩
      have f52 : c₂.nreg 7852 = Yb := by rw [an _ (by omega)]; config_simp; exact e52
      have f56 : c₂.nreg 7856 = i := by rw [an _ (by omega)]; config_simp; exact ha
      have f55 : c₂.nreg 7855 = 0 := by rw [an _ (by omega)]; config_simp; exact g55
      have f54 : c₂.nreg 7854 = 1 := by rw [an _ (by omega)]; config_simp; exact g54
      have fm : c₂.nmem = c₁.nmem := by rw [anm]
      have f57 : c₂.nreg 7857 = lastF XT (i + 1) 0 := by
        rw [a57]; config_simp; rw [ha, e51, xx, g57]; simp only [lastF]
      have f58 : c₂.nreg 7858 = lastF YT i 0 := by rw [an _ (by omega)]; config_simp; exact g58
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [f52, f56]); omega)
      refine spec_seq ?_
      refine spec_use (gbIf_exec (P := P) (t := 7858) _ ‹_› (by config_simp; exact f55)) ?_
      intro c₃ k₃ hk₃ hw₃ ⟨b58, bn, bnm, br, brm, bo⟩
      have e56 : c₃.nreg 7856 = i := by rw [bn _ (by omega)]; config_simp; exact f56
      have e54 : c₃.nreg 7854 = 1 := by rw [bn _ (by omega)]; config_simp; exact f54
      have e55 : c₃.nreg 7855 = 0 := by rw [bn _ (by omega)]; config_simp; exact f55
      have e57 : c₃.nreg 7857 = lastF XT (i + 1) 0 := by
        rw [bn _ (by omega)]; config_simp; exact f57
      have e58 : c₃.nreg 7858 = lastF YT (i + 1) 0 := by
        rw [b58]; config_simp; simp only [f52, f56, fm, xy, f58]; simp only [lastF]
      have en : ∀ r, r < 7854 ∨ 7860 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
        rw [bn _ (by omega)]; config_simp
        simp only [upd_apply, show r ≠ 7859 by omega, ↓reduceIte]
        rw [an _ (by omega)]; config_simp
        simp only [upd_apply, show r ≠ 7859 by omega, ↓reduceIte]
        exact gn r hr
      have e50 : c₃.nreg 7850 = nD := by
        rw [bn _ (by omega)]; config_simp; rw [an _ (by omega)]; config_simp; exact hb
      have em : c₃.nmem = c.nmem := by rw [bnm, fm, gnm]
      have er : c₃.rreg = c.rreg := by rw [br, ar]; config_simp; exact gr
      have erm : c₃.rmem = c.rmem := by rw [brm, arm]; config_simp; exact grm
      have eo : c₃.output = c.output := by rw [bo, ao]; config_simp; exact go
      exec_block
      all_goals try ((try config_simp); (try simp only [e56, e54]); omega)
      dsimp only [J]
      config_simp
      simp only [e56, e54, e55, e57, e58, e50, em, er, erm, eo]
      and_intros
      all_goals first | omega | rfl | trivial |
        (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact en r hr))) ?_
  · dsimp only [J]
    config_simp
    sr_fin
  intro c₂ k₂ hk₂ _ ⟨_, g57, g58, g54, g55, gn, gnm, gr, grm, go⟩
  have e53 : c₂.nreg 7853 = Gb := (gn _ (by omega)).trans h53
  exec_block
  all_goals try ((try config_simp); (try simp only [e53, g54]); omega)
  config_simp
  simp only [e53, g54, g57, g58, gnm, gr, grm, go]
  and_intros
  all_goals first | omega | rfl | trivial |
    (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)


/-! ### On a map -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The dart chosen from the flags of a vertex set** has its tail in the set, if some tail is. -/
theorem lastF_map {nD : ℕ} (σ : D ≃ Fin nD) {XT : ℕ → ℕ} {X : Finset V}
    (hXT : ∀ d, XT (σ d) = if M.tail d ∈ X then 1 else 0) (hX : ∃ d, M.tail d ∈ X) :
    ∃ d₁, M.tail d₁ ∈ X ∧ (σ d₁ : ℕ) = lastF XT nD 0 := by
  obtain ⟨d, hd⟩ := hX
  obtain ⟨h1, h2⟩ := lastF_spec XT 0 nD ⟨σ d, (σ d).2, by rw [hXT, ite_cond_eq_true _ _ (eq_true hd)]; omega⟩
  refine ⟨σ.symm ⟨_, h2⟩, ?_, by simp⟩
  have := hXT (σ.symm ⟨_, h2⟩)
  rw [Equiv.apply_symm_apply] at this
  simp only at this
  by_contra hn
  rw [if_neg hn] at this
  omega

/-- `KBnd 2` from the two words of the input. -/
theorem kBnd_of {nD n : ℕ} (σ : D ≃ Fin nD) {P : Input} {d₀ d₁ : D}
    (h0 : P.data.getD (Klein.iGB nD n) 0 = σ d₁) (h1 : P.data.getD (Klein.iGB nD n + 1) 0 = σ d₀) :
    Klein.KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P := by
  intro i hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using h0
  · simpa using h1

end StEnc

end BKMNW

end PlanarFlow
