module

public import PlanarFlow.BKMNW.S7B

/-!
# Stage 7 of `sepL` composed (III): the left piece and the outputs 1–4

* `s7G_exec'` (`s7G_exec` with the inputs above the outputs, proof copied);
* **`s7bC_exec`** (`odC` after `s7bAB_exec`): `LF[i] = bf (g i ∈ l)` at `LFb = Z + 34 n + 8 k + 11`
  and `g i ∈ r ↔ g i ∉ l`, `l`, `r` the two pieces of `splitOf` for the order `ordE eG N` of the
  classes `clsF`;
* `s7O1` (the gather `LF ∘ FX` to `Sb`), **`s7O1_exec`**.
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

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The gathers of the outputs 2–4**, the inputs above the outputs. -/
theorem s7G_exec' (c : Config) (hc : WordsBounded W c) {m k FXb DFb VFb HTb Sb n : ℕ}
    (r30 : c.nreg 7130 = m) (r31 : c.nreg 7131 = FXb) (r32 : c.nreg 7132 = DFb)
    (r02 : c.nreg 7102 = VFb) (r33 : c.nreg 7133 = Sb + m) (r34 : c.nreg 7134 = Sb + 2 * m)
    (r35 : c.nreg 7135 = k) (r36 : c.nreg 7136 = HTb + 1) (r37 : c.nreg 7137 = Sb + 3 * m)
    (hfx : ∀ i < m, c.nmem (FXb + i) < n)
    (lay : FXb + m ≤ Sb ∧ Sb + 3 * m + k ≤ DFb ∧ Sb + 3 * m + k ≤ VFb ∧ Sb + 3 * m + k ≤ HTb ∧
      DFb + n ≤ W ∧ VFb + n ≤ W ∧ HTb + k + 1 ≤ W) (hW : m + k + 1 ≤ W) :
    ∃ c' t, Exec P W s7G c c' t ∧ t ≤ 18 * m + 7 * k + 30 ∧
      (∀ i < m, c'.nmem (Sb + m + i) = c.nmem (DFb + c.nmem (FXb + i))) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = c.nmem (VFb + c.nmem (FXb + i))) ∧
      (∀ j < k, c'.nmem (Sb + 3 * m + j) = c.nmem (HTb + 1 + j)) ∧
      (∀ a, ¬ (Sb + m ≤ a ∧ a < Sb + 3 * m + k) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6210) ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := lay
  unfold s7G s7G1 s7G2 s7G3
  obtain ⟨c₁, t₁, e₁, ht₁, f1, fm1, fn1, fr1, frm1, fo1⟩ := ggProg_exec (P := P) c hc
    (a := 7130) (b := 7131) (cc := 7132) (dd := 7133) (m := m) (IXb := FXb) (Ab := DFb)
    (OUTb := Sb + m) (by omega) (by omega) (by omega) (by omega) r30 r31 r32 r33 (by omega)
    (by omega) (by omega) (fun j hj => by have := hfx j hj; omega) (fun j hj => by omega)
    (fun j hj => by have := hfx j hj; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := ggProg_exec (P := P) c₁ e₁.wb_right
    (a := 7130) (b := 7131) (cc := 7102) (dd := 7134) (m := m) (IXb := FXb) (Ab := VFb)
    (OUTb := Sb + 2 * m) (by omega) (by omega) (by omega) (by omega)
    (by rw [fn1 _ (by omega)]; exact r30) (by rw [fn1 _ (by omega)]; exact r31)
    (by rw [fn1 _ (by omega)]; exact r02) (by rw [fn1 _ (by omega)]; exact r34) (by omega)
    (by omega) (by omega)
    (fun j hj => by rw [fm1 _ (by omega)]; have := hfx j hj; omega) (fun j hj => by omega)
    (fun j hj => by rw [fm1 _ (by omega)]; have := hfx j hj; omega)
  have q35 : c₂.nreg 7135 = k := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r35
  have q36 : c₂.nreg 7136 = HTb + 1 := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r36
  have q37 : c₂.nreg 7137 = Sb + 3 * m := by rw [fn2 _ (by omega), fn1 _ (by omega)]; exact r37
  obtain ⟨c₃, t₃, e₃, ht₃, s0, s1, s2, sm3, sn3, sr3, srm3, so3⟩ := s7G3a_exec (P := P) c₂
    e₂.wb_right q35 q36 q37
  obtain ⟨c₄, t₄, e₄, ht₄, f4, fm4, fn4, fr4, frm4, fo4⟩ := cpArr_exec (P := P) c₃ e₃.wb_right
    s0 s1 s2 ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [fr4, sr3, fr2, fr1], by rw [frm4, srm3, frm2, frm1], by rw [fo4, so3, fo2, fo1]⟩
  · have hx := hfx i hi
    rw [fm4 _ (by omega), sm3, fm2 _ (by omega), f1 i hi]
  · have hx := hfx i hi
    rw [fm4 _ (by omega), sm3, f2 i hi, fm1 (FXb + i) (by omega), fm1 _ (by omega)]
  · rw [f4 j hj, sm3, fm2 _ (by omega), fm1 _ (by omega)]
  · rw [fm4 a (by omega), sm3, fm2 a (by omega), fm1 a (by omega)]
  · rw [fn4 x (by omega), sn3 x (by omega), fn2 x (by omega), fn1 x (by omega)]


/-- The gather of the output 1: `Sb + i = LF[FX[i]]` (`LFb = WTb + n`). -/
def s7O1 : Stmt := .seq (block [.addN 7198 7186 7100]) (ggProg 7130 7131 7198 7193)

theorem s7O1_exec (c : Config) (hc : WordsBounded W c) {m n FXb WTb Sb : ℕ}
    (r30 : c.nreg 7130 = m) (r31 : c.nreg 7131 = FXb) (r86 : c.nreg 7186 = WTb)
    (r00 : c.nreg 7100 = n) (r93 : c.nreg 7193 = Sb) (hfx : ∀ i < m, c.nmem (FXb + i) < n)
    (lay : FXb + m ≤ Sb ∧ Sb + m ≤ WTb + n ∧ WTb + 2 * n ≤ W) (hW : m + 1 ≤ W) :
    ∃ c' t, Exec P W s7O1 c c' t ∧ t ≤ 9 * m + 9 ∧
      (∀ i < m, c'.nmem (Sb + i) = c.nmem (WTb + n + c.nmem (FXb + i))) ∧
      (∀ a, ¬ (Sb ≤ a ∧ a < Sb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → x ≠ 7198 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  unfold s7O1
  obtain ⟨c₁, t₁, e₁, ht₁, a1, m1, n1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 7198 7186 7100]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 7198 = WTb + n ∧
      c₁.nmem = c.nmem ∧ (∀ x, x ≠ 7198 → c₁.nreg x = c.nreg x) ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [r86, r00]); omega)
    refine ⟨rfl, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [r86, r00]
    · config_simp; simp (disch := omega) only [upd_other]
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := ggProg_exec (P := P) c₁ e₁.wb_right
    (a := 7130) (b := 7131) (cc := 7198) (dd := 7193) (m := m) (IXb := FXb) (Ab := WTb + n)
    (OUTb := Sb) (by omega) (by omega) (by omega) (by omega)
    ((n1 _ (by omega)).trans r30) ((n1 _ (by omega)).trans r31) a1 ((n1 _ (by omega)).trans r93)
    (by omega) (by omega) hW (fun j hj => by rw [m1]; have := hfx j hj; omega)
    (fun j hj => by omega) (fun j hj => by rw [m1]; have := hfx j hj; omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega, fun i hi => by rw [f2 i hi, m1], fun a ha => by
    rw [fm2 a ha, m1], fun x h1 h2 => by rw [fn2 x h1, n1 x h2], by rw [fr2, rr1],
    by rw [frm2, rm1], by rw [fo2, o1]⟩

end Exec

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The flags of the two pieces of the split on the record** (`odC` after `s7bAB_exec`). -/
theorem s7bC_exec {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)} {K A : ℕ}
    {ρ : HPath M} {g : ℕ → D} {gid : D → ℕ} {eG : ℕ → D} {N : ℕ} (c : Config)
    (hc : WordsBounded W c) {n k Z HPb : ℕ} {cid lst : ℕ → ℕ}
    (hOd : OdIn Ps (clsF M Ps Nf Hs K ρ) g n cid lst)
    (hmono : ∀ i j, i < j → j < n → gid (g i) < gid (g j))
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (RB : OdRegsB c n k HPb (Z + n) K (Z + 30 * n + 5 * k + 7) (odM lst n))
    (r53 : c.nreg 7153 = A)
    (mP1 : ∀ i < n, c.nmem (Z + 30 * n + 5 * k + 7 + i) = odPos lst i + 1)
    (mWT : ∀ q < odM lst n, c.nmem (Z + 33 * n + 8 * k + 11 + q) =
      hw M K Hs ρ.mverts (odL g n lst q))
    (hwA : ∀ q < odM lst n, hw M K Hs ρ.mverts (odL g n lst q) ≤ A) (hA3 : 3 * A ≤ W)
    (lay : Z + 35 * n + 8 * k + 12 ≤ W) :
    ∃ c' t, Exec P W odC c c' t ∧ t ≤ 50 * n + 40 ∧
      (∀ i < n, c'.nmem (Z + 34 * n + 8 * k + 11 + i) = bf (g i ∈
        (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ i < n, (g i ∈ (Ps.image (clsF M Ps Nf Hs K ρ) \ (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset).biUnion _root_.id ↔
        g i ∉ (twoGroupsL (hw M K Hs ρ.mverts) A
          (ordE eG N (Ps.image (clsF M Ps Nf Hs K ρ)))).toFinset.biUnion _root_.id)) ∧
      (∀ a, ¬ (Z + 34 * n + 8 * k + 11 ≤ a ∧ a < Z + 35 * n + 8 * k + 11) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4000 ∨ (4013 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x < 7181) ∨
        (7183 < x ∧ x < 7187) ∨ (7187 < x ∧ x < 7190) ∨ 7192 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hmC : odM lst n ≤ n := cnt_le _ _
  obtain ⟨c', t, e, ht, htg, hLF, fm, fn, fr, frm, fo⟩ := odC_exec (P := P) c hc (n := n)
    (mC := odM lst n) (WTb := Z + 33 * n + 8 * k + 11) (A := A) (P1b := Z + 30 * n + 5 * k + 7)
    (wt := fun q => hw M K Hs ρ.mverts (odL g n lst q)) (p1 := fun i => odPos lst i + 1)
    RB.r00 RB.r06 (by rw [RB.r86]; ring) r53 RB.r80 RB.r21 mWT mP1
    (fun q hq => by have := hwA q hq; omega) hmC ⟨by omega, by omega⟩
  have hS := fun i (hi : i < n) => od_left_sem hOd hmono he hesurj (ω := hw M K Hs ρ.mverts)
    (A := A) (wt := fun q => hw M K Hs ρ.mverts (odL g n lst q)) (fun q hq => rfl) htg hi
  refine ⟨c', t, e, ht, fun i hi => ?_, fun i hi => ?_, fun a ha => fm a (by omega), fn,
    fr, frm, fo⟩
  · rw [show Z + 34 * n + 8 * k + 11 + i = Z + 33 * n + 8 * k + 11 + n + i by ring, hLF i hi]
    simp only [Nat.add_sub_cancel]
    unfold bf
    exact if_congr (hS i hi).1.symm rfl rfl
  · rw [(hS i hi).1, (hS i hi).2]

end Sem

end MfDrv

end BKMNW

end PlanarFlow
