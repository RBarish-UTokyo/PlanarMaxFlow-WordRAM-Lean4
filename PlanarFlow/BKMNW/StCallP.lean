module

public import PlanarFlow.BKMNW.StBnd

/-!
# Two small loops of the s-t flow call: the clamped copy and the read-back

* **`clpProg`** (registers `9120 … 9128`): copy `n` words from `Sb` to `Db`, each clamped to
  `cap` (`min`); **`clpProg_exec`** within `11 n + 4` steps. The s-t flow call copies the encoded
  input into the low memory with it: every word of the copy is then at most `cap` (the bound
  `hbd` of `STFlow.st_sNFM_mem`), and the words already below `cap` are copied unchanged.
* **`rdbProg`** (registers `9130 … 9140`): for `i < m`, `O[i] := rdv Z H Mo (I[i])`
  (`rdv Z H Mo v = Z + v` if `v ≤ H`, `Z + v - Mo` otherwise, natural subtraction);
  **`rdbProg_exec`** within `12 m + 4` steps; **`rdv_eq`**: `rdv Z H Mo v = max 0 (Z + sdec Mo H v)`
  (the signed value of a residue word, shifted by `Z`).

Natural words only (`clpProg_natOnly`, `rdbProg_natOnly`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc

variable {P : Input} {W : ℕ}

/-! ### The clamped copy -/

/-- One word of the clamped copy. -/
def clpBody : Stmt :=
  .seq (block [.addN 9126 9121 9124, .loadN 9127 9126])
    (.seq (.ifLtN 9123 9127 (block [.copyN 9127 9123]) .skip)
      (block [.addN 9126 9122 9124, .storeN 9126 9127, .addN 9124 9124 9125]))

/-- **The clamped copy**: `D[i] := min (S[i]) cap` for `i < n` (`9120 = n`, `9121 = Sb`,
`9122 = Db`, `9123 = cap`). -/
def clpProg : Stmt :=
  .seq (block [.constN 9124 0, .constN 9125 1]) (.whileLtN 9124 9120 clpBody)

theorem clpProg_natOnly : Klein.natOnly clpProg = true := by kernel_rfl

/-- The clamp: `r9127 := min r9127 r9123`. -/
theorem clpIf_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (.ifLtN 9123 9127 (block [.copyN 9127 9123]) .skip) c c' k ∧ k ≤ 2 ∧
      (c'.nreg 9127 = min (c.nreg 9127) (c.nreg 9123) ∧
        (∀ r, r ≠ 9127 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : c.nreg 9123 < c.nreg 9127
  · refine spec_ifLtN_true h ?_
    exec_block
    config_simp
    sr_fin
  · refine spec_ifLtN_false h ?_
    refine spec_skip hc ?_
    sr_fin

/-- **The clamped copy** (see the module docstring). -/
theorem clpProg_exec (c : Config) (hc : WordsBounded W c) {n Sb Db cap : ℕ}
    (h20 : c.nreg 9120 = n) (h21 : c.nreg 9121 = Sb) (h22 : c.nreg 9122 = Db)
    (h23 : c.nreg 9123 = cap) (hd : Sb + n ≤ Db ∨ Db + n ≤ Sb) (hS : Sb + n ≤ W)
    (hD : Db + n ≤ W) (hn : n + 1 ≤ W) :
    ∃ c' t, Exec P W clpProg c c' t ∧ t ≤ 11 * n + 4 ∧
      (∀ i < n, c'.nmem (Db + i) = min (c.nmem (Sb + i)) cap) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9124 ∨ 9128 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clpProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 9125 = 1 ∧ (∀ r, (r < 9124 ∨ 9128 < r) → c'.nreg r = c.nreg r) ∧
      (∀ j < i, c'.nmem (Db + j) = min (c.nmem (Sb + j)) cap) ∧
      (∀ a, (a < Db ∨ Db + i ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 9124) (bR := 9120) (body := clpBody) J (K := 9)
    (n := n) _ ‹_› (by config_simp) (by config_simp; exact h20) ?_
    (fun i c₁ hi hw ha hb ⟨g25, gn, gd, gk, gr, grm, go⟩ => by
      have e21 : c₁.nreg 9121 = Sb := (gn _ (by omega)).trans h21
      have e22 : c₁.nreg 9122 = Db := (gn _ (by omega)).trans h22
      have e23 : c₁.nreg 9123 = cap := (gn _ (by omega)).trans h23
      have xs : c₁.nmem (Sb + i) = c.nmem (Sb + i) := gk _ (by omega)
      unfold clpBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e21, ha]); omega)
      refine spec_seq ?_
      refine spec_use (clpIf_exec (P := P) _ ‹_›) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a27, an, anm, ar, arm, ao⟩
      have f22 : c₂.nreg 9122 = Db := by rw [an _ (by omega)]; config_simp; exact e22
      have f24 : c₂.nreg 9124 = i := by rw [an _ (by omega)]; config_simp; exact ha
      have f25 : c₂.nreg 9125 = 1 := by rw [an _ (by omega)]; config_simp; exact g25
      have f27 : c₂.nreg 9127 = min (c.nmem (Sb + i)) cap := by
        rw [a27]; config_simp; simp only [e21, ha, xs, e23]
      have fm : c₂.nmem = c₁.nmem := by rw [anm]
      have fn : ∀ r, (r < 9124 ∨ 9128 < r) → c₂.nreg r = c.nreg r := fun r hr => by
        rw [an _ (by omega)]; config_simp
        simp only [upd_apply, show r ≠ 9127 by omega, show r ≠ 9126 by omega, ↓reduceIte]
        exact gn r hr
      have er : c₂.rreg = c.rreg := by rw [ar]; config_simp; exact gr
      have erm : c₂.rmem = c.rmem := by rw [arm]; config_simp; exact grm
      have eo : c₂.output = c.output := by rw [ao]; config_simp; exact go
      exec_block
      all_goals try ((try config_simp); (try simp only [f22, f24, f25]); omega)
      dsimp only [J]
      config_simp
      simp only [f22, f24, f25, f27, fm, er, erm, eo]
      and_intros
      all_goals first | omega | rfl | trivial | (rw [fn _ (by omega)]; exact h20) |
        (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact fn r hr) |
        (intro j hj; simp only [upd_apply]; split_ifs with h
         · have : j = i := by omega
           subst this; rfl
         · exact gd j (by omega)) |
        (intro a ha'; simp only [upd_apply]; split_ifs with h
         · omega
         · exact gk a (by omega)))) ?_
  · dsimp only [J]
    config_simp
    and_intros
    all_goals first | rfl | trivial | (intros; trivial) | (intro j hj; omega) |
      (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  intro c₂ k₂ hk₂ _ ⟨_, g25, gn, gd, gk, gr, grm, go⟩
  exact ⟨by omega, gd, gk, gn, gr, grm, go⟩

/-! ### The read-back -/

/-- The read-back of a residue word: `Z + v` if `v ≤ H`, else `Z + v - Mo`. -/
def rdv (Z H Mo v : ℕ) : ℕ := if H < v then Z + v - Mo else Z + v

/-- **The read-back is the shifted signed value** (clamped at `0`). -/
theorem rdv_eq (Z H Mo v : ℕ) : (rdv Z H Mo v : ℤ) = max 0 ((Z : ℤ) + STFlow.sdec Mo H v) := by
  unfold rdv STFlow.sdec
  split_ifs with h1 h2 h2
  · omega
  · push_cast; omega
  · omega
  · omega

/-- One word of the read-back. -/
def rdbBody : Stmt :=
  .seq (block [.addN 9138 9131 9136, .loadN 9139 9138, .addN 9140 9133 9139])
    (.seq (.ifLtN 9134 9139 (block [.subN 9140 9140 9135]) .skip)
      (block [.addN 9138 9132 9136, .storeN 9138 9140, .addN 9136 9136 9137]))

/-- **The read-back**: `O[i] := rdv Z H Mo (I[i])` for `i < m` (`9130 = m`, `9131 = Ib`,
`9132 = Ob`, `9133 = Z`, `9134 = H`, `9135 = Mo`). -/
def rdbProg : Stmt :=
  .seq (block [.constN 9136 0, .constN 9137 1]) (.whileLtN 9136 9130 rdbBody)

theorem rdbProg_natOnly : Klein.natOnly rdbProg = true := by kernel_rfl

theorem rdbIf_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (.ifLtN 9134 9139 (block [.subN 9140 9140 9135]) .skip) c c' k ∧ k ≤ 2 ∧
      (c'.nreg 9140 = (if c.nreg 9134 < c.nreg 9139 then c.nreg 9140 - c.nreg 9135
          else c.nreg 9140) ∧
        (∀ r, r ≠ 9140 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : c.nreg 9134 < c.nreg 9139
  · refine spec_ifLtN_true h ?_
    exec_block
    config_simp
    simp only [h, ↓reduceIte]
    sr_fin
  · refine spec_ifLtN_false h ?_
    refine spec_skip hc ?_
    simp only [h, ↓reduceIte]
    sr_fin

/-- **The read-back** (see the module docstring). -/
theorem rdbProg_exec (c : Config) (hc : WordsBounded W c) {m Ib Ob Z H Mo : ℕ}
    (h30 : c.nreg 9130 = m) (h31 : c.nreg 9131 = Ib) (h32 : c.nreg 9132 = Ob)
    (h33 : c.nreg 9133 = Z) (h34 : c.nreg 9134 = H) (h35 : c.nreg 9135 = Mo)
    (hd : Ib + m ≤ Ob ∨ Ob + m ≤ Ib) (hI : Ib + m ≤ W) (hO : Ob + m ≤ W) (hn : m + 1 ≤ W)
    (hZ : ∀ i < m, Z + c.nmem (Ib + i) ≤ W) :
    ∃ c' t, Exec P W rdbProg c c' t ∧ t ≤ 12 * m + 4 ∧
      (∀ i < m, c'.nmem (Ob + i) = rdv Z H Mo (c.nmem (Ib + i))) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9136 ∨ 9140 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rdbProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 9137 = 1 ∧ (∀ r, (r < 9136 ∨ 9140 < r) → c'.nreg r = c.nreg r) ∧
      (∀ j < i, c'.nmem (Ob + j) = rdv Z H Mo (c.nmem (Ib + j))) ∧
      (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 9136) (bR := 9130) (body := rdbBody) J (K := 10)
    (n := m) _ ‹_› (by config_simp) (by config_simp; exact h30) ?_
    (fun i c₁ hi hw ha hb ⟨g37, gn, gd, gk, gr, grm, go⟩ => by
      have e31 : c₁.nreg 9131 = Ib := (gn _ (by omega)).trans h31
      have e32 : c₁.nreg 9132 = Ob := (gn _ (by omega)).trans h32
      have e33 : c₁.nreg 9133 = Z := (gn _ (by omega)).trans h33
      have e34 : c₁.nreg 9134 = H := (gn _ (by omega)).trans h34
      have e35 : c₁.nreg 9135 = Mo := (gn _ (by omega)).trans h35
      have xs : c₁.nmem (Ib + i) = c.nmem (Ib + i) := gk _ (by omega)
      have hz := hZ i hi
      unfold rdbBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e31, e33, ha, xs]); omega)
      refine spec_seq ?_
      refine spec_use (rdbIf_exec (P := P) _ ‹_›) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a40, an, anm, ar, arm, ao⟩
      have f32 : c₂.nreg 9132 = Ob := by rw [an _ (by omega)]; config_simp; exact e32
      have f36 : c₂.nreg 9136 = i := by rw [an _ (by omega)]; config_simp; exact ha
      have f37 : c₂.nreg 9137 = 1 := by rw [an _ (by omega)]; config_simp; exact g37
      have f40 : c₂.nreg 9140 = rdv Z H Mo (c.nmem (Ib + i)) := by
        rw [a40]; config_simp; simp only [e31, ha, xs, e33, e34, e35]; rfl
      have fm : c₂.nmem = c₁.nmem := by rw [anm]
      have fn : ∀ r, (r < 9136 ∨ 9140 < r) → c₂.nreg r = c.nreg r := fun r hr => by
        rw [an _ (by omega)]; config_simp
        simp only [upd_apply, show r ≠ 9140 by omega, show r ≠ 9139 by omega,
          show r ≠ 9138 by omega, ↓reduceIte]
        exact gn r hr
      have er : c₂.rreg = c.rreg := by rw [ar]; config_simp; exact gr
      have erm : c₂.rmem = c.rmem := by rw [arm]; config_simp; exact grm
      have eo : c₂.output = c.output := by rw [ao]; config_simp; exact go
      exec_block
      all_goals try ((try config_simp); (try simp only [f32, f36, f37]); omega)
      dsimp only [J]
      config_simp
      simp only [f32, f36, f37, f40, fm, er, erm, eo]
      and_intros
      all_goals first | omega | rfl | trivial | (rw [fn _ (by omega)]; exact h30) |
        (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact fn r hr) |
        (intro j hj; simp only [upd_apply]; split_ifs with h
         · have : j = i := by omega
           subst this; rfl
         · exact gd j (by omega)) |
        (intro a ha'; simp only [upd_apply]; split_ifs with h
         · omega
         · exact gk a (by omega)))) ?_
  · dsimp only [J]
    config_simp
    and_intros
    all_goals first | rfl | trivial | (intros; trivial) | (intro j hj; omega) |
      (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  intro c₂ k₂ hk₂ _ ⟨_, g37, gn, gd, gk, gr, grm, go⟩
  exact ⟨by omega, gd, gk, gn, gr, grm, go⟩

end StCall

end BKMNW

end PlanarFlow
