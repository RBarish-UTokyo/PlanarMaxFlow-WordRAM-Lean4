module

public import PlanarSeparator.Machine.PieceBridge

/-!
# Small loops of the program of a piece

* `clrLoop`, **`clrLoop_exec`**: clear the memory cells `[a, b)` (the counter `ri` from `a` to
  the bound in `rb`, the register `rz` holding `0`).
* `mapLoop`, **`mapLoop_exec`**: for every vertex `L[j]` of the list, the cell
  `base + L[j]` (`base` in `1042`) gets `mem[pp + j]` if `j < ℓ` and `0` otherwise
  (`pp` in `1064`, `ℓ` in `1065`): the words printed by the separator program written back to
  the vertices (as `List.getD`), or (with `ℓ = 0`) the clearing of the labels.
* `rkClr`, **`rkClr_exec`**: clear the ranks `aRk + g` of the darts `g` of the vertices of the
  list.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### Clearing an interval -/

/-- The body of the clearing loop: `mem[i] := 0; i := i + 1`. -/
def clrBody (ri rz one : ℕ) : Stmt := block [.storeN ri rz, .addN ri ri one]

/-- **The clearing loop** `while i < b do mem[i] := 0; i := i + 1`. -/
def clrLoop (ri rb rz one : ℕ) : Stmt := .whileLtN ri rb (clrBody ri rz one)

theorem clrLoop_exec {c : Config} (hc : WordsBounded W c) {ri rb rz one a b : ℕ}
    (hrb : ri ≠ rb) (hrz : ri ≠ rz) (hone : ri ≠ one)
    (h1 : c.nreg one = 1) (h0 : c.nreg rz = 0) (ha : c.nreg ri = a) (hb : c.nreg rb = b)
    (hab : a ≤ b) (hbW : b ≤ W) :
    ∃ c' k', Exec P W (clrLoop ri rb rz one) c c' k' ∧ k' ≤ 4 * (b - a) + 2 ∧
      (∀ x, a ≤ x → x < b → c'.nmem x = 0) ∧
      (∀ x, (x < a ∨ b ≤ x) → c'.nmem x = c.nmem x) := by
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧ d.nreg ri = i ∧ d.nreg rb = b ∧
    d.nreg one = 1 ∧ d.nreg rz = 0 ∧ a ≤ i ∧ (∀ x, a ≤ x → x < i → d.nmem x = 0) ∧
    (∀ x, (x < a ∨ i ≤ x) → d.nmem x = c.nmem x)
  obtain ⟨c', k', e', hI', hk'⟩ := Exec.forN (P := P) (W := W) (ri := ri) (rN := rb) (N := b)
    (lo := a) (B := 2) (body := clrBody ri rz one) I (fun j d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d h hi => by
      obtain ⟨hw, hri, hrb', h01, hz, hai, hA, hB⟩ := h
      unfold clrBody
      exec_block
      · simp only [Config.nreg_mk, Config.nmem_mk]; rw [hri, h01]; omega
      · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, by omega⟩
        simp only [Config.nreg_mk, Config.nmem_mk]
        rw [upd_same, upd_other _ _ _ (Ne.symm hrb), upd_other _ _ _ (Ne.symm hone),
          upd_other _ _ _ (Ne.symm hrz), hri, h01, hz]
        refine ⟨rfl, hrb', rfl, rfl, by omega, fun x h1 h2 => ?_, fun x hx => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hA x h1 h2
          · rw [upd_same]
        · rw [upd_other _ _ _ (by omega)]; exact hB x (by omega))
    hab ⟨hc, ha, hb, h1, h0, le_rfl, fun x h1 h2 => by omega, fun x _ => rfl⟩
  exact ⟨c', k', e', by omega, hI'.2.2.2.2.2.2.1, hI'.2.2.2.2.2.2.2⟩

/-! ### Writing back to the vertices of the list -/

/-- The body of the write-back loop: `x := (j < ℓ ? mem[pp + j] : 0); mem[base + L[j]] := x`. -/
def mapBody : Stmt :=
  .seq (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1042 1031, .constN 1036 0])
    (.seq (.ifLtN 1030 1065 (block [.addN 1035 1064 1030, .loadN 1036 1035]) .skip)
      (block [.storeN 1034 1036, .addN 1030 1030 1001]))

/-- **The write-back loop** over the list. -/
def mapLoop : Stmt := .seq (.instr (.constN 1030 0)) (.whileLtN 1030 1016 mapBody)

theorem mapLoop_exec {c : Config} (hc : WordsBounded W c) {k ℓ pp base : ℕ} (Lv : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (hk : c.nreg 1016 = k) (hℓ : c.nreg 1065 = ℓ)
    (hpp : c.nreg 1064 = pp) (hbase : c.nreg 1042 = base)
    (hL : ∀ j < k, c.nmem (c.nreg 1015 + j) = Lv j)
    (hinj : ∀ i < k, ∀ j < k, Lv i = Lv j → i = j)
    (hdis : ∀ i < k, ∀ j < k, base + Lv i ≠ c.nreg 1015 + j)
    (hdis' : ∀ i < k, ∀ j < min k ℓ, base + Lv i ≠ pp + j)
    (hW : k + 1 ≤ W) (hWL : c.nreg 1015 + k ≤ W) (hWl : ∀ j < k, base + Lv j ≤ W)
    (hWp : pp + k ≤ W) :
    ∃ c' k', Exec P W mapLoop c c' k' ∧ k' ≤ 15 * k + 3 ∧
      (∀ j < k, c'.nmem (base + Lv j) = if j < ℓ then c.nmem (pp + j) else 0) ∧
      (∀ a, (∀ j < k, a ≠ base + Lv j) → c'.nmem a = c.nmem a) := by
  set aL := c.nreg 1015
  let I : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg 1030 = j ∧
    d.nreg 1016 = k ∧ d.nreg 1001 = 1 ∧ d.nreg 1015 = aL ∧ d.nreg 1042 = base ∧
    d.nreg 1064 = pp ∧ d.nreg 1065 = ℓ ∧
    (∀ j' < j, d.nmem (base + Lv j') = if j' < ℓ then c.nmem (pp + j') else 0) ∧
    (∀ a, (∀ j' < j, a ≠ base + Lv j') → d.nmem a = c.nmem a)
  have e₀ := Exec.constN (P := P) hc 1030 0 (Nat.zero_le _)
  obtain ⟨c', k', e', hI', hk'⟩ := Exec.forN (P := P) (W := W) (ri := 1030) (rN := 1016) (N := k)
    (lo := 0) (B := 13) (body := mapBody) I (fun j d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j d h hj => by
      obtain ⟨hw, h30, h16, h01, h15, h42, h64, h65, hA, hB⟩ := h
      have hv : d.nmem (d.nreg 1015 + d.nreg 1030) = Lv j := by
        rw [h15, h30, hB _ (fun j' _ => (hdis j' (by omega) j hj).symm)]; exact hL j hj
      -- the first block
      obtain ⟨d₁, k₁, e₁, hw₁, g30, g31, g34, g36, g42, g64, g65, g01, g15, g16, hm₁, hk₁⟩ :
          ∃ d₁ k₁, Exec P W (block [.addN 1034 1015 1030, .loadN 1031 1034,
            .addN 1034 1042 1031, .constN 1036 0]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
            d₁.nreg 1030 = j ∧ d₁.nreg 1031 = Lv j ∧ d₁.nreg 1034 = base + Lv j ∧
            d₁.nreg 1036 = 0 ∧ d₁.nreg 1042 = base ∧ d₁.nreg 1064 = pp ∧ d₁.nreg 1065 = ℓ ∧
            d₁.nreg 1001 = 1 ∧ d₁.nreg 1015 = aL ∧ d₁.nreg 1016 = k ∧ d₁.nmem = d.nmem ∧
            k₁ = 4 := by
        exec_block
        · config_simp; rw [h15, h30]; omega
        · config_simp; rw [hv, h42]; exact hWl j hj
        · omega
        · refine ⟨‹WordsBounded _ _›, ?_⟩
          config_simp
          rw [hv]
          simp only [h30, h42, h64, h65, h01, h15, h16, and_self]
      -- the test
      obtain ⟨d₂, k₂, e₂, hw₂, f36, hr₂, hm₂, hk₂⟩ : ∃ d₂ k₂, Exec P W
          (.ifLtN 1030 1065 (block [.addN 1035 1064 1030, .loadN 1036 1035]) .skip) d₁ d₂ k₂ ∧
          WordsBounded W d₂ ∧ d₂.nreg 1036 = (if j < ℓ then c.nmem (pp + j) else 0) ∧
          (∀ r, r ≠ 1035 → r ≠ 1036 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem ∧
          k₂ ≤ 3 := by
        by_cases hjl : j < ℓ
        · have hc' : d₁.nreg 1030 < d₁.nreg 1065 := by rw [g30, g65]; exact hjl
          have hrd : d₁.nmem (pp + j) = c.nmem (pp + j) := by
            rw [hm₁, hB _ (fun j' hj' => (hdis' j' (by omega) j (by omega)).symm)]
          obtain ⟨d₂, k₂, e₂, h₂⟩ : ∃ d₂ k₂, Exec P W
              (block [.addN 1035 1064 1030, .loadN 1036 1035]) d₁ d₂ k₂ ∧
              (WordsBounded W d₂ ∧ d₂.nreg 1036 = c.nmem (pp + j) ∧
              (∀ r, r ≠ 1035 → r ≠ 1036 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem) ∧
              k₂ = 2 := by
            exec_block
            · rw [g64, g30]; omega
            · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, rfl⟩
              config_simp
              rw [g64, g30, hrd]
              refine ⟨rfl, fun r h h' => ?_⟩
              simp only [upd_apply]; split_ifs <;> first | omega | rfl
          refine ⟨d₂, k₂ + 1, .ifLtN_true hc' e₂, h₂.1.1, ?_, h₂.1.2.2.1, h₂.1.2.2.2, by omega⟩
          simp only [hjl, ↓reduceIte]; exact h₂.1.2.1
        · have hc' : ¬ d₁.nreg 1030 < d₁.nreg 1065 := by rw [g30, g65]; exact hjl
          refine ⟨d₁, 0 + 2, .ifLtN_false hc' (.skip hw₁), hw₁, ?_, fun _ _ _ => rfl, rfl,
            by omega⟩
          simp only [hjl, ↓reduceIte]; exact g36
      have q : ∀ r, r ≠ 1035 → r ≠ 1036 → d₂.nreg r = d₁.nreg r := hr₂
      -- the store
      obtain ⟨d₃, k₃, e₃, h₃⟩ : ∃ d₃ k₃, Exec P W (block [.storeN 1034 1036,
          .addN 1030 1030 1001]) d₂ d₃ k₃ ∧ I (j + 1) d₃ ∧ k₃ = 2 := by
        exec_block
        · config_simp; rw [q 1030 (by omega) (by omega), q 1001 (by omega) (by omega), g30,
            g01]; omega
        · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, rfl⟩
          config_simp
          rw [q 1030 (by omega) (by omega), q 1001 (by omega) (by omega), g30, g01,
            q 1034 (by omega) (by omega), g34, f36, q 1016 (by omega) (by omega),
            q 1015 (by omega) (by omega), q 1042 (by omega) (by omega),
            q 1064 (by omega) (by omega), q 1065 (by omega) (by omega), hm₂, hm₁]
          refine ⟨rfl, g16, rfl, g15, g42, g64, g65, fun j' hj' => ?_, fun a ha => ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
            · rw [upd_other _ _ _ (fun e => by
                have := hinj j' (by omega) j hj (by omega); omega)]
              exact hA j' hj'
            · rw [upd_same]
          · rw [upd_other _ _ _ (ha j (by omega))]
            exact hB a (fun j' hj' => ha j' (by omega))
      exact ⟨d₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), h₃.1, by omega⟩)
    (Nat.zero_le _)
    ⟨e₀.wb_right, by config_simp, by config_simp; exact hk, by config_simp; exact h1,
      by config_simp; rfl, by config_simp; exact hbase, by config_simp; exact hpp,
      by config_simp; exact hℓ, fun j' hj' => by omega, fun a _ => rfl⟩
  exact ⟨c', 1 + k', .seq e₀ e', by omega, hI'.2.2.2.2.2.2.2.2.1, hI'.2.2.2.2.2.2.2.2.2⟩

/-! ### Clearing the ranks of the darts of the list -/

/-- The body of the rank-clearing pass: the darts `[ofs v, ofs (v + 1))` of `v = L[j]`, as
the cells `[aRk + ofs v, aRk + ofs (v + 1))`. -/
def rkClrBody : Stmt :=
  .seq (block [.addN 1034 1015 1030, .loadN 1031 1034, .addN 1034 1010 1031, .loadN 1032 1034,
    .addN 1034 1034 1001, .loadN 1033 1034, .addN 1032 1032 1018, .addN 1033 1033 1018])
  (.seq (clrLoop 1032 1033 1039 1001) (.instr (.addN 1030 1030 1001)))

/-- **The rank-clearing pass** over the list. -/
def rkClr : Stmt := .seq (.instr (.constN 1030 0)) (.whileLtN 1030 1016 rkClrBody)

theorem rkClr_exec {c : Config} (hc : WordsBounded W c) {N M k : ℕ} (Lv ofsF : ℕ → ℕ)
    (h1 : c.nreg 1001 = 1) (h0 : c.nreg 1039 = 0) (hk : c.nreg 1016 = k)
    (hL : ∀ j < k, c.nmem (c.nreg 1015 + j) = Lv j) (hLN : ∀ j < k, Lv j < N)
    (hinc : ∀ i j, i < j → j < k → Lv i < Lv j)
    (hofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = ofsF v)
    (hmono : ∀ v v', v ≤ v' → v' ≤ N → ofsF v ≤ ofsF v') (hofsM : ofsF N ≤ M)
    (c0 : c.nreg 1015 + k ≤ c.nreg 1018) (c1 : c.nreg 1010 + N < c.nreg 1018)
    (c4 : c.nreg 1018 + M ≤ W) :
    ∃ c' k', Exec P W rkClr c c' k' ∧ k' ≤ 4 * psum ofsF Lv k + 15 * k + 3 ∧
      (∀ j < k, ∀ g, ofsF (Lv j) ≤ g → g < ofsF (Lv j + 1) → c'.nmem (c.nreg 1018 + g) = 0) ∧
      (∀ a, (∀ j < k, ∀ g, ofsF (Lv j) ≤ g → g < ofsF (Lv j + 1) → a ≠ c.nreg 1018 + g) →
        c'.nmem a = c.nmem a) := by
  set aOfs := c.nreg 1010
  set aL := c.nreg 1015
  set aRk := c.nreg 1018
  let Wr : ℕ → ℕ → Prop := fun j a => ∀ j' < j, ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) →
    a ≠ aRk + g
  let Inv : ℕ → Config → Prop := fun j d => WordsBounded W d ∧ d.nreg 1030 = j ∧ j ≤ k ∧
    d.nreg 1016 = k ∧ d.nreg 1001 = 1 ∧ d.nreg 1039 = 0 ∧ d.nreg 1010 = aOfs ∧
    d.nreg 1015 = aL ∧ d.nreg 1018 = aRk ∧
    (∀ j' < j, ∀ g, ofsF (Lv j') ≤ g → g < ofsF (Lv j' + 1) → d.nmem (aRk + g) = 0) ∧
    (∀ a, Wr j a → d.nmem a = c.nmem a)
  have rd : ∀ j ≤ k, ∀ a, a < aRk → Wr j a := fun j _ a ha j' _ g _ _ => by omega
  have e₀ := Exec.constN (P := P) hc 1030 0 (Nat.zero_le _)
  obtain ⟨c', k', e', ⟨j, hjk, hI'⟩, hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 1030) (b := 1016) (body := rkClrBody) (fun d => ∃ j ≤ k, Inv j d)
    (fun d => 15 * (k - d.nreg 1030) + 4 * (psum ofsF Lv k - psum ofsF Lv (d.nreg 1030)))
    (fun d h => by obtain ⟨_, _, h⟩ := h; exact h.1)
    (fun d h hlt => by
      obtain ⟨j, -, hw, h30, hjk, h16, h01, h39, h10, h15, h18, hA, hB⟩ := h
      rw [h30, h16] at hlt
      have hv := hLN j hlt
      have hpsS : psum ofsF Lv (j + 1) = psum ofsF Lv j + (ofsF (Lv j + 1) - ofsF (Lv j)) := by
        simp [psum, Finset.sum_range_succ]
      have hpk := psum_mono ofsF Lv (show j + 1 ≤ k by omega)
      have hmv := hmono (Lv j) (Lv j + 1) (by omega) (by omega)
      have hM' : ofsF (Lv j + 1) ≤ M := (hmono _ N (by omega) le_rfl).trans hofsM
      have r1 : d.nmem (aL + j) = Lv j := by
        rw [hB _ (rd j hjk _ (by omega))]; exact hL j hlt
      have r3 : d.nmem (aOfs + Lv j) = ofsF (Lv j) := by
        rw [hB _ (rd j hjk _ (by omega))]; exact hofs _ hv.le
      have r4 : d.nmem (aOfs + Lv j + 1) = ofsF (Lv j + 1) := by
        rw [hB _ (rd j hjk _ (by omega)), Nat.add_assoc]; exact hofs _ hv
      obtain ⟨d₁, k₁, e₁, hw₁, g30, g32, g33, g01, g39, g16, g10, g15, g18, hm₁, hk₁⟩ :
          ∃ d₁ k₁, Exec P W (block [.addN 1034 1015 1030, .loadN 1031 1034,
            .addN 1034 1010 1031, .loadN 1032 1034, .addN 1034 1034 1001, .loadN 1033 1034,
            .addN 1032 1032 1018, .addN 1033 1033 1018]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
            d₁.nreg 1030 = j ∧ d₁.nreg 1032 = aRk + ofsF (Lv j) ∧
            d₁.nreg 1033 = aRk + ofsF (Lv j + 1) ∧ d₁.nreg 1001 = 1 ∧ d₁.nreg 1039 = 0 ∧
            d₁.nreg 1016 = k ∧ d₁.nreg 1010 = aOfs ∧ d₁.nreg 1015 = aL ∧ d₁.nreg 1018 = aRk ∧
            d₁.nmem = d.nmem ∧ k₁ = 8 := by
        exec_block
        all_goals try (config_simp; simp only [h15, h30, r1, h10, h01, r3, r4, h18]; omega)
        · refine ⟨‹WordsBounded _ _›, ?_⟩
          config_simp
          simp only [h15, h30, r1, h10, h01, r3, r4, h18, h39, h16]
          exact ⟨trivial, Nat.add_comm _ _, Nat.add_comm _ _, trivial, trivial, trivial, trivial,
            trivial, trivial⟩
      obtain ⟨d₂, k₂, e₂, hk₂, hz₂, hf₂⟩ := clrLoop_exec (P := P) hw₁ (ri := 1032) (rb := 1033)
        (rz := 1039) (one := 1001) (by omega) (by omega) (by omega) g01 g39 g32 g33
        (by omega) (by omega)
      have f₂ : ∀ r, (clrLoop 1032 1033 1039 1001).wr r = false → d₂.nreg r = d₁.nreg r :=
        fun r hr => Exec.nreg_of_wr e₂ hr
      have f30 : d₂.nreg 1030 = j := by rw [f₂ 1030 (by decide), g30]
      have f01 : d₂.nreg 1001 = 1 := by rw [f₂ 1001 (by decide), g01]
      refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ (Exec.addN e₂.wb_right 1030 1030 1001
        (by rw [f30, f01]; omega))), ⟨j + 1, by omega, ?_⟩, ?_⟩
      · refine ⟨Exec.wb_right (Exec.addN (P := P) e₂.wb_right 1030 1030 1001
          (by rw [f30, f01]; omega)), ?_⟩
        config_simp
        rw [f30, f01, f₂ 1016 (by decide), f₂ 1039 (by decide), f₂ 1010 (by decide),
          f₂ 1015 (by decide), f₂ 1018 (by decide), g16, g39, g10, g15, g18]
        refine ⟨rfl, by omega, rfl, rfl, rfl, rfl, rfl, rfl, fun j' hj' g hg1 hg2 => ?_,
          fun a ha => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · have h3 := hinc j' j hj' hlt
            have h4 := hmono (Lv j' + 1) (Lv j) (by omega) (by omega)
            rw [hf₂ _ (by left; omega), hm₁]
            exact hA j' hj' g hg1 hg2
          · exact hz₂ _ (by omega) (by omega)
        · have ha' := ha j (by omega)
          rw [hf₂ _ (by
            by_contra hc
            exact ha' (a - aRk) (by omega) (by omega) (by omega)), hm₁]
          exact hB a (fun j' hj' => ha j' (by omega))
      · simp only [upd_same, f30, f01]
        rw [h30, hpsS]
        have : ofsF (Lv j + 1) - ofsF (Lv j) ≤ psum ofsF Lv k - psum ofsF Lv j := by omega
        have hk2 : k₂ ≤ 4 * (ofsF (Lv j + 1) - ofsF (Lv j)) + 2 := by
          have : aRk + ofsF (Lv j + 1) - (aRk + ofsF (Lv j)) = ofsF (Lv j + 1) - ofsF (Lv j) := by
            omega
          rw [← this]; exact hk₂
        omega)
    ⟨0, Nat.zero_le _, e₀.wb_right, by config_simp, Nat.zero_le _, by config_simp; exact hk,
      by config_simp; exact h1, by config_simp; exact h0, by config_simp; rfl,
      by config_simp; rfl, by config_simp; rfl, fun j' h => by omega, fun a _ => rfl⟩
  obtain ⟨hw', h30', -, h16', -, -, -, -, -, hA', hB'⟩ := hI'
  rw [h30', h16'] at hn
  have hjk' : j = k := by omega
  rw [hjk'] at hA' hB'
  refine ⟨c', 1 + k', .seq e₀ e', ?_, hA', fun a ha => hB' a ha⟩
  simp only [upd_same, show psum ofsF Lv 0 = 0 by simp [psum], Nat.sub_zero] at hk'
  omega

end Piece

end PlanarSeparator
