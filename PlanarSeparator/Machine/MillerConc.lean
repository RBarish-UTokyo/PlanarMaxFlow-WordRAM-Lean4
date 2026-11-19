module

public import PlanarSeparator.Machine.MillerLast

/-!
# Miller's separator on the machine: the concentrated weights

At a level `l` (step 7 of the plan in `PlanarSeparator/Machine/Miller.lean`, at the level `l₂`),
the weight of the strict inside of every component of the faces avoiding the levels `< l` is
moved to one vertex of level `> l` of the component (`PlanarSeparator.Map.wc`). The band theorem
holds for any such choice (`PlanarSeparator.Map.IsConc`,
`PlanarSeparator.Map.exists_band_separator_of`). After the heavy test `hvy` at `l`
(`PlanarSeparator/Machine/MillerTest.lean`), which leaves the labels `lb` of the components at
`bL` and the weight of the vertices of level `> l` of each label at `bSum`:

* `rpass` stores, for every label, a vertex of level `> l` with that label (the last one) at
  `bRep + x`;
* `cpass` writes the image `cnN v` of every vertex (its representative if its level is `> l`,
  itself otherwise) at `bCN + v` and its moved weight `wcN v` at `bWC + v` (the weight of the
  label at a representative, `0` at the other vertices of level `> l`, `w v` at the vertices of
  level `≤ l`).

`conc_exec` runs `zpass`, `hvy`, `rpass`, `cpass` (the program `cprog`) within
`106 k + 59 n + 26` steps; read through the numbering of the vertices, the images `cnN` are a
concentration map at `l` (`isConc_of_rep`, `PlanarSeparator.Map.IsConc`) and `wcN` are its moved
weights (`wcN_eq_sum`, `wcf_eq_sum`, `PlanarSeparator.Map.wcf`).

Registers: those of `hvy`, with `r188 = bRep`, `r189 = bCN`, `r190 = bWC`; the passes write
`r191 … r197`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- The label `r195` of the face of the dart of the vertex `r191`. -/
def labI : List Instr :=
  [.addN 192 164 191, .loadN 194 192, .divN 194 194 142, .addN 192 145 194, .loadN 195 192]

/-- **One vertex** `r191 = v`: if its level is `> l`, it becomes the representative of its
label. -/
def rbody : Stmt :=
  .seq (block [.addN 192 163 191, .loadN 193 192])
    (.seq (.ifLtN 160 193 (block (labI ++ [.addN 192 188 195, .storeN 192 191])) .skip)
      (.instr (.addN 191 191 141)))

/-- **The representatives.** -/
def rpass : Stmt := .seq (.instr (.copyN 191 140)) (.whileLtN 191 161 rbody)

/-- **One vertex** `r191 = v`: its image and its moved weight. -/
def cbody : Stmt :=
  .seq (block [.addN 192 163 191, .loadN 193 192])
    (.seq (.ifLtN 160 193
      (.seq (block (labI ++ [.addN 192 188 195, .loadN 196 192, .addN 192 189 191,
          .storeN 192 196, .subN 197 196 191, .subN 194 191 196, .addN 197 197 194]))
        (.ifLtN 140 197 (block [.addN 192 190 191, .storeN 192 140])
          (block [.addN 192 166 195, .loadN 194 192, .addN 192 190 191, .storeN 192 194])))
      (block [.addN 192 189 191, .storeN 192 191, .addN 192 165 191, .loadN 194 192,
        .addN 192 190 191, .storeN 192 194]))
      (.instr (.addN 191 191 141)))

/-- **The images and the moved weights.** -/
def cpass : Stmt := .seq (.instr (.copyN 191 140)) (.whileLtN 191 161 cbody)

/-- **The concentrated weights** at the level `r160`. -/
def cprog : Stmt := .seq zpass (.seq hvy (.seq rpass cpass))

/-- The image of a vertex: its representative `rp x` (`x` its label) if its level is `> l`. -/
def cnN (l : ℕ) (L fd lb rp : ℕ → ℕ) (v : ℕ) : ℕ := if l < L v then rp (lb (fd v / 3)) else v

/-- The moved weight of a vertex: the weight `S x` of its label `x` if it is the representative
of its label, `0` if it is another vertex of level `> l`, its own weight otherwise. -/
def wcN (l : ℕ) (L fd lb rp S w : ℕ → ℕ) (v : ℕ) : ℕ :=
  if l < L v then (if rp (lb (fd v / 3)) = v then S (lb (fd v / 3)) else 0) else w v

section proofs

variable {k : ℕ} {bA bL bS bR : ℕ} {W : ℕ} {P : Input}
  {l n bV bLv bF bw bSum bRep bCN bWC : ℕ} {L : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem rpass_exec {fd lb : ℕ → ℕ}
    (hlay : bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bRep)
    (hW : bRep + k + 1 + n ≤ W) (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (hH : HR l n bV bLv bF bw bSum c) (h188 : c.nreg 188 = bRep)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v)
    (hF : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g ∧ lb g ≤ k) :
    ∃ c' t, Exec P W rpass c c' t ∧ t ≤ 14 * n + 3 ∧
      (∀ u < n, l < L u → c'.nmem (bRep + lb (fd u / 3)) < n ∧
        l < L (c'.nmem (bRep + lb (fd u / 3))) ∧
        lb (fd (c'.nmem (bRep + lb (fd u / 3))) / 3) = lb (fd u / 3)) ∧
      (∀ r, r < 191 ∨ 198 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bRep ∨ bRep + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 191 = i ∧
    c'.nreg 161 = n ∧ i ≤ n ∧
    (∀ u < i, l < L u → c'.nmem (bRep + lb (fd u / 3)) < i ∧
      l < L (c'.nmem (bRep + lb (fd u / 3))) ∧
      lb (fd (c'.nmem (bRep + lb (fd u / 3))) / 3) = lb (fd u / 3)) ∧
    (∀ r, r < 191 ∨ 198 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bRep ∨ bRep + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 191 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 191) (rN := 161) (N := n)
    (lo := 0) (B := 11) (body := rbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h191, h161, hin, hP, hr, hf, ho⟩ hi => by
      have g : ∀ r, r < 191 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g160 : c₁.nreg 160 = l := by rw [g 160 (by omega)]; exact r160
      have g163 : c₁.nreg 163 = bLv := by rw [g 163 (by omega)]; exact r163
      have g164 : c₁.nreg 164 = bF := by rw [g 164 (by omega)]; exact r164
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have g188 : c₁.nreg 188 = bRep := by rw [g 188 (by omega)]; exact h188
      have mL : c₁.nmem (bLv + i) = L i := by rw [hf _ (Or.inl (by omega))]; exact hL i hi
      have mF : c₁.nmem (bF + i) = fd i := by rw [hf _ (Or.inl (by omega))]; exact (hF i hi).1
      have hfk : fd i / 3 < k := by have := (hF i hi).2; omega
      have mb : c₁.nmem (bL + fd i / 3) = lb (fd i / 3) := by
        rw [hf _ (Or.inl (by omega))]; exact (hlb _ hfk).1
      have hlbk := (hlb _ hfk).2
      unfold rbody labI
      simp only [List.cons_append, List.nil_append]
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g163, h191]; omega
      rename_i hwb
      simp only [g163, h191, mL] at hwb ⊢
      refine spec_seq ?_
      by_cases hli : l < L i
      · refine spec_ifLtN_true (by config_simp; rw [g160]; exact hli) ?_
        exec_block
        all_goals try (config_simp; (try simp only [g164, h191, mF, g142, g145, mb, g188])
                       omega)
        rename_i hwc
        simp only [g164, h191, mF, g142, g145, mb, g188] at hwc ⊢
        refine spec_instr (Exec.addN hwc _ _ _ (by config_simp; rw [h191, g141]; omega))
          fun hw' => ⟨⟨hw', by config_simp; rw [h191, g141], by config_simp; exact h161,
            by omega, fun u hu hlu => ?_, fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
            fun a ha => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hf a ha,
            by config_simp; exact ho⟩, by omega⟩
        config_simp
        by_cases hx : lb (fd u / 3) = lb (fd i / 3)
        · rw [hx, upd_same]; exact ⟨by omega, hli, rfl⟩
        · rw [upd_other _ _ _ (by omega)]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · obtain ⟨a1, a2, a3⟩ := hP u hu hlu; exact ⟨by omega, a2, a3⟩
          · exact absurd rfl hx
      · refine spec_ifLtN_false (by config_simp; rw [g160]; exact hli) ?_
        refine spec_skip ‹_› ?_
        refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h191, g141]; omega))
          fun hw' => ⟨⟨hw', by config_simp; rw [h191, g141], by config_simp; exact h161,
            by omega, fun u hu hlu => ?_, fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
            fun a ha => by config_simp; exact hf a ha, by config_simp; exact ho⟩, by omega⟩
        config_simp
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · obtain ⟨a1, a2, a3⟩ := hP u hu hlu; exact ⟨by omega, a2, a3⟩
        · exact absurd hlu hli)
    (by omega) ⟨e₁.wb_right, by config_simp; exact r140, by config_simp; exact r161, by omega,
      fun u hu => absurd hu (by omega), fun r hr => by
        show upd c.nreg 191 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, -, hP', hr', hf', ho'⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hP', hr', hf', ho'⟩

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem cpass_exec {fd lb rp S w : ℕ → ℕ}
    (hlay : bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bSum ∧
      bSum + k + 1 ≤ bRep ∧ bRep + k + 1 ≤ bCN ∧ bCN + n ≤ bWC)
    (hW : bWC + n ≤ W) (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (hH : HR l n bV bLv bF bw bSum c) (h188 : c.nreg 188 = bRep)
    (h189 : c.nreg 189 = bCN) (h190 : c.nreg 190 = bWC)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v)
    (hF : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k) (hw : ∀ v < n, c.nmem (bw + v) = w v)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g ∧ lb g ≤ k)
    (hS : ∀ x ≤ k, c.nmem (bSum + x) = S x) (hrp : ∀ x ≤ k, c.nmem (bRep + x) = rp x) :
    ∃ c' t, Exec P W cpass c c' t ∧ t ≤ 24 * n + 3 ∧
      (∀ v < n, c'.nmem (bCN + v) = cnN l L fd lb rp v ∧
        c'.nmem (bWC + v) = wcN l L fd lb rp S w v) ∧
      (∀ r, r < 191 ∨ 198 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bCN ∨ bWC + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 191 = i ∧
    c'.nreg 161 = n ∧ i ≤ n ∧
    (∀ v < i, c'.nmem (bCN + v) = cnN l L fd lb rp v ∧
      c'.nmem (bWC + v) = wcN l L fd lb rp S w v) ∧
    (∀ r, r < 191 ∨ 198 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bCN ∨ bWC + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 191 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 191) (rN := 161) (N := n)
    (lo := 0) (B := 22) (body := cbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h191, h161, hin, hP, hr, hf, ho⟩ hi => by
      have g : ∀ r, r < 191 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g140 : c₁.nreg 140 = 0 := by rw [g 140 (by omega)]; exact r140
      have g160 : c₁.nreg 160 = l := by rw [g 160 (by omega)]; exact r160
      have g163 : c₁.nreg 163 = bLv := by rw [g 163 (by omega)]; exact r163
      have g164 : c₁.nreg 164 = bF := by rw [g 164 (by omega)]; exact r164
      have g165 : c₁.nreg 165 = bw := by rw [g 165 (by omega)]; exact r165
      have g166 : c₁.nreg 166 = bSum := by rw [g 166 (by omega)]; exact r166
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have g188 : c₁.nreg 188 = bRep := by rw [g 188 (by omega)]; exact h188
      have g189 : c₁.nreg 189 = bCN := by rw [g 189 (by omega)]; exact h189
      have g190 : c₁.nreg 190 = bWC := by rw [g 190 (by omega)]; exact h190
      have mL : c₁.nmem (bLv + i) = L i := by rw [hf _ (Or.inl (by omega))]; exact hL i hi
      have mF : c₁.nmem (bF + i) = fd i := by rw [hf _ (Or.inl (by omega))]; exact (hF i hi).1
      have mw : c₁.nmem (bw + i) = w i := by rw [hf _ (Or.inl (by omega))]; exact hw i hi
      have hfk : fd i / 3 < k := by have := (hF i hi).2; omega
      have mb : c₁.nmem (bL + fd i / 3) = lb (fd i / 3) := by
        rw [hf _ (Or.inl (by omega))]; exact (hlb _ hfk).1
      have hlbk := (hlb _ hfk).2
      have mr : c₁.nmem (bRep + lb (fd i / 3)) = rp (lb (fd i / 3)) := by
        rw [hf _ (Or.inl (by omega))]; exact hrp _ hlbk
      have hrW : rp (lb (fd i / 3)) ≤ W := by rw [← mr]; exact hw₁.2 _
      have mS : c₁.nmem (bSum + lb (fd i / 3)) = S (lb (fd i / 3)) := by
        rw [hf _ (Or.inl (by omega))]; exact hS _ hlbk
      have post : ∀ (c₂ : Config), WordsBounded W c₂ → c₂.nreg 191 = i + 1 →
          (∀ r, r < 191 ∨ 198 ≤ r → c₂.nreg r = c₁.nreg r) →
          (∀ a, a ≠ bCN + i → a ≠ bWC + i → c₂.nmem a = c₁.nmem a) →
          c₂.nmem (bCN + i) = cnN l L fd lb rp i →
          c₂.nmem (bWC + i) = wcN l L fd lb rp S w i → c₂.output = c₁.output → I (i + 1) c₂ := by
        intro c₂ hw2 h1 h2 h3 h4 h5 h6
        refine ⟨hw2, h1, by rw [h2 161 (by omega)]; exact h161, by omega, fun v hv => ?_,
          fun r hr' => by rw [h2 r hr', hr r hr'], fun a ha => ?_, by rw [h6, ho]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
          · rw [h3 _ (by omega) (by omega), h3 _ (by omega) (by omega)]; exact hP v hv
          · exact ⟨h4, h5⟩
        · rw [h3 _ (by omega) (by omega)]; exact hf a ha
      unfold cbody labI
      simp only [List.cons_append, List.nil_append]
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g163, h191]; omega
      rename_i hwb
      simp only [g163, h191, mL] at hwb ⊢
      refine spec_seq ?_
      by_cases hli : l < L i
      · refine spec_ifLtN_true (by config_simp; rw [g160]; exact hli) ?_
        refine spec_seq ?_
        exec_block
        all_goals try (config_simp; (try simp only [g164, h191, mF, g142, g145, mb, g188, mr,
                         g189]); omega)
        rename_i hwc
        simp only [g164, h191, mF, g142, g145, mb, g188, mr, g189] at hwc ⊢
        by_cases hne : rp (lb (fd i / 3)) = i
        · refine spec_ifLtN_false (by config_simp; rw [g140]; omega) ?_
          exec_block
          all_goals try (config_simp; (try simp only [g166, g190, h191]); omega)
          rename_i hwd
          simp only [g166, g190, h191] at hwd ⊢
          refine spec_instr (Exec.addN hwd _ _ _ (by config_simp; rw [h191, g141]; omega))
            fun hw' => ⟨post _ hw' (by config_simp; rw [h191, g141]) (fun r hr' => by
              config_simp; simp only [upd_apply]; split_ifs <;> omega) (fun a h1 h2 => by
              config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]) ?_ ?_
              (by config_simp), by omega⟩
          · config_simp
            rw [upd_other _ _ _ (by omega), upd_same]
            simp only [cnN, hli, ↓reduceIte]
          · config_simp
            rw [upd_other _ _ _ (by omega), mS]
            simp only [wcN, hli, hne, ↓reduceIte]
        · refine spec_ifLtN_true (by config_simp; rw [g140]; omega) ?_
          exec_block
          all_goals try (config_simp; (try simp only [g190, h191]); omega)
          rename_i hwd
          simp only [g190, h191] at hwd ⊢
          refine spec_instr (Exec.addN hwd _ _ _ (by config_simp; rw [h191, g141]; omega))
            fun hw' => ⟨post _ hw' (by config_simp; rw [h191, g141]) (fun r hr' => by
              config_simp; simp only [upd_apply]; split_ifs <;> omega) (fun a h1 h2 => by
              config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]) ?_ ?_
              (by config_simp), by omega⟩
          · config_simp
            rw [upd_other _ _ _ (by omega), upd_same]
            simp only [cnN, hli, ↓reduceIte]
          · config_simp
            rw [g140]
            simp only [wcN, hli, hne, ↓reduceIte]
      · refine spec_ifLtN_false (by config_simp; rw [g160]; exact hli) ?_
        exec_block
        all_goals try (config_simp; (try simp only [g189, h191, g165, mw, g190]); omega)
        rename_i hwc
        simp only [g189, h191, g165, g190] at hwc ⊢
        refine spec_instr (Exec.addN hwc _ _ _ (by config_simp; rw [h191, g141]; omega))
          fun hw' => ⟨post _ hw' (by config_simp; rw [h191, g141]) (fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> omega) (fun a h1 h2 => by
            config_simp; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]) ?_ ?_
            (by config_simp), by omega⟩
        · config_simp
          rw [upd_other _ _ _ (by omega), upd_same]
          simp only [cnN, hli, ↓reduceIte]
        · config_simp
          rw [upd_other _ _ _ (by omega), mw]
          simp only [wcN, hli, ↓reduceIte])
    (by omega) ⟨e₁.wb_right, by config_simp; exact r140, by config_simp; exact r161, by omega,
      fun u hu => absurd hu (by omega), fun r hr => by
        show upd c.nreg 191 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, -, hP', hr', hf', ho'⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hP', hr', hf', ho'⟩

end proofs

/-! ### The moved weights -/

/-- The representatives found by `rpass`: a vertex of level `> l` of the same label. -/
def RepOk (l n : ℕ) (L fd lb rp : ℕ → ℕ) : Prop :=
  ∀ u < n, l < L u → rp (lb (fd u / 3)) < n ∧ l < L (rp (lb (fd u / 3))) ∧
    lb (fd (rp (lb (fd u / 3))) / 3) = lb (fd u / 3)

theorem cnN_lt {l n : ℕ} {L fd lb rp : ℕ → ℕ} (hrp : RepOk l n L fd lb rp) {v : ℕ}
    (hv : v < n) : cnN l L fd lb rp v < n := by
  unfold cnN
  split_ifs with h
  · exact (hrp v hv h).1
  · exact hv

/-- **The moved weight is the weight sent by `cnN`.** -/
theorem wcN_eq_sum {l n : ℕ} {L fd lb rp w : ℕ → ℕ} (hrp : RepOk l n L fd lb rp) {v : ℕ}
    (hv : v < n) :
    wcN l L fd lb rp (sm l L fd lb w n) w v =
      ∑ u ∈ range n, if cnN l L fd lb rp u = v then w u else 0 := by
  unfold wcN
  by_cases hlv : l < L v
  · simp only [hlv, ↓reduceIte]
    split_ifs with he
    · unfold sm
      refine sum_congr rfl fun u hu => ?_
      have hu := mem_range.1 hu
      unfold cnN
      by_cases hlu : l < L u
      · have e : rp (lb (fd u / 3)) = v ↔ lb (fd u / 3) = lb (fd v / 3) := by
          constructor
          · intro h; have := (hrp u hu hlu).2.2; rw [h] at this; exact this.symm
          · intro h; rw [h, he]
        simp only [hlu, true_and, ↓reduceIte, e]
      · have : u ≠ v := fun h => hlu (h ▸ hlv)
        simp only [hlu, false_and, ↓reduceIte, this]
    · symm
      refine sum_eq_zero fun u hu => ?_
      have hu := mem_range.1 hu
      unfold cnN
      by_cases hlu : l < L u
      · have : rp (lb (fd u / 3)) ≠ v := fun h => by
          have h2 := (hrp u hu hlu).2.2
          rw [h] at h2
          exact he (by rw [h2, h])
        simp only [hlu, ↓reduceIte, this]
      · have : u ≠ v := fun h => hlu (h ▸ hlv)
        simp only [hlu, ↓reduceIte, this]
  · simp only [hlv, ↓reduceIte]
    rw [sum_congr rfl (g := fun u => if v = u then w u else 0) fun u hu => ?_, sum_ite_eq,
      ite_eq_left (mem_range.2 hv)]
    have hu := mem_range.1 hu
    unfold cnN
    by_cases hlu : l < L u
    · have h1 : rp (lb (fd u / 3)) ≠ v := fun h => by
        have := (hrp u hu hlu).2.1; rw [h] at this; exact hlv this
      have h2 : v ≠ u := fun h => hlv (h ▸ hlu)
      simp only [hlu, ↓reduceIte, h1, h2]
    · simp only [hlu, ↓reduceIte, eq_comm]

section Bridge

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}
  (hC : Coded M T₀ k cd A Tm) (vi : P ≃ Fin n) {V L : ℕ → ℕ}
  (hV : ∀ x, V (cd x) = vi (M.vert x)) (hL : ∀ v, L (vi v) = T.height v)
include hC hV hL

/-- Two vertices of level `> l` have the same label if and only if they have the same
component. -/
theorem lab_eq_iff_Yof (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ}
    {fd : ℕ → ℕ} (fdD : P → D) (hfdD : ∀ v, M.vert (fdD v) = v)
    (hfd : ∀ v, fd (vi v) = cd (fdD v)) {lb : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g))
    {u v : P} (hu : l < T.height u) (hv : l < T.height v) :
    lb (fd (vi u) / 3) = lb (fd (vi v) / 3) ↔ Yof T l u = Yof T l v := by
  have hAv := flagF_pos_iff hC vi hV hL (T := T) l
  have hzu := notMem_zone_of_lt hT h3 hu (hfdD u)
  have hzv := notMem_zone_of_lt hT h3 hv (hfdD v)
  rw [hfd, hfd, ← hC.fi_face, ← hC.fi_face, eq_comm, label_eq_iff hC hAv hlb hzv hzu,
    Yof_eq hT h3 hu (hfdD u), Yof_eq hT h3 hv (hfdD v)]
  constructor
  · intro h; exact comp_eq_of_mem h
  · intro h; rw [← h]; exact Map.mem_comp_self hzu

/-- **The images of `cpass` are a concentration map.** -/
theorem isConc_of_rep (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {l : ℕ}
    {fd : ℕ → ℕ} (fdD : P → D) (hfdD : ∀ v, M.vert (fdD v) = v)
    (hfd : ∀ v, fd (vi v) = cd (fdD v)) {lb rp : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g))
    (hrp : RepOk l n L fd lb rp) (cn : P → P)
    (hcn : ∀ v, (vi (cn v) : ℕ) = cnN l L fd lb rp (vi v)) : IsConc T l cn := by
  have key := fun {u v : P} => lab_eq_iff_Yof hC vi hV hL hT h3 fdD hfdD hfd hlb (u := u) (v := v)
  have hvi : ∀ u v : P, (vi u : ℕ) = vi v → u = v := fun u v h => vi.injective (Fin.ext h)
  refine ⟨fun v hv => hvi _ _ ?_, fun v hv => ?_, fun u v hu hv h => hvi _ _ ?_⟩
  · rw [hcn]; unfold cnN; rw [hL, ite_eq_right (not_lt.2 hv)]
  · have hv' : l < L (vi v) := by rw [hL]; exact hv
    obtain ⟨-, h2, h3'⟩ := hrp _ (vi v).2 hv'
    have e : (vi (cn v) : ℕ) = rp (lb (fd (vi v) / 3)) := by
      rw [hcn]; unfold cnN; rw [ite_eq_left hv']
    have hc : l < T.height (cn v) := by rw [← hL, e]; exact h2
    refine ⟨hc, (key hc hv).1 ?_⟩
    rw [e]; exact h3'
  · have hu' : l < L (vi u) := by rw [hL]; exact hu
    have hv' : l < L (vi v) := by rw [hL]; exact hv
    rw [hcn, hcn]; unfold cnN; rw [ite_eq_left hu', ite_eq_left hv', (key hu hv).2 h]

omit hC hV hL in
/-- **The moved weights of `cpass` are those of `cn`**, for the weights `wP v / Σ wP`. -/
theorem wcf_eq_sum {l : ℕ} {fd lb rp w : ℕ → ℕ} (wP : P → ℕ) (hw : ∀ v, w (vi v) = wP v)
    (cn : P → P) (hcn : ∀ v, (vi (cn v) : ℕ) = cnN l L fd lb rp (vi v)) (u : P) :
    wcf cn (wR wP) u =
      ((∑ x ∈ range n, if cnN l L fd lb rp x = vi u then w x else 0 : ℕ) : ℝ) /
        ∑ v, (wP v : ℝ) := by
  have he : ∀ v, cnN l L fd lb rp (vi v) = vi u ↔ cn v = u := fun v => by
    rw [← hcn, Fin.val_inj, vi.injective.eq_iff]
  rw [sum_range_vi vi, Nat.cast_sum]
  unfold wcf wR
  rw [← sum_div, sum_filter]
  congr 1
  refine sum_congr rfl fun v _ => ?_
  simp only [he, hw]
  split_ifs <;> simp

end Bridge

/-! ### The whole program -/

section Whole

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L fd w : ℕ → ℕ}
  {vi : P ≃ Fin n} {wP : P → ℕ} {fdD : P → D}
  {W : ℕ} {P' : Input} {bA bL bS bR bV bLv bF bw bSum bRep bCN bWC : ℕ}

/-- **The concentrated weights on the machine.** For a coded triangulation with a breadth-first
tree, levels, darts and weights in memory (`Setup`, `InMem`), and a level `l < n` in `r160`, the
program `cprog` ends within `106 k + 59 n + 26` steps with, for some concentration map `cn` at
level `l` (`PlanarSeparator.Map.IsConc`), the image `cn v` of every vertex at `bCN` and its
moved weight at `bWC`: the weight of `u` for the weights `wP v / Σ wP` moved by `cn`
(`PlanarSeparator.Map.wcf`) is the number at `bWC + u` divided by `Σ wP`. -/
theorem conc_exec (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum ∧ bSum + k + 1 ≤ bRep ∧
      bRep + k + 1 ≤ bCN ∧ bCN + n ≤ bWC)
    (hW : bWC + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) {l : ℕ} (hl : l < n)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (h188 : c.nreg 188 = bRep) (h189 : c.nreg 189 = bCN) (h190 : c.nreg 190 = bWC)
    (hm : InMem k n bR bV bLv bF bw A V L fd w c.nmem) :
    ∃ c' t, Exec P' W cprog c c' t ∧ t ≤ 106 * k + 59 * n + 26 ∧
      (∃ cn : P → P, IsConc T l cn ∧ (∀ v, c'.nmem (bCN + vi v) = vi (cn v)) ∧
        ∀ u, wcf cn (wR wP) u = (c'.nmem (bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ)) ∧
      (∀ r, r < 150 ∨ (160 ≤ r ∧ r < 169) ∨ (180 ≤ r ∧ r < 183) ∨ (186 ≤ r ∧ r < 191) ∨
        198 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bA ∨ bWC + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hlay
  obtain ⟨m1, m2, m3, m4, m5⟩ := hm
  unfold cprog
  -- the sums are cleared
  obtain ⟨c₁, t₁, e₁, ht₁, hz₁, hr₁, hf₁, ho₁⟩ :=
    zpass_exec (P' := P') (by omega : bSum + k + 1 ≤ W) c hc hR hH
  have hR₁ : CR k bA bL bS bR c₁ := hR.of fun r hr => hr₁ r (Or.inl (by omega))
  have hH₁ : HR l n bV bLv bF bw bSum c₁ := hH.of fun r h1 h2 => hr₁ r (Or.inl (by omega))
  have k₁ : ∀ a < bSum, c₁.nmem a = c.nmem a := fun a ha => hf₁ a (Or.inl ha)
  -- the heavy test: labels and sums
  have htot : ∑ u ∈ range n, w u = ∑ v, wP v := by
    rw [sum_range_vi vi]; exact sum_congr rfl fun u _ => hS.hw u
  have hVn : ∀ x < 3 * k, c₁.nmem (bV + x) = V x ∧ V x < n := fun x hx => by
    refine ⟨by rw [k₁ _ (by omega)]; exact m2 x hx, ?_⟩
    have : V x = vi (M.vert (cd.symm ⟨x, hx⟩)) := by rw [← hS.hV]; simp
    rw [this]; exact (vi _).2
  have hFk : ∀ v < n, fd v < 3 * k := fun v hv => by
    have : fd v = cd (fdD (vi.symm ⟨v, hv⟩)) := by rw [← hS.hfd]; simp
    rw [this]; exact (cd _).2
  obtain ⟨c₂, t₂, e₂, ht₂, lb, -, hcls, -, -, hS₂, hlb₂, hr₂, hf₂, ho₂⟩ :=
    hvy_exec (P := P') (L := L) (revOk hS.coded) ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩
      ⟨by omega, hW.2⟩ htot c₁ e₁.wb_right hR₁ hH₁
      (by rw [hr₁ 168 (Or.inl (by omega))]; exact h168)
      (fun x hx => by rw [k₁ _ (by omega)]; exact m1 x hx) hVn
      (fun v hv => by rw [k₁ _ (by omega)]; exact m3 v hv)
      (fun v hv => ⟨by rw [k₁ _ (by omega)]; exact m4 v hv, hFk v hv⟩)
      (fun v hv => by rw [k₁ _ (by omega)]; exact m5 v hv) hz₁
  have hR₂ : CR k bA bL bS bR c₂ := hR₁.of fun r hr => hr₂ r (Or.inl hr)
  have hH₂ : HR l n bV bLv bF bw bSum c₂ :=
    hH₁.of fun r h1 h2 => hr₂ r (Or.inr (Or.inl ⟨h1, by omega⟩))
  have k₂ : ∀ a < bA, c₂.nmem a = c.nmem a := fun a ha => by
    rw [hf₂ a (Or.inl ha), k₁ a (by omega)]
  have g₂ : ∀ r, 186 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hr₂ r (Or.inr (Or.inr (by omega))), hr₁ r (Or.inr hr)]
  -- the representatives
  obtain ⟨c₃, t₃, e₃, ht₃, hP₃, hr₃, hf₃, ho₃⟩ := rpass_exec (P := P') (fd := fd) (lb := lb)
    (L := L) (bRep := bRep)
    ⟨l3, l4, l6, by omega⟩ (by omega) c₂ e₂.wb_right hR₂ hH₂
    (by rw [g₂ 188 (by omega)]; exact h188)
    (fun v hv => by rw [k₂ _ (by omega)]; exact m3 v hv)
    (fun v hv => ⟨by rw [k₂ _ (by omega)]; exact m4 v hv, hFk v hv⟩) hlb₂
  have hR₃ : CR k bA bL bS bR c₃ := hR₂.of fun r hr => hr₃ r (Or.inl (by omega))
  have hH₃ : HR l n bV bLv bF bw bSum c₃ := hH₂.of fun r h1 h2 => hr₃ r (Or.inl (by omega))
  have k₃ : ∀ a < bRep, c₃.nmem a = c₂.nmem a := fun a ha => hf₃ a (Or.inl ha)
  set rp : ℕ → ℕ := fun x => c₃.nmem (bRep + x) with hrp
  have hRep : RepOk l n L fd lb rp := hP₃
  -- the images and the moved weights
  obtain ⟨c₄, t₄, e₄, ht₄, hP₄, hr₄, hf₄, ho₄⟩ := cpass_exec (P := P') (fd := fd) (lb := lb)
    (L := L) (bRep := bRep) (bCN := bCN) (bWC := bWC) (rp := rp) (S := sm l L fd lb w n) (w := w)
    ⟨l3, l4, l5, l6, by omega, l9, l10, l11⟩ (by omega) c₃ e₃.wb_right hR₃ hH₃
    (by rw [hr₃ 188 (Or.inl (by omega)), g₂ 188 (by omega)]; exact h188)
    (by rw [hr₃ 189 (Or.inl (by omega)), g₂ 189 (by omega)]; exact h189)
    (by rw [hr₃ 190 (Or.inl (by omega)), g₂ 190 (by omega)]; exact h190)
    (fun v hv => by rw [k₃ _ (by omega), k₂ _ (by omega)]; exact m3 v hv)
    (fun v hv => ⟨by rw [k₃ _ (by omega), k₂ _ (by omega)]; exact m4 v hv, hFk v hv⟩)
    (fun v hv => by rw [k₃ _ (by omega), k₂ _ (by omega)]; exact m5 v hv)
    (fun g hg => by rw [k₃ _ (by omega)]; exact hlb₂ g hg)
    (fun x hx => by rw [k₃ _ (by omega)]; exact hS₂ x hx) (fun x _ => rfl)
  -- the concentration map
  let cn : P → P := fun v => vi.symm ⟨cnN l L fd lb rp (vi v), cnN_lt hRep (vi v).2⟩
  have hcn : ∀ v, (vi (cn v) : ℕ) = cnN l L fd lb rp (vi v) := fun v => by simp [cn]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    ⟨cn, isConc_of_rep hS.coded vi hS.hV hS.hL hS.bfs hS.tri fdD hS.hfdD hS.hfd hcls hRep cn hcn,
      fun v => by rw [(hP₄ _ (vi v).2).1, hcn], fun u => ?_⟩, fun r hr => ?_, fun a ha => ?_,
    by rw [ho₄, ho₃, ho₂, ho₁]⟩
  · rw [wcf_eq_sum vi wP hS.hw cn hcn, (hP₄ _ (vi u).2).2, wcN_eq_sum hRep (vi u).2]
  · rw [hr₄ r (by omega), hr₃ r (by omega), hr₂ r (by omega), hr₁ r (by omega)]
  · rw [hf₄ a (by omega), hf₃ a (by omega), hf₂ a (by omega), hf₁ a (by omega)]

end Whole

end MillerProg

end PlanarSeparator
