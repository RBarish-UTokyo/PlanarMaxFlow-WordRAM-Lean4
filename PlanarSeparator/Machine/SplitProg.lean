module

public import PlanarSeparator.Machine.BsplitProg

/-!
# The split of a node on the machine: the passes

The passes of `PlanarSeparator.SepRoutine.splitW` for the square of `G` on the machine (with
the names of `PlanarSeparator.Piece.splitW_eq_sp`):

* `bdry_square_eq`: the boundary of `W` in the square is `N[N[W]] \ W`;
* `spN1`: from the flags `2` on `W` and `1` on `N[W] \ W`, the sorted list of `N[W]`, the flags
  `2` on `N[W]` and the zones `1` on `W`, `2` on `N[W] \ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {W : ℕ} {P : Input}

/-- The boundary of `W` in the square of `G`. -/
theorem bdry_square_eq (W : Finset (Fin N)) :
    bdry (PlanarSeparator.square G) W = closedNbhd G (closedNbhd G W) \ W := by
  ext y
  simp only [bdry, mem_filter, mem_univ, true_and, mem_sdiff, closedNbhd, mem_biUnion,
    mem_insert, SimpleGraph.mem_neighborFinset, square_adj]
  constructor
  · rintro ⟨hy, x, hx, -, h | ⟨k, h1, h2⟩⟩
    · exact ⟨⟨x, ⟨x, hx, Or.inl rfl⟩, Or.inr h⟩, hy⟩
    · exact ⟨⟨k, ⟨x, hx, Or.inr h1⟩, Or.inr h2⟩, hy⟩
  · rintro ⟨⟨z, ⟨x, hx, hz⟩, hy'⟩, hy⟩
    refine ⟨hy, x, hx, fun h => hy (h ▸ hx), ?_⟩
    rcases hz with rfl | hz <;> rcases hy' with rfl | hy'
    · exact absurd hx hy
    · exact Or.inl hy'
    · exact Or.inl hz
    · by_cases hxy : G.Adj z y
      · exact Or.inr ⟨z, hz, hxy⟩
      · exact Or.inr ⟨z, hz, hy'⟩

/-- The names of the pieces along the vertices from `N - j` up. -/
theorem dedup_range'_succ (f : ℕ → ℕ) (D : Finset (Fin N)) {j : ℕ} (hj : j < N) :
    (((List.range' (N - (j + 1)) (j + 1)).filter (· ∈ UN D)).map f).dedup =
      if N - (j + 1) ∈ UN D then
        (if f (N - (j + 1)) ∈ (((List.range' (N - j) j).filter (· ∈ UN D)).map f).dedup then
          (((List.range' (N - j) j).filter (· ∈ UN D)).map f).dedup
        else f (N - (j + 1)) :: (((List.range' (N - j) j).filter (· ∈ UN D)).map f).dedup)
      else (((List.range' (N - j) j).filter (· ∈ UN D)).map f).dedup := by
  rw [List.range'_succ, show N - (j + 1) + 1 = N - j by omega]
  by_cases h : N - (j + 1) ∈ UN D
  · rw [iteT h, List.filter_cons_of_pos (by simpa using h), List.map_cons]
    by_cases h' : f (N - (j + 1)) ∈ (((List.range' (N - j) j).filter (· ∈ UN D)).map f).dedup
    · rw [iteT h', List.dedup_cons_of_mem (List.mem_dedup.1 h')]
    · rw [iteF h', List.dedup_cons_of_notMem (fun h'' => h' (List.mem_dedup.2 h''))]
  · rw [iteF h, List.filter_cons_of_neg (by simpa using h)]

theorem spList_eq_range' (f : ℕ → ℕ) (D : Finset (Fin N)) :
    spList f D = (((List.range' (N - N) N).filter (· ∈ UN D)).map f).dedup := by
  rw [Nat.sub_self, ← List.range_eq_range']; rfl

/-! ### The first pass: the closed neighbourhood -/

def spN1Body : Stmt := .seq (block [.addN 1397 1202 1395, .loadN 1398 1397])
  (.seq (.ifLtN 0 1398
      (.seq (block [.addN 1399 1200 1396, .storeN 1399 1395, .addN 1396 1396 1001,
          .storeN 1397 1389, .addN 1397 1390 1395])
        (.ifLtN 1398 1389 (.instr (.storeN 1397 1389)) (.instr (.storeN 1397 1001))))
      .skip)
    (.instr (.addN 1395 1395 1001)))

/-- **The first pass**: the sorted list of `C = N[U]` at `1200` (length in `1396`), the flags
`2` on `C`, the zones (`1390`) `1` on `U` and `2` on `C \ U`. -/
def spN1 : Stmt := .seq (block [.constN 1395 0, .constN 1396 0, .constN 1389 2])
  (.whileLtN 1395 1204 spN1Body)

open scoped Classical in
theorem spN1_exec {d : Config} (hw : WordsBounded W d) {U C : Finset (Fin N)} (hUC : U ⊆ C)
    {a0 aF aZ : ℕ} (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h04 : d.nreg 1204 = N)
    (h00 : d.nreg 1200 = a0) (h02 : d.nreg 1202 = aF) (h90 : d.nreg 1390 = aZ)
    (hF : ∀ x < N, d.nmem (aF + x) = if x ∈ UN U then 2 else if x ∈ UN C then 1 else 0)
    (hZ : ∀ x < N, d.nmem (aZ + x) = 0)
    (l1 : a0 + N ≤ aF) (l2 : aF + N ≤ aZ) (l3 : aZ + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W spN1 d d' k ∧ WordsBounded W d' ∧ d'.nreg 1396 = #C ∧
      (∀ t < #C, d'.nmem (a0 + t) = lv C t) ∧
      (∀ x < N, d'.nmem (aF + x) = if x ∈ UN C then 2 else 0) ∧
      (∀ x < N, d'.nmem (aZ + x) = if x ∈ UN U then 1 else if x ∈ UN C then 2 else 0) ∧
      (∀ a, (a < a0 ∨ aZ + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1389 → r ≠ 1395 → r ≠ 1396 → r ≠ 1397 → r ≠ 1398 → r ≠ 1399 →
        d'.nreg r = d.nreg r) ∧ k ≤ 14 * N + 5 := by
  have hCN := card_le_N C
  let zf : ℕ → ℕ := fun x => if x ∈ UN U then 1 else if x ∈ UN C then 2 else 0
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1395 = j ∧
    c.nreg 1204 = N ∧ c.nreg 1389 = 2 ∧ c.nreg 1396 = #((UN C).filter (· < j)) ∧
    (∀ t < #((UN C).filter (· < j)), c.nmem (a0 + t) = lv C t) ∧
    (∀ x < N, c.nmem (aF + x) = if x < j then (if x ∈ UN C then 2 else 0) else d.nmem (aF + x)) ∧
    (∀ x < N, c.nmem (aZ + x) = if x < j then zf x else 0) ∧
    (∀ a, (a < a0 ∨ aZ + N ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1389 → r ≠ 1395 → r ≠ 1396 → r ≠ 1397 → r ≠ 1398 → r ≠ 1399 →
      c.nreg r = d.nreg r)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1395 0, .constN 1396 0,
      .constN 1389 2]) d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 3 := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨⟨‹_›, by config_simp, by config_simp; exact h04, by config_simp,
        by config_simp; simp, fun t ht => by simp at ht, fun x hx => by simp,
        fun x hx => by simp [hZ x hx], fun _ _ => rfl,
        fun r h1 h2 h3 _ _ _ => by simp [h1, h2, h3]⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1395) (rN := 1204)
    (N := N) (lo := 0) (B := 12) (body := spN1Body) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h95, h04', h89, h96, hl, hf, hz, hfr, hq⟩ := h
      have r1 : c.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h01]
      have r0 : c.nreg 0 = 0 := by rw [hq 0 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h0]
      have r00 : c.nreg 1200 = a0 := by rw [hq 1200 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h00]
      have r02 : c.nreg 1202 = aF := by rw [hq 1202 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h02]
      have r90 : c.nreg 1390 = aZ := by rw [hq 1390 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h90]
      have mf : c.nmem (aF + j) = d.nmem (aF + j) := by rw [hf j hj, iteF (by omega)]
      have hcs := card_filter_lt_succ C j
      have hcl : #((UN C).filter (· < j + 1)) ≤ #C := by
        rw [← card_UN C]; exact card_filter_le _ _
      unfold spN1Body
      refine spec_seq ?_
      exec_block
      · rw [r02, h95]; omega
      · refine spec_seq ?_
        by_cases hjC : j ∈ UN C
        · rw [iteT hjC] at hcs
          have hcnt : lv C #((UN C).filter (· < j)) = j := lv_card_filter C hjC
          have hf0 : 0 < d.nmem (aF + j) := by
            rw [hF j hj]; split_ifs <;> simp_all
          refine spec_ifLtN_true ?_ ?_
          · config_simp; rw [r0, r02, h95, mf]; exact hf0
          refine spec_seq ?_
          exec_block
          · config_simp; rw [r00, h96]; omega
          · config_simp; rw [h96, r1]; omega
          · config_simp; rw [r90, h95]; omega
          · by_cases hjU : j ∈ UN U
            · have h2 : d.nmem (aF + j) = 2 := by rw [hF j hj, iteT hjU]
              refine spec_ifLtN_false ?_ ?_
              · config_simp; rw [r02, h95, mf, h2, h89]; omega
              refine spec_instr (Exec.storeN ‹_› _ _) fun hw₂ => ?_
              refine spec_instr (Exec.addN hw₂ _ _ _ (by config_simp; rw [h95]; omega))
                fun hw₃ => ?_
              refine ⟨⟨hw₃, by config_simp; rw [h95, r1], by config_simp; exact h04',
                by config_simp; exact h89, by config_simp; rw [h96, r1, hcs], fun t ht => ?_,
                fun x hx => ?_, fun x hx => ?_, fun a ha => ?_,
                fun r a1 a2 a3 a4 a5 a6 => ?_⟩, by omega⟩
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega)]
                rw [hcs] at ht
                rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
                · rw [upd_other _ _ _ (by omega)]; exact hl t ht
                · rw [upd_same, hcnt]
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega)]
                by_cases hxj : x = j
                · rw [hxj, upd_same, h89, iteT (show j < j + 1 by omega), iteT hjC]
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hf x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h95, r02, r00, h96, r1]
                by_cases hxj : x = j
                · rw [hxj, upd_same, iteT (show j < j + 1 by omega)]; simp [zf, hjU]
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                    upd_other _ _ _ (by omega), hz x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
                exact hfr a ha
              · simp only [Config.nreg_mk, upd_apply, a1, a2, a3, a4, a5, a6, ite_false]
                exact hq r a1 a2 a3 a4 a5 a6
            · have h1' : d.nmem (aF + j) = 1 := by rw [hF j hj, iteF hjU, iteT hjC]
              refine spec_ifLtN_true ?_ ?_
              · config_simp; rw [r02, h95, mf, h1', h89]; omega
              refine spec_instr (Exec.storeN ‹_› _ _) fun hw₂ => ?_
              refine spec_instr (Exec.addN hw₂ _ _ _ (by config_simp; rw [h95]; omega))
                fun hw₃ => ?_
              refine ⟨⟨hw₃, by config_simp; rw [h95, r1], by config_simp; exact h04',
                by config_simp; exact h89, by config_simp; rw [h96, r1, hcs], fun t ht => ?_,
                fun x hx => ?_, fun x hx => ?_, fun a ha => ?_,
                fun r a1 a2 a3 a4 a5 a6 => ?_⟩, by omega⟩
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega)]
                rw [hcs] at ht
                rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
                · rw [upd_other _ _ _ (by omega)]; exact hl t ht
                · rw [upd_same, hcnt]
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega)]
                by_cases hxj : x = j
                · rw [hxj, upd_same, h89, iteT (show j < j + 1 by omega), iteT hjC]
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hf x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h95, r02, r00, h96, h89]
                by_cases hxj : x = j
                · rw [hxj, upd_same, iteT (show j < j + 1 by omega)]; simp [zf, hjU, hjC]
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                    upd_other _ _ _ (by omega), hz x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h95, r02, r00, h96, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
                exact hfr a ha
              · simp only [Config.nreg_mk, upd_apply, a1, a2, a3, a4, a5, a6, ite_false]
                exact hq r a1 a2 a3 a4 a5 a6
        · rw [iteF hjC, Nat.add_zero] at hcs
          have hjU : j ∉ UN U := fun h => hjC (by
            obtain ⟨hN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hN, hUC hm⟩)
          have hf0 : d.nmem (aF + j) = 0 := by rw [hF j hj, iteF hjU, iteF hjC]
          refine spec_ifLtN_false ?_ ?_
          · config_simp; rw [r0, r02, h95, mf, hf0]; omega
          refine spec_skip ‹_› ?_
          refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h95]; omega))
            fun hw₃ => ?_
          refine ⟨⟨hw₃, by config_simp; rw [h95, r1], by config_simp; exact h04',
            by config_simp; exact h89, by config_simp; rw [h96]; omega, fun t ht => ?_,
            fun x hx => ?_, fun x hx => ?_, fun a ha => ?_,
            fun r a1 a2 a3 a4 a5 a6 => ?_⟩, by omega⟩
          · rw [hcs] at ht; exact hl t ht
          · rw [hf x hx]
            by_cases hxj : x = j
            · rw [hxj, iteF (show ¬ j < j by omega), iteT (show j < j + 1 by omega), iteF hjC,
                hf0]
            · by_cases hxl : x < j
              · rw [iteT hxl, iteT (show x < j + 1 by omega)]
              · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
          · rw [hz x hx]
            by_cases hxj : x = j
            · rw [hxj, iteF (show ¬ j < j by omega), iteT (show j < j + 1 by omega)]
              simp [zf, hjU, hjC]
            · by_cases hxl : x < j
              · rw [iteT hxl, iteT (show x < j + 1 by omega)]
              · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
          · exact hfr a ha
          · simp only [Config.nreg_mk, upd_apply, a1, a2, a3, a4, a5, a6, ite_false]
            exact hq r a1 a2 a3 a4 a5 a6)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, -, h96₁, hl₁, hf₁, hz₁, hfr₁, hq₁⟩ := h₁
  rw [card_filter_lt_N] at h96₁ hl₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h96₁, hl₁, fun x hx => by rw [hf₁ x hx, iteT hx],
    fun x hx => by rw [hz₁ x hx, iteT hx], hfr₁, hq₁, by omega⟩

end Piece

end PlanarSeparator
