module

public import PlanarSeparator.Machine.SplitProg

/-!
# The split of a node on the machine: more passes

Passes of the machine form of `PlanarSeparator.SepRoutine.splitW` (with the names of
`PlanarSeparator.Piece.splitW_eq_sp`):

* `spClr`: the zeros on an array of `N` words;
* `spN2`: from the flags `2` on `C` and `1` on `D \ C` and the zones `1` on `U`, `2` on
  `C \ U`: the sorted list of `D`, its size, the size of `D \ U`, the zones `1` on `U` and `2`
  on `D \ U`, the flags cleared;
* `spWt`: the weights `c₁` on the zone `1` and `c₂` on the zone `2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Lean Elab Tactic Meta in
/-- Clear every hypothesis that mentions a machine configuration or is an implication. -/
elab "spclear" : tactic => do
  liftMetaTactic fun g => do
    let g' ← g.withContext do
      let mut fvs : Array FVarId := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if (← isProp t) then
          let bad := t.foldConsts false fun c b => b || c.components.contains `Config
          if bad || t.isForall then fvs := fvs.push d.fvarId
      g.tryClearMany fvs
    return [g']

/-- `omega` after `spclear`. -/
macro "spomega" : tactic => `(tactic| (spclear; omega))

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {W : ℕ} {P : Input}

theorem mem_UN_sdiff {A B : Finset (Fin N)} {x : ℕ} : x ∈ UN (A \ B) ↔ x ∈ UN A ∧ x ∉ UN B := by
  simp only [UN, map_sdiff, mem_sdiff]

/-! ### The zeros on an array -/

def spClrBody (r : ℕ) : Stmt := block [.addN 1411 r 1410, .storeN 1411 0, .addN 1410 1410 1001]

/-- **The zeros** on the `N` words from `nreg r` (`nreg 1204 = N`, `nreg 0 = 0`). -/
def spClr (r : ℕ) : Stmt := .seq (.instr (.constN 1410 0)) (.whileLtN 1410 1204 (spClrBody r))

theorem spClr_exec {d : Config} (hw : WordsBounded W d) {r b : ℕ} (hr : r ≠ 1410) (hr' : r ≠ 1411)
    (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h04 : d.nreg 1204 = N) (hb : d.nreg r = b)
    (hbW : b + N ≤ W) :
    ∃ d' k, Exec P W (spClr r) d d' k ∧ WordsBounded W d' ∧ (∀ x < N, d'.nmem (b + x) = 0) ∧
      (∀ a, (a < b ∨ b + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r', r' ≠ 1410 → r' ≠ 1411 → d'.nreg r' = d.nreg r') ∧ k ≤ 5 * N + 3 := by
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1204 = N ∧ (∀ x < j, c.nmem (b + x) = 0) ∧
    (∀ a, (a < b ∨ b + j ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r', r' ≠ 1410 → r' ≠ 1411 → c.nreg r' = d.nreg r')
  have e0 := Exec.constN (P := P) hw 1410 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1204)
    (N := N) (lo := 0) (B := 3) (body := spClrBody r) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10, h04', hz, hm, hq⟩ := h
      have r1 : c.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega), h01]
      have r0 : c.nreg 0 = 0 := by rw [hq 0 (by omega) (by omega), h0]
      have rb : c.nreg r = b := by rw [hq r hr hr', hb]
      unfold spClrBody
      exec_block
      · rw [rb, h10]; omega
      · config_simp; rw [h10, r1]; omega
      · refine ⟨⟨‹_›, by config_simp; rw [h10, r1], by config_simp; exact h04',
          fun x hx => ?_, fun a ha => ?_, fun r'' a1 a2 => ?_⟩, by omega⟩
        · config_simp
          rw [rb, h10, r0]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hz x hx
          · rw [upd_same]
        · config_simp
          rw [rb, h10, upd_other _ _ _ (by omega)]
          exact hm a (by omega)
        · simp only [Config.nreg_mk, upd_apply, a1, a2, ite_false]
          exact hq r'' a1 a2)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h04,
      fun x hx => absurd hx (by omega), fun a _ => rfl,
      fun r'' a1 _ => by simp [a1]⟩
  obtain ⟨hw₁, -, -, hz₁, hm₁, hq₁⟩ := h₁
  exact ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, hz₁, fun a ha => hm₁ a ha, hq₁, by omega⟩

/-! ### The closed neighbourhood of the closed neighbourhood -/

def spN2Body : Stmt := .seq (block [.addN 1411 1202 1410, .loadN 1412 1411])
  (.seq (.ifLtN 0 1412
      (block [.storeN 1411 0, .addN 1411 1312 1403, .storeN 1411 1410, .addN 1403 1403 1001,
        .addN 1411 1390 1410, .loadN 1413 1411, .subN 1414 1413 1001, .subN 1415 1001 1413,
        .addN 1414 1414 1415, .addN 1404 1404 1414, .addN 1415 1001 1414, .storeN 1411 1415])
      .skip)
    (.instr (.addN 1410 1410 1001)))

/-- **The second pass**: from the flags (`1202`) `2` on `C` and `1` on `D \ C`, and the zones
(`1390`) `1` on `U` and `2` on `C \ U`: the sorted list of `D` at `1312` (size in `1403`), the
size of `D \ U` in `1404`, the zones `1` on `U` and `2` on `D \ U`, the flags cleared. -/
def spN2 : Stmt := .seq (block [.constN 1410 0, .constN 1403 0, .constN 1404 0])
  (.whileLtN 1410 1204 spN2Body)

theorem spN2_exec {d : Config} (hw : WordsBounded W d) {U C D : Finset (Fin N)} (hUC : U ⊆ C)
    (hCD : C ⊆ D) {aF aV aZ : ℕ} (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0)
    (h04 : d.nreg 1204 = N) (h02 : d.nreg 1202 = aF) (h12 : d.nreg 1312 = aV)
    (h90 : d.nreg 1390 = aZ)
    (hF : ∀ x < N, d.nmem (aF + x) = if x ∈ UN C then 2 else if x ∈ UN D then 1 else 0)
    (hZ : ∀ x < N, d.nmem (aZ + x) = if x ∈ UN U then 1 else if x ∈ UN C then 2 else 0)
    (l1 : aF + N ≤ aV) (l2 : aV + N ≤ aZ) (l3 : aZ + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W spN2 d d' k ∧ WordsBounded W d' ∧ d'.nreg 1403 = #D ∧
      d'.nreg 1404 = #(D \ U) ∧ (∀ t < #D, d'.nmem (aV + t) = lv D t) ∧
      (∀ x < N, d'.nmem (aF + x) = 0) ∧
      (∀ x < N, d'.nmem (aZ + x) = if x ∈ UN U then 1 else if x ∈ UN D then 2 else 0) ∧
      (∀ a, (a < aF ∨ aF + N ≤ a) → (a < aV ∨ aV + N ≤ a) → (a < aZ ∨ aZ + N ≤ a) →
        d'.nmem a = d.nmem a) ∧
      (∀ r, spN2.wr r = false → d'.nreg r = d.nreg r) ∧ k ≤ 18 * N + 5 := by
  have hDN := card_le_N D
  have hUD : U ⊆ D := hUC.trans hCD
  have hcD : ∀ j, #((UN D).filter (· < j)) ≤ #D := fun j => by
    rw [← card_UN D]; exact card_filter_le _ _
  have hcDU : ∀ j, #((UN (D \ U)).filter (· < j)) ≤ #D := fun j => by
    rw [← card_UN D]
    exact (card_filter_le _ _).trans (card_le_card (map_subset_map.2 sdiff_subset))
  let zf : ℕ → ℕ := fun x => if x ∈ UN U then 1 else if x ∈ UN D then 2 else 0
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1204 = N ∧ c.nreg 1403 = #((UN D).filter (· < j)) ∧
    c.nreg 1404 = #((UN (D \ U)).filter (· < j)) ∧
    (∀ t < #((UN D).filter (· < j)), c.nmem (aV + t) = lv D t) ∧
    (∀ x < N, c.nmem (aF + x) = if x < j then 0 else d.nmem (aF + x)) ∧
    (∀ x < N, c.nmem (aZ + x) = if x < j then zf x else d.nmem (aZ + x)) ∧
    (∀ a, (a < aF ∨ aF + N ≤ a) → (a < aV ∨ aV + N ≤ a) → (a < aZ ∨ aZ + N ≤ a) →
        c.nmem a = d.nmem a) ∧
    (∀ r, spN2.wr r = false → c.nreg r = d.nreg r)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1410 0, .constN 1403 0,
      .constN 1404 0]) d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 3 := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨⟨‹_›, by config_simp, by config_simp; exact h04, by config_simp; simp,
        by config_simp; simp, fun t ht => by simp at ht, fun x hx => by simp,
        fun x hx => by simp, fun _ _ _ _ => rfl, fun r hr => ?_⟩, rfl⟩
      simp only [spN2, spN2Body, Stmt.wr, block, Instr.wr, Bool.or_eq_false_iff] at hr
      simp only [upd_apply]
      split_ifs <;> simp_all
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1204)
    (N := N) (lo := 0) (B := 16) (body := spN2Body) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10, h04', h03, h04c, hl, hf, hz, hfr, hq⟩ := h
      have q : ∀ r, spN2.wr r = false → c.nreg r = d.nreg r := hq
      have r1 : c.nreg 1001 = 1 := by rw [q 1001 (by decide), h01]
      have r0 : c.nreg 0 = 0 := by rw [q 0 (by decide), h0]
      have r02 : c.nreg 1202 = aF := by rw [q 1202 (by decide), h02]
      have r12 : c.nreg 1312 = aV := by rw [q 1312 (by decide), h12]
      have r90 : c.nreg 1390 = aZ := by rw [q 1390 (by decide), h90]
      have mf : c.nmem (aF + j) = d.nmem (aF + j) := by rw [hf j hj, iteF (by omega)]
      have mz : c.nmem (aZ + j) = d.nmem (aZ + j) := by rw [hz j hj, iteF (by omega)]
      have hcs := card_filter_lt_succ D j
      have hcs' := card_filter_lt_succ (D \ U) j
      have hD1 := hcD (j + 1)
      have hDU1 := hcDU (j + 1)
      obtain ⟨c', k, e, h', hk⟩ : ∃ c' k, Exec P W spN2Body c c' k ∧
          (WordsBounded W c' ∧ c'.nreg 1410 = j + 1 ∧
          c'.nreg 1204 = N ∧ c'.nreg 1403 = #((UN D).filter (· < j + 1)) ∧
          c'.nreg 1404 = #((UN (D \ U)).filter (· < j + 1)) ∧
          (∀ t < #((UN D).filter (· < j + 1)), c'.nmem (aV + t) = lv D t) ∧
          (∀ x < N, c'.nmem (aF + x) = if x < j + 1 then 0 else d.nmem (aF + x)) ∧
          (∀ x < N, c'.nmem (aZ + x) = if x < j + 1 then zf x else d.nmem (aZ + x)) ∧
          (∀ a, (a < aF ∨ aF + N ≤ a) → (a < aV ∨ aV + N ≤ a) → (a < aZ ∨ aZ + N ≤ a) →
            c'.nmem a = d.nmem a)) ∧ k ≤ 16 := by
        unfold spN2Body
        refine spec_seq ?_
        exec_block
        · rw [r02, h10]; omega
        · refine spec_seq ?_
          by_cases hjD : j ∈ UN D
          · rw [iteT hjD] at hcs
            have hcnt : lv D #((UN D).filter (· < j)) = j := lv_card_filter D hjD
            have hf0 : 0 < d.nmem (aF + j) := by
              rw [hF j hj]; split_ifs <;> simp_all
            have hz2 : d.nmem (aZ + j) ≤ 2 := by rw [hZ j hj]; split_ifs <;> simp
            have hz1 : d.nmem (aZ + j) = 1 ↔ j ∈ UN U := by
              rw [hZ j hj]; split_ifs <;> simp_all
            have hdd : d.nmem (aZ + j) - 1 + (1 - d.nmem (aZ + j)) =
                if j ∈ UN U then 0 else 1 := by
              split_ifs with hu
              · rw [hz1.2 hu]
              · have := hz1.not.2 hu; omega
            have hjDU : (j ∈ UN (D \ U)) ↔ j ∉ UN U := by
              rw [mem_UN_sdiff]; exact ⟨fun h => h.2, fun h => ⟨hjD, h⟩⟩
            have hcs'' : #((UN (D \ U)).filter (· < j + 1)) =
                #((UN (D \ U)).filter (· < j)) + if j ∈ UN U then 0 else 1 := by
              rw [hcs']; congr 1; by_cases hu : j ∈ UN U
              · rw [iteF (fun h => hjDU.1 h hu), iteT hu]
              · rw [iteT (hjDU.2 hu), iteF hu]
            refine spec_ifLtN_true ?_ ?_
            · config_simp; rw [r0, r02, h10, mf]; exact hf0
            exec_block
            · config_simp; rw [r12, h03]; omega
            · config_simp; rw [h03, r1]; omega
            · config_simp; rw [r90, h10]; omega
            · config_simp; rw [r90, h10, upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega), mz, r1]
              omega
            · config_simp; rw [r90, h10, upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega), mz, r1, hdd, h04c]
              split_ifs <;> omega
            · config_simp; rw [r90, h10, upd_other _ _ _ (by omega),
                upd_other _ _ _ (by omega), mz, r1, hdd]
              split_ifs <;> omega
            · refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h10, r1]; omega))
                fun hw₃ => ?_
              have ez : c.nmem (aZ + j) = d.nmem (aZ + j) := mz
              refine ⟨⟨hw₃, by config_simp; rw [h10, r1], by config_simp; exact h04',
                by config_simp; rw [h03, r1, hcs], ?_, fun t ht => ?_,
                fun x hx => ?_, fun x hx => ?_, fun a ha1 ha2 ha3 => ?_⟩, by omega⟩
              · config_simp
                rw [r90, h10, r02, r12, h03, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega), mz, r1, hdd, h04c, hcs'']
              · config_simp
                rw [r90, h10, r02, r12, h03, upd_other _ _ _ (by omega)]
                rw [hcs] at ht
                rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hl t ht
                · rw [upd_same, hcnt]
              · config_simp
                rw [r90, h10, r02, r12, h03, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega), r0]
                by_cases hxj : x = j
                · rw [hxj, upd_same, iteT (show j < j + 1 by omega)]
                · rw [upd_other _ _ _ (by omega), hf x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h10, r02, r12, h03]
                by_cases hxj : x = j
                · subst hxj
                  rw [upd_same, iteT (show x < x + 1 by omega), upd_other _ _ _ (by omega),
                    upd_other _ _ _ (by omega), mz, r1, hdd]
                  simp only [zf, iteT hjD]
                  split_ifs <;> rfl
                · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
                    upd_other _ _ _ (by omega), hz x hx]
                  by_cases hxl : x < j
                  · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                  · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
              · config_simp
                rw [r90, h10, r02, r12, h03, upd_other _ _ _ (by omega),
                  upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
                exact hfr a ha1 ha2 ha3
          · rw [iteF hjD, Nat.add_zero] at hcs
            have hjDU : j ∉ UN (D \ U) := fun h => hjD (mem_UN_sdiff.1 h).1
            rw [iteF hjDU, Nat.add_zero] at hcs'
            have hjC : j ∉ UN C := fun h => hjD (by
              obtain ⟨hN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hN, hCD hm⟩)
            have hf0 : d.nmem (aF + j) = 0 := by rw [hF j hj, iteF hjC, iteF hjD]
            refine spec_ifLtN_false ?_ ?_
            · config_simp; rw [r0, r02, h10, mf, hf0]; omega
            refine spec_skip ‹_› ?_
            refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h10, r1]; omega))
              fun hw₃ => ?_
            refine ⟨⟨hw₃, by config_simp; rw [h10, r1], by config_simp; exact h04',
              by config_simp; rw [h03]; omega, by config_simp; rw [h04c]; omega,
              fun t ht => ?_, fun x hx => ?_, fun x hx => ?_, fun a ha1 ha2 ha3 => ?_⟩,
              by omega⟩
            · rw [hcs] at ht; exact hl t ht
            · rw [hf x hx]
              by_cases hxj : x = j
              · rw [hxj, iteF (show ¬ j < j by omega), iteT (show j < j + 1 by omega), hf0]
              · by_cases hxl : x < j
                · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
            · rw [hz x hx]
              by_cases hxj : x = j
              · have hjU : j ∉ UN U := fun h => hjD (by
                  obtain ⟨hN, hm⟩ := mem_UN.1 h; exact mem_UN.2 ⟨hN, hUD hm⟩)
                rw [hxj, iteF (show ¬ j < j by omega), iteT (show j < j + 1 by omega), hZ j hj]
                simp [zf, hjU, hjC, hjD]
              · by_cases hxl : x < j
                · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
            · exact hfr a ha1 ha2 ha3
      exact ⟨c', k, e, ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1,
        h'.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2, fun r hr => by
          rw [Exec.nreg_of_wr e (by
            simp only [spN2, Stmt.wr, Bool.or_eq_false_iff] at hr; exact hr.2)]
          exact q r hr⟩, hk⟩)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h03₁, h04₁, hl₁, hf₁, hz₁, hfr₁, hq₁⟩ := h₁
  rw [card_filter_lt_N] at h03₁ hl₁
  rw [card_filter_lt_N] at h04₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h03₁, h04₁, hl₁, fun x hx => by rw [hf₁ x hx, iteT hx],
    fun x hx => by rw [hz₁ x hx, iteT hx], hfr₁, hq₁, by omega⟩

/-! ### The weights -/

def spWtBody : Stmt := .seq (block [.addN 1411 1390 1410, .loadN 1413 1411, .addN 1411 1014 1410])
  (.seq (.ifLtN 0 1413
      (.ifLtN 1001 1413 (.instr (.storeN 1411 1406)) (.instr (.storeN 1411 1405))) .skip)
    (.instr (.addN 1410 1410 1001)))

/-- **The weights**: `nreg 1405` on the zone `1`, `nreg 1406` on the zone `2` (array `1014`). -/
def spWt : Stmt := .seq (.instr (.constN 1410 0)) (.whileLtN 1410 1204 spWtBody)

theorem spWt_exec {d : Config} (hw : WordsBounded W d) {X Y : Finset (Fin N)} {aw aZ c₁ c₂ : ℕ}
    (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h04 : d.nreg 1204 = N)
    (h14 : d.nreg 1014 = aw) (h90 : d.nreg 1390 = aZ) (h05 : d.nreg 1405 = c₁)
    (h06 : d.nreg 1406 = c₂)
    (hZ : ∀ x < N, d.nmem (aZ + x) = if x ∈ UN X then 1 else if x ∈ UN Y then 2 else 0)
    (l1 : aw + N ≤ aZ) (l2 : aZ + N ≤ W) :
    ∃ d' k, Exec P W spWt d d' k ∧ WordsBounded W d' ∧
      (∀ x < N, d'.nmem (aw + x) =
        if x ∈ UN X then c₁ else if x ∈ UN Y then c₂ else d.nmem (aw + x)) ∧
      (∀ a, (a < aw ∨ aw + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, spWt.wr r = false → d'.nreg r = d.nreg r) ∧ k ≤ 12 * N + 3 := by
  let g : ℕ → ℕ := fun x => if x ∈ UN X then c₁ else if x ∈ UN Y then c₂ else d.nmem (aw + x)
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1204 = N ∧ (∀ x < N, c.nmem (aw + x) = if x < j then g x else d.nmem (aw + x)) ∧
    (∀ a, (a < aw ∨ aw + N ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, spWt.wr r = false → c.nreg r = d.nreg r)
  have e0 := Exec.constN (P := P) hw 1410 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1204)
    (N := N) (lo := 0) (B := 10) (body := spWtBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10, h04', hm, hfr, hq⟩ := h
      have q : ∀ r, spWt.wr r = false → c.nreg r = d.nreg r := hq
      have r1 : c.nreg 1001 = 1 := by rw [q 1001 (by decide), h01]
      have r0 : c.nreg 0 = 0 := by rw [q 0 (by decide), h0]
      have r14 : c.nreg 1014 = aw := by rw [q 1014 (by decide), h14]
      have r90 : c.nreg 1390 = aZ := by rw [q 1390 (by decide), h90]
      have r05 : c.nreg 1405 = c₁ := by rw [q 1405 (by decide), h05]
      have r06 : c.nreg 1406 = c₂ := by rw [q 1406 (by decide), h06]
      have mz : c.nmem (aZ + j) = d.nmem (aZ + j) := hfr _ (Or.inr (by omega))
      obtain ⟨c', k, e, h', hk⟩ : ∃ c' k, Exec P W spWtBody c c' k ∧
          (WordsBounded W c' ∧ c'.nreg 1410 = j + 1 ∧ c'.nreg 1204 = N ∧
          (∀ x < N, c'.nmem (aw + x) = if x < j + 1 then g x else d.nmem (aw + x)) ∧
          (∀ a, (a < aw ∨ aw + N ≤ a) → c'.nmem a = d.nmem a)) ∧ k ≤ 10 := by
        unfold spWtBody
        refine spec_seq ?_
        exec_block
        · rw [r90, h10]; omega
        · config_simp; rw [r14, h10]; omega
        · -- the value stored at `aw + j`
          have post : ∀ (c₂' : Config) (v : ℕ), WordsBounded W c₂' → c₂'.nreg 1410 = j →
              c₂'.nreg 1204 = N → (∀ r, r ≠ 1411 → r ≠ 1413 → c₂'.nreg r = c.nreg r) →
              c₂'.nmem = upd c.nmem (aw + j) v → v = g j →
              ∃ c' k, Exec P W (.instr (.addN 1410 1410 1001)) c₂' c' k ∧
                (WordsBounded W c' ∧ c'.nreg 1410 = j + 1 ∧ c'.nreg 1204 = N ∧
                (∀ x < N, c'.nmem (aw + x) = if x < j + 1 then g x else d.nmem (aw + x)) ∧
                (∀ a, (a < aw ∨ aw + N ≤ a) → c'.nmem a = d.nmem a)) ∧ k ≤ 1 := by
            intro c₂' v hw₂ g10 g04 gq gm gv
            have g1 : c₂'.nreg 1001 = 1 := by rw [gq 1001 (by omega) (by omega), r1]
            refine spec_instr (Exec.addN hw₂ _ _ _ (by rw [g10, g1]; omega)) fun hw₃ => ?_
            refine ⟨⟨hw₃, by config_simp; rw [g10, g1], by config_simp; exact g04,
              fun x hx => ?_, fun a ha => ?_⟩, le_rfl⟩
            · config_simp; rw [gm]
              by_cases hxj : x = j
              · rw [hxj, upd_same, iteT (show j < j + 1 by omega), gv]
              · rw [upd_other _ _ _ (by omega), hm x hx]
                by_cases hxl : x < j
                · rw [iteT hxl, iteT (show x < j + 1 by omega)]
                · rw [iteF hxl, iteF (show ¬ x < j + 1 by omega)]
            · config_simp; rw [gm, upd_other _ _ _ (by omega)]; exact hfr a ha
          refine spec_seq ?_
          by_cases hjX : j ∈ UN X
          · have hz : d.nmem (aZ + j) = 1 := by rw [hZ j hj, iteT hjX]
            refine spec_ifLtN_true (by config_simp; rw [r0, r90, h10, mz, hz]; omega) ?_
            refine spec_ifLtN_false (by config_simp; rw [r1, r90, h10, mz, hz]; omega) ?_
            refine spec_instr (Exec.storeN ‹_› _ _) fun hw₂ => ?_
            obtain ⟨c', k, e, h', hk⟩ := post _ (c.nreg 1405) hw₂ (by config_simp; exact h10)
              (by config_simp; exact h04') (fun r a1 a2 => by simp [a1, a2])
              (by config_simp; rw [r14, h10]) (by rw [r05]; simp [g, hjX])
            exact ⟨c', k, e, h', by omega⟩
          · by_cases hjY : j ∈ UN Y
            · have hz : d.nmem (aZ + j) = 2 := by rw [hZ j hj, iteF hjX, iteT hjY]
              refine spec_ifLtN_true (by config_simp; rw [r0, r90, h10, mz, hz]; omega) ?_
              refine spec_ifLtN_true (by config_simp; rw [r1, r90, h10, mz, hz]; omega) ?_
              refine spec_instr (Exec.storeN ‹_› _ _) fun hw₂ => ?_
              obtain ⟨c', k, e, h', hk⟩ := post _ (c.nreg 1406) hw₂ (by config_simp; exact h10)
                (by config_simp; exact h04') (fun r a1 a2 => by simp [a1, a2])
                (by config_simp; rw [r14, h10]) (by rw [r06]; simp [g, hjX, hjY])
              exact ⟨c', k, e, h', by omega⟩
            · have hz : d.nmem (aZ + j) = 0 := by rw [hZ j hj, iteF hjX, iteF hjY]
              refine spec_ifLtN_false (by config_simp; rw [r0, r90, h10, mz, hz]; omega) ?_
              refine spec_skip ‹_› ?_
              have hv : c.nmem (aw + j) = g j := by
                rw [hm j hj, iteF (by omega)]; simp [g, hjX, hjY]
              obtain ⟨c', k, e, h', hk⟩ := post _ (c.nmem (aw + j)) ‹_›
                (by config_simp; exact h10) (by config_simp; exact h04')
                (fun r a1 a2 => by simp [a1, a2]) (by config_simp) hv
              exact ⟨c', k, e, h', by omega⟩
      exact ⟨c', k, e, ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, fun r hr => by
          rw [Exec.nreg_of_wr e (by
            simp only [spWt, Stmt.wr, Bool.or_eq_false_iff] at hr; exact hr.2)]
          exact q r hr⟩, hk⟩)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h04,
      fun x hx => by simp, fun a _ => rfl, fun r hr => by
        simp only [spWt, Stmt.wr, Instr.wr, Bool.or_eq_false_iff] at hr
        simp only [upd_apply]
        split_ifs <;> simp_all⟩
  obtain ⟨hw₁, -, -, hm₁, hfr₁, hq₁⟩ := h₁
  exact ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun x hx => by rw [hm₁ x hx, iteT hx], hfr₁,
    fun r hr => by rw [hq₁ r hr], by omega⟩

/-! ### The marks of the outputs -/

theorem mem_iff_lv' (U : Finset (Fin N)) {v : Fin N} : v ∈ U ↔ ∃ l < #U, lv U l = v := by
  rw [mem_iff_lv U v, length_clist_ord]

theorem lv_le_N (U : Finset (Fin N)) (j : ℕ) : lv U j ≤ N := by
  by_cases h : j < #U
  · exact (lv_ltN U h).le
  · unfold lv
    rw [List.getD_eq_default _ _ (by rw [List.length_map, length_clist_ord]; omega)]
    exact Nat.zero_le _

def spMk2Body : Stmt := block [.addN 1411 1200 1410, .loadN 1412 1411, .addN 1411 1310 1412,
  .loadN 1413 1411, .addN 1413 1413 1413, .addN 1411 1019 1412, .storeN 1411 1413,
  .addN 1410 1410 1001]

/-- **The marks `2 sf`** (array `1019`) along the list at `1200`. -/
def spMk2 : Stmt := .seq (.instr (.constN 1410 0)) (.whileLtN 1410 1201 spMk2Body)

theorem spMk2_exec {d : Config} (hw : WordsBounded W d) {U : Finset (Fin N)} {a0 am aS : ℕ}
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 1200 = a0) (h01' : d.nreg 1201 = #U)
    (h19 : d.nreg 1019 = am) (h10 : d.nreg 1310 = aS)
    (hl : ∀ l < #U, d.nmem (a0 + l) = lv U l) (hS : ∀ v ∈ U, d.nmem (aS + v) ≤ 1)
    (l1 : am + N ≤ a0) (l2 : a0 + N ≤ aS) (l3 : aS + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W spMk2 d d' k ∧ WordsBounded W d' ∧
      (∀ v ∈ U, d'.nmem (am + v) = 2 * d.nmem (aS + v)) ∧
      (∀ a, (a < am ∨ am + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, spMk2.wr r = false → d'.nreg r = d.nreg r) ∧ k ≤ 10 * N + 3 := by
  have hUN := card_le_N U
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1201 = #U ∧ (∀ l < j, c.nmem (am + lv U l) = 2 * d.nmem (aS + lv U l)) ∧
    (∀ a, (a < am ∨ am + N ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, spMk2.wr r = false → c.nreg r = d.nreg r)
  have e0 := Exec.constN (P := P) hw 1410 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1201)
    (N := #U) (lo := 0) (B := 8) (body := spMk2Body) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10', h01c, hm, hfr, hq⟩ := h
      have q : ∀ r, spMk2.wr r = false → c.nreg r = d.nreg r := hq
      have r1 : c.nreg 1001 = 1 := by rw [q 1001 (by decide), h01]
      have r00 : c.nreg 1200 = a0 := by rw [q 1200 (by decide), h00]
      have r19 : c.nreg 1019 = am := by rw [q 1019 (by decide), h19]
      have r10 : c.nreg 1310 = aS := by rw [q 1310 (by decide), h10]
      have hv := lv_ltN U hj
      have mv : c.nmem (a0 + j) = lv U j := by rw [hfr _ (Or.inr (by omega))]; exact hl j hj
      have ms : c.nmem (aS + lv U j) = d.nmem (aS + lv U j) := hfr _ (Or.inr (by omega))
      have hs1 : d.nmem (aS + lv U j) ≤ 1 := hS ⟨lv U j, hv⟩ ((mem_iff_lv' U).2 ⟨j, hj, rfl⟩)
      obtain ⟨c', k, e, h', hk⟩ : ∃ c' k, Exec P W spMk2Body c c' k ∧
          (WordsBounded W c' ∧ c'.nreg 1410 = j + 1 ∧ c'.nreg 1201 = #U ∧
          (∀ l < j + 1, c'.nmem (am + lv U l) = 2 * d.nmem (aS + lv U l)) ∧
          (∀ a, (a < am ∨ am + N ≤ a) → c'.nmem a = d.nmem a)) ∧ k ≤ 8 := by
        unfold spMk2Body
        exec_block
        · rw [r00, h10']; omega
        · config_simp; rw [r10, r00, h10', mv]; omega
        · config_simp; rw [r10, r00, h10', mv, ms]; omega
        · config_simp; rw [r19, r00, h10', mv]; omega
        · config_simp; rw [h10', r1]; omega
        · refine ⟨⟨‹_›, by config_simp; rw [h10', r1], by config_simp; exact h01c,
            fun l hl' => ?_, fun a ha => ?_⟩, by omega⟩
          · config_simp
            rw [r19, r10, r00, h10', mv, ms]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with hl' | rfl
            · rw [upd_other _ _ _ (fun h => by
                have := lv_inj' U (hl'.trans hj) hj (by omega); omega)]
              exact hm l hl'
            · rw [upd_same]; ring
          · config_simp
            rw [r19, r00, h10', mv, upd_other _ _ _ (by omega)]
            exact hfr a ha
      exact ⟨c', k, e, ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, fun r hr => by
          rw [Exec.nreg_of_wr e (by
            simp only [spMk2, Stmt.wr, Bool.or_eq_false_iff] at hr; exact hr.2)]
          exact q r hr⟩, hk⟩)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h01',
      fun l hl' => absurd hl' (by omega), fun a _ => rfl, fun r hr => by
        simp only [spMk2, Stmt.wr, Instr.wr, Bool.or_eq_false_iff] at hr
        simp only [upd_apply]
        split_ifs <;> simp_all⟩
  obtain ⟨hw₁, -, -, hm₁, hfr₁, hq₁⟩ := h₁
  refine ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun v hv => ?_, hfr₁,
    fun r hr => by rw [hq₁ r hr], by omega⟩
  obtain ⟨l, hl', hlv⟩ := (mem_iff_lv' U).1 hv
  rw [← hlv]; exact hm₁ l hl'

def spMk1Body : Stmt := block [.addN 1411 1200 1410, .loadN 1412 1411, .addN 1411 1310 1412,
  .loadN 1413 1411, .subN 1413 1001 1413, .addN 1411 1311 1412, .loadN 1414 1411,
  .addN 1411 1394 1414, .loadN 1414 1411, .subN 1414 1389 1414, .mulN 1413 1413 1414,
  .addN 1411 1019 1412, .storeN 1411 1413, .addN 1410 1410 1001]

/-- **The marks `(1 - sf) (2 - J[pid])`** (array `1019`) along the list at `1200`. -/
def spMk1 : Stmt := .seq (.instr (.constN 1410 0)) (.whileLtN 1410 1201 spMk1Body)

theorem spMk1_exec {d : Config} (hw : WordsBounded W d) {U : Finset (Fin N)}
    {a0 am aS aP aJ : ℕ}
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 1200 = a0) (h01' : d.nreg 1201 = #U)
    (h19 : d.nreg 1019 = am) (h10 : d.nreg 1310 = aS) (h11 : d.nreg 1311 = aP)
    (h94 : d.nreg 1394 = aJ) (h89 : d.nreg 1389 = 2)
    (hl : ∀ l < #U, d.nmem (a0 + l) = lv U l) (hP : ∀ v ∈ U, d.nmem (aP + v) ≤ N)
    (l1 : am + N ≤ a0) (l2 : a0 + N ≤ aS) (l3 : aS + N ≤ aP) (l4 : aP + N ≤ aJ)
    (l5 : aJ + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W spMk1 d d' k ∧ WordsBounded W d' ∧
      (∀ v ∈ U, d'.nmem (am + v) =
        (1 - d.nmem (aS + v)) * (2 - d.nmem (aJ + d.nmem (aP + v)))) ∧
      (∀ a, (a < am ∨ am + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, spMk1.wr r = false → d'.nreg r = d.nreg r) ∧ k ≤ 16 * N + 3 := by
  have hUN := card_le_N U
  let g : ℕ → ℕ := fun v => (1 - d.nmem (aS + v)) * (2 - d.nmem (aJ + d.nmem (aP + v)))
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1201 = #U ∧ (∀ l < j, c.nmem (am + lv U l) = g (lv U l)) ∧
    (∀ a, (a < am ∨ am + N ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, spMk1.wr r = false → c.nreg r = d.nreg r)
  have e0 := Exec.constN (P := P) hw 1410 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1201)
    (N := #U) (lo := 0) (B := 14) (body := spMk1Body) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10', h01c, hm, hfr, hq⟩ := h
      have q : ∀ r, spMk1.wr r = false → c.nreg r = d.nreg r := hq
      have r1 : c.nreg 1001 = 1 := by rw [q 1001 (by decide), h01]
      have r00 : c.nreg 1200 = a0 := by rw [q 1200 (by decide), h00]
      have r19 : c.nreg 1019 = am := by rw [q 1019 (by decide), h19]
      have r10 : c.nreg 1310 = aS := by rw [q 1310 (by decide), h10]
      have r11 : c.nreg 1311 = aP := by rw [q 1311 (by decide), h11]
      have r94 : c.nreg 1394 = aJ := by rw [q 1394 (by decide), h94]
      have r89 : c.nreg 1389 = 2 := by rw [q 1389 (by decide), h89]
      have hv := lv_ltN U hj
      have mv : c.nmem (a0 + j) = lv U j := by rw [hfr _ (Or.inr (by omega))]; exact hl j hj
      have ms : c.nmem (aS + lv U j) = d.nmem (aS + lv U j) := hfr _ (Or.inr (by omega))
      have mp : c.nmem (aP + lv U j) = d.nmem (aP + lv U j) := hfr _ (Or.inr (by omega))
      have hp : d.nmem (aP + lv U j) ≤ N := hP ⟨lv U j, hv⟩ ((mem_iff_lv' U).2 ⟨j, hj, rfl⟩)
      have mj : c.nmem (aJ + d.nmem (aP + lv U j)) = d.nmem (aJ + d.nmem (aP + lv U j)) :=
        hfr _ (Or.inr (by omega))
      have hgle : g (lv U j) ≤ 2 := by
        simp only [g]
        rcases Nat.eq_zero_or_pos (1 - d.nmem (aS + lv U j)) with h0 | h0
        · rw [h0]; omega
        · have : 1 - d.nmem (aS + lv U j) = 1 := by omega
          rw [this]; omega
      obtain ⟨c', k, e, h', hk⟩ : ∃ c' k, Exec P W spMk1Body c c' k ∧
          (WordsBounded W c' ∧ c'.nreg 1410 = j + 1 ∧ c'.nreg 1201 = #U ∧
          (∀ l < j + 1, c'.nmem (am + lv U l) = g (lv U l)) ∧
          (∀ a, (a < am ∨ am + N ≤ a) → c'.nmem a = d.nmem a)) ∧ k ≤ 14 := by
        unfold spMk1Body
        exec_block
        · rw [r00, h10']; omega
        · config_simp; rw [r10, r00, h10', mv]; omega
        · config_simp; rw [r11, r00, h10', mv]; omega
        · config_simp; rw [r94, r11, r00, h10', mv, mp]; omega
        · config_simp; rw [r94, r11, r10, r00, h10', mv, mp, ms, mj, r1, r89]
          exact hgle.trans hW2
        · config_simp; rw [r19, r00, h10', mv]; omega
        · config_simp; rw [h10', r1]; omega
        · refine ⟨⟨‹_›, by config_simp; rw [h10', r1], by config_simp; exact h01c,
            fun l hl' => ?_, fun a ha => ?_⟩, by omega⟩
          · config_simp
            rw [r19, r94, r11, r10, r00, h10', mv, mp, ms, mj, r1, r89]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with hl' | rfl
            · rw [upd_other _ _ _ (fun h => by
                have := lv_inj' U (hl'.trans hj) hj (by omega); omega)]
              exact hm l hl'
            · rw [upd_same]
          · config_simp
            rw [r19, r00, h10', mv, upd_other _ _ _ (by omega)]
            exact hfr a ha
      exact ⟨c', k, e, ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, fun r hr => by
          rw [Exec.nreg_of_wr e (by
            simp only [spMk1, Stmt.wr, Bool.or_eq_false_iff] at hr; exact hr.2)]
          exact q r hr⟩, hk⟩)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h01',
      fun l hl' => absurd hl' (by omega), fun a _ => rfl, fun r hr => by
        simp only [spMk1, Stmt.wr, Instr.wr, Bool.or_eq_false_iff] at hr
        simp only [upd_apply]
        split_ifs <;> simp_all⟩
  obtain ⟨hw₁, -, -, hm₁, hfr₁, hq₁⟩ := h₁
  refine ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun v hv => ?_, hfr₁,
    fun r hr => by rw [hq₁ r hr], by omega⟩
  obtain ⟨l, hl', hlv⟩ := (mem_iff_lv' U).1 hv
  rw [← hlv]; exact hm₁ l hl'

/-! ### The pieces: names and counts -/

theorem card_filter_ge_succ (T : Finset ℕ) (q : ℕ → Prop) [DecidablePred q] {j : ℕ}
    (hj : j < N) :
    #(T.filter (fun x => N - (j + 1) ≤ x ∧ q x)) =
      #(T.filter (fun x => N - j ≤ x ∧ q x)) + if N - (j + 1) ∈ T ∧ q (N - (j + 1)) then 1 else 0 := by
  have e : T.filter (fun x => N - (j + 1) ≤ x ∧ q x) =
      T.filter (fun x => N - j ≤ x ∧ q x) ∪ T.filter (fun x => x = N - (j + 1) ∧ q x) := by
    ext y; simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hy : N - j ≤ y
      · exact Or.inl ⟨h1, hy, h3⟩
      · exact Or.inr ⟨h1, by omega, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨h1, by omega, h3⟩
  rw [e, card_union_of_disjoint (disjoint_filter.2 fun _ _ h1 h2 => by omega)]
  congr 1
  split_ifs with h
  · rw [card_eq_one]; refine ⟨N - (j + 1), ?_⟩
    ext y; simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h' => h'.2.1
    · rintro rfl; exact ⟨h.1, rfl, h.2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]; rintro y hy ⟨rfl, hq⟩; exact h ⟨hy, hq⟩

theorem cnt_N (A : Finset (Fin N)) (p : ℕ → ℕ) (i : ℕ) :
    #((UN A).filter (fun x => N - N ≤ x ∧ p x = i)) = spCnt p A i := by
  unfold spCnt UN
  rw [filter_map, card_map]
  congr 1
  ext v; simp

theorem length_dedup_range'_le (p : ℕ → ℕ) (D : Finset (Fin N)) (a j : ℕ) :
    (((List.range' a j).filter (· ∈ UN D)).map p).dedup.length ≤ j := by
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by rw [List.length_range'])

theorem lt_of_mem_dedup_range' {p : ℕ → ℕ} {D : Finset (Fin N)} (hp : ∀ x ∈ UN D, p x < N)
    {a j i : ℕ} (hi : i ∈ (((List.range' a j).filter (· ∈ UN D)).map p).dedup) : i < N := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hi)
  exact hp x (by simpa using (List.mem_filter.1 hx).2)

def spPcBody : Stmt :=
  .seq (block [.addN 1410 1410 1001, .subN 1411 1204 1410, .addN 1412 1390 1411, .loadN 1413 1412])
    (.ifLtN 0 1413
      (.seq (block [.addN 1412 1310 1411, .loadN 1414 1412])
        (.ifLtN 1414 1001
          (block [.addN 1412 1311 1411, .loadN 1415 1412,
            .addN 1412 1391 1415, .loadN 1416 1412, .subN 1417 1389 1413, .addN 1416 1416 1417,
            .storeN 1412 1416,
            .addN 1412 1392 1415, .loadN 1416 1412, .subN 1417 1413 1001, .addN 1416 1416 1417,
            .storeN 1412 1416,
            .addN 1412 1393 1415, .loadN 1416 1412, .subN 1417 1001 1416, .storeN 1412 1001,
            .subN 1418 1350 1001, .storeN 1418 1415, .subN 1350 1350 1417, .addN 1351 1351 1417])
          .skip))
      .skip)

/-- **The pieces pass**: along the vertices from `N - 1` down, for the vertices of
`D = (X ∪ Y) \ S` (zones `1` on `X`, `2` on `Y`, flags `1` on `S`) with names `p`: the counts
of the names on `X \ S` (`1391`) and `Y \ S` (`1392`), the seen names (`1393`), and the list
of the names (`spList`) prepended downwards from `1350` (its length in `1351`). -/
def spPc : Stmt := .seq (.instr (.constN 1410 0)) (.whileLtN 1410 1204 spPcBody)

set_option maxHeartbeats 2000000 in
theorem spPc_exec {d : Config} (hw : WordsBounded W d) {X Y S : Finset (Fin N)} (hXY : Disjoint X Y)
    {p : ℕ → ℕ} (hp : ∀ x ∈ UN ((X ∪ Y) \ S), p x < N)
    {aZ aS aP aW aB aN aL : ℕ} (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0)
    (h04 : d.nreg 1204 = N) (h89 : d.nreg 1389 = 2)
    (h90 : d.nreg 1390 = aZ) (h10 : d.nreg 1310 = aS) (h11 : d.nreg 1311 = aP)
    (h91 : d.nreg 1391 = aW) (h92 : d.nreg 1392 = aB) (h93 : d.nreg 1393 = aN)
    (h50 : d.nreg 1350 = aL + N) (h51 : d.nreg 1351 = 0)
    (hZ : ∀ x < N, d.nmem (aZ + x) = if x ∈ UN X then 1 else if x ∈ UN Y then 2 else 0)
    (hS : ∀ x < N, d.nmem (aS + x) = if x ∈ UN S then 1 else 0)
    (hP : ∀ x ∈ UN ((X ∪ Y) \ S), d.nmem (aP + x) = p x)
    (hW0 : ∀ i < N, d.nmem (aW + i) = 0) (hB0 : ∀ i < N, d.nmem (aB + i) = 0)
    (hN0 : ∀ i < N, d.nmem (aN + i) = 0)
    (l1 : aL + N ≤ aS) (l2 : aS + N ≤ aP) (l3 : aP + N ≤ aZ) (l4 : aZ + N ≤ aW)
    (l5 : aW + N ≤ aB) (l6 : aB + N ≤ aN) (l7 : aN + N ≤ W) (hW2 : 2 ≤ W) :
    ∃ d' k, Exec P W spPc d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1351 = (spList p ((X ∪ Y) \ S)).length ∧
      d'.nreg 1350 = aL + N - (spList p ((X ∪ Y) \ S)).length ∧
      (∀ t < (spList p ((X ∪ Y) \ S)).length,
        d'.nmem (aL + N - (spList p ((X ∪ Y) \ S)).length + t) =
          (spList p ((X ∪ Y) \ S)).getD t 0) ∧
      (∀ i < N, d'.nmem (aW + i) = spCnt p (X \ S) i) ∧
      (∀ i < N, d'.nmem (aB + i) = spCnt p (Y \ S) i) ∧
      (∀ a, (a < aL ∨ aL + N ≤ a) → (a < aW ∨ aN + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, spPc.wr r = false → d'.nreg r = d.nreg r) ∧ k ≤ 32 * N + 3 := by
  set D := (X ∪ Y) \ S with hD
  let L : ℕ → List ℕ := fun j => (((List.range' (N - j) j).filter (· ∈ UN D)).map p).dedup
  let cnt : Finset (Fin N) → ℕ → ℕ → ℕ := fun A j i =>
    #((UN (A \ S)).filter (fun x => N - j ≤ x ∧ p x = i))
  have hLlen : ∀ j, (L j).length ≤ j := fun j => length_dedup_range'_le p D _ j
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1410 = j ∧
    c.nreg 1204 = N ∧ c.nreg 1351 = (L j).length ∧ c.nreg 1350 = aL + N - (L j).length ∧
    (∀ t < (L j).length, c.nmem (aL + N - (L j).length + t) = (L j).getD t 0) ∧
    (∀ i < N, c.nmem (aN + i) = if i ∈ L j then 1 else 0) ∧
    (∀ i < N, c.nmem (aW + i) = cnt X j i) ∧ (∀ i < N, c.nmem (aB + i) = cnt Y j i) ∧
    (∀ a, (a < aL ∨ aL + N ≤ a) → (a < aW ∨ aN + N ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, spPc.wr r = false → c.nreg r = d.nreg r)
  have wrne : ∀ r, spPc.wr r = false → r ≠ 1410 ∧ r ≠ 1411 ∧ r ≠ 1412 ∧ r ≠ 1413 ∧ r ≠ 1414 ∧
      r ≠ 1415 ∧ r ≠ 1416 ∧ r ≠ 1417 ∧ r ≠ 1418 ∧ r ≠ 1350 ∧ r ≠ 1351 := by
    intro r hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert hr; decide)
  have e0 := Exec.constN (P := P) hw 1410 0 (Nat.zero_le _)
  have cnt0 : ∀ A i, cnt A 0 i = 0 := fun A i => by
    simp only [cnt, Nat.sub_zero, card_eq_zero, filter_eq_empty_iff]
    intro x hx h; exact absurd (lt_of_mem_UN hx) (by omega)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1410) (rN := 1204)
    (N := N) (lo := 0) (B := 30) (body := spPcBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h10', h04', h51', h50', hl, hn, hcw, hcb, hfr, hq⟩ := h
      have q : ∀ r, spPc.wr r = false → c.nreg r = d.nreg r := hq
      have r1 : c.nreg 1001 = 1 := by rw [q 1001 (by decide), h01]
      have r0 : c.nreg 0 = 0 := by rw [q 0 (by decide), h0]
      have r89 : c.nreg 1389 = 2 := by rw [q 1389 (by decide), h89]
      have r90 : c.nreg 1390 = aZ := by rw [q 1390 (by decide), h90]
      have r10 : c.nreg 1310 = aS := by rw [q 1310 (by decide), h10]
      have r11 : c.nreg 1311 = aP := by rw [q 1311 (by decide), h11]
      have r91 : c.nreg 1391 = aW := by rw [q 1391 (by decide), h91]
      have r92 : c.nreg 1392 = aB := by rw [q 1392 (by decide), h92]
      have r93 : c.nreg 1393 = aN := by rw [q 1393 (by decide), h93]
      obtain ⟨x, hx⟩ : ∃ x, x = N - (j + 1) := ⟨_, rfl⟩
      have hxN : x < N := by omega
      have mz : c.nmem (aZ + x) = d.nmem (aZ + x) := hfr _ (Or.inr (by omega)) (Or.inl (by omega))
      have ms : c.nmem (aS + x) = d.nmem (aS + x) := hfr _ (Or.inr (by omega)) (Or.inl (by omega))
      have mp : c.nmem (aP + x) = d.nmem (aP + x) := hfr _ (Or.inr (by omega)) (Or.inl (by omega))
      have hLs : L (j + 1) = if x ∈ UN D then (if p x ∈ L j then L j else p x :: L j)
          else L j := by rw [hx]; exact dedup_range'_succ p D hj
      have hcs : ∀ A i, cnt A (j + 1) i = cnt A j i + if x ∈ UN (A \ S) ∧ p x = i then 1 else 0 :=
        fun A i => by rw [hx]; exact card_filter_ge_succ (UN (A \ S)) (fun y => p y = i) hj
      have hLj := hLlen j
      have hLj1 := hLlen (j + 1)
      -- the trivial cases
      have triv : x ∉ UN D → ∀ (c' : Config), WordsBounded W c' → c'.nreg 1410 = j + 1 →
          (∀ r, r ≠ 1410 → r ≠ 1411 → r ≠ 1412 → r ≠ 1413 → r ≠ 1414 → c'.nreg r = c.nreg r) →
          c'.nmem = c.nmem → I (j + 1) c' := by
        intro hxD c' hw₂ g10 gq gm
        have hL : L (j + 1) = L j := by rw [hLs, iteF hxD]
        have hc0 : ∀ A, A ⊆ D ∪ S → ∀ i, cnt A (j + 1) i = cnt A j i := fun A hA i => by
          have hn' : ¬ (x ∈ UN (A \ S) ∧ p x = i) := by
            rintro ⟨h1, -⟩
            obtain ⟨h1, h2⟩ := mem_UN_sdiff.1 h1
            obtain ⟨hN', hm⟩ := mem_UN.1 h1
            rcases mem_union.1 (hA hm) with h3 | h3
            · exact hxD (mem_UN.2 ⟨hN', h3⟩)
            · exact h2 (mem_UN.2 ⟨hN', h3⟩)
          rw [hcs, iteF hn', Nat.add_zero]
        have hXs : X ⊆ D ∪ S := fun v hv => by
          by_cases h : v ∈ S
          · exact mem_union_right _ h
          · exact mem_union_left _ (by rw [hD]; exact mem_sdiff.2 ⟨mem_union_left _ hv, h⟩)
        have hYs : Y ⊆ D ∪ S := fun v hv => by
          by_cases h : v ∈ S
          · exact mem_union_right _ h
          · exact mem_union_left _ (by rw [hD]; exact mem_sdiff.2 ⟨mem_union_right _ hv, h⟩)
        refine ⟨hw₂, g10,
          (by rw [gq 1204 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h04'),
          (by rw [gq 1351 (by omega) (by omega) (by omega) (by omega) (by omega), hL]; exact h51'),
          (by rw [gq 1350 (by omega) (by omega) (by omega) (by omega) (by omega), hL]; exact h50'),
          fun t ht => by rw [gm, hL]; rw [hL] at ht; exact hl t ht,
          fun i hi => by rw [gm, hL]; exact hn i hi, fun i hi => by rw [gm, hc0 X hXs]; exact hcw i hi,
          fun i hi => by rw [gm, hc0 Y hYs]; exact hcb i hi, fun a h1 h2 => by rw [gm]; exact hfr a h1 h2,
          fun r hr => by
            obtain ⟨n0, n1, n2, n3, n4, -⟩ := wrne r hr
            rw [gq r n0 n1 n2 n3 n4]
            exact q r hr⟩
      unfold spPcBody
      refine spec_seq ?_
      exec_block
      · rw [h10', r1]; omega
      · config_simp; rw [r90, h04', h10', r1, ← hx]; omega
      · have hxr : c.nreg 1204 - (c.nreg 1410 + c.nreg 1001) = x := by rw [h04', h10', r1, hx]
        by_cases hXY' : x ∈ UN X ∨ x ∈ UN Y
        · have hz : d.nmem (aZ + x) = if x ∈ UN X then 1 else 2 := by
            rw [hZ x hxN]; rcases hXY' with h | h
            · rw [iteT h, iteT h]
            · have : x ∉ UN X := fun h' => by
                obtain ⟨_, h1⟩ := mem_UN.1 h'; obtain ⟨_, h2⟩ := mem_UN.1 h
                exact disjoint_left.1 hXY h1 h2
              rw [iteF this, iteF this, iteT h]
          have hz1 : 0 < d.nmem (aZ + x) := by rw [hz]; split_ifs <;> omega
          refine spec_ifLtN_true (by config_simp; rw [r0, r90, hxr, mz]; exact hz1) ?_
          refine spec_seq ?_
          exec_block
          · config_simp; rw [r10, hxr]; omega
          · by_cases hxS : x ∈ UN S
            · have hs : d.nmem (aS + x) = 1 := by rw [hS x hxN, iteT hxS]
              refine spec_ifLtN_false (by config_simp; rw [r10, hxr, r1, ms, hs]; omega) ?_
              refine spec_skip ‹_› ?_
              refine ⟨triv (fun h => (mem_UN_sdiff.1 h).2 hxS) _ ‹_›
                (by config_simp; rw [h10', r1]) (fun r a1 a2 a3 a4 a5 => by
                  simp [a1, a2, a3, a4, a5]) (by config_simp), by omega⟩
            · have hs : d.nmem (aS + x) = 0 := by rw [hS x hxN, iteF hxS]
              have hxD : x ∈ UN D := by
                rw [hD, mem_UN_sdiff]
                refine ⟨?_, hxS⟩
                rcases hXY' with h' | h'
                · obtain ⟨hN'', h''⟩ := mem_UN.1 h'; exact mem_UN.2 ⟨hN'', mem_union_left _ h''⟩
                · obtain ⟨hN'', h''⟩ := mem_UN.1 h'; exact mem_UN.2 ⟨hN'', mem_union_right _ h''⟩
              have hpx : p x < N := hp x hxD
              have vi : c.nmem (aP + x) = p x := by rw [mp]; exact hP x hxD
              have vW : c.nmem (aW + p x) = cnt X j (p x) := hcw _ hpx
              have vB : c.nmem (aB + p x) = cnt Y j (p x) := hcb _ hpx
              have vN : c.nmem (aN + p x) = if p x ∈ L j then 1 else 0 := hn _ hpx
              have hcwle : cnt X j (p x) ≤ N := (card_filter_le _ _).trans (by
                rw [card_UN]; exact card_le_N _)
              have hcble : cnt Y j (p x) ≤ N := (card_filter_le _ _).trans (by
                rw [card_UN]; exact card_le_N _)
              have nWB : aB + p x ≠ aW + p x := by omega
              have nNW : aN + p x ≠ aW + p x := by omega
              have nNB : aN + p x ≠ aB + p x := by omega
              have hXs : x ∈ UN (X \ S) ↔ x ∈ UN X := by
                rw [mem_UN_sdiff]; exact ⟨fun h => h.1, fun h => ⟨h, hxS⟩⟩
              have hYs : x ∈ UN (Y \ S) ↔ x ∉ UN X := by
                rw [mem_UN_sdiff]
                constructor
                · rintro ⟨h1, -⟩ h2
                  obtain ⟨_, h1'⟩ := mem_UN.1 h1; obtain ⟨_, h2'⟩ := mem_UN.1 h2
                  exact disjoint_left.1 hXY h2' h1'
                · intro h; exact ⟨hXY'.resolve_left h, hxS⟩
              refine spec_ifLtN_true (by config_simp; rw [r10, hxr, r1, ms, hs]; omega) ?_
              exec_block
              · config_simp; rw [r11, hxr]; omega
              · config_simp; rw [r91, r11, hxr, vi]; omega
              · config_simp; rw [r91, r11, r89, r90, hxr, vi, vW, mz, hz]; split_ifs <;> omega
              · config_simp; rw [r92, r11, hxr, vi]; omega
              · config_simp
                rw [r92, r91, r11, r89, r90, hxr, r1, vi, mz, hz, upd_other _ _ _ nWB, vB]
                split_ifs <;> omega
              · config_simp; rw [r93, r11, hxr, vi]; omega
              · config_simp
                rw [r93, r92, r91, r11, r89, r90, hxr, r1, h51', vi,
                  upd_other _ _ _ nNB, upd_other _ _ _ nNW, vN]
                split_ifs <;> omega
              · have hL' : L (j + 1) = if p x ∈ L j then L j else p x :: L j := by
                  rw [hLs, iteT hxD]
                have hvN1 : c.nmem (aN + p x) ≤ 1 := by rw [vN]; split_ifs <;> omega
                have hlt : (L j).length < N := by omega
                refine ⟨⟨‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
                · config_simp; rw [h10', r1]
                · config_simp; exact h04'
                · config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    upd_other _ _ _ nNB, upd_other _ _ _ nNW, vN, hL']
                  split_ifs <;> simp
                · config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    upd_other _ _ _ nNB, upd_other _ _ _ nNW, vN, hL']
                  split_ifs <;> simp <;> omega
                · intro t ht
                  config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    mz, hz, vW, upd_other _ _ _ nWB, vB, upd_other _ _ _ nNB,
                    upd_other _ _ _ nNW, vN]
                  rw [hL'] at ht ⊢
                  by_cases hm : p x ∈ L j
                  · rw [iteT hm] at ht ⊢
                    simp only [upd_apply]
                    rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega)]
                    exact hl t ht
                  · rw [iteF hm] at ht ⊢
                    rw [List.length_cons] at ht ⊢
                    simp only [upd_apply]
                    rcases Nat.eq_zero_or_pos t with rfl | ht0
                    · rw [iteT (by omega)]; rfl
                    · rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega)]
                      have := hl (t - 1) (by omega)
                      rw [show aL + N - ((L j).length + 1) + t = aL + N - (L j).length + (t - 1)
                        by omega, this]
                      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
                      simp
                · intro i hi
                  config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    mz, hz, vW, upd_other _ _ _ nWB, vB, upd_other _ _ _ nNB,
                    upd_other _ _ _ nNW, vN]
                  rw [hL']
                  simp only [upd_apply]
                  rw [iteF (by omega)]
                  by_cases hip : i = p x
                  · subst hip
                    rw [iteT rfl]
                    split_ifs <;> simp_all
                  · rw [iteF (by omega), iteF (by omega), iteF (by omega), hn i hi]
                    split_ifs <;> simp_all
                · intro i hi
                  config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    mz, hz, vW, upd_other _ _ _ nWB, vB, upd_other _ _ _ nNB,
                    upd_other _ _ _ nNW, vN]
                  simp only [upd_apply]
                  rw [iteF (by omega), iteF (by omega), iteF (by omega), hcs X i]
                  by_cases hip : i = p x
                  · subst hip
                    rw [iteT rfl]
                    by_cases hxX : x ∈ UN X
                    · rw [iteT hxX, iteT ⟨hXs.2 hxX, rfl⟩]
                    · rw [iteF hxX, iteF (fun h => hxX (hXs.1 h.1))]
                  · rw [iteF (by omega), hcw i hi, iteF (fun h => hip h.2.symm), Nat.add_zero]
                · intro i hi
                  config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    mz, hz, vW, upd_other _ _ _ nWB, vB, upd_other _ _ _ nNB,
                    upd_other _ _ _ nNW, vN]
                  simp only [upd_apply]
                  rw [iteF (by omega), iteF (by omega), hcs Y i]
                  by_cases hip : i = p x
                  · subst hip
                    rw [iteT rfl]
                    by_cases hxX : x ∈ UN X
                    · rw [iteT hxX, iteF (fun h => hYs.1 h.1 hxX)]
                    · rw [iteF hxX, iteT ⟨hYs.2 hxX, rfl⟩]
                  · rw [iteF (by omega), iteF (by omega), hcb i hi, iteF (fun h => hip h.2.symm), Nat.add_zero]
                · intro a ha1 ha2
                  config_simp
                  simp only [r93, r92, r91, r11, r89, r90, h04', h10', r1, h50', h51', ← hx, vi,
                    mz, hz, vW, upd_other _ _ _ nWB, vB, upd_other _ _ _ nNB,
                    upd_other _ _ _ nNW, vN]
                  simp only [upd_apply]
                  rw [iteF (by omega), iteF (by omega), iteF (by omega), iteF (by omega)]
                  exact hfr a ha1 ha2
                · intro r hr
                  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := wrne r hr
                  simp only [Config.nreg_mk, upd_apply, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9,
                    n10, ite_false]
                  exact q r hr
        · have hz : d.nmem (aZ + x) = 0 := by
            rw [hZ x hxN, iteF (fun h => hXY' (Or.inl h)), iteF (fun h => hXY' (Or.inr h))]
          refine spec_ifLtN_false (by config_simp; rw [r0, r90, hxr, mz, hz]; omega) ?_
          refine spec_skip ‹_› ?_
          refine ⟨triv (fun h => by
            obtain ⟨h1, -⟩ := mem_UN_sdiff.1 h
            obtain ⟨hN', h2⟩ := mem_UN.1 h1
            rcases mem_union.1 h2 with h3 | h3
            · exact hXY' (Or.inl (mem_UN.2 ⟨hN', h3⟩))
            · exact hXY' (Or.inr (mem_UN.2 ⟨hN', h3⟩))) _ ‹_›
            (by config_simp; rw [h10', r1]) (fun r a1 a2 a3 a4 a5 => by
              simp [a1, a2, a3, a4, a5]) (by config_simp), by omega⟩)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h04,
      by config_simp; rw [h51]; simp [L], by config_simp; rw [h50]; simp [L],
      fun t ht => by simp [L] at ht, fun i hi => by simp [L, hN0 i hi],
      fun i hi => by rw [cnt0]; exact hW0 i hi, fun i hi => by rw [cnt0]; exact hB0 i hi,
      fun a _ _ => rfl, fun r hr => by
        obtain ⟨n0, -⟩ := wrne r hr
        simp only [Config.nreg_mk, upd_apply, n0, ite_false]⟩
  obtain ⟨hw₁, -, -, h51₁, h50₁, hl₁, -, hcw₁, hcb₁, hfr₁, hq₁⟩ := h₁
  have hLN : L N = spList p D := (spList_eq_range' p D).symm
  rw [hLN] at h51₁ h50₁ hl₁
  exact ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, h51₁, h50₁, hl₁,
    fun i hi => by rw [hcw₁ i hi]; exact cnt_N _ p i,
    fun i hi => by rw [hcb₁ i hi]; exact cnt_N _ p i, hfr₁,
    fun r hr => by rw [hq₁ r hr], by omega⟩

/-! ### Facts for the composition -/

theorem dv_pid_le
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N))
    (μ : Fin N → ℕ) (L : ℕ) :
    ∀ (k : ℕ) (U : Finset (Fin N)) (s : DSt), (∀ x, s.pid x ≤ N) →
      ∀ x, (dv sep μ L k U s).pid x ≤ N
  | 0, U, s, h, x => by
    simp only [dv, dLeaf]; split_ifs
    · exact lv_le_N U 0
    · exact h x
  | k + 1, U, s, h, x => by
    simp only [dv]; split_ifs
    · simp only [dLeaf]; split_ifs
      · exact lv_le_N U 0
      · exact h x
    · exact dv_pid_le sep μ L k _ _ (dv_pid_le sep μ L k _ _ (by simpa [dMark] using h)) x

theorem sum_spMu_le (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (W : Finset (Fin N)) :
    ∑ v, spMu H W v ≤ 40 * N * N := by
  have hd : Disjoint W (bdry H W) := disjoint_left.2 fun v hv hb => by
    simp only [bdry, mem_filter, mem_univ, true_and] at hb; exact hb.1 hv
  have e : ∀ v, spMu H W v = (if v ∈ W then 20 * max #(bdry H W) 1 else 0) +
      (if v ∈ bdry H W then 20 * #W else 0) := fun v => by
    simp only [spMu]
    by_cases h1 : v ∈ W
    · rw [iteT h1, iteT h1, iteF (disjoint_left.1 hd h1), Nat.add_zero]
    · rw [iteF h1, iteF h1, Nat.zero_add]
  simp only [e, sum_add_distrib, sum_ite_mem, univ_inter, sum_const, smul_eq_mul]
  have hm := card_le_N W
  have hb := card_le_N (bdry H W)
  rcases Nat.eq_zero_or_pos #W with h0 | h0
  · rw [h0]; omega
  · have : max #(bdry H W) 1 ≤ N := max_le hb (by omega)
    nlinarith

theorem sf_eq_UN {f : ℕ → ℕ} (hf : ∀ x, f x = 0 ∨ f x = 1) {x : ℕ} (hx : x < N) :
    f x = if x ∈ UN (univ.filter fun v : Fin N => f v = 1) then 1 else 0 := by
  have : x ∈ UN (univ.filter fun v : Fin N => f v = 1) ↔ f x = 1 := by
    rw [mem_UN]; simp [hx]
  by_cases h : f x = 1
  · rw [iteT (this.2 h), h]
  · rw [iteF (fun h' => h (this.1 h'))]; exact (hf x).resolve_right h

variable {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]

/-- `SBase` survives a change of the memory outside its arrays and of the weights. -/
theorem SBase.congr' {R : Kasteleyn.RotationSystem G} {w w' : Fin N → ℕ} {Z M : ℕ}
    {c d : Config} (h : SBase G R w Z W M c) (hw : WordsBounded W d)
    (hr : ∀ r, KeptS r → r ≠ 1201 → d.nreg r = c.nreg r)
    (hm : ∀ a, a < Z ∨ (c.nreg 1010 ≤ a ∧ a < c.nreg 1014) ∨
      (c.nreg 1017 ≤ a ∧ a < c.nreg 1019) ∨ (c.nreg 1102 ≤ a ∧ a < c.nreg 1103) ∨
      (c.nreg 1104 ≤ a ∧ a < c.nreg 1010) ∨ (c.nreg 1202 ≤ a ∧ a < c.nreg 1202 + N) →
      d.nmem a = c.nmem a)
    (hwt : ∀ v < N, d.nmem (c.nreg 1014 + v) = SepProg.wI w' v) (hwM : ∑ v, w' v ≤ M)
    (hrr : d.rreg = c.rreg) (hrm : d.rmem = c.rmem) : SBase G R w' Z W M d := by
  have := h.lU; have := h.lC; have := h.lQ; have := h.lW; have := h.lS; have := h.l0
  have := h.l1; have := h.l2; have := h.l3; have := h.l4; have := h.l5; have := h.l6
  have := h.l7; have := h.lA; have := h.lB; have := h.lF; have := h.lV; have := h.lZ
  have K : ∀ r, KeptS r → r ≠ 1201 → d.nreg r = c.nreg r := hr
  have k1001 := K 1001 (by unfold KeptS; omega) (by omega)
  have k1100 := K 1100 (by unfold KeptS; omega) (by omega)
  have k1102 := K 1102 (by unfold KeptS; omega) (by omega)
  have k1103 := K 1103 (by unfold KeptS; omega) (by omega)
  have k1104 := K 1104 (by unfold KeptS; omega) (by omega)
  have k1105 := K 1105 (by unfold KeptS; omega) (by omega)
  have k1010 := K 1010 (by unfold KeptS; omega) (by omega)
  have k1011 := K 1011 (by unfold KeptS; omega) (by omega)
  have k1012 := K 1012 (by unfold KeptS; omega) (by omega)
  have k1013 := K 1013 (by unfold KeptS; omega) (by omega)
  have k1014 := K 1014 (by unfold KeptS; omega) (by omega)
  have k1015 := K 1015 (by unfold KeptS; omega) (by omega)
  have k1017 := K 1017 (by unfold KeptS; omega) (by omega)
  have k1018 := K 1018 (by unfold KeptS; omega) (by omega)
  have k1019 := K 1019 (by unfold KeptS; omega) (by omega)
  have k1200 := K 1200 (by unfold KeptS; omega) (by omega)
  have k1202 := K 1202 (by unfold KeptS; omega) (by omega)
  have k1203 := K 1203 (by unfold KeptS; omega) (by omega)
  have k1204 := K 1204 (by unfold KeptS; omega) (by omega)
  refine ⟨hw, by rw [k1001]; exact h.one, (by rw [K 0 (by unfold KeptS; omega) (by omega)]; exact h.r0),
    by rw [k1100, k1102]; exact h.lU, by rw [k1102, k1103]; exact h.lC,
    by rw [k1103, k1104]; exact h.lQ, by rw [k1104, k1105]; exact h.lW,
    by rw [k1105, k1010]; exact h.lS, by rw [k1010, k1011]; exact h.l0,
    by rw [k1011, k1012]; exact h.l1, by rw [k1012, k1013]; exact h.l2,
    by rw [k1013, k1014]; exact h.l3, by rw [k1014, k1015]; exact h.l4,
    by rw [k1015, k1017]; exact h.l5, by rw [k1017, k1018]; exact h.l6,
    by rw [k1018, k1019]; exact h.l7, by rw [k1019, k1200]; exact h.lA,
    by rw [k1200, k1202]; exact h.lB, by rw [k1202, k1203]; exact h.lF,
    by rw [k1203]; exact h.lV, fun v hv => ?_, fun g hg => ?_, fun g hg => ?_, fun v hv => ?_,
    fun x hx => ?_, fun j hj => ?_, fun j hj => ?_, fun g hg => ?_, fun x hx => ?_,
    fun g hg => ?_, by rw [k1100]; exact h.lZ,
    fun a ha => by rw [hm a (Or.inl ha)]; exact h.zero a ha,
    fun r hr => by rw [K r (by unfold KeptS; omega) (by omega)]; exact h.zreg r hr,
    fun r hr => by rw [hrr]; exact h.rz r hr, fun a ha => by rw [hrm]; exact h.rmz a ha,
    by rw [k1204]; exact h.nN, fun x hx => ?_, h.sw, h.big, hwM⟩
  · rw [k1010, hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact h.ofs v hv
  · rw [k1011, hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact h.tl g hg
  · rw [k1012, hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact h.rv g hg
  · rw [k1014]; exact hwt v hv
  · rw [k1102, hm _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]; exact h.cid x hx
  · rw [k1104, hm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))]
    exact h.cw j hj
  · rw [k1105, hm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))]
    exact h.sn j hj
  · rw [k1013, hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact h.ro g hg
  · rw [k1017, hm _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h.lab x hx
  · rw [k1018, hm _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h.rk g hg
  · rw [k1202, hm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))]
    exact h.fz x hx

end Piece

end PlanarSeparator
