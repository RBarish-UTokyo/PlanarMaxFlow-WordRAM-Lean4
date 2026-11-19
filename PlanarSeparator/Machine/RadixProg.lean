module

public import PlanarSeparator.Machine.RadixSort

/-!
# The radix sort on the machine

A stable counting sort pass `csPass` (keys `x / q mod β`, counts at `nreg 1264`, input at
`nreg 1262`, output at `nreg 1263`, `k = nreg 1261` items, `β = nreg 1260`), in
`24 k + 12 β + 13` steps, leaving the counts zero (`csPass_exec`).

Registers: `1260` `β`, `1261` `k`, `1262` input, `1263` output, `1264` counts, `1265` counter,
`1266` item, `1267` key, `1268`, `1271` addresses, `1269` scratch, `1270` running sum,
`1272` `q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

def csCntBody : Stmt := block [.addN 1268 1262 1265, .loadN 1266 1268, .divN 1267 1266 1272,
  .modN 1267 1267 1260, .addN 1268 1264 1267, .loadN 1269 1268, .addN 1269 1269 1001,
  .storeN 1268 1269, .addN 1265 1265 1001]

def csPreBody : Stmt := block [.addN 1268 1264 1265, .loadN 1269 1268, .storeN 1268 1270,
  .addN 1270 1270 1269, .addN 1265 1265 1001]

def csPlaBody : Stmt := block [.addN 1268 1262 1265, .loadN 1266 1268, .divN 1267 1266 1272,
  .modN 1267 1267 1260, .addN 1268 1264 1267, .loadN 1269 1268, .addN 1271 1263 1269,
  .storeN 1271 1266, .addN 1269 1269 1001, .storeN 1268 1269, .addN 1265 1265 1001]

def csClrBody : Stmt := block [.addN 1268 1264 1265, .storeN 1268 0, .addN 1265 1265 1001]

/-- **A stable counting sort pass.** -/
def csPass : Stmt := .seq (block [.constN 1265 0]) (.seq (.whileLtN 1265 1261 csCntBody)
  (.seq (.seq (block [.constN 1265 0]) (block [.constN 1270 0])) (.seq (.whileLtN 1265 1260 csPreBody)
    (.seq (block [.constN 1265 0]) (.seq (.whileLtN 1265 1261 csPlaBody)
      (.seq (block [.constN 1265 0]) (.whileLtN 1265 1260 csClrBody)))))))

/-- The registers written by the pass. -/
def csW (r : ℕ) : Prop := 1265 ≤ r ∧ r ≤ 1271

section pass

variable {β k aIn aOut aCnt q : ℕ} {L : List ℕ}

/-- The fixed data of a pass. -/
structure CsL (β k aIn aOut aCnt q : ℕ) (L : List ℕ) (W : ℕ) (d : Config) : Prop where
  one : d.nreg 1001 = 1
  r0 : d.nreg 0 = 0
  rb : d.nreg 1260 = β
  rk : d.nreg 1261 = k
  rIn : d.nreg 1262 = aIn
  rOut : d.nreg 1263 = aOut
  rCnt : d.nreg 1264 = aCnt
  rq : d.nreg 1272 = q
  len : L.length = k
  inp : ∀ i < k, d.nmem (aIn + i) = L.getD i 0
  hβ : 0 < β
  nd : L.Nodup
  hLW : ∀ x ∈ L, x ≤ W
  d1 : aIn + k ≤ aCnt ∨ aCnt + β ≤ aIn
  d2 : aOut + k ≤ aCnt ∨ aCnt + β ≤ aOut
  d3 : aIn + k ≤ aOut ∨ aOut + k ≤ aIn
  wIn : aIn + k ≤ W
  wOut : aOut + k ≤ W
  wCnt : aCnt + β ≤ W

theorem CsL.congr {d d' : Config} (h : CsL β k aIn aOut aCnt q L W d)
    (hr : ∀ r, ¬ csW r → d'.nreg r = d.nreg r)
    (hm : ∀ i < k, d'.nmem (aIn + i) = d.nmem (aIn + i)) : CsL β k aIn aOut aCnt q L W d' :=
  { h with
    one := by rw [hr _ (by unfold csW; omega)]; exact h.one
    r0 := by rw [hr _ (by unfold csW; omega)]; exact h.r0
    rb := by rw [hr _ (by unfold csW; omega)]; exact h.rb
    rk := by rw [hr _ (by unfold csW; omega)]; exact h.rk
    rIn := by rw [hr _ (by unfold csW; omega)]; exact h.rIn
    rOut := by rw [hr _ (by unfold csW; omega)]; exact h.rOut
    rCnt := by rw [hr _ (by unfold csW; omega)]; exact h.rCnt
    rq := by rw [hr _ (by unfold csW; omega)]; exact h.rq
    inp := fun i hi => by rw [hm i hi]; exact h.inp i hi }

theorem getD_mem_W {L : List ℕ} (hLW : ∀ x ∈ L, x ≤ W) (i : ℕ) : L.getD i 0 ≤ W := by
  rw [List.getD_eq_getElem?_getD]
  rcases e : L[i]? with _ | x
  · simp
  · simpa using hLW x (List.mem_of_getElem? e)

theorem length_csBlk_take_le (κ : ℕ → ℕ) (L : List ℕ) (i t : ℕ) :
    (csBlk κ (L.take i) t).length ≤ i := by
  unfold csBlk
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The key of the `i`-th item, as computed. -/
theorem key_lt {x : ℕ} (hβ : 0 < β) : x / q % β < β := Nat.mod_lt _ hβ

set_option maxHeartbeats 1000000 in
theorem csCnt_loop {d : Config} (hw : WordsBounded W d) (hL : CsL β k aIn aOut aCnt q L W d)
    (h65 : d.nreg 1265 = 0) (hz : ∀ t < β, d.nmem (aCnt + t) = 0) :
    ∃ d' t, Exec P W (.whileLtN 1265 1261 csCntBody) d d' t ∧ WordsBounded W d' ∧
      (∀ t < β, d'.nmem (aCnt + t) = (csBlk (fun x => x / q % β) L t).length) ∧
      (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, ¬ csW r → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ t ≤ 11 * k + 2 := by
  set κ : ℕ → ℕ := fun x => x / q % β with hκ
  let I : ℕ → Config → Prop := fun i c => WordsBounded W c ∧ c.nreg 1265 = i ∧
    c.nreg 1261 = k ∧
    (∀ t < β, c.nmem (aCnt + t) = (csBlk κ (L.take i) t).length) ∧
    (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, ¬ csW r → c.nreg r = d.nreg r) ∧
    c.output = d.output ∧ c.rreg = d.rreg ∧ c.rmem = d.rmem
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1265) (rN := 1261)
    (N := k) (lo := 0) (B := 9) (body := csCntBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c hI hi => by
      obtain ⟨hw', g65, g61, gC, gm, gq, go, gr, grm⟩ := hI
      have hl := hL.congr gq (fun j hj => gm _ (by have := hL.d1; omega))
      have hx := hl.inp i hi
      have hxW := getD_mem_W hL.hLW i
      have hkey := key_lt (x := L.getD i 0) (q := q) hL.hβ
      have hcnt : c.nmem (aCnt + L.getD i 0 / q % β) =
          (csBlk κ (L.take i) (L.getD i 0 / q % β)).length := gC _ hkey
      have hcle := length_csBlk_take_le κ L i (L.getD i 0 / q % β)
      have hwk := hL.wIn; have hwc := hL.wCnt
      have hLk := hL.len
      have hkW : k ≤ W := by omega
      have r62 := hl.rIn; have r64 := hl.rCnt; have r72 := hl.rq; have r60 := hl.rb
      have r01 := hl.one
      unfold csCntBody
      exec_block
      rotate_right
      · refine ⟨⟨‹_›, by config_simp; rw [g65, r01], by config_simp; exact g61,
          fun t ht => ?_, fun a ha => ?_, fun r hr => ?_, by config_simp; exact go,
          by config_simp; exact gr, by config_simp; exact grm⟩, by omega⟩
        · config_simp
          rw [upd_apply, r64, r62, g65, hx, r72, r60]
          rw [csBlk_take_succ κ L i t (by omega), List.length_append]
          rw [List.getD_eq_getElem _ _ (by omega)] at hcnt ⊢
          split_ifs with e1 e2 e2
          · have ht' : L[i] / q % β = t := by omega
            rw [ht'] at hcnt ⊢; rw [hcnt, r01]; rfl
          · exfalso; apply e2; simp only [hκ]; omega
          · exfalso; apply e1; simp only [hκ] at e2; omega
          · simp only [List.length_nil, Nat.add_zero]; exact gC t ht
        · config_simp
          rw [upd_apply, r64, r62, g65, hx, r72, r60]
          split_ifs with e
          · exfalso; rcases ha with ha | ha <;> omega
          · exact gm a ha
        · unfold csW at hr
          simp only [Config.nreg_mk, upd_apply,
            show r ≠ 1265 by omega, show r ≠ 1266 by omega, show r ≠ 1267 by omega,
            show r ≠ 1268 by omega, show r ≠ 1269 by omega, ite_false]
          exact gq r (by unfold csW; omega)
      all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
        [g65, r62, r64, r72, r60, r01, hx] <;> omega)
      )
    (Nat.zero_le _) ⟨hw, h65, hL.rk, fun t ht => by simp [csBlk, hz t ht], fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨hw₁, -, -, hC₁, hm₁, hq₁, ho₁, hr₁, hrm₁⟩ := h₁
  refine ⟨d₁, k₁, e₁, hw₁, fun t ht => ?_, hm₁, hq₁, ho₁, hr₁, hrm₁, by omega⟩
  rw [hC₁ t ht, ← hL.len, List.take_length]

theorem csS_le_k {d : Config} (hL : CsL β k aIn aOut aCnt q L W d) (t : ℕ) (ht : t ≤ β) :
    (csS (fun x => x / q % β) L t).length ≤ k := by
  have := csS_mono (fun x => x / q % β) L ht
  rw [length_csS _ L hL.nd (fun x _ => key_lt hL.hβ), hL.len] at this
  exact this

set_option maxHeartbeats 1000000 in
theorem csPre_loop {d : Config} (hw : WordsBounded W d) (hL : CsL β k aIn aOut aCnt q L W d)
    (h65 : d.nreg 1265 = 0) (h70 : d.nreg 1270 = 0)
    (hC : ∀ t < β, d.nmem (aCnt + t) = (csBlk (fun x => x / q % β) L t).length) :
    ∃ d' t, Exec P W (.whileLtN 1265 1260 csPreBody) d d' t ∧ WordsBounded W d' ∧
      (∀ t < β, d'.nmem (aCnt + t) = (csS (fun x => x / q % β) L t).length) ∧
      (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, ¬ csW r → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ t ≤ 7 * β + 2 := by
  set κ : ℕ → ℕ := fun x => x / q % β with hκ
  let I : ℕ → Config → Prop := fun t c => WordsBounded W c ∧ c.nreg 1265 = t ∧
    c.nreg 1260 = β ∧ c.nreg 1270 = (csS κ L t).length ∧
    (∀ t' < t, c.nmem (aCnt + t') = (csS κ L t').length) ∧
    (∀ t', t ≤ t' → t' < β → c.nmem (aCnt + t') = (csBlk κ L t').length) ∧
    (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, ¬ csW r → c.nreg r = d.nreg r) ∧
    c.output = d.output ∧ c.rreg = d.rreg ∧ c.rmem = d.rmem
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1265) (rN := 1260)
    (N := β) (lo := 0) (B := 5) (body := csPreBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun t c hI ht => by
      obtain ⟨hw', g65, g60, g70, gA, gB, gm, gq, go, gr, grm⟩ := hI
      have hl := hL.congr gq (fun j hj => gm _ (by have := hL.d1; omega))
      have r64 := hl.rCnt; have r01 := hl.one
      have hct := gB t le_rfl ht
      have hS := csS_succ κ L t
      have hk1 := csS_le_k hL (t + 1) ht
      have hwc := hL.wCnt
      have hkW : k ≤ W := by have := hL.wIn; omega
      rw [hS, List.length_append] at hk1
      unfold csPreBody
      exec_block
      rotate_right
      · refine ⟨⟨‹_›, by config_simp; rw [g65, r01], by config_simp; exact g60, ?_,
          fun t' ht' => ?_, fun t' h1 h2 => ?_, fun a ha => ?_, fun r hr => ?_,
          by config_simp; exact go, by config_simp; exact gr, by config_simp; exact grm⟩,
          by omega⟩
        · config_simp; rw [g70, r64, g65, hct, hS, List.length_append]
        · config_simp
          rw [upd_apply, r64, g65]
          split_ifs with e
          · have : t' = t := by omega
            subst this; exact g70
          · exact gA t' (by omega)
        · config_simp
          rw [upd_apply, r64, g65]
          split_ifs with e
          · omega
          · exact gB t' (by omega) h2
        · config_simp
          rw [upd_apply, r64, g65]
          split_ifs with e
          · rcases ha with ha | ha <;> omega
          · exact gm a ha
        · unfold csW at hr
          simp only [Config.nreg_mk, upd_apply, show r ≠ 1265 by omega,
            show r ≠ 1268 by omega, show r ≠ 1269 by omega, show r ≠ 1270 by omega, ite_false]
          exact gq r (by unfold csW; omega)
      all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
        [g65, r64, r01, g70, hct] <;> omega))
    (Nat.zero_le _) ⟨hw, h65, hL.rb, by rw [h70]; rfl, fun t' ht' => by omega,
      fun t' _ h2 => hC t' h2, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨hw₁, -, -, -, hA₁, -, hm₁, hq₁, ho₁, hr₁, hrm₁⟩ := h₁
  exact ⟨d₁, k₁, e₁, hw₁, hA₁, hm₁, hq₁, ho₁, hr₁, hrm₁, by omega⟩

theorem csBlk_take_last (κ : ℕ → ℕ) (L : List ℕ) {i : ℕ} (hi : i < L.length) :
    (csBlk κ L (κ L[i])).getD (csBlk κ (L.take i) (κ L[i])).length 0 = L[i] := by
  have hp := csBlk_take_prefix κ L (i + 1) (κ L[i])
  rw [csBlk_take_succ κ L i _ hi, if_pos rfl] at hp
  obtain ⟨r, hr⟩ := hp
  rw [← hr, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

set_option maxHeartbeats 2000000 in
theorem csPla_loop {d : Config} (hw : WordsBounded W d) (hL : CsL β k aIn aOut aCnt q L W d)
    (h65 : d.nreg 1265 = 0)
    (hC : ∀ t < β, d.nmem (aCnt + t) = (csS (fun x => x / q % β) L t).length) :
    ∃ d' t, Exec P W (.whileLtN 1265 1261 csPlaBody) d d' t ∧ WordsBounded W d' ∧
      (∀ p < k, d'.nmem (aOut + p) = (csS (fun x => x / q % β) L β).getD p 0) ∧
      (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → (a < aOut ∨ aOut + k ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, ¬ csW r → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ t ≤ 13 * k + 2 := by
  set κ : ℕ → ℕ := fun x => x / q % β with hκ
  let I : ℕ → Config → Prop := fun i c => WordsBounded W c ∧ c.nreg 1265 = i ∧
    c.nreg 1261 = k ∧
    (∀ t < β, c.nmem (aCnt + t) = (csS κ L t).length + (csBlk κ (L.take i) t).length) ∧
    (∀ t < β, ∀ j < (csBlk κ (L.take i) t).length,
      c.nmem (aOut + ((csS κ L t).length + j)) = (csBlk κ L t).getD j 0) ∧
    (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → (a < aOut ∨ aOut + k ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, ¬ csW r → c.nreg r = d.nreg r) ∧
    c.output = d.output ∧ c.rreg = d.rreg ∧ c.rmem = d.rmem
  have hLk := hL.len
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1265) (rN := 1261)
    (N := k) (lo := 0) (B := 11) (body := csPlaBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c hI hi => by
      obtain ⟨hw', g65, g61, gC, gO, gm, gq, go, gr, grm⟩ := hI
      have hiL : i < L.length := by omega
      have hl := hL.congr gq (fun j hj => gm _ (by have := hL.d1; omega)
        (by have := hL.d3; omega))
      have hx := hl.inp i hi
      rw [List.getD_eq_getElem _ _ hiL] at hx
      have hxW := getD_mem_W hL.hLW i
      rw [List.getD_eq_getElem _ _ hiL] at hxW
      have hkey : L[i] / q % β < β := key_lt hL.hβ
      have hcnt := gC (L[i] / q % β) hkey
      have hpre := csBlk_take_prefix κ L (i + 1) (L[i] / q % β)
      rw [csBlk_take_succ κ L i _ hiL] at hpre
      have hκi : κ L[i] = L[i] / q % β := rfl
      have hlen1 : (csBlk κ (L.take i) (L[i] / q % β)).length + 1 ≤
          (csBlk κ L (L[i] / q % β)).length := by
        have := hpre.length_le
        simp only [hκi, ↓reduceIte, List.length_append, List.length_singleton] at this
        exact this
      have hend : (csS κ L (L[i] / q % β)).length + (csBlk κ L (L[i] / q % β)).length ≤ k := by
        have := csS_le_k hL (L[i] / q % β + 1) hkey
        rw [csS_succ, List.length_append] at this; exact this
      have hwo := hL.wOut; have hwc := hL.wCnt
      have hd2 := hL.d2
      have r62 := hl.rIn; have r63 := hl.rOut; have r64 := hl.rCnt; have r72 := hl.rq
      have r60 := hl.rb; have r01 := hl.one
      have hlast := csBlk_take_last κ L hiL
      rw [hκi] at hlast
      set p := (csS κ L (L[i] / q % β)).length + (csBlk κ (L.take i) (L[i] / q % β)).length
        with hp
      have hpk : p + 1 ≤ k := by omega
      have hkW : k ≤ W := by have := hL.wIn; omega
      have hwi := hL.wIn
      obtain ⟨c₁, k₁, e₁, hk₁, hw₁, f65, fmem, fq, fo, fr, frm⟩ : ∃ c₁ k₁,
          Exec P W csPlaBody c c₁ k₁ ∧ k₁ = 11 ∧ WordsBounded W c₁ ∧ c₁.nreg 1265 = i + 1 ∧
          (∀ a, c₁.nmem a = if a = aCnt + L[i] / q % β then p + 1 else
            if a = aOut + p then L[i] else c.nmem a) ∧
          (∀ r, ¬ csW r → c₁.nreg r = c.nreg r) ∧
          c₁.output = c.output ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
        unfold csPlaBody
        exec_block
        rotate_right
        · refine ⟨rfl, ‹_›, by config_simp; rw [g65, r01], fun a => ?_, fun r hr => ?_, rfl,
            rfl, rfl⟩
          · config_simp
            simp only [upd_apply, g65, r62, r63, r64, r72, r60, r01, hx, hcnt]
          · unfold csW at hr
            simp only [Config.nreg_mk, upd_apply,
              show r ≠ 1265 by omega, show r ≠ 1266 by omega, show r ≠ 1267 by omega,
              show r ≠ 1268 by omega, show r ≠ 1269 by omega, show r ≠ 1271 by omega, ite_false]
        all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
          [g65, r62, r63, r64, r72, r60, r01, hx, hcnt] <;> omega)
      refine ⟨c₁, k₁, e₁, ⟨hw₁, f65, by rw [fq 1261 (by unfold csW; omega), g61],
        fun t ht => ?_, fun t ht j hj => ?_, fun a h1 h2 => ?_,
        fun r hr => by rw [fq r hr, gq r hr], by rw [fo, go], by rw [fr, gr], by rw [frm, grm]⟩,
        by omega⟩
      · rw [fmem, csBlk_take_succ κ L i t hiL, List.length_append]
        by_cases et : t = L[i] / q % β
        · subst et
          simp only [hκi, ↓reduceIte, List.length_singleton]
          omega
        · have h1 : ¬ (aCnt + t = aCnt + L[i] / q % β) := by omega
          have hS := csS_le_k hL t ht.le
          have h2 : ¬ (aCnt + t = aOut + p) := by omega
          have h3 : ¬ (κ L[i] = t) := by rw [hκi]; exact fun h => et h.symm
          simp only [h1, h2, h3, ↓reduceIte, List.length_nil, Nat.add_zero]
          exact gC t ht
      · rw [csBlk_take_succ κ L i t hiL, List.length_append] at hj
        have hjB : j < (csBlk κ L t).length := by
          have := (csBlk_take_prefix κ L (i + 1) t).length_le
          rw [csBlk_take_succ κ L i t hiL, List.length_append] at this
          omega
        have hS := csS_le_k hL t ht.le
        have hS1 : (csS κ L t).length + (csBlk κ L t).length ≤ k := by
          have := csS_le_k hL (t + 1) ht
          rw [csS_succ, List.length_append] at this; exact this
        have h1 : ¬ (aOut + ((csS κ L t).length + j) = aCnt + L[i] / q % β) := by omega
        rw [fmem]
        simp only [h1, ↓reduceIte]
        by_cases et : t = L[i] / q % β
        · subst et
          simp only [hκi, ↓reduceIte, List.length_singleton] at hj
          by_cases ej : j = (csBlk κ (L.take i) (L[i] / q % β)).length
          · subst ej
            have h2 : aOut + ((csS κ L (L[i] / q % β)).length +
                (csBlk κ (L.take i) (L[i] / q % β)).length) = aOut + p := by rw [hp]
            simp only [h2, ↓reduceIte]
            exact hlast.symm
          · have h2 : ¬ (aOut + ((csS κ L (L[i] / q % β)).length + j) = aOut + p) := by omega
            simp only [h2, ↓reduceIte]
            exact gO _ ht j (by omega)
        · have h3 : ¬ (κ L[i] = t) := by rw [hκi]; exact fun h => et h.symm
          simp only [h3, ↓reduceIte, List.length_nil, Nat.add_zero] at hj
          have h2 : ¬ (aOut + ((csS κ L t).length + j) = aOut + p) := by
            rcases Nat.lt_or_gt_of_ne et with h' | h'
            · have := csS_start_lt κ L h'; omega
            · have := csS_start_lt κ L h'; omega
          simp only [h2, ↓reduceIte]
          exact gO t ht j hj
      · rw [fmem]
        have e1 : ¬ (a = aCnt + L[i] / q % β) := by rcases h1 with h1 | h1 <;> omega
        have e2 : ¬ (a = aOut + p) := by rcases h2 with h2 | h2 <;> omega
        simp only [e1, e2, ↓reduceIte]
        exact gm a h1 h2)
    (Nat.zero_le _) ⟨hw, h65, hL.rk, fun t ht => by simp [csBlk, hC t ht],
      fun t _ j hj => by simp [csBlk] at hj, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨hw₁, -, -, -, hO₁, hm₁, hq₁, ho₁, hr₁, hrm₁⟩ := h₁
  refine ⟨d₁, k₁, e₁, hw₁, fun p hp => ?_, hm₁, hq₁, ho₁, hr₁, hrm₁, by omega⟩
  have hlenS := length_csS κ L hL.nd (fun x _ => key_lt hL.hβ) (β := β)
  refine csS_value κ L (f := fun p => d₁.nmem (aOut + p)) (by rw [hlenS]; omega) ?_
  intro t ht j hj
  rw [← hL.len, List.take_length] at hO₁
  exact hO₁ t ht j hj

theorem csClr_loop {d : Config} (hw : WordsBounded W d) (hL : CsL β k aIn aOut aCnt q L W d)
    (h65 : d.nreg 1265 = 0) :
    ∃ d' t, Exec P W (.whileLtN 1265 1260 csClrBody) d d' t ∧ WordsBounded W d' ∧
      (∀ t < β, d'.nmem (aCnt + t) = 0) ∧
      (∀ a, (a < aCnt ∨ aCnt + β ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, ¬ csW r → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ t ≤ 5 * β + 2 := by
  let I : ℕ → Config → Prop := fun t c => WordsBounded W c ∧ c.nreg 1265 = t ∧
    c.nreg 1260 = β ∧ (∀ t' < t, c.nmem (aCnt + t') = 0) ∧
    (∀ a, (a < aCnt ∨ aCnt + t ≤ a) → c.nmem a = d.nmem a) ∧
    (∀ r, ¬ csW r → c.nreg r = d.nreg r) ∧
    c.output = d.output ∧ c.rreg = d.rreg ∧ c.rmem = d.rmem
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1265) (rN := 1260)
    (N := β) (lo := 0) (B := 3) (body := csClrBody) I (fun i c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun t c hI ht => by
      obtain ⟨hw', g65, g60, gZ, gm, gq, go, gr, grm⟩ := hI
      have hl := hL.congr gq (fun j hj => gm _ (by have := hL.d1; omega))
      have r64 := hl.rCnt; have r01 := hl.one; have r0 := hl.r0
      have hwc := hL.wCnt
      unfold csClrBody
      exec_block
      rotate_right
      · refine ⟨⟨‹_›, by config_simp; rw [g65, r01], by config_simp; exact g60,
          fun t' ht' => ?_, fun a ha => ?_, fun r hr => ?_,
          by config_simp; exact go, by config_simp; exact gr, by config_simp; exact grm⟩,
          by omega⟩
        · config_simp
          rw [upd_apply, r64, g65, r0]
          split_ifs with e
          · rfl
          · exact gZ t' (by omega)
        · config_simp
          rw [upd_apply, r64, g65, r0]
          split_ifs with e
          · omega
          · exact gm a (by omega)
        · unfold csW at hr
          simp only [Config.nreg_mk, upd_apply, show r ≠ 1265 by omega,
            show r ≠ 1268 by omega, ite_false]
          exact gq r (by unfold csW; omega)
      all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
        [g65, r64, r01] <;> omega))
    (Nat.zero_le _) ⟨hw, h65, hL.rb, fun t' ht' => by omega, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨hw₁, -, -, hZ₁, hm₁, hq₁, ho₁, hr₁, hrm₁⟩ := h₁
  exact ⟨d₁, k₁, e₁, hw₁, hZ₁, fun a ha => hm₁ a (by omega), hq₁, ho₁, hr₁, hrm₁, by omega⟩

theorem cs_reset {d : Config} (hw : WordsBounded W d) (r : ℕ) (hr : csW r) :
    ∃ d' t, Exec P W (block [.constN r 0]) d d' t ∧ t = 1 ∧ WordsBounded W d' ∧
      d'.nreg r = 0 ∧ (∀ r', r' ≠ r → d'.nreg r' = d.nreg r') ∧ d'.nmem = d.nmem ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  exec_block
  rotate_right
  · exact ⟨rfl, ‹_›, by config_simp, fun r' h => by simp [upd_apply, h], rfl, rfl, rfl, rfl⟩
  · omega

set_option maxHeartbeats 1000000 in
/-- **A stable counting sort pass**: the output `csS (x / q mod β) L β`, the counts zero again,
within `24 k + 12 β + 13` steps. -/
theorem csPass_exec {d : Config} (hw : WordsBounded W d) (hL : CsL β k aIn aOut aCnt q L W d)
    (hz : ∀ t < β, d.nmem (aCnt + t) = 0) :
    ∃ d' t, Exec P W csPass d d' t ∧ WordsBounded W d' ∧
      (∀ p < k, d'.nmem (aOut + p) = (csS (fun x => x / q % β) L β).getD p 0) ∧
      (∀ a, (a < aOut ∨ aOut + k ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, ¬ csW r → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      t ≤ 24 * k + 12 * β + 13 := by
  have hd2 := hL.d2
  obtain ⟨c₀, k₀, e₀, hk₀, hw₀, a65, aq, am, ao, ar, arm⟩ := cs_reset (P := P) hw 1265
    (by unfold csW; omega)
  have hl₀ := hL.congr (fun r hr => aq r (by unfold csW at hr; omega)) (fun _ _ => by rw [am])
  obtain ⟨c₁, k₁, e₁, hw₁, hC₁, m₁, q₁, o₁, r₁, rm₁, hk₁⟩ := csCnt_loop (P := P) hw₀ hl₀ a65
    (fun t ht => by rw [am]; exact hz t ht)
  have hl₁ := hl₀.congr q₁ (fun j hj => m₁ _ (by have := hL.d1; omega))
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, b65, bq, bm, bo, br, brm⟩ := cs_reset (P := P) hw₁ 1265
    (by unfold csW; omega)
  obtain ⟨c₃, k₃, e₃, hk₃, hw₃, b70, bq', bm', bo', br', brm'⟩ := cs_reset (P := P) hw₂ 1270
    (by unfold csW; omega)
  have hl₃ := (hl₁.congr (fun r hr => bq r (by unfold csW at hr; omega))
    (fun _ _ => by rw [bm])).congr (fun r hr => bq' r (by unfold csW at hr; omega))
    (fun _ _ => by rw [bm'])
  obtain ⟨c₄, k₄, e₄, hw₄, hC₄, m₄, q₄, o₄, r₄, rm₄, hk₄⟩ := csPre_loop (P := P) hw₃ hl₃
    (by rw [bq' 1265 (by omega)]; exact b65) b70 (fun t ht => by rw [bm', bm]; exact hC₁ t ht)
  have hl₄ := hl₃.congr q₄ (fun j hj => m₄ _ (by have := hL.d1; omega))
  obtain ⟨c₅, k₅, e₅, hk₅, hw₅, d65, dq, dm, do', dr, drm⟩ := cs_reset (P := P) hw₄ 1265
    (by unfold csW; omega)
  have hl₅ := hl₄.congr (fun r hr => dq r (by unfold csW at hr; omega)) (fun _ _ => by rw [dm])
  obtain ⟨c₆, k₆, e₆, hw₆, hO₆, m₆, q₆, o₆, r₆, rm₆, hk₆⟩ := csPla_loop (P := P) hw₅ hl₅ d65
    (fun t ht => by rw [dm]; exact hC₄ t ht)
  have hl₆ := hl₅.congr q₆ (fun j hj => m₆ _ (by have := hL.d1; omega)
    (by have := hL.d3; omega))
  obtain ⟨c₇, k₇, e₇, hk₇, hw₇, f65, fq, fm, fo, fr, frm⟩ := cs_reset (P := P) hw₆ 1265
    (by unfold csW; omega)
  have hl₇ := hl₆.congr (fun r hr => fq r (by unfold csW at hr; omega)) (fun _ _ => by rw [fm])
  obtain ⟨c₈, k₈, e₈, hw₈, hZ₈, m₈, q₈, o₈, r₈, rm₈, hk₈⟩ := csClr_loop (P := P) hw₇ hl₇ f65
  refine ⟨c₈, k₀ + (k₁ + (k₂ + k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈)))))),
    .seq e₀ (.seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    hw₈, fun p hp => ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_, by omega⟩
  · rw [m₈ _ (by omega), fm]; exact hO₆ p hp
  · by_cases hc : aCnt ≤ a ∧ a < aCnt + β
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < β ∧ a = aCnt + t := ⟨a - aCnt, by omega, by omega⟩
      rw [hZ₈ t ht, hz t ht]
    · rw [m₈ a (by omega), fm, m₆ a (by omega) ha, dm, m₄ a (by omega), bm', bm,
        m₁ a (by omega), am]
  · rw [q₈ r hr, fq r (by unfold csW at hr; omega), q₆ r hr, dq r (by unfold csW at hr; omega),
      q₄ r hr, bq' r (by unfold csW at hr; omega), bq r (by unfold csW at hr; omega), q₁ r hr,
      aq r (by unfold csW at hr; omega)]
  · rw [o₈, fo, o₆, do', o₄, bo', bo, o₁, ao]
  · rw [r₈, fr, r₆, dr, r₄, br', br, r₁, ar]
  · rw [rm₈, frm, rm₆, drm, rm₄, brm', brm, rm₁, arm]

end pass

end Piece

end PlanarSeparator
