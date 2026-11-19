module

public import PlanarFlow.BKMNW.NfArcs
public import PlanarFlow.BKMNW.NfSwP

/-!
# The lengths of the explicit arcs of a stage on the machine

The FR input of stage `i` has the `2k` explicit arcs `dartAt a` (`d l` at `a = 2l`, `rev (d l)` at
`a = 2l + 1`) with the lengths `w.lenD P c s.1 s.2` (`SW.lenD_d`, `SW.lenD_rev`):

* `SW.elD`, `SW.elR` (the lengths in words) and **`SW.lenD_words`**;
* program **`elP`** `= elInit ; while (l < k) elBody ; elPatch`: the generic entries
  `EL[2l] = CW[l] + Mb·[i < l] + 2K − FW[l]`, `EL[2l+1] = CR[l] + Mb·[i < l] + FW[l]`, then the two
  entries of `d i` patched from the outputs of `swP` (`9333 = [bv < 0]`, `9341 = |bv| − val0`,
  `9330 = cob + K`, `9337 = f2 + K`); **`elP_exec`** (`≤ 16 k + 30` steps) and **`elP_val`**:
  `EL[a] = lenD (dartAt a) + K` for `a < 2k`.

Registers: `9370` (`l`), `9371` (`k`), `9372` (`i`), `9373` (`Mb`), `9374 … 9377` (bases `CW`,
`CR`, `FW`, `EL`), scratch `9378 … 9387`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The lengths in words -/

namespace SW

variable (w : SW)

/-- The length of the arc of `d l`, in words. -/
def elD (Mb : ℤ) (cw : ℕ → ℤ) (l : ℕ) : ℤ :=
  if ¬ w.bv < 0 ∧ l = w.i then |w.bv| - w.val0 + w.cob
  else (if w.i + 1 ≤ l then cw l + Mb else cw l) - (if l = w.i then w.f2 else w.Fw l)

/-- The length of the arc of `rev (d l)`, in words. -/
def elR (Mb : ℤ) (cr : ℕ → ℤ) (l : ℕ) : ℤ :=
  if w.bv < 0 ∧ l = w.i then |w.bv| - w.val0 - w.cob
  else (if w.i + 1 ≤ l then cr l + Mb else cr l) + (if l = w.i then w.f2 else w.Fw l)

/-- **The lengths of the explicit arcs in words.** -/
theorem lenD_words {P : SPath M} (c : D → ℤ) {f₀ : D → ℤ} {b : ℕ} {β : ℕ → F}
    {idx : F → ℕ} (hw : w.OK P c f₀ b β idx) {s : (D → ℤ) × (F → ℤ)}
    (hs : SRep P f₀ b β s w.Fw w.Pw) {l : ℕ} (hl : l < P.k) :
    w.lenD P c s.1 s.2 (P.d l) =
      w.elD (4 * absSum c + 1) (fun l => c (P.d l)) l ∧
    w.lenD P c s.1 s.2 (M.rev (P.d l)) =
      w.elR (4 * absSum c + 1) (fun l => c (M.rev (P.d l))) l := by
  obtain ⟨hF, hanti, hoff, hph⟩ := hs
  have hi := hw.hi
  have hd := P.d_mem w.i hi
  have hfa : M.face (P.d w.i) ∈ P.faces := P.face_mem hd
  have hfb : M.face (M.rev (P.d w.i)) ∈ P.faces := P.face_mem (P.rev_mem_darts hd)
  have hcob : M.cob s.2 (P.d w.i) = w.cob := by
    simp only [CombMap.cob, SW.cob]
    rw [← hph _ (by rw [hw.ib]; exact hw.idx_lt _ hfb), ← hph _ (by rw [hw.ia]; exact hw.idx_lt _ hfa),
      hw.ia, hw.ib, hw.β_idx _ hfa, hw.β_idx _ hfb]
  rw [w.lenD_d c s.1 s.2 hi hcob hl, w.lenD_rev c s.1 s.2 hanti hi hcob hl, P.cap_d c _ hl,
    P.cap_rev_d c _ hl, hF l hl]
  exact ⟨rfl, rfl⟩

end SW

/-! ### The program -/

/-- `l := 0`, `one := 1`. -/
def elInit : Stmt := block [.constN 9370 0, .constN 9387 1]

/-- The generic entries of the arcs of `d l`, `rev (d l)`. -/
def elBodyA : Stmt :=
  block [.addN 9378 9374 9370, .loadN 9378 9378, .addN 9379 9375 9370, .loadN 9379 9379,
    .addN 9380 9376 9370, .loadN 9380 9380, .constN 9381 0]

/-- The boost: `9381 := Mb` when `i < l`. -/
def elBodyB : Stmt := .ifLtN 9372 9370 (block [.copyN 9381 9373]) .skip

/-- The two stores. -/
def elBodyC : Stmt :=
  block [.addN 9382 9378 9381, .addN 9382 9382 9310, .addN 9382 9382 9310,
    .subN 9382 9382 9380, .addN 9383 9370 9370, .addN 9383 9383 9377, .storeN 9383 9382,
    .addN 9384 9379 9381, .addN 9384 9384 9380, .addN 9383 9383 9387, .storeN 9383 9384,
    .addN 9370 9370 9387]

/-- One step of the loop. -/
def elBody : Stmt := .seq elBodyA (.seq elBodyB elBodyC)

/-- The entries of `d i` when `bv < 0` (`e = d i`): `EL[2i] = CW[i] + 2K − f2'`,
`EL[2i+1] = xv + 2K − cob'`. -/
def elPatchN : Stmt :=
  block [.addN 9385 9374 9372, .loadN 9385 9385, .addN 9385 9385 9310, .addN 9385 9385 9310,
    .subN 9385 9385 9337, .addN 9383 9372 9372, .addN 9383 9383 9377, .storeN 9383 9385,
    .addN 9386 9341 9310, .addN 9386 9386 9310, .subN 9386 9386 9330, .addN 9383 9383 9387,
    .storeN 9383 9386]

/-- The entries of `d i` when `bv ≥ 0` (`e = rev (d i)`): `EL[2i] = xv + cob'`,
`EL[2i+1] = CR[i] + f2'`. -/
def elPatchQ : Stmt :=
  block [.addN 9386 9375 9372, .loadN 9386 9386, .addN 9386 9386 9337, .addN 9385 9341 9330,
    .addN 9383 9372 9372, .addN 9383 9383 9377, .storeN 9383 9385, .addN 9383 9383 9387,
    .storeN 9383 9386]

/-- **The lengths of the explicit arcs of a stage.** -/
def elP : Stmt :=
  .seq elInit (.seq (.whileLtN 9370 9371 elBody) (.ifLtN 9333 9387 elPatchQ elPatchN))

/-! ### The run -/

variable {P : Input} {W : ℕ}

/-- The generic value of the arc of `d l`. -/
def elV1 (K i Mbw : ℕ) (CW FW : ℕ → ℕ) (l : ℕ) : ℕ :=
  CW l + (if i < l then Mbw else 0) + K + K - FW l

/-- The generic value of the arc of `rev (d l)`. -/
def elV2 (i Mbw : ℕ) (CR FW : ℕ → ℕ) (l : ℕ) : ℕ := CR l + (if i < l then Mbw else 0) + FW l

theorem elBody_exec (c : Config) (hc : WordsBounded W c) {K l i Mbw CWb CRb FWb ELb : ℕ}
    (r70 : c.nreg 9370 = l) (r72 : c.nreg 9372 = i) (r73 : c.nreg 9373 = Mbw)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r77 : c.nreg 9377 = ELb) (r10 : c.nreg 9310 = K) (r87 : c.nreg 9387 = 1)
    (hCW : c.nmem (CWb + l) ≤ 2 * K) (hCR : c.nmem (CRb + l) ≤ 2 * K)
    (hFW : c.nmem (FWb + l) ≤ 2 * K) (hMb : Mbw ≤ K) (hW : 8 * K + 1 ≤ W)
    (hEL : ELb + 2 * l + 1 ≤ W) (hA : CWb + l ≤ W ∧ CRb + l ≤ W ∧ FWb + l ≤ W) :
    ∃ c' t, Exec P W elBody c c' t ∧ t ≤ 22 ∧ c'.nreg 9370 = l + 1 ∧
      (∀ a, c'.nmem a = if a = ELb + 2 * l then
        c.nmem (CWb + l) + (if i < l then Mbw else 0) + K + K - c.nmem (FWb + l)
        else if a = ELb + 2 * l + 1 then
          c.nmem (CRb + l) + (if i < l then Mbw else 0) + c.nmem (FWb + l) else c.nmem a) ∧
      (∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨c₁, t₁, e₁, ht₁, a78, a79, a80, a81, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W elBodyA c c₁ t₁ ∧ t₁ = 7 ∧ c₁.nreg 9378 = c.nmem (CWb + l) ∧
      c₁.nreg 9379 = c.nmem (CRb + l) ∧ c₁.nreg 9380 = c.nmem (FWb + l) ∧ c₁.nreg 9381 = 0 ∧
      (∀ r, (r < 9378 ∨ 9381 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold elBodyA
    exec_block
    all_goals try ((try config_simp); (try simp only [r70, r74, r75, r76]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r70, r74, r75, r76])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c₂, t₂, e₂, ht₂, b81, bk, bm, br, brm, bo⟩ : ∃ c₂ t₂,
      Exec P W elBodyB c₁ c₂ t₂ ∧ t₂ ≤ 2 ∧ c₂.nreg 9381 = (if i < l then Mbw else 0) ∧
      (∀ r, r ≠ 9381 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    have q72 : c₁.nreg 9372 = i := by rw [ak _ (by omega), r72]
    have q70 : c₁.nreg 9370 = l := by rw [ak _ (by omega), r70]
    have q73 : c₁.nreg 9373 = Mbw := by rw [ak _ (by omega), r73]
    unfold elBodyB
    by_cases hil : i < l
    · obtain ⟨c₂, t₂, e₂, ht₂, g81, gk, gm, gr, grm, go⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 9381 9373]) c₁ c₂ t₂ ∧ t₂ = 1 ∧ c₂.nreg 9381 = Mbw ∧
          (∀ r, r ≠ 9381 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧
          c₂.output = c₁.output := by
        have hw1 := e₁.wb_right
        exec_block
        refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        · exact q73
        · simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, _, .ifLtN_true (by rw [q72, q70]; exact hil) e₂, by omega, ?_, gk, gm, gr, grm,
        go⟩
      rw [g81]; simp only [hil, ↓reduceIte]
    · refine ⟨c₁, _, .ifLtN_false (by rw [q72, q70]; exact hil) (.skip e₁.wb_right), le_refl _, ?_,
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      rw [a81]; simp only [hil, ↓reduceIte]
  obtain ⟨c₃, t₃, e₃, ht₃, d70, dm, dk, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W elBodyC c₂ c₃ t₃ ∧ t₃ = 12 ∧ c₃.nreg 9370 = l + 1 ∧
      (∀ a, c₃.nmem a = if a = ELb + 2 * l then
        c.nmem (CWb + l) + (if i < l then Mbw else 0) + K + K - c.nmem (FWb + l)
        else if a = ELb + 2 * l + 1 then
          c.nmem (CRb + l) + (if i < l then Mbw else 0) + c.nmem (FWb + l) else c.nmem a) ∧
      (∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 ≤ r) → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have hw2 := e₂.wb_right
    have s78 : c₂.nreg 9378 = c.nmem (CWb + l) := by rw [bk _ (by omega), a78]
    have s79 : c₂.nreg 9379 = c.nmem (CRb + l) := by rw [bk _ (by omega), a79]
    have s80 : c₂.nreg 9380 = c.nmem (FWb + l) := by rw [bk _ (by omega), a80]
    have s70 : c₂.nreg 9370 = l := by rw [bk _ (by omega), ak _ (by omega), r70]
    have s77 : c₂.nreg 9377 = ELb := by rw [bk _ (by omega), ak _ (by omega), r77]
    have s10 : c₂.nreg 9310 = K := by rw [bk _ (by omega), ak _ (by omega), r10]
    have s87 : c₂.nreg 9387 = 1 := by rw [bk _ (by omega), ak _ (by omega), r87]
    have sm : c₂.nmem = c.nmem := by rw [bm, am]
    have hmb : (if i < l then Mbw else 0) ≤ K := by split_ifs <;> omega
    unfold elBodyC
    exec_block
    all_goals try ((try config_simp); (try simp only [s78, s79, s80, s70, s77, s10, s87, b81]); omega)
    refine ⟨rfl, ?_, fun a => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [s78, s79, s80, s70, s77, s10, s87, b81, sm])
    all_goals try (simp only [upd_apply]; split_ifs <;> omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, d70, dm, fun r h1 h2 => ?_, by rw [dr, br, ar],
    by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  rw [dk r h1 h2, bk r (by omega), ak r (by omega)]

theorem elPatchQ_exec (c : Config) (hc : WordsBounded W c) {K i CRb ELb XV COB F2 : ℕ}
    (r72 : c.nreg 9372 = i) (r75 : c.nreg 9375 = CRb) (r77 : c.nreg 9377 = ELb)
    (r87 : c.nreg 9387 = 1) (r41 : c.nreg 9341 = XV) (r30 : c.nreg 9330 = COB)
    (r37 : c.nreg 9337 = F2) (hb : XV + COB ≤ W ∧ CRb + i ≤ W ∧ c.nmem (CRb + i) + F2 ≤ W ∧
      ELb + 2 * i + 1 ≤ W) :
    ∃ c' t, Exec P W elPatchQ c c' t ∧ t = 9 ∧
      (∀ a, c'.nmem a = if a = ELb + 2 * i then XV + COB
        else if a = ELb + 2 * i + 1 then c.nmem (CRb + i) + F2 else c.nmem a) ∧
      (∀ r, (r < 9378 ∨ 9387 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  unfold elPatchQ
  exec_block
  all_goals try ((try config_simp); (try simp only [r72, r75, r77, r87, r41, r30, r37]); omega)
  refine ⟨rfl, fun a => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r72, r75, r77, r87, r41, r30, r37])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem elPatchN_exec (c : Config) (hc : WordsBounded W c) {K i CWb ELb XV COB F2 : ℕ}
    (r72 : c.nreg 9372 = i) (r74 : c.nreg 9374 = CWb) (r77 : c.nreg 9377 = ELb)
    (r87 : c.nreg 9387 = 1) (r10 : c.nreg 9310 = K) (r41 : c.nreg 9341 = XV)
    (r30 : c.nreg 9330 = COB) (r37 : c.nreg 9337 = F2)
    (hb : c.nmem (CWb + i) + K + K ≤ W ∧ CWb + i ≤ W ∧ XV + K + K ≤ W ∧ ELb + 2 * i + 1 ≤ W) :
    ∃ c' t, Exec P W elPatchN c c' t ∧ t = 13 ∧
      (∀ a, c'.nmem a = if a = ELb + 2 * i then c.nmem (CWb + i) + K + K - F2
        else if a = ELb + 2 * i + 1 then XV + K + K - COB else c.nmem a) ∧
      (∀ r, (r < 9378 ∨ 9387 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  unfold elPatchN
  exec_block
  all_goals try ((try config_simp); (try simp only [r72, r74, r77, r87, r10, r41, r30, r37]); omega)
  refine ⟨rfl, fun a => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r72, r74, r77, r87, r10, r41, r30, r37])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **The lengths of the explicit arcs of a stage on the machine.** -/
theorem elP_exec (c : Config) (hc : WordsBounded W c)
    {K k i Mbw CWb CRb FWb ELb NG XV COB F2 : ℕ}
    (r71 : c.nreg 9371 = k) (r72 : c.nreg 9372 = i) (r73 : c.nreg 9373 = Mbw)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r77 : c.nreg 9377 = ELb) (r10 : c.nreg 9310 = K) (r33 : c.nreg 9333 = NG)
    (r41 : c.nreg 9341 = XV) (r30 : c.nreg 9330 = COB) (r37 : c.nreg 9337 = F2)
    (hik : i < k) (hNG : NG ≤ 1)
    (hCW : ∀ l < k, c.nmem (CWb + l) ≤ 2 * K) (hCR : ∀ l < k, c.nmem (CRb + l) ≤ 2 * K)
    (hFW : ∀ l < k, c.nmem (FWb + l) ≤ 2 * K) (hMb : Mbw ≤ K) (hXV : XV ≤ 2 * K)
    (hCOB : COB ≤ 3 * K) (hF2 : F2 ≤ 3 * K) (hW : 8 * K + 1 ≤ W)
    (hdis : CWb + k ≤ ELb ∧ CRb + k ≤ ELb ∧ FWb + k ≤ ELb) (hEL : ELb + 2 * k ≤ W) :
    ∃ c' t, Exec P W elP c c' t ∧ t ≤ 24 * k + 20 ∧
      (∀ l < k, c'.nmem (ELb + 2 * l) =
          (if l = i then (if NG < 1 then XV + COB else c.nmem (CWb + i) + K + K - F2)
            else elV1 K i Mbw (fun l => c.nmem (CWb + l)) (fun l => c.nmem (FWb + l)) l) ∧
        c'.nmem (ELb + 2 * l + 1) =
          (if l = i then (if NG < 1 then c.nmem (CRb + i) + F2 else XV + K + K - COB)
            else elV2 i Mbw (fun l => c.nmem (CRb + l)) (fun l => c.nmem (FWb + l)) l)) ∧
      (∀ a, ¬ (ELb ≤ a ∧ a < ELb + 2 * k) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d1, d2, d3⟩ := hdis
  obtain ⟨c₁, t₁, e₁, ht₁, a70, a87, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W elInit c c₁ t₁ ∧ t₁ = 2 ∧ c₁.nreg 9370 = 0 ∧ c₁.nreg 9387 = 1 ∧
      (∀ r, r ≠ 9370 → r ≠ 9387 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold elInit
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ l' < l, c'.nmem (ELb + 2 * l') =
        elV1 K i Mbw (fun l => c.nmem (CWb + l)) (fun l => c.nmem (FWb + l)) l' ∧
      c'.nmem (ELb + 2 * l' + 1) =
        elV2 i Mbw (fun l => c.nmem (CRb + l)) (fun l => c.nmem (FWb + l)) l') ∧
    (∀ a, ¬ (ELb ≤ a ∧ a < ELb + 2 * l) → c'.nmem a = c.nmem a) ∧
    (∀ r, r ≠ 9370 → (r < 9378 ∨ 9387 ≤ r) → c'.nreg r = c₁.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have q : ∀ r, r ≠ 9370 → r ≠ 9387 → (r < 9378 ∨ 9387 ≤ r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 _ => ak r h1 h2
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := NegSSSP.forLoop_exec (P := P) (a := 9370) (bR := 9371)
    (body := elBody) J (K := 22) (n := k) c₁ e₁.wb_right a70
    (by rw [q _ (by omega) (by omega) (by omega), r71])
    ⟨fun l' hl' => absurd hl' (by omega), fun a _ => by rw [am], fun _ _ _ => rfl, ar, arm, ao⟩
    (fun l c' hl hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have s : ∀ r, r ≠ 9370 → r ≠ 9387 → (r < 9378 ∨ 9387 ≤ r) → c'.nreg r = c.nreg r :=
        fun r h1 h2 h3 => by rw [jn r h1 h3, q r h1 h2 h3]
      have mCW : c'.nmem (CWb + l) = c.nmem (CWb + l) := j2 _ (by omega)
      have mCR : c'.nmem (CRb + l) = c.nmem (CRb + l) := j2 _ (by omega)
      have mFW : c'.nmem (FWb + l) = c.nmem (FWb + l) := j2 _ (by omega)
      obtain ⟨c'', t, ex, ht, h70, hm, hk, hr, hrm, ho⟩ :=
        elBody_exec (P := P) c' hw (K := K) (l := l) (i := i) (Mbw := Mbw) (CWb := CWb)
          (CRb := CRb) (FWb := FWb) (ELb := ELb) ha
          (s _ (by omega) (by omega) (by omega) |>.trans r72)
          (s _ (by omega) (by omega) (by omega) |>.trans r73)
          (s _ (by omega) (by omega) (by omega) |>.trans r74)
          (s _ (by omega) (by omega) (by omega) |>.trans r75)
          (s _ (by omega) (by omega) (by omega) |>.trans r76)
          (s _ (by omega) (by omega) (by omega) |>.trans r77)
          (s _ (by omega) (by omega) (by omega) |>.trans r10)
          (by rw [jn _ (by omega) (by omega), a87])
          (by rw [mCW]; exact hCW l hl) (by rw [mCR]; exact hCR l hl)
          (by rw [mFW]; exact hFW l hl) hMb hW (by omega) ⟨by omega, by omega, by omega⟩
      refine ⟨c'', t, ex, ht, h70, by rw [hk _ (by omega) (by omega)]; exact hb,
        fun l' hl' => ?_, fun a ha' => ?_, fun r h1 h2 => (hk r h1 (by omega)).trans (jn r h1 h2),
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | rfl
        · rw [hm, hm]
          simp only [show ELb + 2 * l' ≠ ELb + 2 * l by omega,
            show ELb + 2 * l' ≠ ELb + 2 * l + 1 by omega,
            show ELb + 2 * l' + 1 ≠ ELb + 2 * l by omega,
            show ELb + 2 * l' + 1 ≠ ELb + 2 * l + 1 by omega, ↓reduceIte]
          exact j1 l' h
        · rw [hm, hm, mCW, mCR, mFW]
          simp only [↓reduceIte, show ELb + 2 * l' + 1 ≠ ELb + 2 * l' by omega]
          exact ⟨rfl, rfl⟩
      · rw [hm]
        simp only [show a ≠ ELb + 2 * l by omega, show a ≠ ELb + 2 * l + 1 by omega, ↓reduceIte]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  have s : ∀ r, r ≠ 9370 → r ≠ 9387 → (r < 9378 ∨ 9387 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by rw [jn r h1 h3, q r h1 h2 h3]
  have s87 : c₂.nreg 9387 = 1 := by rw [jn _ (by omega) (by omega), a87]
  have hj2 : ∀ l < k, c₂.nmem (CWb + l) = c.nmem (CWb + l) ∧
      c₂.nmem (CRb + l) = c.nmem (CRb + l) := fun l hl => ⟨j2 _ (by omega), j2 _ (by omega)⟩
  -- the patch
  obtain ⟨c₃, t₃, e₃, ht₃, pm, pk, pr, prm, po⟩ : ∃ c₃ t₃,
      Exec P W (.ifLtN 9333 9387 elPatchQ elPatchN) c₂ c₃ t₃ ∧ t₃ ≤ 15 ∧
      (∀ a, c₃.nmem a = if a = ELb + 2 * i then
          (if NG < 1 then XV + COB else c.nmem (CWb + i) + K + K - F2)
        else if a = ELb + 2 * i + 1 then
          (if NG < 1 then c.nmem (CRb + i) + F2 else XV + K + K - COB) else c₂.nmem a) ∧
      (∀ r, (r < 9378 ∨ 9387 ≤ r) → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    by_cases hng : NG < 1
    · obtain ⟨c₃, t₃, e₃, ht₃, m3, k3, r3, rm3, o3⟩ :=
        elPatchQ_exec (P := P) c₂ hw₂ (K := K) (i := i) (CRb := CRb) (ELb := ELb) (XV := XV)
          (COB := COB) (F2 := F2) (s _ (by omega) (by omega) (by omega) |>.trans r72)
          (s _ (by omega) (by omega) (by omega) |>.trans r75)
          (s _ (by omega) (by omega) (by omega) |>.trans r77) s87
          (s _ (by omega) (by omega) (by omega) |>.trans r41)
          (s _ (by omega) (by omega) (by omega) |>.trans r30)
          (s _ (by omega) (by omega) (by omega) |>.trans r37)
          ⟨by omega, by have := hc.1 9375; have := hc.1 9372; omega,
            by rw [(hj2 i hik).2]; have := hCR i hik; omega, by omega⟩
      refine ⟨c₃, _, .ifLtN_true (by rw [s _ (by omega) (by omega) (by omega), r33, s87]; exact hng)
        e₃, by omega, fun a => ?_, k3, r3, rm3, o3⟩
      rw [m3 a, (hj2 i hik).2]; simp only [hng, ↓reduceIte]
    · obtain ⟨c₃, t₃, e₃, ht₃, m3, k3, r3, rm3, o3⟩ :=
        elPatchN_exec (P := P) c₂ hw₂ (K := K) (i := i) (CWb := CWb) (ELb := ELb) (XV := XV)
          (COB := COB) (F2 := F2) (s _ (by omega) (by omega) (by omega) |>.trans r72)
          (s _ (by omega) (by omega) (by omega) |>.trans r74)
          (s _ (by omega) (by omega) (by omega) |>.trans r77) s87
          (s _ (by omega) (by omega) (by omega) |>.trans r10)
          (s _ (by omega) (by omega) (by omega) |>.trans r41)
          (s _ (by omega) (by omega) (by omega) |>.trans r30)
          (s _ (by omega) (by omega) (by omega) |>.trans r37)
          ⟨by rw [(hj2 i hik).1]; have := hCW i hik; omega,
            by have := hc.1 9374; have := hc.1 9372; omega, by omega, by omega⟩
      refine ⟨c₃, _, .ifLtN_false (by rw [s _ (by omega) (by omega) (by omega), r33, s87]; exact hng)
        e₃, by omega, fun a => ?_, k3, r3, rm3, o3⟩
      rw [m3 a, (hj2 i hik).1]; simp only [hng, ↓reduceIte]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun l hl => ⟨?_, ?_⟩, fun a ha => ?_,
    fun r h1 h2 => ?_, by rw [pr, jr], by rw [prm, jrm], by rw [po, jo]⟩
  · rw [pm]
    by_cases hli : l = i
    · subst hli; simp only [↓reduceIte]
    · simp only [hli, ↓reduceIte, show ELb + 2 * l ≠ ELb + 2 * i by omega,
        show ELb + 2 * l ≠ ELb + 2 * i + 1 by omega]
      exact (j1 l hl).1
  · rw [pm]
    by_cases hli : l = i
    · subst hli; simp only [↓reduceIte, show ELb + 2 * l + 1 ≠ ELb + 2 * l by omega]
    · simp only [hli, ↓reduceIte, show ELb + 2 * l + 1 ≠ ELb + 2 * i by omega,
        show ELb + 2 * l + 1 ≠ ELb + 2 * i + 1 by omega]
      exact (j1 l hl).2
  · rw [pm]
    simp only [show a ≠ ELb + 2 * i by omega, show a ≠ ELb + 2 * i + 1 by omega, ↓reduceIte]
    exact j2 a ha
  · rw [pk r (by omega), s r h1 (by omega) (by omega)]

/-- **The words written by `elP` are the lengths of the explicit arcs** (with the offset `K`). -/
theorem elP_val (w : SW) {K Mbw NG XV COB F2 : ℕ} {Mb : ℤ} {cw cr : ℕ → ℤ}
    {CW CR FW : ℕ → ℕ} {l : ℕ} (hCW : (CW l : ℤ) = cw l) (hCR : (CR l : ℤ) = cr l)
    (hFW : (FW l : ℤ) = w.Fw l + K) (hCWi : (CW w.i : ℤ) = cw w.i) (hCRi : (CR w.i : ℤ) = cr w.i)
    (hMb : (Mbw : ℤ) = Mb) (hNG : NG = if w.bv < 0 then 1 else 0)
    (hXV : (XV : ℤ) = |w.bv| - w.val0) (hCOB : (COB : ℤ) = w.cob + K) (hF2 : (F2 : ℤ) = w.f2 + K)
    (hb1 : w.Fw l ≤ cw l + K) (hb2 : w.f2 ≤ cw w.i + K) (hb3 : w.cob ≤ |w.bv| - w.val0 + K) :
    (((if l = w.i then (if NG < 1 then XV + COB else CW w.i + K + K - F2)
        else elV1 K w.i Mbw CW FW l : ℕ) : ℤ) = w.elD Mb cw l + K) ∧
    (((if l = w.i then (if NG < 1 then CR w.i + F2 else XV + K + K - COB)
        else elV2 w.i Mbw CR FW l : ℕ) : ℤ) = w.elR Mb cr l + K) := by
  have hM0 : (0 : ℤ) ≤ Mb := by rw [← hMb]; positivity
  unfold SW.elD SW.elR elV1 elV2
  by_cases hli : l = w.i
  · subst hli
    by_cases hneg : w.bv < 0
    · have : ¬ NG < 1 := by rw [hNG]; simp [hneg]
      simp only [↓reduceIte, this, hneg, not_true_eq_false, false_and, true_and,
        show ¬ (w.i + 1 ≤ w.i) by omega]
      constructor <;> push_cast [Nat.cast_sub (by omega : F2 ≤ CW w.i + K + K),
        Nat.cast_sub (by omega : COB ≤ XV + K + K)] <;> omega
    · have : NG < 1 := by rw [hNG]; simp [hneg]
      simp only [↓reduceIte, this, hneg, not_false_eq_true, true_and, false_and,
        show ¬ (w.i + 1 ≤ w.i) by omega]
      constructor <;> push_cast <;> omega
  · simp only [hli, ↓reduceIte, false_and, and_false]
    by_cases hil : w.i < l
    · simp only [hil, ↓reduceIte, show w.i + 1 ≤ l by omega]
      constructor <;> push_cast [Nat.cast_sub (by omega : FW l ≤ CW l + Mbw + K + K)] <;> omega
    · simp only [hil, ↓reduceIte, show ¬ (w.i + 1 ≤ l) by omega]
      constructor <;> push_cast [Nat.cast_sub (by omega : FW l ≤ CW l + 0 + K + K)] <;> omega

end BKMNW

end PlanarFlow
