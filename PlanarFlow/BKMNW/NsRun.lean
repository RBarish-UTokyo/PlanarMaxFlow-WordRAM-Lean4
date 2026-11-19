module

public import PlanarFlow.BKMNW.NsRunBC

/-!
# The negSSSP step of a call as one program

* Stage D (`wrProg ; nsZ ; nsF`, **`nsW_exec`**): the input part of the root frame at `A`, the
  scratch arrays cleared, the arguments `r7325 = A`, `r7326 = m` of the call.
* **`nsPrep_exec`**: from the dart order of a map `M` (index arrays `RV`, `RT`, lengths
  `LN = ℓ + K` with `|ℓ| ≤ K`) and a zero scratch region, within `300 m + 200` steps the root
  frame's input part `InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) m (repsN …) A …`
  of the negative-length shortest paths on the dual, the scratch zero again.
* **`negStep_exec`**: `nsPrep ; negCallH` from the zero memory `MemZ Wz`: the outcome
  `negMach (nsIds M h d₀) M I ℓ` in the copy at `Ob`, the memory `≤ Wz` zero again, within
  `300 m + 200 + (9 negT C C₀ m + 12 fsz + 7 fin + 3291 + 12 m + 4628)` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

theorem setZ_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.subN 5030 7519 7505, .copyN 5031 7505]) c c' t ∧ t = 2 ∧
      c'.nreg 5030 = c.nreg 7519 - c.nreg 7505 ∧ c'.nreg 5031 = c.nreg 7505 ∧
      (∀ r, (r < 5030 ∨ 5031 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem nsF_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W nsF c c' t ∧ t = 2 ∧
      c'.nreg 7325 = c.nreg 7506 ∧ c'.nreg 7326 = c.nreg 7500 ∧
      (∀ r, r ≠ 7325 → r ≠ 7326 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nsF
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- Clearing the scratch arrays and setting the arguments of the call (generic). -/
theorem nsZF_exec (c : Config) (hc : WordsBounded W c) {K S : ℕ} (r00 : c.nreg 7500 = m)
    (r05 : c.nreg 7505 = S) (d9 : c.nreg 7519 = S + 9 * m + 1) (w : S + 9 * m + 1 + 1 ≤ W) :
    ∃ c' t, Exec P W (.seq nsZ nsF) c c' t ∧ t ≤ 45 * m + 14 ∧
      (∀ a, S ≤ a → a < S + 9 * m + 1 → c'.nmem a = 0) ∧
      (∀ a, (a < S ∨ S + 9 * m + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7325 = c.nreg 7506 ∧ c'.nreg 7326 = m ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → r ≠ 7325 → r ≠ 7326 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have w1 : S + (9 * m + 1) ≤ W := by omega
  have w2 : 9 * m + 1 + 1 ≤ W := by omega
  unfold nsZ
  obtain ⟨c₁, t₁, e₁, ht₁, z0, z1, zR, zm, zr, zrm, zo⟩ := setZ_exec (P := P) c hc
  have e0 : c₁.nreg 5030 = 9 * m + 1 := by rw [z0, d9, r05]; omega
  obtain ⟨c₂, t₂, e₂, ht₂, f1, f2, fR, fr, frm, fo⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right e0 (by rw [z1, r05]) w1 w2
  obtain ⟨c₃, t₃, e₃, ht₃, g0, g1, gR, gm, gr, grm, go⟩ := nsF_exec (P := P) c₂ e₂.wb_right
  refine ⟨c₃, (t₁ + t₂) + t₃, .seq (.seq e₁ e₂) e₃, by clear * - ht₁ ht₂ ht₃; omega,
    fun a h1 h2 => ?_, fun a ha => ?_, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [gr, fr, zr], by rw [grm, frm, zrm], by rw [go, fo, zo]⟩
  · have := f1 (a - S) (by clear * - h1 h2; omega)
    rw [show S + (a - S) = a by clear * - h1; omega] at this
    rw [gm, this]
  · rw [gm, f2 a (by clear * - ha; omega), zm]
  · rw [g0, fR _ (by decide), zR _ (by decide)]
  · rw [g1, fR _ (by decide), zR _ (by decide), r00]
  · rw [gR r h2 h3, fR r (by clear * - h1; omega), zR r (by clear * - h1; omega)]

/-- **Stage D**: the input part of the root frame, the scratch cleared, the call's arguments. -/
theorem nsW_exec (h : EnumOK M en m) (d₀ : D) (ℓ : D → ℤ) (c : Config) (hc : WordsBounded W c)
    {RVb K S A : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S) (r06 : c.nreg 7506 = A) (hL : LayRegs c m K S)
    (r25 : c.nreg 7525 = rtL M ℓ) (r26 : c.nreg 7526 = (fLi M en m h d₀).length)
    (r27 : c.nreg 7527 = (cLi M en m h d₀).length)
    (hLR : LRep (fLi M en m h d₀) c.nmem (S + 7 * m) (S + 6 * m) m)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hNX : ∀ i < m, en i ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) →
      c.nmem (S + i) < m ∧ en (c.nmem (S + i)) =
        ret (rotPerm M.dual) (rcl M.dual (repsN M.dual (nsIds M h d₀).gd)) (en i))
    (hLAB : ∀ i < m, c.nmem (S + 2 * m + i) = labI M en m i + 1)
    (hMLN : ∀ i < m, (c.nmem (S + 5 * m + i) : ℤ) = minLen M.dual ℓ (en i) + K)
    (hK : ∀ i < m, |ℓ (en i)| ≤ K)
    (sA : S + 9 * m + 1 ≤ A) (sR : S + 9 * m + 1 ≤ RVb)
    (dR : RVb + m ≤ A ∨ A + 6 + 10 * m ≤ RVb) (wR : RVb + m ≤ W) (wA : A + 6 + 10 * m ≤ W)
    (wL : 2 * K + rtL M ℓ ≤ W) :
    ∃ c' t, Exec P W (.seq wrProg (.seq nsZ nsF)) c c' t ∧ t ≤ 90 * m + 40 ∧
      InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
        (repsN M.dual (nsIds M h d₀).gd) A
        (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) c' ∧
      (∀ a, S ≤ a → a < S + 9 * m + 1 → c'.nmem a = 0) ∧
      (∀ a, (a < S ∨ S + 9 * m + 1 ≤ a) → (a < A ∨ A + Frame.fsz
        (repsN M.dual (nsIds M h d₀).gd).card (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.nreg 7325 = A ∧ c'.nreg 7326 = m ∧
      (∀ r, ¬ NsScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set fL := fLi M en m h d₀ with hfL
  set cL := cLi M en m h d₀ with hcL
  have hk : fL.length ≤ m := length_le_of_nodup (fLi_nodup h d₀) fun x hx => fLi_lt h d₀ hx
  have hmk : cL.length ≤ fL.length := by
    rw [hfL, hcL]; unfold fLi; rw [List.length_append]; omega
  have hfsz : Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) = 6 + 5 * fL.length + 5 * cL.length := by
    rw [card_eq h d₀, ck_eq h d₀]; rfl
  have hx : ∀ t < fL.length, c.nmem (S + 7 * m + t) < m ∧
      en (c.nmem (S + 7 * m + t)) ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) := fun t ht => by
    rw [hLR.1 t ht, List.getD_eq_getElem _ _ ht]
    have hm := List.getElem_mem ht
    exact ⟨fLi_lt h d₀ hm, (mem_fLi_iff h d₀ (fLi_lt h d₀ hm)).1 hm⟩
  have hml : ∀ t < cL.length, c.nmem (S + 5 * m + c.nmem (S + 7 * m + t)) + rtL M ℓ ≤ W :=
    fun t ht => by
      have hxm := (hx t (by omega)).1
      have h1 := hMLN _ hxm
      have h2 := minLen_le (N := M.dual) ℓ (d := en (c.nmem (S + 7 * m + t)))
        (x := en (c.nmem (S + 7 * m + t))) rfl rfl
      have h3 := hK _ hxm
      rw [abs_le] at h3
      clear * - h1 h2 h3 wL
      omega
  have w1 : S + 7 * m + fL.length ≤ A := by clear * - hk sA; omega
  have w2 : S + 6 * m + m ≤ A := by clear * - sA; omega
  have w3 : S + m ≤ A := by clear * - sA; omega
  have w4 : S + 2 * m + m ≤ A := by clear * - sA; omega
  have w5 : S + 5 * m + m ≤ A := by clear * - sA; omega
  have w6 : RVb + m ≤ A ∨ A + 4 + 5 * fL.length + cL.length ≤ RVb := by
    clear * - dR hk hmk; omega
  have w7 : A + 4 + 5 * fL.length + cL.length ≤ W := by clear * - wA hk hmk; omega
  have w8 : S + 9 * m + 1 + 1 ≤ W := by clear * - sA wA; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := hL
  have hL₀ : LayRegs c m K S := ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩
  obtain ⟨c₁, t₁, e₁, ht₁, h0, h1, h2, h3, hW5, hln, hF, hR, hr, hrm, ho⟩ :=
    wrProg_exec (P := P) c hc (m := m) (RVb := RVb) (K := K) (A := A) (NXb := S)
      (LABb := S + 2 * m) (MLb := S + 5 * m) (POb := S + 6 * m) (CDb := S + 7 * m)
      (L := rtL M ℓ) (k := fL.length) (m' := cL.length)
      ⟨r00, r01, r04, r06, d0, d2, d5, d6, d7, r25, r26, r27⟩
      (fun t ht => (hx t ht).1) (fun t ht => by rw [hRV _ (hx t ht).1]; exact rvI_lt h _)
      (fun t ht => (hNX _ (hx t ht).1 (hx t ht).2).1) hml hmk w1 w2 w3 w4 w5 w6 wR w7
  obtain ⟨c₂, t₂, e₂, ht₂, z1, z2, z25, z26, zR, zr, zrm, zo⟩ := nsZF_exec (P := P) c₁ e₁.wb_right
    (K := K) (by rw [hR _ (by decide), r00]) (by rw [hR _ (by decide), r05])
    (by rw [hR _ (by decide), d9]) w8
  have hup : ∀ a, A ≤ a → c₂.nmem a = c₁.nmem a := fun a ha => z2 a (by clear * - ha sA; omega)
  have hin : InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
      (repsN M.dual (nsIds M h d₀).gd) A
      (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
        (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) c₂ :=
    inP_of_W5 h d₀ ℓ K c₂ c.nmem hLR hRV hNX hLAB hMLN
      (by rw [hup _ le_rfl]; exact h0) (by rw [hup _ (by omega)]; exact h1)
      (by rw [hup _ (by omega)]; exact h2) (by rw [hup _ (by omega)]; exact h3)
      (fun t ht => (hW5 t ht).of ht fun a h1 h2 => hup a (by clear * - h1; omega))
      (fun t ht => by rw [hup (A + 4 + 5 * fL.length + t) (by omega)]; exact hln t ht)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by clear * - ht₁ ht₂ hk hmk; omega, hin, z1,
    fun a h1 h2 => ?_, by rw [z25, hR _ (by decide), r06], z26, fun r hr' => ?_,
    by rw [zr, hr], by rw [zrm, hrm], by rw [zo, ho]⟩
  · rw [hfsz] at h2
    rw [z2 a h1, hF a (by clear * - h2; omega)]
  · obtain ⟨q1, -, -, q4, q5, q6, q7⟩ := nsScr_out hr'
    rw [zR r (by clear * - q4; omega) q6 q7, hR r (by clear * - q5; omega)]

/-- **The preparation of a negSSSP call** (see the module docstring): within `300 m + 200` steps
the input part of the root frame of the negative-length shortest paths on `M.dual` for the
identifiers `nsIds M h d₀`, from the index arrays of the reverse and the rotation and the lengths
in the offset `K`; the scratch region `[S, S + 9 m + 1 + tsz m)` zero again, all other memory
outside the frame kept. -/
theorem nsPrep_exec (h : EnumOK M en m) (d₀ : D) (ℓ : D → ℤ) (c : Config) (hc : WordsBounded W c)
    {RVb RTb LNb K S A : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb)
    (r02 : c.nreg 7502 = RTb) (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S) (r06 : c.nreg 7506 = A)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hLN : ∀ i < m, c.nmem (LNb + i) = (ℓ (en i) + K).toNat) (hK : ∀ i < m, |ℓ (en i)| ≤ K)
    (hz : ∀ a, S ≤ a → a < S + 9 * m + 1 + tsz m → c.nmem a = 0)
    (sR : S + 9 * m + 1 + tsz m ≤ RVb) (sT : S + 9 * m + 1 + tsz m ≤ RTb)
    (sN : S + 9 * m + 1 + tsz m ≤ LNb) (sA : S + 9 * m + 1 + tsz m ≤ A)
    (dR : RVb + m ≤ A ∨ A + 6 + 10 * m ≤ RVb) (wR : RVb + m ≤ W) (wT : RTb + m ≤ W)
    (wN : LNb + m ≤ W) (wA : A + 6 + 10 * m ≤ W) (wL : 2 * K + rtL M ℓ ≤ W) :
    ∃ c' t, Exec P W nsPrep c c' t ∧ t ≤ 300 * m + 200 ∧
      InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
        (repsN M.dual (nsIds M h d₀).gd) A
        (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) c' ∧
      (∀ a, S ≤ a → a < S + 9 * m + 1 + tsz m → c'.nmem a = 0) ∧
      (∀ a, (a < S ∨ S + 9 * m + 1 + tsz m ≤ a) → (a < A ∨ A + Frame.fsz
        (repsN M.dual (nsIds M h d₀).gd).card (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.nreg 7325 = A ∧ c'.nreg 7326 = m ∧
      (∀ r, ¬ NsScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ts := tsz_pos m
  have wK : 2 * K ≤ W := by clear * - wL; omega
  have wL' : rtL M ℓ ≤ W := by clear * - wL; omega
  have s1 : S + 9 * m + 1 ≤ RVb := by clear * - sR; omega
  have s2 : S + 9 * m + 1 ≤ RTb := by clear * - sT; omega
  have s3 : S + 9 * m + 1 ≤ A := by clear * - sA; omega
  have z1 : ∀ a, S ≤ a → a < S + 9 * m + 1 → c.nmem a = 0 := fun a h1 h2 =>
    hz a h1 (by clear * - h2; omega)
  unfold nsPrep
  -- stage A
  obtain ⟨c₁, t₁, e₁, ht₁, L₁, X₁, P₁, B₁, F₁, R₁, rr₁, rm₁, o₁⟩ :=
    nsA_exec h c hc r00 r01 r02 r04 r05 hRV hRT z1 s1 s2 wR wT wK (P := P)
  have q1 : ∀ x, ¬ NsScr x → c₁.nreg x = c.nreg x := R₁
  -- stage B
  obtain ⟨c₂, t₂, e₂, ht₂, K₂, M₂, L25, F₂, R₂, r22, rr₂, rm₂, o₂⟩ :=
    nsB_exec h d₀ ℓ c₁ e₁.wb_right (by rw [q1 _ (by clear * -; unfold NsScr; omega), r00]) (by rw [q1 _ (by clear * -; unfold NsScr; omega), r01])
      (by rw [q1 _ (by clear * -; unfold NsScr; omega), r03]) (by rw [q1 _ (by clear * -; unfold NsScr; omega), r04]) L₁ B₁
      (fun i hi => by rw [F₁ _ (by clear * - s1; omega)]; exact hRV i hi)
      (fun i hi => by rw [F₁ _ (by clear * - sN; omega)]; exact hLN i hi) hK
      (fun a h1 h2 => by rw [F₁ _ (by clear * - h1; omega)]; exact hz a (by clear * - h1; omega) h2)
      sR sN wR wN wK wL' (P := P)
  have L₂ : LayRegs c₂ m K S := L₁.of fun r h1 h2 => by
    by_cases e : r = 7522
    · subst e; rw [r22, L₁.2.2.2.2.2.2.2.2.2.2.2.2]
    · exact R₂ r (by clear * - h1 h2 e; omega)
  have F₂' : ∀ a, (a < S + 4 * m ∨ S + 6 * m ≤ a) → c₂.nmem a = c₁.nmem a := fun a ha =>
    F₂ a fun h' => by clear * - h' ha; omega
  -- stage C
  obtain ⟨c₃, t₃, e₃, ht₃, LR₃, n27, n26, NX₃, F₃, L₃, r25₃, R₃, rr₃, rm₃, o₃⟩ :=
    nsC_exec h d₀ c₂ e₂.wb_right (by rw [R₂ _ (by decide), q1 _ (by clear * -; unfold NsScr; omega), r00])
      (by rw [R₂ _ (by decide), q1 _ (by clear * -; unfold NsScr; omega), r01]) L₂
      (fun i hi => by rw [F₂' _ (by clear * - hi; omega)]; exact X₁ i hi)
      (fun i hi => by rw [F₂' _ (by clear * - hi; omega)]; exact P₁ i hi) K₂
      (fun i hi => by rw [F₂' _ (by clear * - s1; omega), F₁ _ (by clear * - s1; omega)]; exact hRV i hi)
      (fun j hj => by rw [F₂' _ (by clear * - hj; omega), F₁ _ (by clear * - hj; omega)];
                      exact z1 _ (by clear * -; omega) (by clear * - hj; omega))
      (fun j hj => by rw [F₂' _ (by clear * - hj; omega), F₁ _ (by clear * - hj; omega)];
                      exact z1 _ (by clear * -; omega) (by clear * - hj; omega))
      s1 wR (P := P)
  have q3 : ∀ x, ¬ NsScr x → c₃.nreg x = c.nreg x := fun x hx => by
    have hx' := nsScr_out hx
    rw [R₃ x hx, R₂ x (by clear * - hx'; omega), q1 x hx]
  -- stage D
  obtain ⟨c₄, t₄, e₄, ht₄, I₄, Z₄, F₄, r325, r326, R₄, rr₄, rm₄, o₄⟩ :=
    nsW_exec h d₀ ℓ c₃ e₃.wb_right (by rw [q3 _ (by clear * -; unfold NsScr; omega), r00]) (by rw [q3 _ (by clear * -; unfold NsScr; omega), r01])
      (by rw [q3 _ (by clear * -; unfold NsScr; omega), r04]) (by rw [q3 _ (by clear * -; unfold NsScr; omega), r05])
      (by rw [q3 _ (by clear * -; unfold NsScr; omega), r06]) L₃ (by rw [r25₃, L25]) n26 n27 LR₃
      (fun i hi => by rw [F₃ _ (by clear * - s1; omega), F₂' _ (by clear * - s1; omega),
        F₁ _ (by clear * - s1; omega)]; exact hRV i hi) NX₃
      (fun i hi => by rw [F₃ _ (by clear * - hi; omega), F₂' _ (by clear * - hi; omega)]; exact B₁ i hi)
      (fun i hi => by rw [F₃ _ (by clear * - hi; omega)]; exact M₂ i hi) hK s3 s1 dR wR wA wL
      (P := P)
  refine ⟨c₄, t₁ + ((t₂ + t₃) + t₄), .seq e₁ (.seq (.seq e₂ e₃) e₄),
    by clear * - ht₁ ht₂ ht₃ ht₄; omega, I₄, fun a h1 h2 => ?_, fun a h1 h2 => ?_, r325, r326,
    fun r hr => ?_, by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩
  · by_cases ha : a < S + 9 * m + 1
    · exact Z₄ a h1 ha
    · have hA : a < A := by clear * - h2 sA; omega
      rw [F₄ a (by clear * - ha; omega) (Or.inl hA), F₃ a (by clear * - ha; omega),
        F₂' a (by clear * - ha; omega), F₁ a (by clear * - ha; omega), hz a h1 h2]
  · have hs : a < S ∨ S + 9 * m + 1 ≤ a := by clear * - h1; omega
    rw [F₄ a hs h2, F₃ a (by clear * - h1; omega), F₂' a (by clear * - h1; omega),
      F₁ a (by clear * - h1; omega)]
  · rw [R₄ r hr, R₃ r hr]
    have hr' := nsScr_out hr
    rw [R₂ r (by clear * - hr'; omega), R₁ r hr]

open MfDrv in
/-- **The negSSSP step of a call as one program** (see the module docstring): from the zero
memory `≤ Wz` (which holds the scratch region), the dart order of `M` (index arrays of the reverse
and the rotation, lengths `ℓ + K` with `|ℓ| ≤ K`), `negStep = nsPrep ; negCallH` runs within
`300 m + 200 + (9 negT C C₀ m + 12 fsz + 7 fin + 3291 + (12 m + 4628))` steps to a configuration
with the machine outcome `negMach (nsIds M h d₀) M I ℓ` encoded in the copy of the root frame at
`Ob` and the memory `≤ Wz` zero again; all memory above `Wz` outside the frame at `A`, the copy at
`Ob` and the log at `p` kept; the driver registers `3000 … 3012` kept. -/
theorem negStep_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (h : EnumOK M en m) (d₀ : D) (ℓ : D → ℤ)
    (hpre : NegPre M ℓ) (I P' : Input) (c : Config) (hc : WordsBounded W c)
    {RVb RTb LNb K S A Wz Ob p : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb)
    (r02 : c.nreg 7502 = RTb) (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S) (r06 : c.nreg 7506 = A) (r22 : c.nreg 7322 = Ob)
    (r24 : c.nreg 7324 = p)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hLN : ∀ i < m, c.nmem (LNb + i) = (ℓ (en i) + K).toNat) (hK : ∀ i < m, |ℓ (en i)| ≤ K)
    (hzW : ∀ a ≤ Wz, c.nmem a = 0) (hS : S + 9 * m + 1 + tsz m ≤ Wz + 1)
    (sR : Wz < RVb) (sT : Wz < RTb) (sN : Wz < LNb) (hA : Wz < A)
    (dR : RVb + m ≤ A ∨ A + 6 + 10 * m ≤ RVb) (wR : RVb + m ≤ W) (wT : RTb + m ≤ W)
    (wN : LNb + m ≤ W) (wA : A + 6 + 10 * m ≤ W) (wL : 2 * K + rtL M ℓ ≤ W)
    (hWz : rtW m (rtL M ℓ) m ≤ Wz)
    (hAO : A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ p)
    (hpW : p + negT C C₀ m ≤ W) (hw2 : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL M ℓ) ≤ W) :
    ∃ d' t, Exec P' W negStep c d' t ∧
      t ≤ 300 * m + 200 + (9 * negT C C₀ m +
        12 * Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) +
        7 * Frame.fin (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) + 3291 + (12 * m + 4628)) ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res (nsIds M h d₀) M.dual (rtL M ℓ) (repsN M.dual (nsIds M h d₀).gd)
        (negMach (nsIds M h d₀) M I ℓ) Ob
        (Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) d' ∧
      (∀ a, Wz < a →
        (a < A ∨ A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        (a < Ob ∨ Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ m ≤ a) → d'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = c.nreg r) ∧
      (∀ r, ¬ ncScr r → ¬ NsScr r → d'.nreg r = c.nreg r) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ d'.output = c.output := by
  have hcard := card_eq_m h
  have hfsz : Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ 6 + 10 * m := by
    have h1 := card_le_n (repsN M.dual (nsIds M h d₀).gd)
    have h2 := ck_le_n M.dual (repsN M.dual (nsIds M h d₀).gd)
    unfold Frame.fsz; rw [hcard] at h1 h2; clear * - h1 h2; omega
  obtain ⟨c₁, t₁, e₁, ht₁, I₁, Z₁, F₁, r25, r26, R₁, rr₁, rm₁, o₁⟩ :=
    nsPrep_exec h d₀ ℓ c hc r00 r01 r02 r03 r04 r05 r06 hRV hRT hLN hK
      (fun a h1 h2 => hzW a (by clear * - h2 hS; omega)) (by clear * - hS sR; omega)
      (by clear * - hS sT; omega) (by clear * - hS sN; omega) (by clear * - hS hA; omega)
      dR wR wT wN wA wL (P := P')
  have hz₁ : ∀ a ≤ Wz, c₁.nmem a = 0 := fun a ha => by
    by_cases h1 : S ≤ a ∧ a < S + 9 * m + 1 + tsz m
    · exact Z₁ a h1.1 h1.2
    · rw [F₁ a (by clear * - h1; omega) (Or.inl (by clear * - ha hA; omega)), hzW a ha]
  have q : ∀ r, ¬ NsScr r → c₁.nreg r = c.nreg r := R₁
  have hWz' : rtW (Fintype.card D) (rtL M ℓ) (nsIds M h d₀).G ≤ Wz := by
    rw [nsIds_G, hcard]; exact hWz
  have hpW' : p + negT C C₀ (Fintype.card D) ≤ W := by rw [hcard]; exact hpW
  have hw2' : spWs (Fintype.card D) + 205 ≤ W := by rw [hcard]; exact hw2
  have hw3' : fxWB (Fintype.card D) (rtL M ℓ) ≤ W := by rw [hcard]; exact hw3
  obtain ⟨d', t, ex, ht, hz', hres, hF, hk1, hk2, hr', hrm', ho'⟩ :=
    negCallH_exec C C₀ hC (nsIds M h d₀) hpre I P' c₁ e₁.wb_right
      (by rw [q _ (by clear * -; unfold NsScr; omega), r22])
      (by rw [q _ (by clear * -; unfold NsScr; omega), r24]) r25
      (by rw [r26, nsIds_G]) hz₁ I₁ hWz' hA hAO hOp hpW' hw2' hw3'
  rw [hcard] at ht hF
  refine ⟨d', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht; omega, hz', hres,
    fun a h1 h2 h3 h4 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, by rw [hr', rr₁],
    by rw [hrm', rm₁], by rw [ho', o₁]⟩
  · rw [hF a h1 h3 h4, F₁ a (Or.inr (by clear * - h1 hS; omega)) h2]
  · rw [hk1 r h1 h2, q r (by clear * - h1 h2; unfold NsScr; omega)]
  · rw [hk2 r h1, q r h2]

end NsStep

end BKMNW

end PlanarFlow
