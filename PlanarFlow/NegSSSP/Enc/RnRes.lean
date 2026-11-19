module

public import PlanarFlow.NegSSSP.Enc.RnRun
public import PlanarFlow.NegSSSP.Frame
public import PlanarFlow.NegSSSP.SplitStage

/-!
# The outcome of a node written to its frame, renormalized (`Res`)

`resProg = resSet ; rnProg ; resFlag ; copy loop` (registers `2940 … 2955`; the inputs
`r3004 = d` the frame, `r2950 = w`, `r2951 = Tb`, `r2952 = HHb`, `r2953 = Fb`, `r2954 = Ab`,
`r2955 = Ib`): from a feasible potential `f` of the piece in the offset encoding
`F[v] = f (ι v) + Lf` (any `Lf`: the node's bound `H`), the node numbers of the tails and
heads of the darts `cδ a` at `Tb`, `HHb`, the global vertex identifiers `I[v] = gv (ι v)` at
`Ib`, and the lengths read **in the frame** (`InP`), it writes the outcome region of the frame:
flag `0`, `w`, the identifiers, and the renormalized potential `(g (ι v) + L).toNat`.

**`resProg_res`**: `PotOut (pg N P ℓ) (some g)` and `Res g N L P (some g) d e`, with
`|g| ≤ Σ_{d ∈ P} |ℓ d| ≤ L` whatever `Lf` is, within `rnCost m w + 7 w + 37` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- The registers of `rnProg` from the frame (`Rb = d + fin m k` in `r2946`, `Rb + 2` in
`r2947`). -/
def resSet : Stmt := block [.constN 2940 1, .addN 2941 3004 2940, .loadN 2966 2941,
  .addN 2941 2941 2940, .loadN 2942 2941, .addN 2941 2941 2940, .loadN 2972 2941,
  .constN 2943 4, .addN 2944 3004 2943, .constN 2943 5, .mulN 2945 2942 2943,
  .addN 2970 2944 2945, .addN 2946 2970 2966, .addN 2947 2946 2940, .addN 2947 2947 2940,
  .addN 2973 2947 2966, .addN 2973 2973 2966, .copyN 2967 2950, .copyN 2968 2951,
  .copyN 2969 2952, .copyN 2971 2953, .copyN 2974 2954]

/-- The flag `0` and `w`. -/
def resFlag : Stmt := block [.constN 2940 0, .storeN 2946 2940, .constN 2940 1,
  .addN 2941 2946 2940, .storeN 2941 2950, .constN 2948 0]

/-- One identifier: `mem[Rb + 2 + v] := I[v]`. -/
def resCpBody : Stmt := block [.addN 2941 2955 2948, .loadN 2949 2941, .addN 2941 2947 2948,
  .storeN 2941 2949, .addN 2948 2948 2940]

/-- **The outcome written to the frame.** -/
def resProg : Stmt := .seq resSet <| .seq rnProg <| .seq resFlag (.whileLtN 2948 2950 resCpBody)

set_option maxHeartbeats 2000000 in
theorem resSet_exec (c : Config) (hc : WordsBounded W c) {d m k L w Tb HHb Fb Ab : ℕ}
    (r04 : c.nreg 3004 = d) (r30 : c.nreg 2950 = w) (r31 : c.nreg 2951 = Tb)
    (r32 : c.nreg 2952 = HHb) (r33 : c.nreg 2953 = Fb) (r34 : c.nreg 2954 = Ab)
    (hm : c.nmem (d + 1) = m) (hk : c.nmem (d + 2) = k) (hL : c.nmem (d + 3) = L)
    (hW : d + 4 + 5 * k + m + 2 + m + m ≤ W) :
    ∃ c' t, Exec I W resSet c c' t ∧ t = 22 ∧ c'.nreg 2966 = m ∧ c'.nreg 2967 = w ∧
      c'.nreg 2968 = Tb ∧ c'.nreg 2969 = HHb ∧ c'.nreg 2970 = d + 4 + 5 * k ∧
      c'.nreg 2971 = Fb ∧ c'.nreg 2972 = L ∧ c'.nreg 2973 = d + 4 + 5 * k + m + 2 + m + m ∧
      c'.nreg 2974 = Ab ∧ c'.nreg 2946 = d + 4 + 5 * k + m ∧
      c'.nreg 2947 = d + 4 + 5 * k + m + 2 ∧
      (∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2966) ∨ 2974 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold resSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r30, r31, r32, r33, r34, hm, hk, hL]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r04, r30, r31, r32, r33, r34, hm, hk, hL])
  all_goals try omega
  repeat rw [upd_other _ _ _ (by omega)]

theorem resFlag_exec (c : Config) (hc : WordsBounded W c) {Rb w : ℕ}
    (r26 : c.nreg 2946 = Rb) (r30 : c.nreg 2950 = w) (hW : Rb + 1 ≤ W) :
    ∃ c' t, Exec I W resFlag c c' t ∧ t = 6 ∧
      c'.nmem = upd (upd c.nmem Rb 0) (Rb + 1) w ∧ c'.nreg 2940 = 1 ∧ c'.nreg 2948 = 0 ∧
      (∀ r, r ≠ 2940 → r ≠ 2941 → r ≠ 2948 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold resFlag
  exec_block
  all_goals try ((try config_simp); (try simp only [r26, r30]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r26, r30])
  repeat rw [upd_other _ _ _ (by omega)]

/-- **The identifiers copied** (`mem[Rb + 2 + v] := I[v]`, `v < w`). -/
theorem resCp_exec (c : Config) (hc : WordsBounded W c) {w Ib R2 : ℕ}
    (r20 : c.nreg 2940 = 1) (r28 : c.nreg 2948 = 0) (r30 : c.nreg 2950 = w)
    (r35 : c.nreg 2955 = Ib) (r27 : c.nreg 2947 = R2) (hW1 : Ib + w ≤ W) (hW2 : R2 + w + 1 ≤ W)
    (hd : R2 + w ≤ Ib ∨ Ib + w ≤ R2) :
    ∃ c' t, Exec I W (.whileLtN 2948 2950 resCpBody) c c' t ∧ t ≤ 7 * w + 2 ∧
      (∀ v < w, c'.nmem (R2 + v) = c.nmem (Ib + v)) ∧
      (∀ a, (a < R2 ∨ R2 + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2941 → r ≠ 2948 → r ≠ 2949 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (R2 + v) = c.nmem (Ib + v)) ∧
      (∀ a, (a < R2 ∨ R2 + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2941 → r ≠ 2948 → r ≠ 2949 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := I) (a := 2948) (bR := 2950)
    (body := resCpBody) J (K := 5) (n := w) c hc r28 r30
    ⟨fun v hv => absurd hv (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q20 : c'.nreg 2940 = 1 := (jn _ (by omega) (by omega) (by omega)).trans r20
      have q35 : c'.nreg 2955 = Ib := (jn _ (by omega) (by omega) (by omega)).trans r35
      have q27 : c'.nreg 2947 = R2 := (jn _ (by omega) (by omega) (by omega)).trans r27
      have eI : c'.nmem (Ib + i) = c.nmem (Ib + i) := j2 _ (by omega)
      obtain ⟨c'', t, ex, ht, hm, h28, hn, hr, hrm, ho⟩ : ∃ c'' t,
          Exec I W resCpBody c' c'' t ∧ t = 5 ∧
          c''.nmem = upd c'.nmem (R2 + i) (c.nmem (Ib + i)) ∧ c''.nreg 2948 = i + 1 ∧
          (∀ r, r ≠ 2941 → r ≠ 2948 → r ≠ 2949 → c''.nreg r = c'.nreg r) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        unfold resCpBody
        exec_block
        all_goals try ((try config_simp); (try simp only [q20, q35, q27, ha]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q20, q35, q27, ha, eI])
        repeat rw [upd_other _ _ _ (by omega)]
      refine ⟨c'', t, ex, by omega, h28, (hn _ (by omega) (by omega) (by omega)).trans hb,
        fun v hv => ?_, fun a ha' => ?_,
        fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3), by rw [hr, jr], by rw [hrm, jrm],
        by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 v hv
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, by omega, j1, j2, jn, jr, jrm, jo⟩

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The renormalized outcome of a node written to its frame** (see the module docstring). -/
theorem resProg_res {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e : ℕ} {f : V → ℤ} {ν : V → ℕ}
    {ι : ℕ → V} {w Tb HHb Fb Ab Ib Lf : ℕ} (c : Config) (hc : WordsBounded W c)
    (hin : InP g N ℓ L n P d e c) (hf : (pg N P ℓ).IsPot f)
    (r04 : c.nreg 3004 = d) (r30 : c.nreg 2950 = w) (r31 : c.nreg 2951 = Tb)
    (r32 : c.nreg 2952 = HHb) (r33 : c.nreg 2953 = Fb) (r34 : c.nreg 2954 = Ab)
    (r35 : c.nreg 2955 = Ib)
    (hν : ∀ x ∈ verts N P, ν x < w ∧ ι (ν x) = x)
    (hι : ∀ v < w, ι v ∈ verts N P ∧ ν (ι v) = v) (hw : w ≤ 2 * P.card)
    (hT : ∀ a < P.card, c.nmem (Tb + a) = ν (N.tail (cδ g N P a)))
    (hH : ∀ a < P.card, c.nmem (HHb + a) = ν (N.head (cδ g N P a)))
    (hF : ∀ v < w, (c.nmem (Fb + v) : ℤ) = f (ι v) + Lf)
    (hI : ∀ v < w, c.nmem (Ib + v) = g.gv (ι v))
    (hfL : ∀ v < w, |f (ι v)| ≤ Lf) (hℓL : ∀ x ∈ P, |ℓ x| ≤ L) (hL : ∑ x ∈ P, |ℓ x| ≤ L)
    (lT : Tb + P.card ≤ Ab) (lH : HHb + P.card ≤ Ab) (lF : Fb + w ≤ Ab) (lI : Ib + w ≤ Ab)
    (le : e ≤ Ab) (dF : Fb + w ≤ d ∨ e ≤ Fb) (dI : Ib + w ≤ d ∨ e ≤ Ib)
    (wE : Ab + 5 * (P.card + w) + 8 * (w + 1) + 1 ≤ W) (wV : 4 * Lf + 2 * L + L + 2 ≤ W) :
    ∃ c' t g', Exec I W resProg c c' t ∧ t ≤ 22 + rnCost P.card w + 6 + (7 * w + 2) ∧
      PotOut (pg N P ℓ) (some g') ∧ Res g N L P (some g') d e c' ∧
      (∀ a, (a < d + fin P.card (ck N P) ∨ e ≤ a) →
        (a < Ab ∨ Ab + 5 * (P.card + w) + 8 * (w + 1) + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 2990 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have he := hin.en
  have hmk := ck_ge (N := N) P
  have hck : ck N P = (rcl N P).card := rfl
  unfold fsz at he
  -- the registers of `rnProg`
  obtain ⟨c₁, t₁, e₁, ht₁, q66, q67, q68, q69, q70, q71, q72, q73, q74, q26, q27, qn₁, qm₁, qr₁,
    qrm₁, qo₁⟩ := resSet_exec (I := I) (k := ck N P) c hc r04 r30 r31 r32 r33 r34 hin.rm hin.rk
      hin.rL (by omega)
  have hw₁ := e₁.wb_right
  -- the renormalization
  obtain ⟨c₂, t₂, e₂, ht₂, ⟨g', hpot, hbd, hout⟩, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ :=
    rnProg_pot (P := I) (Q := P) (N := N) (ℓ := ℓ) (f := f) (e := cδ g N P) (ν := ν) (ι := ι)
      (Lf := Lf) hf c₁ hw₁ q66 q67 q68 q69 q70 q71 q72 q73 q74
      (fun a ha => cδ_memP ha)
      (fun a ha b hb hab => cδ_inj (by omega) (by omega) hab)
      (fun x hx => by obtain ⟨h1, h2⟩ := cδ_idxOf (g := g) (N := N) hx; exact ⟨_, h1, h2⟩)
      hν hι
      (fun a ha => by rw [qm₁]; exact hT a ha) (fun a ha => by rw [qm₁]; exact hH a ha)
      (fun a ha => by
        rw [qm₁, hin.ln a ha]
        have := abs_le.1 (hℓL _ (cδ_memP (g := g) (N := N) ha))
        exact Int.toNat_of_nonneg (by omega))
      (fun v hv => by rw [qm₁]; exact hF v hv) hfL hℓL hL
      (by omega) (by omega) (by omega) lF (by omega) (by omega) (by omega) wV
  have hw₂ := e₂.wb_right
  -- the flag and `w`
  obtain ⟨c₃, t₃, e₃, ht₃, fm₃, f20, f28, fn₃, fr₃, frm₃, fo₃⟩ :=
    resFlag_exec (I := I) (Rb := d + 4 + 5 * ck N P + P.card) (w := w) c₂ hw₂
      (by rw [hn₂ _ (by omega)]; exact q26)
      (by rw [hn₂ _ (by omega), qn₁ _ (by omega)]; exact r30) (by omega)
  have hw₃ := e₃.wb_right
  -- the identifiers
  obtain ⟨c₄, t₄, e₄, ht₄, cp₄, cm₄, cn₄, cr₄, crm₄, co₄⟩ :=
    resCp_exec (I := I) (w := w) (Ib := Ib) (R2 := d + 4 + 5 * ck N P + P.card + 2) c₃ hw₃
      f20 f28
      (by rw [fn₃ _ (by omega) (by omega) (by omega), hn₂ _ (by omega), qn₁ _ (by omega)]
          exact r30)
      (by rw [fn₃ _ (by omega) (by omega) (by omega), hn₂ _ (by omega), qn₁ _ (by omega)]
          exact r35)
      (by rw [fn₃ _ (by omega) (by omega) (by omega), hn₂ _ (by omega)]; exact q27)
      (by omega) (by omega) (by omega)
  -- the memory outside the outcome region and the scratch is kept
  have keep : ∀ a, (a < d + 4 + 5 * ck N P + P.card ∨ e ≤ a) →
      (a < Ab ∨ Ab + 5 * (P.card + w) + 8 * (w + 1) + 1 ≤ a) → c₄.nmem a = c.nmem a :=
    fun a h1 h2 => by
      rw [cm₄ a (by omega), fm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm₂ a h2 (by omega), qm₁]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), g', .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hpot,
    ⟨by unfold fsz; omega, ?_⟩, fun a h1 h2 => keep a (by unfold fin at h1; omega) h2,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold fin
    refine ⟨?_, w, ι, hw, ?_, fun v hv => ⟨(hι v hv).1, ?_, ?_, ?_⟩, fun x hx =>
      ⟨ν x, (hν x hx).1, (hν x hx).2⟩⟩
    · rw [cm₄ _ (by omega), fm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        upd_apply, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [cm₄ _ (by omega), fm₃, upd_apply, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [show d + (4 + 5 * ck N P + P.card) + 2 + v = d + 4 + 5 * ck N P + P.card + 2 + v by
        omega, cp₄ v hv, fm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        hm₂ _ (by omega) (by omega), qm₁]
      exact hI v hv
    · rw [cm₄ _ (by omega), fm₃, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        show d + (4 + 5 * ck N P + P.card) + 2 + 2 * P.card + v =
          d + 4 + 5 * ck N P + P.card + 2 + P.card + P.card + v by omega]
      exact hout v hv
    · obtain ⟨b1, b2⟩ := hbd _ (hι v hv).1
      exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [cn₄ r (by omega) (by omega) (by omega), fn₃ r (by omega) (by omega) (by omega),
      hn₂ r (by omega), qn₁ r (by omega)]
  · rw [cr₄, fr₃, hr₂, qr₁]
  · rw [crm₄, frm₃, hrm₂, qrm₁]
  · rw [co₄, fo₃, ho₂, qo₁]

end Frame

end NegSSSP

end PlanarFlow
