module

public import PlanarSeparator.Machine.PieceCallC

/-!
# The program of a piece, fourth part: the separator program and the write-back

From the state `Mid`: the separator program as a subroutine (`PlanarSeparator.ltSubR_exec`, on
the induced rotation system of `C`, plane for a connected `C` of at least two vertices), then
the word printed for the `j`-th vertex written to its mark cell (`mapLoop`, as `List.getD`):
**`back_exec`**, the state `Post`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G} {w : Fin N → ℕ} {C : Finset (Fin N)} {Z W : ℕ}

/-- **The separator program and the write-back of its words to the marks.** -/
def back : Stmt :=
  .seq (ltSubR 1060 1001 1061 1062 1063)
    (.seq (block [.subN 1065 1060 1064, .copyN 1042 1019]) mapLoop)

variable (G R w C Z W) in
/-- **The state after the write-back**: the marks of the vertices of `C`, the zero cells from
`β + len` to `Z`, the labels and ranks as in `Mid`, the rest as before. -/
structure Post (c d : Config) : Prop where
  wb : WordsBounded W d
  regs : ∀ r, Kept r → d.nreg r = c.nreg r
  r62 : d.nreg 1062 = bB #C (mI G C) (∑ v ∈ C, w v)
  r63 : d.nreg 1063 = lenL #C (mI G C)
  r64 : d.nreg 1064 = pP #C (mI G C) (∑ v ∈ C, w v)
  mark : ∀ j < #C, d.nmem (c.nreg 1019 + lv C j) = (ltOut (ltIn R (ord N) C w)).getD j 0
  hi : ∀ a, bB #C (mI G C) (∑ v ∈ C, w v) + lenL #C (mI G C) ≤ a → a < Z → d.nmem a = 0
  lab : ∀ x < N, d.nmem (c.nreg 1017 + x) = labV C x
  rk : ∀ g < nD G, d.nmem (c.nreg 1018 + g) = rkA G C g
  rest : ∀ a, Z ≤ a → (a < c.nreg 1017 ∨ c.nreg 1017 + N ≤ a) →
    (a < c.nreg 1018 ∨ c.nreg 1018 + nD G ≤ a) → (∀ j < #C, a ≠ c.nreg 1019 + lv C j) →
    d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

theorem sum_cemb (C : Finset (Fin N)) (w : Fin N → ℕ) :
    ∑ i, w (cemb (ord N) C i) = ∑ v ∈ C, w v := by
  conv_rhs => rw [← map_cemb mem_ord C]
  rw [sum_map]

set_option maxHeartbeats 1000000 in
theorem back_exec {P : Input} {c d : Config} (hp : Pre G R w C Z W c) (hm : Mid G R w C Z W c d)
    (hR : R.IsPlane) (hC : InConn G C) (h2 : 2 ≤ #C) :
    ∃ d' t, Exec P W back d d' t ∧ t ≤ 6 * kK #C (mI G C) + 15 * #C + 5 ∧
      Post G R w C Z W c d' := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  set k := #C with hkdef
  set m := mI G C with hmdef
  set sw := ∑ v ∈ C, w v with hswdef
  set β := bB k m sw with hβdef
  set p := pP k m sw with hpdef
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  set aMk := c.nreg 1019
  have lZ := hp.lZ; have l0 := hp.l0; have l1 := hp.l1; have l2 := hp.l2; have l3 := hp.l3
  have l4 := hp.l4; have l5 := hp.l5; have l6 := hp.l6; have l7 := hp.l7; have l8 := hp.l8
  have hbig : 2 * β ≤ Z := hp.big
  have hβ : β = p + kK k m + 1 := rfl
  have hlen : lenL k m = 2 * k + 3 + 3 * m := rfl
  have hKK : kK k m = 320 * m + 191 * k + 403 := rfl
  have hp0 : 2 * k + 3 + 3 * m + 2 ≤ p := by rw [hpdef]; unfold pP; omega
  have hkN : k ≤ N := by have := card_le_univ C; simpa using this
  have hβ' : bB #C (mI G C) (∑ v ∈ C, w v) = β := rfl
  have hp' : pP #C (mI G C) (∑ v ∈ C, w v) = p := rfl
  have hlen' : lenL #C (mI G C) = lenL k m := rfl
  have hK' : kK #C (mI G C) = kK k m := rfl
  set e := cemb (ord N) C
  have hr : univ.map e = C := map_cemb mem_ord C
  have hne : C.Nonempty := card_pos.1 (by omega)
  have hplane := InducedRot.indRot_isPlane R e hR (connected_comap e hr hC hne)
    (by rw [Fintype.card_fin]; omega)
  have hcard : (dkeys (G.comap e)).card = m := card_comap G C
  have hsum : ∑ i, w (e i) = sw := sum_cemb C w
  obtain ⟨hDlen, -⟩ := ltIn_words G R C w
  rw [hk] at hDlen
  have hDlen' : (ltIn R (ord N) C w).data.length = lenL k m := hDlen
  obtain ⟨d₇, t₇, e₇, ht₇, hp₇, hmem₇, hreg₇, hkeep₇, ho₇, hrr₇, hrm₇⟩ :=
    ltSubR_exec (G.comap e) (InducedRot.indRot R e) hplane (fun i => w (e i)) (dartNum _)
    (fun d d' h => dartNum_lt _ h) (P' := P) (rp := 1060) (ro := 1001) (tmp := 1061)
    (rβ := 1062) (rlen := 1063) (W' := W) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm.wb
    (fun r hr => by rw [hm.regs r (Or.inl hr)]; exact hp.zreg r hr)
    (fun r hr => by rw [hm.rr]; exact hp.rz r hr)
    (fun a ha => by
      rw [hm.r60, hcard] at ha
      exact hm.low a (by omega))
    (fun a ha => by
      rw [hm.r60, hcard] at ha
      rw [hm.rm]; exact hp.rmz a (by omega))
    (by rw [hm.regs 1001 (Or.inr (Or.inl rfl))]; exact hp.one)
    (by rw [hm.r60, hcard, hsum, hp']; rw [hpdef]; unfold pP; omega)
    ⟨by rw [hm.r60, hm.r62, hcard]; omega,
     by rw [hm.r60, hm.r62, hcard]; omega,
     by rw [hm.r63]; exact hDlen'.symm,
     fun i hi => by
      rw [hm.r60, hcard] at hi
      rw [hm.r62]
      exact hm.data i (by omega)⟩
  rw [hm.r60, hcard, hp'] at hkeep₇
  rw [hcard] at ht₇
  rw [hm.r60] at hp₇ hmem₇
  have hKn : 320 * m + 191 * (clist (ord N) C).length + 403 = kK k m := by rw [hk]; rfl
  rw [hKn] at hkeep₇ ht₇
  set out := ltOut (ltIn R (ord N) C w) with hout
  have hout' : ltOut (sepInput (InducedRot.indRot R e) (fun i => w (e i)) (dartNum (G.comap e))) =
    out := rfl
  rw [hout'] at hp₇ hmem₇
  have R7 : ∀ r, Kept r → d₇.nreg r = c.nreg r := fun r hr => by
    rw [hreg₇ r (by unfold Kept at hr; omega) (by unfold Kept at hr; omega)
      (by unfold Kept at hr; omega), hm.regs r (Or.inr hr)]
  have M7 : ∀ a, p + kK k m < a → d₇.nmem a = d.nmem a := hkeep₇
  -- the length of the output and the base of the marks
  obtain ⟨d₈, t₈, e₈, hw₈, g65, g42, gr₈, gm₈, ht₈⟩ : ∃ d₈ t₈, Exec P W
      (block [.subN 1065 1060 1064, .copyN 1042 1019]) d₇ d₈ t₈ ∧ WordsBounded W d₈ ∧
      d₈.nreg 1065 = out.length ∧ d₈.nreg 1042 = aMk ∧
      (∀ r, r ≠ 1065 → r ≠ 1042 → d₈.nreg r = d₇.nreg r) ∧ d₈.nmem = d₇.nmem ∧ t₈ = 2 := by
    have hw := e₇.wb_right
    have a64 : d₇.nreg 1064 = p := by
      rw [hreg₇ 1064 (by norm_num) (by norm_num) (by norm_num)]; exact hm.r64
    have a19 : d₇.nreg 1019 = aMk := R7 1019 (by unfold Kept; omega)
    exec_block
    refine ⟨‹WordsBounded _ _›, ?_⟩
    config_simp
    rw [hp₇, a64, a19]
    refine ⟨by omega, rfl, fun r h1 h2 => ?_⟩
    simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have R8 : ∀ r, Kept r → d₈.nreg r = c.nreg r := fun r hr => by
    rw [gr₈ r (by unfold Kept at hr; omega) (by unfold Kept at hr; omega), R7 r hr]
  have h64 : d₈.nreg 1064 = p := by
    rw [gr₈ 1064 (by omega) (by omega), hreg₇ 1064 (by norm_num) (by norm_num) (by norm_num)]
    exact hm.r64
  have hlvN : ∀ j < k, lv C j < N := fun j hj => lv_lt C (by omega)
  -- the write-back
  obtain ⟨d₉, t₉, e₉, ht₉, hmk₉, hfr₉⟩ := mapLoop_exec (P := P) hw₈ (k := k) (ℓ := out.length)
    (pp := p) (base := aMk) (lv C) (R8 1001 (Or.inl rfl) ▸ hp.one)
    (by rw [R8 1016 (by unfold Kept; omega)]; exact hp.kk) g65 h64 g42
    (fun j hj => by
      rw [R8 1015 (by unfold Kept; omega), gm₈, M7 _ (by omega),
        hm.rest _ (by omega) (by omega) (by omega)]
      exact hp.L j hj)
    (fun i hi j hj h => lv_inj C (by omega) (by omega) h)
    (fun i hi j hj => by rw [R8 1015 (by unfold Kept; omega)]; have := hlvN i hi; omega)
    (fun i hi j hj => by have := hlvN i hi; have : j < k := lt_of_lt_of_le hj (min_le_left _ _)
                         omega)
    (by omega) (by rw [R8 1015 (by unfold Kept; omega)]; omega)
    (fun j hj => by have := hlvN j hj; omega) (by omega)
  have M9 : ∀ a, (∀ j < k, a ≠ aMk + lv C j) → d₉.nmem a = d₇.nmem a := fun a ha => by
    rw [hfr₉ a ha, gm₈]
  have hback : Exec P W back d d₉ (t₇ + (t₈ + t₉)) := .seq e₇ (.seq e₈ e₉)
  refine ⟨d₉, _, hback, by omega, ⟨e₉.wb_right, fun r hr => ?_, ?_, ?_, ?_, fun j hj => ?_,
    fun a h1 h2 => ?_, fun x hx => ?_, fun g hg => ?_, fun a h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩⟩
  · rw [nreg_of_scr e₉ (by decide) (by unfold Kept at hr; omega), R8 r hr]
  · rw [Exec.nreg_of_wr e₉ (r := 1062) (by decide), gr₈ 1062 (by omega) (by omega),
      hreg₇ 1062 (by norm_num) (by norm_num) (by norm_num)]
    exact hm.r62
  · rw [Exec.nreg_of_wr e₉ (r := 1063) (by decide), gr₈ 1063 (by omega) (by omega),
      hreg₇ 1063 (by norm_num) (by norm_num) (by norm_num)]
    exact hm.r63
  · rw [Exec.nreg_of_wr e₉ (r := 1064) (by decide), h64]
  · rw [hmk₉ j hj, gm₈]
    by_cases hjo : j < out.length
    · simp only [hjo, ↓reduceIte]
      rw [hmem₇ j hjo, List.getD_eq_getElem _ _ hjo]
    · simp only [hjo, ↓reduceIte]
      exact (List.getD_eq_default _ _ (show out.length ≤ j by omega)).symm
  · rw [M9 a (fun j hj => by omega), M7 a (by omega),
      show a = β + (a - β) by omega, hm.data _ (by omega),
      List.getD_eq_default _ _ (by rw [hDlen']; omega)]
  · rw [M9 _ (fun j hj => by omega), M7 _ (by omega)]; exact hm.lab x hx
  · rw [M9 _ (fun j hj => by omega), M7 _ (by omega)]; exact hm.rk g hg
  · rw [M9 a h4, M7 a (by omega)]; exact hm.rest a h1 h2 h3
  · rw [Exec.output_of_ou e₉ (by decide), Exec.output_of_ou e₈ (by decide), ho₇]; exact hm.out
  · rw [(Exec.real_of_noReal e₉ (by decide)).1, (Exec.real_of_noReal e₈ (by decide)).1, hrr₇]
    exact hm.rr
  · rw [(Exec.real_of_noReal e₉ (by decide)).2, (Exec.real_of_noReal e₈ (by decide)).2, hrm₇]
    exact hm.rm

end Piece

end PlanarSeparator
