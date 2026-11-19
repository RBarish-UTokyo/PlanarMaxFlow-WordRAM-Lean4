module

public import PlanarSeparator.Machine.PieceCallB

/-!
# The program of a piece, third part: from `S1` to `Mid`

**`front2_exec`**: the layout block, the second rank pass and the dart pass write the words of
`ltIn R (ord N) C w` at the base `bB` (the state `Mid`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G} {w : Fin N → ℕ} {C : Finset (Fin N)} {Z W : ℕ}

set_option maxHeartbeats 1000000 in
theorem front2_exec {P : Input} {c d : Config} (hp : Pre G R w C Z W c) (hs : S1 G w C Z W c d)
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ d' t, Exec P W front2 d d' t ∧
      t ≤ 44 * #C + (6 * Δ + 36) * psum (gofs G) (lv C) #C + 43 ∧ Mid G R w C Z W c d' := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  set k := #C with hkdef
  set m := mI G C with hmdef
  set sw := ∑ v ∈ C, w v with hswdef
  set β := bB k m sw with hβdef
  set aOfs := c.nreg 1010
  set aTl := c.nreg 1011
  set aRv := c.nreg 1012
  set aRo := c.nreg 1013
  set aW := c.nreg 1014
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  have lZ := hp.lZ; have l0 := hp.l0; have l1 := hp.l1; have l2 := hp.l2; have l3 := hp.l3
  have l4 := hp.l4; have l5 := hp.l5; have l6 := hp.l6; have l7 := hp.l7; have l8 := hp.l8
  have hbig : 2 * β ≤ Z := hp.big
  have hbig2 : 2 * (16 * m + 12 * k + 3 * sw + 23 + (320 * m + 191 * k + 403) + 1) ≤ Z := hbig
  have hβ : β = pP k m sw + kK k m + 1 := rfl
  have hlen : lenL k m = 2 * k + 3 + 3 * m := rfl
  have hZW : Z ≤ W := by omega
  have hkN : k ≤ N := by have := card_le_univ C; simpa using this
  have hq : ∀ d : G.Dart, d.fst ∈ C →
      ((fun g => 0 < labV C (tlG G (rvG G g))) (dartNum G d) ↔ d.snd ∈ C) :=
    fun d h => labV_hq G C d h
  have hmp : m ≤ psum (gofs G) (lv C) k := by
    have := cntB_lv_card G C (fun g => 0 < labV C (tlG G (rvG G g))) hq
    rw [hk] at this
    rw [hmdef, mI, ← this]
    exact cntB_le_psum _ _ _ _
  have hlenβ : 2 * k + 3 + 3 * m + 2 ≤ β := by rw [hβ]; unfold pP kK; omega
  have hlvN : ∀ j < k, lv C j < N := fun j hj => lv_lt C (by omega)
  have hlinc : ∀ i j, i < j → j < k → lv C i < lv C j := fun i j h hj => lv_inc C i j h (by omega)
  have hN := nwfG G R
  have hD : ∀ r, (r < 1000 ∨ Kept r) → d.nreg r = c.nreg r := hs.regs
  -- the layout block
  obtain ⟨d₄, t₄, e₄, hw₄, sp, ht₄⟩ := setupB_exec (P := P) hs.wb (k := k) (m := m) (sw := sw)
    (by rw [hD 1001 (Or.inr (Or.inl rfl)), hp.one]) (by rw [hD 1016 (by unfold Kept; omega), hp.kk])
    hs.m' hs.sw (by omega)
  have R4 : ∀ r, (r < 1000 ∨ Kept r) → d₄.nreg r = c.nreg r := fun r hr => by
    rw [sp.regs r (by unfold Kept at hr; omega), hD r hr]
  have M4 : ∀ a, β + 2 * k + 3 ≤ a → d₄.nmem a = d.nmem a := fun a ha =>
    sp.mo a (by omega) (by omega) (by omega)
  -- the memory of `d` above `Z`
  have Dm : ∀ a, Z ≤ a → (a < aLab ∨ aLab + N ≤ a) → (a < aRk ∨ aRk + nD G ≤ a) →
      d₄.nmem a = c.nmem a := fun a h1 h2 h3 => by
    rw [M4 a (by omega), hs.rest a h1 h2 h3]
  -- the second rank pass
  obtain ⟨d₅, t₅, e₅, ht₅, -, -, hO₅, hW₅, hrk₅, hfr₅⟩ := rankLoop_exec (P := P) hw₄
    (N := N) (M := nD G) (k := k) (lv C) (gofs G) (tlG G) (rvG G) (SepProg.wI w) (labV C)
    (by rw [R4 1001 (Or.inr (Or.inl rfl)), hp.one])
    (by rw [R4 1016 (by unfold Kept; omega), hp.kk])
    (fun j hj => by
      rw [R4 1015 (by unfold Kept; omega), Dm _ (by omega) (by omega) (by omega)]
      exact hp.L j hj) hlvN hlinc
    (fun v hv => by
      rw [R4 1010 (by unfold Kept; omega), Dm _ (by omega) (by omega) (by omega)]
      exact hp.ofs v hv) (gofs_mono G) (gofs_le G N)
    (fun v hv => by
      rw [R4 1014 (by unfold Kept; omega), Dm _ (by omega) (by omega) (by omega)]
      exact hp.wt v hv)
    (fun g hg => by
      rw [R4 1012 (by unfold Kept; omega), Dm _ (by omega) (by omega) (by omega)]
      exact ⟨hp.rv g hg, hN.rv_lt g hg⟩)
    (fun g hg => by
      rw [R4 1011 (by unfold Kept; omega), Dm _ (by omega) (by omega) (by omega)]
      exact ⟨hp.tl g hg, hN.tl_lt g hg⟩)
    (fun x hx => by
      rw [R4 1017 (by unfold Kept; omega), M4 _ (by omega)]; exact hs.lab x hx)
    (by rw [sp.r50, sp.r51]; omega)
    (by rw [sp.r51, R4 1010 (by unfold Kept; omega)]; omega)
    (by rw [R4 1010 (by unfold Kept; omega), R4 1011 (by unfold Kept; omega)]; omega)
    (by rw [R4 1011 (by unfold Kept; omega), R4 1012 (by unfold Kept; omega)]; omega)
    (by rw [R4 1012 (by unfold Kept; omega), R4 1014 (by unfold Kept; omega)]; omega)
    (by rw [R4 1014 (by unfold Kept; omega), R4 1015 (by unfold Kept; omega)]; omega)
    (by rw [R4 1015 (by unfold Kept; omega), R4 1017 (by unfold Kept; omega)]; omega)
    (by rw [R4 1017 (by unfold Kept; omega), R4 1018 (by unfold Kept; omega)]; omega)
    (by rw [R4 1018 (by unfold Kept; omega)]; omega)
    (by rw [← hk, wsum_lv C w]; omega)
  rw [sp.r50] at hO₅
  rw [sp.r51] at hW₅
  rw [R4 1018 (by unfold Kept; omega)] at hrk₅
  rw [sp.r50, sp.r51, R4 1018 (by unfold Kept; omega)] at hfr₅
  have R5 : ∀ r, (r < 1000 ∨ Kept r) → d₅.nreg r = c.nreg r := fun r hr => by
    rw [nreg_of_scr e₅ (by decide) (by unfold Kept at hr; omega), R4 r hr]
  have M5 : ∀ a, (a < β + 2 ∨ β + 2 * k + 3 ≤ a) → (a < aRk ∨ aRk + nD G ≤ a) →
      d₅.nmem a = d₄.nmem a := fun a h1 h2 => hfr₅ a (fun j hj => ⟨by omega, by omega,
        fun g hg1 hg2 _ => by have := gofs_le G (lv C j + 1); omega⟩)
  have rk₅ : ∀ g < nD G, d₅.nmem (aRk + g) = rkA G C g := by
    refine rk_after G C _ hq aRk d₅.nmem d₄.nmem
      (fun j hj g h1 h2 hq' => hrk₅ j (by omega) g h1 h2 hq')
      (fun g hg hne => hfr₅ _ (fun j hj => ⟨by omega, by omega,
        fun g' h1 h2 h3 => by have := hne j (by omega) g' h1 h2 h3; omega⟩))
      (fun g hg hin => by
        rw [M4 _ (by omega), hs.rk g hg]; simp [rkA, hin])
  -- the dart pass
  obtain ⟨d₆, t₆, e₆, ht₆, hD₆, hfr₆⟩ := dartLoop_exec (P := P) e₅.wb_right (N := N) (M := nD G)
    (k := k) (m' := m) (Δ := Δ) (lv C) (gofs G) (rkA G C) (rvG G) (roG G R) (frA G C R)
    (by rw [R5 1001 (Or.inr (Or.inl rfl)), hp.one])
    (by rw [R5 1016 (by unfold Kept; omega), hp.kk])
    (fun j hj => by
      rw [R5 1015 (by unfold Kept; omega), M5 _ (by omega) (by omega),
        Dm _ (by omega) (by omega) (by omega)]
      exact hp.L j hj) hlvN hlinc
    (fun v hv => by
      rw [R5 1010 (by unfold Kept; omega), M5 _ (by omega) (by omega),
        Dm _ (by omega) (by omega) (by omega)]
      exact hp.ofs v hv) (gofs_mono G) (gofs_le G N)
    (fun x hx => by rw [R5 1018 (by unfold Kept; omega)]; exact rk₅ x hx)
    (fun x hx => by
      rw [R5 1013 (by unfold Kept; omega), M5 _ (by omega) (by omega),
        Dm _ (by omega) (by omega) (by omega)]
      exact hp.ro x hx)
    (fun g hg _ => by
      rw [R5 1012 (by unfold Kept; omega), M5 _ (by omega) (by omega),
        Dm _ (by omega) (by omega) (by omega)]
      exact ⟨hp.rv g hg, hN.rv_lt g hg⟩)
    (fun g _ => rkA_le G C g) (rkA_hfr G C R hΔ) (rkA_inj G C)
    (by rw [Exec.nreg_of_wr e₅ (r := 1052) (by decide), sp.r52, R5 1010 (by unfold Kept; omega)]
        omega)
    (by rw [R5 1010 (by unfold Kept; omega), R5 1012 (by unfold Kept; omega)]; omega)
    (by rw [R5 1012 (by unfold Kept; omega), R5 1013 (by unfold Kept; omega)]; omega)
    (by rw [R5 1013 (by unfold Kept; omega), R5 1015 (by unfold Kept; omega)]; omega)
    (by rw [R5 1015 (by unfold Kept; omega), R5 1018 (by unfold Kept; omega)]; omega)
    (by rw [R5 1018 (by unfold Kept; omega)]; omega)
  rw [Exec.nreg_of_wr e₅ (r := 1052) (by decide), sp.r52] at hD₆ hfr₆
  have M6 : ∀ a, (a < β + 2 * k + 3 ∨ β + 2 * k + 3 + 3 * m ≤ a) → d₆.nmem a = d₅.nmem a :=
    fun a h => hfr₆ a h
  have hfront : Exec P W front2 d d₆ (t₄ + (t₅ + t₆)) := .seq e₄ (.seq e₅ e₆)
  -- the words
  have hdata : ∀ i < Z - β, d₆.nmem (β + i) = (ltIn R (ord N) C w).data.getD i 0 := by
    refine data_eq G R w C (fun i => d₆.nmem (β + i)) (Z - β) ?_ ?_ (fun j hj => ?_) ?_
      (fun j hj => ?_) (fun j hj g h1 h2 hp' => ?_) (fun i hi hiZ => ?_)
    · show d₆.nmem (β + 0) = k
      rw [Nat.add_zero, M6 _ (by omega), M5 _ (by omega) (by omega)]; exact sp.m0
    · show d₆.nmem (β + 1) = m
      rw [M6 _ (by omega), M5 _ (by omega) (by omega)]; exact sp.m1
    · show d₆.nmem (β + (2 + j)) = _
      rw [M6 (β + (2 + j)) (by omega), show β + (2 + j) = β + 2 + j by omega, hO₅ j hj]
      exact cntB_lv G C (fun g => 0 < labV C (tlG G (rvG G g))) hq j (by omega)
    · show d₆.nmem (β + (2 + k)) = m
      rw [M6 _ (by omega), show β + (2 + k) = β + 2 + k by omega,
        hfr₅ _ (fun j hj => ⟨by omega, by omega, fun g hg1 hg2 _ => by omega⟩)]
      exact sp.m2
    · show d₆.nmem (β + (k + 3 + j)) = _
      rw [M6 _ (by omega), show β + (k + 3 + j) = β + k + 3 + j by omega, hW₅ j hj]
    · obtain ⟨f0, f1, f2⟩ := hD₆ j hj g h1 h2 hp'
      simp only [Nat.add_assoc] at f0 f1 f2 ⊢
      exact ⟨f0, f1, f2⟩
    · show d₆.nmem (β + i) = 0
      rw [hlen] at hi
      rw [M6 (β + i) (by omega), M5 (β + i) (by omega) (by omega),
        sp.mo (β + i) (by omega) (by omega) (by omega)]
      exact hs.zero _ (by omega)
  have hβ' : bB #C (mI G C) (∑ v ∈ C, w v) = β := rfl
  refine ⟨d₆, _, hfront, ?_, ⟨e₆.wb_right, fun r hr => ?_, ?_, ?_, ?_, ?_, fun a ha => ?_,
    fun i hi => hdata i (by omega), fun x hx => ?_, fun g hg => ?_, fun a h1 h2 h3 => ?_,
    ?_, ?_, ?_⟩⟩
  · have : (6 * Δ + 36) * psum (gofs G) (lv C) k =
        (6 * Δ + 22) * psum (gofs G) (lv C) k + 14 * psum (gofs G) (lv C) k := by ring
    omega
  · rw [nreg_of_scr e₆ (by decide) (by unfold Kept at hr; omega), R5 r hr]
  · rw [Exec.nreg_of_wr e₆ (r := 1060) (by decide), Exec.nreg_of_wr e₅ (r := 1060) (by decide)]
    exact sp.r60
  · rw [Exec.nreg_of_wr e₆ (r := 1064) (by decide), Exec.nreg_of_wr e₅ (r := 1064) (by decide)]
    exact sp.r64
  · rw [Exec.nreg_of_wr e₆ (r := 1062) (by decide), Exec.nreg_of_wr e₅ (r := 1062) (by decide)]
    exact sp.r62
  · rw [Exec.nreg_of_wr e₆ (r := 1063) (by decide), Exec.nreg_of_wr e₅ (r := 1063) (by decide)]
    exact sp.r63
  · rw [M6 a (by omega), M5 a (by omega) (by omega), sp.mo a (by omega) (by omega) (by omega)]
    exact hs.zero _ (by omega)
  · rw [M6 (aLab + x) (by omega), M5 (aLab + x) (by omega) (by omega), M4 (aLab + x) (by omega)]
    exact hs.lab x hx
  · rw [M6 (aRk + g) (by omega)]; exact rk₅ g hg
  · rw [M6 a (by omega), M5 a (by omega) h3, Dm a h1 h2 h3]
  · rw [Exec.output_of_ou hfront (by decide)]; exact hs.out
  · rw [(Exec.real_of_noReal hfront (by decide)).1]; exact hs.rr
  · rw [(Exec.real_of_noReal hfront (by decide)).2]; exact hs.rm

end Piece

end PlanarSeparator
