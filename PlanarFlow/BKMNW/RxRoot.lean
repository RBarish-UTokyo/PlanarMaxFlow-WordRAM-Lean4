module

public import PlanarFlow.BKMNW.RxProg2
public import PlanarFlow.BKMNW.MfRoot

/-!
# The root frame with its decomposition record

**`rfxProg_root`**: `rfProg ; rxProg` writes, from the index arrays of `rfProg_root` and two more
input arrays (`VT[i] = ν (tail (en i))`, `RT[i]` the index of `st (en i)` on the darts of the
piece map of the core, the bases in `mem (Hb - 1)`, `mem (Hb - 2)`), the extended frame `FInLX`
of the root call `(ds.dec S T univ [] st true, [], σ)` at `Hb + 5` (record of phase `0`, flag `1`)
and the driver's initial cells, within `95 N + 200` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

set_option maxHeartbeats 4000000 in
/-- **The root frame with its record** (see the module docstring). -/
theorem rfxProg_root {I : Input} {W : ℕ} {Reach : MCall M → Prop} (st σ : Perm D)
    (hτ : (ds.dec S T univ [] st true).piece = univ)
    (hR : Reach (ds.dec S T univ [] st true, [], σ))
    (hok : CallOk M S T (ds.dec S T univ [] st true, [], σ))
    {m REVb SIGb CAPb KRb VTb RTb Hb : ℕ} {en : ℕ → D} (hen : ∀ y, ∃ i < m, en i = y)
    (hgid : ∀ i < m, gid (en i) = i) (c : Config) (hc : WordsBounded W c)
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = REVb) (r2 : c.nreg 6702 = SIGb)
    (r3 : c.nreg 6703 = CAPb) (r4 : c.nreg 6704 = KRb)
    (r5 : c.nreg 6705 = ntag (ds.dec S T univ [] st true)) (r6 : c.nreg 6706 = Z)
    (r7 : c.nreg 6707 = Hb)
    (hrev : ∀ i < m, c.nmem (REVb + i) < m ∧ en (c.nmem (REVb + i)) = M.rev (en i))
    (hsig : ∀ i < m, c.nmem (SIGb + i) < m ∧ en (c.nmem (SIGb + i)) = σ (en i))
    (hcap : ∀ i < m, (c.nmem (CAPb + i) : ℤ) = u (en i) ∧ c.nmem (CAPb + i) ≤ Z)
    (hkr : ∀ i < m, c.nmem (KRb + i) = lrk S T (hunion []) (M.tail (en i)))
    (hv : c.nmem (Hb - 1) = VTb) (hrt : c.nmem (Hb - 1 - 1) = RTb)
    (hvt : ∀ i < m, c.nmem (VTb + i) = ν (M.tail (en i)))
    (hst : ∀ i < m, en i ∈ pdarts M (core M ds.Q univ) [] →
      c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = st (en i))
    (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb) (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb)
    (i5 : VTb + m ≤ Hb - 2) (i6 : RTb + m ≤ Hb - 2) (hHb : 2 ≤ Hb)
    (w : Hb + 5 + 4 + 7 * m + 1 + 3 + 7 * m ≤ W) :
    ∃ c' t, Exec I W (.seq rfProg rxProg) c c' t ∧ t ≤ 95 * m + 200 ∧ WordsBounded W c' ∧
      c'.nreg 3000 = 0 ∧ c'.nreg 3001 = 1 ∧ c'.nreg 3002 = Hb ∧
      c'.nreg 3003 = Hb + 5 + 4 + 7 * m + 1 + 3 + 7 * m ∧ c'.nmem Hb = 0 ∧
      c'.nmem (Hb + 1) = 0 ∧ c'.nmem (Hb + 2) = Hb + 5 + 4 + 7 * m + 1 + 3 + 7 * m ∧
      FInLX M ds Reach gid ν u S T Z (ds.dec S T univ [] st true, [], σ) (Hb + 5)
        (Hb + 5 + 4 + 7 * m + 1 + 3 + 7 * m) c' ∧
      c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin1, o1⟩ :=
    rfProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (u := u) (S := S) (T := T)
      (Z := Z) _ σ hτ hR hok hen hgid c hc r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4
      (by clear * - w; omega)
  -- the memory below `Hb` is kept by `rfProg` (`rfProg_exec`, by determinism)
  obtain ⟨c₀, t₁x, e₁x, -, -, -, -, -, -, -, -, -, -, -, -, gidj, -, -, -, -, -, kb, -, -⟩ :=
    rfProg_exec (P := I) c hc r0 r1 r2 r3 r4 r5 r6 r7 i1 i2 i3 i4 (by clear * - w; omega)
  have hcc := (Exec.det e₁x e₁).1
  rw [hcc] at kb gidj
  obtain ⟨-, -, m', en', hL, -⟩ := hin1
  have hcardD : (univ : Finset D).card = m := by
    have : (univ : Finset D) = (range m).image en := by
      ext y; simp only [mem_univ, mem_image, mem_range, true_iff]; exact hen y
    rw [this, card_image_of_injOn (fun i hi j hj e => by
      simp only [coe_range, Set.mem_Iio] at hi hj
      have h1 := hgid i hi; have h2 := hgid j hj; rw [e] at h1; omega), card_range]
  have hm : m' = m := by
    rw [hL.card]; show (pdarts M (ds.dec S T univ [] st true).piece []).card = m
    rw [hτ, pdarts_univ_nil, hcardD]
  subst hm
  have hN : c₁.nmem (Hb + 5) = m' := hL.hm
  obtain ⟨c₂, t₂, e₂, ht₂, z3, zH2, zp, zR0, zR1, zR2, zGP, zRP, zHP, zKP, zVP, zSP, zFX, zk, zr, zrr,
    zrm, zo⟩ := rxProg_exec (I := I) c₁ hw₁ b2 hN hHb
      (by rw [kb _ (by clear * - hHb; omega)]; exact hv)
      (by rw [kb _ (by clear * - hHb; omega)]; exact hrt) i5 i6 w
  have hL2 : Lay M gid u S T Z (ds.dec S T univ [] st true, [], σ) m' en' (Hb + 5) c₂.nmem :=
    hL.congr fun a h1 h2 => zk a (Or.inr ⟨by clear * - h1; omega, by clear * - h2; omega⟩)
  -- the enumerations agree
  have hee : ∀ i < m', en' i = en i := fun i hi => by
    have h1 := hL.gd i hi
    rw [gidj i hi] at h1
    obtain ⟨k, hk, hke⟩ := hen (en' i)
    have := hgid k hk
    rw [hke, ← h1] at this
    rw [← hke, this]
  have hp' : c₂.nmem (Hb + 5 + fsz m') = Hb + 5 + 4 + 7 * m' + 1 := by
    rw [show Hb + 5 + fsz m' = Hb + 5 + 4 + 7 * m' by unfold fsz; omega]; exact zp
  have hpc : (ds.dec S T univ [] st true, ([] : List (Finset V)), σ).1.piece = univ := hτ
  have hA : RArr M gid ν S T (ds.dec S T univ [] st true, [], σ) m' m' (Hb + 5 + 4 + 7 * m' + 1)
      en' c₂.nmem :=
    { g_mem := fun i _ => by rw [hpc]; exact mem_univ _
      g_surj := fun y _ => by
        obtain ⟨k, hk, rfl⟩ := hen y; exact ⟨k, hk, hee k hk⟩
      g_mono := hL.en_mono
      gp := fun i hi => by rw [zGP i hi]; have := hL.gd i hi; rwa [show Hb + 5 + 4 + i = Hb + 9 + i by omega] at this
      rp := fun i hi => by rw [zRP i hi]; have := hL.rv i hi; rwa [show Hb + 5 + 4 + m' + i = Hb + 9 + m' + i by omega] at this
      hp := fun i hi => by rw [zHP i hi]; have := hL.hl i hi; rwa [show Hb + 5 + 4 + 5 * m' + i = Hb + 9 + 5 * m' + i by omega] at this
      kp := fun i hi => by rw [zKP i hi]; have := hL.kr i hi; rwa [show Hb + 5 + 4 + 4 * m' + i = Hb + 9 + 4 * m' + i by omega] at this
      vp := fun i hi => by rw [zVP i hi, kb _ (by clear * - hi i5; omega), hvt i hi, hee i hi]
      fx := fun i hi => by rw [zFX i hi, show Hb + 9 + i = Hb + 5 + 4 + i by omega, gidj i hi]; exact hi
      fx_mem := fun i hi => by rw [zFX i hi, show Hb + 9 + i = Hb + 5 + 4 + i by omega, gidj i hi]; exact hL.en_mem i hi
      fx_surj := fun y hy => by
        obtain ⟨i, hi, rfl⟩ := hL.en_surj y hy
        exact ⟨i, hi, by rw [zFX i hi, show Hb + 9 + i = Hb + 5 + 4 + i by omega, gidj i hi]⟩
      fx_mono := fun i j hij hj => by
        rw [zFX i (by omega), zFX j hj, show Hb + 9 + i = Hb + 5 + 4 + i by omega,
          show Hb + 9 + j = Hb + 5 + 4 + j by omega, gidj i (by omega), gidj j hj]
        exact hL.en_mono i j hij hj }
  have hLR : LayR M ds gid ν S T (ds.dec S T univ [] st true, [], σ) m' m'
      (Hb + 5 + 4 + 7 * m' + 1) en' c₂.nmem := by
    refine ⟨zR0, by rw [zR1]; omega, by rw [zR2], ?_, fun _ => hA⟩
    rw [zR1, zR2]
    refine Or.inl ⟨rfl, st, ?_, fun i hi hi' => ?_⟩
    · show ds.dec S T univ [] st true = ds.dec S T (ds.dec S T univ [] st true).piece [] st
        (decide (1 = 1))
      rw [hτ]; rfl
    · rw [hpc, hee i hi] at hi'
      rw [zSP i hi, kb _ (by clear * - hi i6; omega), hee i hi]
      obtain ⟨a1, a2⟩ := hst i hi hi'
      refine ⟨a1, ?_⟩
      rw [hee _ a1]; exact a2
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, e₂.wb_right,
    by rw [zr 3000 (by decide)]; exact b0, by rw [zr 3001 (by decide)]; exact b1,
    by rw [zr 3002 (by decide)]; exact b2, z3, by rw [zk Hb (Or.inl (by omega))]; exact m0,
    by rw [zk (Hb + 1) (Or.inl (by omega))]; exact m1, zH2,
    ⟨hR, hok, m', en', m', en', hL2, by rw [hp']; unfold fsz; omega, ?_, by rw [hp']; exact hLR⟩,
    by rw [zo, o1]⟩
  rw [hp', zR1]; unfold rszL; simp; omega


end MfDrv

end BKMNW

end PlanarFlow
