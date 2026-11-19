module

public import PlanarFlow.BKMNW.NcTop

/-!
# `s2cP` and its specification `S2CPSpecN''`

`s2c U g π H = −(c2s (U ∘ rev) (−g) π H)` (`s2c_machNFT`, `rfl`). **`s2cP fzP pbP = hdF ; hdCs ;
(tgN ; ngL) ; (gaGl ; lgProg) ; c2cP fzP pbP ; (tgN ; ngL)`**: the frame block, the capacity base
`b`, `FL := 2Z − FL` (so `FL = Z + (−g)`), the gather `CPg[t] = CP[RV t]` (`U ∘ rev`) at `b`, the
core on the mirrored problem, `FL := 2Z − FL`.

**`s2cP_spec`**: `S2CPSpecN'' M (machNFT gid I (pchCall gid)) Reach gid u S T Z I W Wz wzc
(s2cP fzP pbP) (s2cT fzT pbT) rO` under the hypotheses of `c2sP_spec`, with
`s2cT fzT pbT x j i = c2sT fzT pbT x j i + 2 (11 m + 14) + (9 m + 8)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall STFlow OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

universe w

/-- **The program of SingleSourceToCycleLimitedMaxFlow** with the parameter programs. -/
def s2cP (fzP pbP : Stmt) : Stmt :=
  .seq hdF (.seq hdCs (.seq (.seq tgN ngL) (.seq (.seq gaGl lgProg)
    (.seq (c2cP fzP pbP) (.seq tgN ngL)))))

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The step function of `s2cP`.** -/
noncomputable def s2cT (fzT pbT : MCall M → ℕ → ℕ) (x : MCall M) (j i : ℕ) : ℕ :=
  c2sT fzT pbT x j i + 2 * (11 * (pdarts M x.1.piece x.2.1).card + 14) +
    (9 * (pdarts M x.1.piece x.2.1).card + 8)

set_option maxHeartbeats 8000000 in
/-- **`s2cP` meets `S2CPSpecN''`** relative to the machine's family `machNFT gid I (pchCall gid)`,
with the zero-area function `wzc`, given the parameter programs' specifications. -/
theorem s2cP_spec {Reach : MCall M → Prop} {I : Input} {W Wz : ℕ} {fzP pbP : Stmt}
    {fzT pbT : MCall M → ℕ → ℕ} {fzR pbR : ℕ → ℕ} {rO : MCall M → ℕ}
    (hfz : FzPSpec M gid u S T Z I W fzP fzT fzR) (hpb : PbPSpec M gid u S T Z I W pbP pbT pbR)
    (hgid : Injective gid) (hu0 : ∀ d, 0 ≤ u d)
    (hrO : ∀ x, c2sRoom fzR pbR (pdarts M x.1.piece x.2.1).card Z ≤ rO x) :
    S2CPSpecN'' M (machNFT gid I (pchCall gid)) Reach gid u S T Z I W Wz wzc (s2cP fzP pbP)
      (s2cT fzT pbT) rO := by
  intro l r π Hs σ h d e b m en j i πj H hReach hok hde heb hW oD hWz hj hH hh c hpre hL hFLs hc
    r04 r05 r06
  obtain ⟨⟨⟨r00, r02⟩, hz⟩, hSeg⟩ := hpre
  set C := xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h with hC
  set g := C.c2s j πj i H with hgd
  have hHmem : H ∈ sHoles (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs)
      (segsP h.1 π.segs h.2) j := List.mem_of_getElem? hH
  obtain ⟨y₀, -⟩ := sHoles_nonempty h.1 (segsP h.1 π.segs h.2) j hHmem
  have hm : 0 < m := by
    obtain ⟨i, hi, -⟩ := hL.en_surj y₀.1 y₀.2; omega
  have hmc := lay_card' h.1 hL hm
  have hRm := hrO (.node l r π, Hs, σ)
  rw [← hmc] at hRm
  unfold c2sRoom at hRm
  have hfr : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  have w3 := wzQ_room hWz (by omega : Wz < W)
  have w4 := stRm_ge (m := m) (by omega)
  obtain ⟨hpl, hrot, hft⟩ := lay_plane h.1 hok hL hm
  have hinj : ∀ a ∈ pdarts M (l.piece ∪ r.piece) Hs, ∀ b ∈ pdarts M (l.piece ∪ r.piece) Hs,
      gid a = gid b → a = b := fun a _ b _ e => hgid e
  -- the capacities
  have hU : ∀ y, 0 ≤ C.U y ∧ C.U y ≤ Z := fun y => by
    obtain ⟨t, ht, e⟩ := hL.en_surj y.1 y.2
    have := (hL.cp t ht)
    refine ⟨hu0 _, ?_⟩
    show u y.1 ≤ Z
    rw [← e, ← this.1]; exact_mod_cast this.2
  have hUZ : ∀ y, C.U y ≤ (Z : ℤ) := fun y => (hU y).2
  have hgb := pseudo_bound hh.pseudo hUZ
  -- the frame block
  obtain ⟨c₁, k₁, e₁, hk₁, hR₁, K₁, m₁, rr₁, rm₁, o₁⟩ := hdF_exec (P := I) c hc r04 r06 hL.hm hL.hz
    hfr (by omega) (by omega) w3 (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, a30, K₂, m₂, rr₂, rm₂, o₂⟩ := hdCs_exec (P := I) c₁ e₁.wb_right
  have hR₂ : HdRegs c₂ d b m Z := hR₁.congr fun r hr => K₂ r (by omega)
  have q₂ : ∀ r, r < 9813 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [K₂ r (by omega), K₁ r (Or.inl hr)]
  have mem₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  -- `FL := 2Z − FL`
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, f₃, g₃, -, -, rr₃, rm₃, o₃⟩ := negFL_exec (P := I) c₂ e₂.wb_right
    hR₂.r16 hR₂.r18 hR₂.r19 (by omega) hm
  have K₃ : ∀ r, (r < 9790 ∨ (9799 ≤ r ∧ r < 9820) ∨ 9822 < r) → c₃.nreg r = c₂.nreg r :=
    fun r hr => g₃ r (by unfold ArScr; omega)
  have hR₃ : HdRegs c₃ d b m Z := hR₂.congr fun r hr => K₃ r (by omega)
  -- the gather `CPg[t] = CP[RV t]`
  obtain ⟨c₄, k₄, e₄, hk₄, b10, b11, b12, b13, K₄, m₄, rr₄, rm₄, o₄⟩ := gaGl_exec (P := I) c₃
    e₃.wb_right
  rw [hR₃.r32] at b10; rw [hR₃.r74] at b11; rw [hR₃.r78] at b12; rw [hR₃.r34] at b13
  have mem₃ : ∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a) → c₃.nmem a = c.nmem a :=
    fun a ha => by rw [f₃ a ha, mem₂]
  have hRV : ∀ t < m, c₄.nmem (d + 4 + m + t) < m := fun t ht => by
    rw [m₄, mem₃ _ (by omega)]; exact (hL.rv t ht).1
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅, g₅, rr₅, rm₅, o₅⟩ := lgProg_exec (P := I) c₄ e₄.wb_right
    b10 b11 b12 b13 (by omega) (by omega) (by omega)
    (fun t ht => by have := hRV t ht; omega)
    (fun t ht => by omega) (fun t ht => by have := hRV t ht; omega)
  have K₅ : ∀ r, (r < 6210 ∨ 6217 < r) → c₅.nreg r = c₃.nreg r := fun r hr => by
    rw [g₅ r (by omega), K₄ r (by omega)]
  have hR₅ : HdRegs c₅ d b m Z := hR₃.congr fun r hr => K₅ r (by omega)
  have mem₅ : ∀ a, (a < b ∨ b + m ≤ a) → c₅.nmem a = c₃.nmem a := fun a ha => by
    rw [f₅ a (by omega), m₄]
  have q₅ : ∀ r, r < 6210 → c₅.nreg r = c.nreg r := fun r hr => by
    rw [K₅ r (by omega), K₃ r (by omega), q₂ r (by omega)]
  have q₅' : ∀ r, 6800 ≤ r → r ≤ 6819 → c₅.nreg r = c.nreg r := fun r h1 h2 => by
    rw [K₅ r (by omega), K₃ r (by omega), q₂ r (by omega)]
  -- the frame and the mirrored arrays at `c₅`
  have hL₅ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₅.nmem :=
    hL.congr fun a h1 h2 => by rw [mem₅ a (by omega), mem₃ a (by omega)]
  have hSeg₅ : SegsAt' M en m π e b c₅ := by
    unfold SegsAt' at hSeg ⊢
    rw [q₅' 6807 (by omega) (by omega)]
    exact hSeg.congr fun a h1 h2 => by
      rw [mem₅ a (by omega), mem₃ a (by unfold fsz at hde; have := hSeg.1.1; omega)]
  have hz₅ : MemZ Wz c₅ := fun a ha => by rw [mem₅ a (by omega), mem₃ a (by omega)]; exact hz a ha
  have hFL₅ : ∀ t < m, (c₅.nmem (d + 4 + 6 * m + t) : ℤ) =
      Z + -(g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t)) := fun t ht => by
    have h1 : (c.nmem (d + 4 + 6 * m + t) : ℤ) =
        Z + g (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t) :=
      (hFLs t ht).trans (congrArg (fun z => (Z : ℤ) + z) ((fext_mem _ (hL.en_mem t ht)).trans
        (congrArg _ (Subtype.ext (layEn_val ht).symm))))
    have h2 := hgb (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t)
    have e5 : c₅.nmem (d + 4 + 6 * m + t) = 2 * Z - c.nmem (d + 4 + 6 * m + t) := by
      rw [mem₅ _ (Or.inl (by omega)), v₃ t ht, mem₂]
    rw [e5]
    omega
  have hCP₅ : ∀ t < m, (c₅.nmem (b + t) : ℤ) =
      (fun y => C.U ((pmap h.1).rev y))
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t) := fun t ht => by
    have hr := hL.rv t ht
    have e0 : c₄.nmem (d + 4 + m + t) = c.nmem (d + 4 + m + t) := by
      rw [m₄]; exact mem₃ _ (Or.inl (by omega))
    rw [v₅ t ht, e0, m₄, mem₃ _ (Or.inl (by have := hr.1; omega)), (hL.cp _ hr.1).1, hr.2]
    show u (M.rev (en t)) = u ((pmap h.1).rev (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m
      hL₅.en_mem hm t)).1
    exact congrArg u ((congrArg M.rev (layEn_val ht).symm).trans (pmap_rev h.1 _).symm)
  have hU' : ∀ y, 0 ≤ C.U ((pmap h.1).rev y) ∧ C.U ((pmap h.1).rev y) ≤ Z := fun y => hU _
  -- the core on the mirrored problem
  obtain ⟨c₆, k₆, e₆, hk₆, v₆, z₆, f₆, g₆, o₆⟩ := c2cP_exec (I := I) (W := W) hfz hpb h hok hinj
    hm hj hH (HoleS2C.mirror hh) hU' c₅ e₅.wb_right hL₅ hSeg₅ hde heb hz₅ oD hWz hFL₅ hCP₅ hR₅
    (by rw [K₅ 9830 (by omega), K₃ 9830 (by omega), a30]; exact hR₁.r34)
    (by rw [q₅ 3004 (by omega)]; exact r04) (by rw [q₅ 3005 (by omega)]; exact r05)
    (by rw [q₅ 3006 (by omega)]; exact r06) (by rw [q₅' 6800 (by omega) (by omega)]; exact r00)
    (by rw [q₅' 6802 (by omega) (by omega)]; exact r02)
    (by omega) (Or.inl le_rfl) (by omega) (by omega) (by omega) (by omega)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose_spec)
  -- the bound of the mirrored `c2s`
  have hmssp : MSSPSpecAt (pmap h.1) (Klein.msspPlaneK (pmap h.1)) πj :=
    fun ℓ hℓ x hx => Klein.msspPlaneK_spec hpl hrot hft πj ℓ hℓ x hx
  obtain ⟨hxT, hTT, hstT, hokT⟩ := stFlowT_eq gid I (.node l r π, Hs, σ) h.1 hpl hrot hinj
  have hparts := c2sParts hpl (pushSpec_pchCall gid (.node l r π, Hs, σ) h.1 hpl)
    (fun y => (hU' y).1) (fun y => (hU' y).2) (HoleS2C.mirror hh) hmssp (frRef_spec _)
    (negLay_spec gid I (.node l r π, Hs, σ) h.1) (hstT ▸ STFlow.StChoice.spec hpl hokT)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose_spec)
  have hcb : ∀ y, -(Z : ℤ) ≤ C.O.c2s (fun y => C.U ((pmap h.1).rev y)) (-g) πj H y ∧
      C.O.c2s (fun y => C.U ((pmap h.1).rev y)) (-g) πj H y ≤ Z := fun y =>
    (hparts y).2.2.2.2.2.2
  -- `FL := 2Z − FL`
  have kk₆ : ∀ r, 9816 ≤ r → r ≤ 9819 → c₆.nreg r = c₅.nreg r := fun r h1 h2 =>
    g₆ r (Or.inr (Or.inr ⟨h1, h2⟩))
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, f₇, g₇, -, -, rr₇, rm₇, o₇⟩ := negFL_exec (P := I) c₆ e₆.wb_right
    (m := m) (d := d) (Z := Z) (by rw [kk₆ 9816 (by omega) (by omega)]; exact hR₅.r16)
    (by rw [kk₆ 9818 (by omega) (by omega)]; exact hR₅.r18)
    (by rw [kk₆ 9819 (by omega) (by omega)]; exact hR₅.r19) (by omega) hm
  have eT : tailT fzT pbT (.node l r π, Hs, σ) j = 12 + stCostZ m (4 * pcoreB
      (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
      (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
      10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
      (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) := by
    rw [tailT, ← hmc]
    exact rfl
  have eC : s2cT fzT pbT (.node l r π, Hs, σ) j i =
      68 + hdCost m + tailT fzT pbT (.node l r π, Hs, σ) j + 2 * (11 * m + 14) + (9 * m + 8) := by
    rw [s2cT, c2sT, ← hmc]
  refine ⟨c₇, k₁ + (k₂ + (k₃ + ((k₄ + k₅) + (k₆ + k₇)))),
    e₁.seq (e₂.seq (e₃.seq ((e₄.seq e₅).seq (e₆.seq e₇)))), ?_, fun r hr => ?_,
    fun a h1 h2 => ?_, ?_, fun t ht => ?_⟩
  · rw [eC, eT]; omega
  · rw [g₇ r (by unfold ArScr; omega), g₆ r (hr.elim Or.inl (fun h' => Or.inr (Or.inl h'))),
      K₅ r (by omega), K₃ r (by omega), q₂ r (by omega)]
  · have h2' : a < d + 4 + 6 * m ∨ d + 4 + 6 * m + m ≤ a := by omega
    obtain ⟨x1, x2⟩ := f₆ a h1 h2'
    refine ⟨?_, by rw [rm₇, x2, rm₅, rm₄, rm₃, rm₂, rm₁]⟩
    rw [f₇ a h2', x1, mem₅ a (Or.inl h1), mem₃ a h2']
  · rw [o₇, o₆, o₅, o₄, o₃, o₂, o₁]
  · have hv := v₇ t ht
    have h6 : (c₆.nmem (d + 4 + 6 * m + t) : ℤ) = Z + C.O.c2s (fun y => C.U ((pmap h.1).rev y))
        (-g) πj H (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t) := v₆ t ht
    have hb := hcb (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t)
    have e2 : fext (B := pdarts M (l.piece ∪ r.piece) Hs)
        (C.O.s2c C.U (C.c2s j πj i H) πj H) (en t) =
        -(C.O.c2s (fun y => C.U ((pmap h.1).rev y)) (-g) πj H
          (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₅.en_mem hm t)) :=
      (fext_mem _ (hL.en_mem t ht)).trans (congrArg (fun z => -z)
        (congrArg (C.O.c2s (fun y => C.U ((pmap h.1).rev y)) (-g) πj H)
          (Subtype.ext (layEn_val ht).symm)))
    show (c₇.nmem (d + 4 + 6 * m + t) : ℤ) = Z + fext (B := pdarts M (l.piece ∪ r.piece) Hs)
      (C.O.s2c C.U (C.c2s j πj i H) πj H) (en t)
    rw [e2, hv]
    omega

end NcStep

end BKMNW

end PlanarFlow
