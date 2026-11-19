module

public import PlanarFlow.BKMNW.NcCore
public import PlanarFlow.BKMNW.ThSpec

/-!
# `c2sP` and its specification `C2SPSpecN''`

**`c2sP fzP pbP = hdF ; hdCc ; c2cP fzP pbP`**: the frame block (`m`, `Z`, `b`, the bases, the
zero-area base `ib = wzQ m Z + 339 m + 128`), the frame's capacities as `CPb`, the core.

**`c2sP_spec`**: given `FzPSpec`, `PbPSpec`, `Injective gid`, `0 ≤ u` and the room
`c2sRoom fzR pbR m Z ≤ rO x` (`m` the darts of the piece), `c2sP fzP pbP` meets
**`C2SPSpecN'' M (machNFT gid I (pchCall gid)) Reach gid u S T Z I W Wz wzc (c2sP fzP pbP)
(c2sT fzT pbT) rO`** with the zero-area function **`wzc m Z = 3 (m + Z + 100)^32`** and the step
function `c2sT fzT pbT x j i = 68 + hdCost m + 12 + stCostZ m (4 pcoreB … + 3) + 10 + (11m+4) +
(fzT x j + 4 + (11m+4)) + (pbT x j + 4 + (11m+4))`.
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

/-- **The program of CycleToSingleSinkLimitedMaxFlow** with the parameter programs `fzP`
(FixConservationOnPath with frozen vertices) and `pbP` (the push-back). -/
def c2sP (fzP pbP : Stmt) : Stmt := .seq hdF (.seq hdCc (c2cP fzP pbP))

/-- **The room of `c2sP` above `b`**: the head's arrays, the scratch of `stCallZ`, the scratch of
the parameter programs and `6 Z` (the words of the flows are below `6 Z`). -/
def c2sRoom (fzR pbR : ℕ → ℕ) (m Z : ℕ) : ℕ := 28 * m + 10 + stRm m + fzR m + pbR m + 6 * Z

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The step bound of the tail at a call with `m` darts. -/
noncomputable def tailT (fzT pbT : MCall M → ℕ → ℕ) (x : MCall M) (j : ℕ) : ℕ :=
  12 + stCostZ (pdarts M x.1.piece x.2.1).card
    (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
      (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) (pdarts M x.1.piece x.2.1).card
      (4 * (pdarts M x.1.piece x.2.1).card + 1) + 3) +
    10 + (11 * (pdarts M x.1.piece x.2.1).card + 4) +
    (fzT x j + 4 + (11 * (pdarts M x.1.piece x.2.1).card + 4)) +
    (pbT x j + 4 + (11 * (pdarts M x.1.piece x.2.1).card + 4))

/-- **The step function of `c2sP`.** -/
noncomputable def c2sT (fzT pbT : MCall M → ℕ → ℕ) (x : MCall M) (j i : ℕ) : ℕ :=
  68 + hdCost (pdarts M x.1.piece x.2.1).card + tailT fzT pbT x j

/-- The number of darts of the frame is that of the piece, when the frame has a dart. -/
lemma lay_card' {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) :
    m = (pdarts M x.1.piece x.2.1).card :=
  lay_card hP hl hm (pmap_faceTrans hP)

/-- The words of the frame block: `wzQ m Z + 339 m + 128 ≤ W` from the zero area. -/
lemma wzQ_room {m Z Wz W : ℕ} (hWz : wzc m Z ≤ Wz) (hW : Wz < W) :
    wzQ m Z + 339 * m + 128 ≤ W := by
  have h1 : 339 * m + 128 ≤ wzQ m Z := by
    unfold wzQ
    have hq : 100 ≤ wzq m Z := by unfold wzq; omega
    have h3 : 10000 * wzq m Z ≤ wzq m Z ^ 3 := by
      have : wzq m Z ^ 3 = wzq m Z * wzq m Z * wzq m Z := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have : 339 * m + 128 ≤ wzq m Z ^ 3 := by unfold wzq at hq h3 ⊢; omega
    exact this.trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold wzc at hWz; omega

/-- `stRm m ≥ 4·10⁹` for `1 ≤ m`. -/
lemma stRm_ge {m : ℕ} (hm : 1 ≤ m) : 4000000000 ≤ stRm m := by
  unfold stRm; have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity); omega

set_option maxHeartbeats 4000000 in
/-- **`c2sP` meets `C2SPSpecN''`** relative to the machine's family `machNFT gid I (pchCall gid)`,
with the zero-area function `wzc`, given the parameter programs' specifications. -/
theorem c2sP_spec {Reach : MCall M → Prop} {I : Input} {W Wz : ℕ} {fzP pbP : Stmt}
    {fzT pbT : MCall M → ℕ → ℕ} {fzR pbR : ℕ → ℕ} {rO : MCall M → ℕ}
    (hfz : FzPSpec M gid u S T Z I W fzP fzT fzR) (hpb : PbPSpec M gid u S T Z I W pbP pbT pbR)
    (hgid : Injective gid) (hu0 : ∀ d, 0 ≤ u d)
    (hrO : ∀ x, c2sRoom fzR pbR (pdarts M x.1.piece x.2.1).card Z ≤ rO x) :
    C2SPSpecN'' M (machNFT gid I (pchCall gid)) Reach gid u S T Z I W Wz wzc (c2sP fzP pbP)
      (c2sT fzT pbT) rO := by
  intro l r π Hs σ h d e b m en j i πj H hReach hok hde heb hW oD hWz hj hH hh c hpre hL hFLs hc
    r04 r05 r06
  obtain ⟨⟨⟨r00, r02⟩, hz⟩, hSeg⟩ := hpre
  -- `0 < m` and `m` is the number of darts of the piece
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
  -- the frame block
  obtain ⟨c₁, k₁, e₁, hk₁, hR₁, K₁, m₁, rr₁, rm₁, o₁⟩ := hdF_exec (P := I) c hc r04 r06 hL.hm hL.hz
    hfr (by omega) (by omega) w3 (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, a30, K₂, m₂, rr₂, rm₂, o₂⟩ := hdCc_exec (P := I) c₁ e₁.wb_right
  have hR₂ : HdRegs c₂ d b m Z := hR₁.congr fun r hr => K₂ r (by omega)
  have q₂ : ∀ r, r < 9813 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [K₂ r (by omega), K₁ r (Or.inl hr)]
  have mem₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  have hL₂ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₂.nmem := by rw [mem₂]; exact hL
  have hSeg₂ : SegsAt' M en m π e b c₂ := by
    unfold SegsAt' at hSeg ⊢; rw [q₂ 6807 (by omega), mem₂]; exact hSeg
  have hz₂ : MemZ Wz c₂ := fun a ha => by rw [mem₂]; exact hz a ha
  have hFL : ∀ t < m, (c₂.nmem (d + 4 + 6 * m + t) : ℤ) =
      Z + (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).hole j πj i
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm t) := fun t ht =>
    (congrArg (fun z : ℕ => (z : ℤ)) (congrFun mem₂ _)).trans ((hFLs t ht).trans
      (congrArg (fun z => (Z : ℤ) + z) ((fext_mem _ (hL.en_mem t ht)).trans
        (congrArg _ (Subtype.ext (layEn_val ht).symm)))))
  have hCP : ∀ t < m, (c₂.nmem (d + 4 + 3 * m + t) : ℤ) =
      (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).U
        (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm t) := fun t ht => by
    rw [show c₂.nmem (d + 4 + 3 * m + t) = c.nmem (d + 4 + 3 * m + t) from congrFun mem₂ _,
      (hL.cp t ht).1]
    show u (en t) = u (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL₂.en_mem hm t).1
    congr 1; exact (layEn_val ht).symm
  have hU : ∀ y, 0 ≤ (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).U y ∧
      (xCtxN M (machNFT gid I (pchCall gid)) u S T l r π Hs σ h).U y ≤ Z := fun y => by
    obtain ⟨t, ht, e⟩ := hL.en_surj y.1 y.2
    have := (hL.cp t ht)
    refine ⟨hu0 _, ?_⟩
    show u y.1 ≤ Z
    rw [← e, ← this.1]; exact_mod_cast this.2
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, z₃, f₃, g₃, o₃⟩ := c2cP_exec (I := I) (W := W) hfz hpb h hok
    (fun a _ b _ e => hgid e) hm hj hH hh hU c₂ e₂.wb_right hL₂ hSeg₂ hde heb hz₂ oD hWz hFL hCP
    hR₂ (by rw [a30]; exact hR₁.r78) (by rw [q₂ 3004 (by omega)]; exact r04)
    (by rw [q₂ 3005 (by omega)]; exact r05) (by rw [q₂ 3006 (by omega)]; exact r06)
    (by rw [q₂ 6800 (by omega)]; exact r00) (by rw [q₂ 6802 (by omega)]; exact r02)
    (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose)
    (fun v => (pmap_tail_surj (x := (.node l r π, Hs, σ)) h.1 v).choose_spec)
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), ?_, fun r hr => ?_, fun a h1 h2 => ?_, ?_,
    fun t ht => ?_⟩
  · have eT : tailT fzT pbT (.node l r π, Hs, σ) j = 12 + stCostZ m (4 * pcoreB
        (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))
        (SFace σ (pdarts M (l.piece ∪ r.piece) Hs) (revPerm M)) m (4 * m + 1) + 3) +
        10 + (11 * m + 4) + (fzT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) +
        (pbT (.node l r π, Hs, σ) j + 4 + (11 * m + 4)) := by
      rw [tailT, ← hmc]
      exact rfl
    have eC : c2sT fzT pbT (.node l r π, Hs, σ) j i =
        68 + hdCost m + tailT fzT pbT (.node l r π, Hs, σ) j := by
      rw [c2sT, ← hmc]
    rw [eC, eT]
    omega
  · rw [g₃ r (hr.elim Or.inl (fun h' => Or.inr (Or.inl h'))), q₂ r (by omega)]
  · obtain ⟨x1, x2⟩ := f₃ a h1 (by omega)
    exact ⟨by rw [x1, mem₂], by rw [x2, rm₂, rm₁]⟩
  · rw [o₃, o₂, o₁]
  · exact (v₃ t ht).trans (congrArg (fun z => (Z : ℤ) + z)
      ((congrArg _ (Subtype.ext (layEn_val ht))).trans (fext_mem _ (hL.en_mem t ht)).symm))

end NcStep

end BKMNW

end PlanarFlow
