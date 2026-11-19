module

public import PlanarFlow.BKMNW.LinRoot
public import PlanarFlow.BKMNW.MfCost

/-!
# The root frame of the max-flow driver from index arrays, and the whole program

* **`rfProg_root`**: for a root call `(τ, [], σ)` with `τ.piece = univ` (of `Reach`, with the
  invariants `CallOk`), and the darts enumerated by `en` (`gid (en i) = i`), from the index arrays
  `REV[i]` (index of `rev (en i)`), `SIG[i]` (index of `σ (en i)`), `CAP[i] = u (en i) ≤ Z`,
  `KR[i] = lrk S T ∅ (tail (en i))` and the tag `ntag τ`, `rfProg` writes `FInL` of the root call
  at `Hb + 5` and the driver's initial cells and registers, within `46 m + 80` steps.
* `lpreMap_hyps` (the preprocessed map without loops is plane with transitive rotations and faces
  when `M` has a dart that is not a loop), **`callOk_root`** (the invariants at the root call of
  the decomposition of the headline theorem).
* **`mfMain_cMach`**: **one fixed program** `rfProg ; driver mtProg mlProg (splitS sepP)
  (nodeSF stepP)` computes, from the index arrays of the preprocessed map, the root flow `arunL`
  (whose restriction is a maximum flow of `M`, `IsMax`) within
  `46 N + 80 + (headline with cMach) + 1000 (2 N + 1) + 2` steps; the remaining hypotheses are
  `SepPSpec sepP`, `StepPSpec stepP`, their costs (`sT m ≤ C m lg m`, `stT ≤ runsCharge`) and
  rooms, the tag `ntag τ` of the root, and the word bound.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

section Gen

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The root frame from index arrays** (see the module docstring). -/
theorem rfProg_root {I : Input} {W : ℕ} {Reach : MCall M → Prop} (τ : ADec M) (σ : Perm D)
    (hτ : τ.piece = univ) (hR : Reach (τ, [], σ)) (hok : CallOk M S T (τ, [], σ))
    {m REVb SIGb CAPb KRb Hb : ℕ} {en : ℕ → D} (hen : ∀ y, ∃ i < m, en i = y)
    (hgid : ∀ i < m, gid (en i) = i) (c : Config) (hc : WordsBounded W c)
    (r0 : c.nreg 6700 = m) (r1 : c.nreg 6701 = REVb) (r2 : c.nreg 6702 = SIGb)
    (r3 : c.nreg 6703 = CAPb) (r4 : c.nreg 6704 = KRb) (r5 : c.nreg 6705 = ntag τ)
    (r6 : c.nreg 6706 = Z) (r7 : c.nreg 6707 = Hb)
    (hrev : ∀ i < m, c.nmem (REVb + i) < m ∧ en (c.nmem (REVb + i)) = M.rev (en i))
    (hsig : ∀ i < m, c.nmem (SIGb + i) < m ∧ en (c.nmem (SIGb + i)) = σ (en i))
    (hcap : ∀ i < m, (c.nmem (CAPb + i) : ℤ) = u (en i) ∧ c.nmem (CAPb + i) ≤ Z)
    (hkr : ∀ i < m, c.nmem (KRb + i) = lrk S T (hunion []) (M.tail (en i)))
    (i1 : REVb + m ≤ Hb) (i2 : SIGb + m ≤ Hb) (i3 : CAPb + m ≤ Hb) (i4 : KRb + m ≤ Hb)
    (w : Hb + 9 + 7 * m ≤ W) :
    ∃ c' t, Exec I W rfProg c c' t ∧ t ≤ 46 * m + 80 ∧ WordsBounded W c' ∧
      c'.nreg 3000 = 0 ∧ c'.nreg 3001 = 1 ∧ c'.nreg 3002 = Hb ∧
      c'.nreg 3003 = Hb + 9 + 7 * m ∧ c'.nmem Hb = 0 ∧ c'.nmem (Hb + 1) = 0 ∧
      c'.nmem (Hb + 2) = Hb + 9 + 7 * m ∧
      FInL M Reach gid u S T Z (τ, [], σ) (Hb + 5) (Hb + 9 + 7 * m) c' ∧
      c'.output = c.output := by
  obtain ⟨c', t, ex, ht, b0, b1, b2, b3, b4, b5, b6, h0, h1, h2, h3, vg, vr, vs, vc, vk, vh, -,
    -, vo⟩ := rfProg_exec (P := I) c hc r0 r1 r2 r3 r4 r5 r6 r7 i1 i2 i3 i4 w
  have hB : pdarts M (τ, ([] : List (Finset V)), σ).1.piece (τ, ([] : List (Finset V)), σ).2.1 =
      univ := by
    show pdarts M τ.piece [] = univ
    rw [hτ, pdarts_univ_nil]
  refine ⟨c', t, ex, ht, ex.wb_right, b3, b4, b5, b6, b0, b1, b2,
    ⟨hR, hok, m, en, ?_, by unfold fsz; omega⟩, vo⟩
  exact {
    hm := h0
    hk := h1
    tag := h2
    hz := h3
    en_mem := fun i _ => by rw [hB]; exact mem_univ _
    en_surj := fun y _ => hen y
    en_mono := fun i j hij hj => by rw [hgid i (by omega), hgid j hj]; exact hij
    gd := fun i hi => by rw [vg i hi, hgid i hi]
    rv := fun i hi => by rw [vr i hi]; exact hrev i hi
    sg := fun i hi => by rw [vs i hi]; exact hsig i hi
    cp := fun i hi => by rw [vc i hi]; exact hcap i hi
    kr := fun i hi => by rw [vk i hi]; exact hkr i hi
    hl := fun i hi => by
      rw [vh i hi]
      simp [hlab, hunion] }

end Gen

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

open PlanarSeparator.StDart in
/-- **The preprocessed map without loops is plane with transitive rotations and faces**, and has a
dart, when `M` is plane with transitive rotations and faces and has a dart that is not a loop. -/
lemma lpreMap_hyps (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) : (lpreMap M).IsPlane ∧ (lpreMap M).RotTrans ∧
      (lpreMap M).FaceTrans ∧ Nonempty (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) := by
  have hP1 := nlMap_isPlane hM hrot hface hx₀
  have : Nonempty (SDart (nlDarts M)) := ⟨⟨x₀, hx₀⟩⟩
  have hP2 := triMap_isPlane hP1 nlMap_rotTrans nlMap_faceTrans
  exact ⟨CombMap.pendant_isPlane _ hP2, CombMap.pendant_rotTrans _ (triMap_rotTrans _),
    CombMap.pendant_faceTrans _ (triMap_faceTrans _), ⟨Sum.inl (old ⟨x₀, hx₀⟩)⟩⟩

/-- **The invariants at the root call** of a decomposition meeting `BalDecA` of the preprocessed
map without loops. -/
lemma callOk_root (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {S T : Finset _} {κ η s : ℕ} {τ : ADec (lpreMap M)}
    (hbal : BalDecA (lpreMap M) S T κ η s τ) :
    CallOk (lpreMap M) S T (τ, [], rotPerm (lpreMap M)) := by
  obtain ⟨hP, hr, hf, hD⟩ := lpreMap_hyps hM hrot hface hx₀
  obtain ⟨hall, hgood, hpg, hleaf, -⟩ := hbal
  have h0 : PieceInv (lpreMap M) τ.piece [] (rotPerm (lpreMap M)) := by
    rw [hall]; exact pieceInv_root hP hr hf hD
  exact ⟨ADec.PMOk.of_pieceInv τ [] _ List.Pairwise.nil hgood hpg h0, hgood, hpg, hleaf,
    by simp [hunion], by simp [hunion], List.Pairwise.nil⟩

/-- **The whole program** `rfProg ; driver mtProg mlProg (splitS sepP) (nodeSF stepP)` (see the
module docstring), with the machine subroutine costs `cMach C C₀`. -/
theorem mfMain_cMach (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) {C C₀ : ℕ} (hC : 68 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ} {sepP stepP : Stmt} {sT : ℕ → ℕ}
    {sR : ℕ → ℕ → ℕ} {stT rT : MCall (lpreMap M) → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    StepPSpec (lpreMap M) (planeOracles fun X => frRef X) Reach gid u' S' T' Z I W stepP stT rT →
    (∀ m, sT m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      stT (.node l r π, Hs, σ) ≤ runsCharge (lpreMap M) (cMach C C₀) l r π Hs σ) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rT x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 0 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb →
    Hb + 9 + 7 * N + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq rfProg (driver mtProg mlProg (splitS sepP) (nodeSF stepP))) c₀ c' t ∧
      t ≤ 46 * N + 80 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ u' S' T' Reach N hsep hstep hsT hstT hsR hrT REVb SIGb CAPb KRb en hen hgid hHb
    c₀ hc₀ r0 r1 r2 r3 r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀
    (cMach_bounds C C₀)
  have hok := callOk_root hM hrot hface hx₀ hbal
  have hW' : Hb + 9 + 7 * N ≤ W := le_trans (Nat.le_add_right _ _) hW
  obtain ⟨c₁, t₁, e₁, ht₁, hw₁, b0, b1, b2, b3, m0, m1, m2, hin, ho₁⟩ :=
    rfProg_root (I := I) (W := W) (Reach := Reach) (gid := gid) (u := u') (S := S') (T := T')
      (Z := Z) τ (rotPerm (lpreMap M)) hbal.1 (calls_self _ _ _) hok hen hgid c₀ hc₀ r0 r1 r2 r3
      r4 r5 r6 r7 hrev hsig hcap hkr i1 i2 i3 i4 hW'
  obtain ⟨hpc, c', t, ex, ht, hout, hmax⟩ := mfDriveFrame_cMach hM hrot hface hu hST e hsurj d₀
    hC hC₀ hZ hsep hstep hsT hstT hsR hrT hHb c₁ hw₁ b0 b1 b2 b3 m0 m1 m2 (by omega) le_rfl hW hin
  have ht' : t ≤ (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2 := ht
  exact ⟨hpc, c', t₁ + t, .seq e₁ ex, by omega, hout, hmax⟩

end Head

end MfDrv

end BKMNW

end PlanarFlow
