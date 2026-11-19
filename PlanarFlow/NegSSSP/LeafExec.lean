module

public import PlanarFlow.NegSSSP.LeafRun

/-!
# The leaf of the driver on the frame: the run

**`leafS_exec`**: the field `leaf` of `NSpecR` for `leafS Gt` (`LeafRun.lean`), with the
invariant `GZ Hb Gt g.G` (reals zero, the numbering table zero), the inputs `InPR`, the outcome
`Res`, the room `rLf m k = 6k + 31m + 9` above the heap top and the cost
`lfCost m k w` (`w = #verts N P ≤ 2m`): `O(m²)` (Bellman–Ford, `w` rounds of `m` arcs) plus the
renormalization `O((m + w) log w)`. Global hypotheses: `|ℓ| ≤ L`, `Σ |ℓ| ≤ L`,
`8 (#D)² (L + 1) + 3L + 2 ≤ W`, the table below the heap.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- The room of the leaf above the heap top. -/
def rLf (m k : ℕ) : ℕ := 6 * k + 31 * m + 9

/-- The cost of the leaf. -/
def lfCost (m k w : ℕ) : ℕ :=
  20 + (25 * (2 * k) + 9) + 15 + lbCost m w w + 2 + 8 + (22 + rnCost m w + 6 + (7 * w + 2))

set_option maxHeartbeats 8000000 in
/-- **The leaf of the driver** (the field `leaf` of `NSpecR`). -/
theorem leafS_exec {ℓ : D → ℤ} {L Hb Gt : ℕ} (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |ℓ x| ≤ L) (hsumL : ∑ x, |ℓ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    {n : ℕ} {P : Finset D} {d e h : ℕ} {c : Config} (hg : GZ Hb Gt g.G c)
    (hc : WordsBounded W c) (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h)
    (b1 : Hb + 5 ≤ d) (b3 : e ≤ h) (hroom : h + rLf P.card (ck N P) ≤ W)
    (hin' : InPR g N ℓ L n P d e c) :
    ∃ c' t o, Exec I W (leafS Gt) c c' t ∧ t ≤ lfCost P.card (ck N P) (verts N P).card ∧
      GZ Hb Gt g.G c' ∧ RegKeep c c' ∧ HeapKeep Hb h d e c c' ∧ c'.output = c.output ∧
      PotOut (pg N P ℓ) o ∧ Res g N L P o d e c' := by
  obtain ⟨hPr, hin⟩ := hin'
  have he := hin.en
  unfold fsz at he
  have hmk := ck_ge (N := N) P
  have hk2 : ck N P ≤ 2 * P.card := card_rcl_le P
  have hhW : h ≤ W := r03 ▸ WordsBounded.nreg hc 3003
  have hmD : P.card ≤ Fintype.card D := card_le_univ _
  unfold rLf at hroom
  -- the registers
  obtain ⟨c₁, t₁, e₁, ht₁, s25, s26, s30, s31, s32, s75, s76, s77, s78, s79, sn₁, sm₁, sr₁,
    srm₁, so₁⟩ := lfSet_exec (I := I) Gt c hc r04 r03 hin.rm hin.rk hin.rL (by omega)
      (by omega) (by omega)
  have hw₁ := e₁.wb_right
  -- the numbering
  have hAv : ∀ i < 2 * ck N P, c₁.nmem (d + 3 * ck N P + 4 + i) < g.G := fun i hi => by
    rw [sm₁]
    by_cases hik : i < ck N P
    · rw [show d + 3 * ck N P + 4 + i = d + 4 + 3 * ck N P + i by omega, hin.gt i hik]
      exact g.gv_lt _
    · rw [show d + 3 * ck N P + 4 + i = d + 4 + 4 * ck N P + (i - ck N P) by omega,
        hin.gh _ (by omega)]
      exact g.gv_lt _
  obtain ⟨c₂, t₂, e₂, ht₂, w, ν, hwn, n82, hO, hlt, hI, hsurj, nm₂, nn₂, nr₂, nrm₂, no₂⟩ :=
    nmProg_exec (P := I) (nG := g.G) c₁ hw₁ s75 s76 s77 s78 s79 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hAv (fun a ha => by rw [sm₁]; exact hg.2.2 a ha)
  have hw₂ := e₂.wb_right
  obtain ⟨P1, P2, hwv⟩ := leaf_num (g := g) (N := N) (P := P)
    (A := fun i => c₁.nmem (d + 3 * ck N P + 4 + i))
    (Imem := fun v => c₂.nmem (h + 2 * ck N P + v)) (w := w) (ν := ν)
    (fun j hj => by
      simp only [sm₁]
      rw [show d + 3 * ck N P + 4 + j = d + 4 + 3 * ck N P + j by omega]; exact hin.gt j hj)
    (fun j hj => by
      simp only [sm₁]
      rw [show d + 3 * ck N P + 4 + (ck N P + j) = d + 4 + 4 * ck N P + j by omega]
      exact hin.gh j hj)
    hlt hI hsurj
  have hw2m : w ≤ 2 * P.card := hwv ▸ NTree.card_verts_le (N := N) P
  -- the arrays of the arcs
  have hT₂ : ∀ a < P.card, c₂.nmem (h + a) = ν (g.gv (N.tail (cδ g N P a))) := fun a ha => by
    rw [hO a (by omega), sm₁, show d + 3 * ck N P + 4 + a = d + 4 + 3 * ck N P + a by omega,
      hin.gt a (by omega)]
  have hH₂ : ∀ a < P.card, c₂.nmem (h + ck N P + a) = ν (g.gv (N.head (cδ g N P a))) :=
    fun a ha => by
      rw [Nat.add_assoc, hO _ (by omega), sm₁,
        show d + 3 * ck N P + 4 + (ck N P + a) = d + 4 + 4 * ck N P + a by omega,
        hin.gh a (by omega)]
  have hL₂ : ∀ a < P.card, c₂.nmem (d + 5 * ck N P + 4 + a) = (ℓ (cδ g N P a) + L).toNat :=
    fun a ha => by
      rw [nm₂ _ (by omega) (by omega), sm₁,
        show d + 5 * ck N P + 4 + a = d + 4 + 5 * ck N P + a by omega]
      exact hin.ln a ha
  -- products
  have p1 : w * P.card ≤ 2 * Fintype.card D * Fintype.card D := by
    have := Nat.mul_le_mul hw2m hmD
    have : 2 * P.card * Fintype.card D ≤ 2 * Fintype.card D * Fintype.card D :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have p2 : w * P.card * L ≤ 2 * Fintype.card D * Fintype.card D * L := Nat.mul_le_mul_right _ p1
  have p3 : 2 * Fintype.card D * Fintype.card D * L ≤
      8 * Fintype.card D * Fintype.card D * (L + 1) := by
    have : 2 * Fintype.card D * Fintype.card D * L ≤ 2 * Fintype.card D * Fintype.card D * (L + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have : 2 * Fintype.card D * Fintype.card D * (L + 1) ≤
        8 * Fintype.card D * Fintype.card D * (L + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have p4 : 2 * Fintype.card D * Fintype.card D ≤ 8 * Fintype.card D * Fintype.card D * (L + 1) := by
    have : 2 * Fintype.card D * Fintype.card D * 1 ≤ 8 * Fintype.card D * Fintype.card D * (L + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))) (by omega)
    omega
  have p5 : 4 * (2 * Fintype.card D * Fintype.card D * L) ≤
      8 * Fintype.card D * Fintype.card D * (L + 1) := by
    have : 8 * Fintype.card D * Fintype.card D * L ≤ 8 * Fintype.card D * Fintype.card D * (L + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have : 4 * (2 * Fintype.card D * Fintype.card D * L) = 8 * Fintype.card D * Fintype.card D * L :=
      by ring
    omega
  -- the registers of Bellman–Ford
  have k₂ : ∀ r, (r < 2880 ∨ 2886 < r) → c₂.nreg r = c₁.nreg r := nn₂
  obtain ⟨c₃, t₃, e₃, ht₃, q00, q01, q02, q03, q04, q05, q06, q07, q08, qn₃, qm₃, qr₃, qrm₃,
    qo₃⟩ := lbSet_exec (I := I) c₂ hw₂ (d := d) (h := h) (m := P.card) (k := ck N P) (L := L)
      (w := w)
      (by rw [k₂ _ (by omega), sn₁ _ (by omega)]; exact r04)
      (by rw [k₂ _ (by omega), sn₁ _ (by omega)]; exact r03)
      (by rw [k₂ _ (by omega)]; exact s30) (by rw [k₂ _ (by omega)]; exact s31)
      (by rw [k₂ _ (by omega)]; exact s32) (by rw [k₂ _ (by omega)]; exact s75) n82
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw₃ := e₃.wb_right
  -- Bellman–Ford
  have hlay : LBLay P.card w h (h + ck N P) (d + 5 * ck N P + 4) (h + 4 * ck N P)
      (w * P.card * L) L w W :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  have hℓP : ∀ a < P.card, |ℓ (cδ g N P a)| ≤ L := fun a _ => hℓ _
  have hLLz : ∀ a < P.card, (((ℓ (cδ g N P a) + L).toNat : ℕ) : ℤ) = ℓ (cδ g N P a) + L :=
    fun a ha => by have := abs_le.1 (hℓP a ha); exact Int.toNat_of_nonneg (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, hI₄, hf₄, hm₄, hn₄, hr₄, hrm₄, ho₄⟩ :=
    lbProg_exec (I := I) (T := fun a => ν (g.gv (N.tail (cδ g N P a))))
      (H := fun a => ν (g.gv (N.head (cδ g N P a))))
      (LL := fun a => (ℓ (cδ g N P a) + L).toNat) (lam := fun a => ℓ (cδ g N P a)) hlay le_rfl
      (fun a ha => by
        show ν (g.gv (N.tail (cδ g N P a))) < w
        rw [← hT₂ a ha, hO a (by omega)]; exact hlt a (by omega))
      (fun a ha => by
        show ν (g.gv (N.head (cδ g N P a))) < w
        rw [← hH₂ a ha, Nat.add_assoc, hO _ (by omega)]; exact hlt _ (by omega))
      hLLz
      (fun a ha => by have := abs_le.1 (hℓP a ha); show -(L : ℤ) ≤ ℓ (cδ g N P a); omega)
      (fun a ha => by have := abs_le.1 (hℓP a ha); show ℓ (cδ g N P a) ≤ L; omega)
      c₃ hw₃ ⟨fun a ha => by rw [qm₃]; exact hT₂ a ha, fun a ha => by rw [qm₃]; exact hH₂ a ha,
        fun a ha => by rw [qm₃]; exact hL₂ a ha⟩ q00 q01 q02 q03 q04 q05 q06 q07 q08
  have hw₄ := e₄.wb_right
  -- the memory after Bellman–Ford
  have M4 : ∀ a, (a < h + 4 * ck N P ∨ h + 4 * ck N P + w ≤ a) →
      c₄.nmem a = c₂.nmem a := fun a h1 => by rw [hm₄ a h1, qm₃]
  have M2 : ∀ a, a < h → c₂.nmem a = c.nmem a := fun a ha => by
    rw [nm₂ a (by omega) (by omega), sm₁]
  have K4 : ∀ r, 3000 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hn₄ r (by omega), qn₃ r (by omega), k₂ r (by omega), sn₁ r (by omega)]
  have hle : ∀ v < w, c₄.nmem (h + 4 * ck N P + v) ≤ w * P.card * L := hI₄.le_K
  have r26 : c₄.nreg 2426 = 0 := by
    rw [hn₄ _ (by omega), qn₃ _ (by omega), k₂ _ (by omega)]; exact s26
  have r25 : c₄.nreg 2425 = 1 := by
    rw [hn₄ _ (by omega), qn₃ _ (by omega), k₂ _ (by omega)]; exact s25
  have RR : c₄.rreg = c.rreg ∧ c₄.rmem = c.rmem ∧ c₄.output = c.output :=
    ⟨by rw [hr₄, qr₃, nr₂, sr₁], by rw [hrm₄, qrm₃, nrm₂, srm₁], by rw [ho₄, qo₃, no₂, so₁]⟩
  have r30₄ : c₄.nreg 2430 = P.card := by
    rw [hn₄ _ (by omega), qn₃ _ (by omega), k₂ _ (by omega)]; exact s30
  have r31₄ : c₄.nreg 2431 = ck N P := by
    rw [hn₄ _ (by omega), qn₃ _ (by omega), k₂ _ (by omega)]; exact s31
  have hverts : ∀ a < P.card, N.tail (cδ g N P a) ∈ verts N P ∧ N.head (cδ g N P a) ∈ verts N P :=
    fun a ha => ⟨mem_verts.2 ⟨_, cδ_memP ha, Or.inl rfl⟩, mem_verts.2 ⟨_, cδ_memP ha, Or.inr rfl⟩⟩
  rcases hf₄ with ⟨f0, hnv⟩ | ⟨f1, j, hj, hvj⟩
  · -- no arc relaxable: the renormalized outcome
    have hcnd : ¬ c₄.nreg 2426 < c₄.nreg 2424 := by rw [r26, f0]; omega
    obtain ⟨c₅, t₅, e₅, ht₅, u50, u51, u52, u53, u54, u55, un₅, um₅, ur₅, urm₅, uo₅⟩ :=
      lfRes_exec (I := I) c₄ hw₄ (h := h) (k := ck N P) (w := w)
        (by rw [K4 _ (by omega)]; exact r03) r31₄
        (by rw [hn₄ _ (by omega), qn₃ _ (by omega), k₂ _ (by omega)]; exact s75)
        (by rw [hn₄ _ (by omega), qn₃ _ (by omega)]; exact n82) (by omega)
    have hw₅ := e₅.wb_right
    have hfeas := lb_feas (T := fun a => ν (g.gv (N.tail (cδ g N P a))))
      (H := fun a => ν (g.gv (N.head (cδ g N P a))))
      (LL := fun a => (ℓ (cδ g N P a) + L).toNat) (lam := fun a => ℓ (cδ g N P a))
      (Db := h + 4 * ck N P) (K := w * P.card * L) (L := L) (mem := c₄.nmem) hLLz
      (fun j hj => hnv j hj)
    let f : V → ℤ := fun x =>
      (c₄.nmem (h + 4 * ck N P + ν (g.gv x)) : ℤ) - ((w * P.card * L : ℕ) : ℤ)
    have hpot : (pg N P ℓ).IsPot f := fun ⟨x, hx⟩ => by
      obtain ⟨h1, h2⟩ := cδ_idxOf (g := g) (N := N) hx
      have := hfeas _ h1
      try simp only at this
      rw [h2] at this
      exact this
    have hin₅ : InP g N ℓ L n P d e c₅ := inP_stab hin fun a h1 h2 =>
      ⟨by rw [um₅, M4 a (by omega), M2 a (by omega)], by rw [urm₅, RR.2.1]⟩
    have hle' : P.card ≤ ck N P := hmk
    obtain ⟨c₆, t₆, g', e₆, ht₆, hpo, hres, hm₆, hn₆, hr₆, hrm₆, ho₆⟩ :=
      resProg_res (I := I) (g := g) (N := N) (f := f) (ν := fun x => ν (g.gv x))
        (ι := fun v => gInv g N (c₂.nmem (h + 2 * ck N P + v))) (w := w)
        (Tb := h) (HHb := h + ck N P) (Fb := h + 4 * ck N P) (Ab := h + 6 * ck N P)
        (Ib := h + 2 * ck N P) (Lf := w * P.card * L) c₅ hw₅ hin₅ hpot
        (by rw [un₅ _ (by omega), K4 _ (by omega)]; exact r04) u50 u51 u52 u53 u54 u55
        (fun x hx => P1 x hx) (fun v hv => ⟨(P2 v hv).1, (P2 v hv).2.1⟩) hw2m
        (fun a ha => by rw [um₅, M4 _ (by omega)]; exact hT₂ a ha)
        (fun a ha => by rw [um₅, M4 _ (by omega)]; exact hH₂ a ha)
        (fun v hv => by
          rw [um₅]
          show _ = (c₄.nmem (h + 4 * ck N P +
            ν (g.gv (gInv g N (c₂.nmem (h + 2 * ck N P + v))))) : ℤ) -
              ((w * P.card * L : ℕ) : ℤ) + ((w * P.card * L : ℕ) : ℤ)
          rw [(P2 v hv).2.1]; ring)
        (fun v hv => by rw [um₅, M4 _ (by omega)]; exact (P2 v hv).2.2)
        (fun v hv => by
          show |(c₄.nmem (h + 4 * ck N P +
            ν (g.gv (gInv g N (c₂.nmem (h + 2 * ck N P + v))))) : ℤ) -
              ((w * P.card * L : ℕ) : ℤ)| ≤ ((w * P.card * L : ℕ) : ℤ)
          rw [(P2 v hv).2.1]
          have := hle v hv
          obtain ⟨K, hK⟩ : ∃ K, w * P.card * L = K := ⟨_, rfl⟩
          rw [hK] at this ⊢
          rw [abs_le]; constructor <;> omega)
        (fun x _ => hℓ x)
        ((sum_le_sum_of_subset_of_nonneg (subset_univ P) (fun _ _ _ => abs_nonneg _)).trans hsumL)
        (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inr (by omega)) (by omega) (by omega)
    refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆ + 2)))), some g',
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_false hcnd (.seq e₅ e₆))))), ?_, ?_,
      fun r hr => ?_, fun a h1 h2 h3 => ?_, by rw [ho₆, uo₅, RR.2.2], hpo, hres⟩
    · rw [← hwv]; unfold lfCost; omega
    · refine ⟨fun r => by rw [hr₆, ur₅, RR.1]; exact hg.1 r,
        fun a ha => by rw [hrm₆, urm₅, RR.2.1]; exact hg.2.1 a ha, fun a ha => ?_⟩
      rw [hm₆ _ (by omega) (by omega), um₅, M4 _ (by omega), M2 _ (by omega)]
      exact hg.2.2 a ha
    · rw [hn₆ r (by omega), un₅ r (by omega), K4 r hr]
    · refine ⟨?_, by rw [hrm₆, urm₅, RR.2.1]⟩
      rw [hm₆ _ (by omega) (by omega), um₅, M4 _ (by omega), M2 _ (by omega)]
  · -- an arc still relaxable: no feasible potential
    have hcnd : c₄.nreg 2426 < c₄.nreg 2424 := by rw [r26, f1]; omega
    obtain ⟨c₅, t₅, e₅, ht₅, um₅, un₅, ur₅, urm₅, uo₅⟩ :=
      lfNone_exec (I := I) c₄ hw₄ (d := d) (m := P.card) (k := ck N P)
        (by rw [K4 _ (by omega)]; exact r04) r30₄ r31₄ r25 (by omega) (by omega)
    have hno : ¬ ∃ p : ℕ → ℤ, ∀ a < P.card, p (ν (g.gv (N.head (cδ g N P a)))) ≤
        p (ν (g.gv (N.tail (cδ g N P a)))) + ℓ (cδ g N P a) :=
      lb_noPot (T := fun a => ν (g.gv (N.tail (cδ g N P a))))
        (H := fun a => ν (g.gv (N.head (cδ g N P a))))
        (LL := fun a => (ℓ (cδ g N P a) + L).toNat) (lam := fun a => ℓ (cδ g N P a))
        (fun a ha => by
          show ν (g.gv (N.tail (cδ g N P a))) < w
          exact (P1 _ (hverts a ha).1).1)
        (fun a ha => by
          show ν (g.gv (N.head (cδ g N P a))) < w
          exact (P1 _ (hverts a ha).2).1)
        hLLz le_rfl hI₄ hj hvj
    refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + 1)))), none,
      .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.ifLtN_true hcnd e₅)))), ?_, ?_,
      fun r hr => ?_, fun a h1 h2 h3 => ?_, by rw [uo₅, RR.2.2], ?_, ?_⟩
    · rw [← hwv]; unfold lfCost; omega
    · refine ⟨fun r => by rw [ur₅, RR.1]; exact hg.1 r,
        fun a ha => by rw [urm₅, RR.2.1]; exact hg.2.1 a ha, fun a ha => ?_⟩
      rw [um₅, upd_other _ _ _ (by omega), M4 _ (by omega), M2 _ (by omega)]
      exact hg.2.2 a ha
    · rw [un₅ r (by omega), K4 r hr]
    · refine ⟨?_, by rw [urm₅, RR.2.1]⟩
      rw [um₅, upd_other _ _ _ (by omega), M4 _ (by omega), M2 _ (by omega)]
    · rintro ⟨q, hq⟩
      refine hno ⟨fun v => q (gInv g N (c₂.nmem (h + 2 * ck N P + v))),
        fun a ha => ?_⟩
      try simp only
      rw [(P1 _ (hverts a ha).1).2, (P1 _ (hverts a ha).2).2]
      exact hq ⟨_, cδ_memP ha⟩
    · refine ⟨hin.en, ?_⟩
      show c₅.nmem (d + fin P.card (ck N P)) ≠ 0
      rw [um₅]
      unfold fin
      rw [show d + (4 + 5 * ck N P + P.card) = d + 5 * ck N P + P.card + 4 by omega, upd_same]
      omega

end Frame

end NegSSSP

end PlanarFlow
