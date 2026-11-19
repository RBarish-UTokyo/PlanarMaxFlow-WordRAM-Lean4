module

public import PlanarFlow.NegSSSP.NdMid

/-!
# The node step of the driver, given its full branch

**`nodeS Gt F`**: the front (`ndFront`: the split re-run, the children's outcome regions and
flags, the work area cleared); if a child has no outcome, the flag `none` (`ndNone`);
otherwise the numbering, the children's values and their combination (`ndB`), then
* if the parts share no vertex (`#bdry = 0`): the combined potential renormalized (`ndC ;
  resProg`), a feasible potential of the piece (`nd_comb_pot`);
* otherwise the **full branch** `F` (Klein's multiple-source shortest paths, Bellman–Ford over
  the dense distance graphs, FR-Dijkstra: the fixed node program `nodeFullR` with its inputs
  and the store log), a parameter of this file.

**`nodeS_exec`**: `nodeS Gt F` meets the field `node` of `NSpecR` with the invariant `GZ0`,
given that `F` meets it in its own case (both children with an outcome, a shared vertex),
`hF`. Cost `ndCost m k w + ncF P₀ P₁`, room `rNd m k + rF P`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- The flag `1` at the start of the outcome region `d + 5k + m + 4`. -/
def ndNone : Stmt := block [.constN 2483 5, .mulN 2484 2483 2475, .addN 2484 2484 3004,
  .addN 2484 2484 2474, .constN 2483 4, .addN 2484 2484 2483, .storeN 2484 2472]

/-- The registers of `resProg`: `w`, `T = h`, `H = h + k`, `F = h + 8k`, the scratch
`h + 10k`, `I = h + 2k`. -/
def ndC : Stmt := block [.copyN 2950 2464, .copyN 2951 3003, .addN 2952 3003 2475,
  .constN 2483 8, .mulN 2484 2483 2475, .addN 2953 3003 2484, .constN 2483 10,
  .mulN 2484 2483 2475, .addN 2954 3003 2484, .constN 2483 2, .mulN 2484 2483 2475,
  .addN 2955 3003 2484]

/-- **The node step of the driver**, with the full branch `F`. -/
def nodeS (Gt : ℕ) (F : Stmt) : Stmt :=
  .seq ndFront (.ifLtN 2473 2486 ndNone (.seq (ndB Gt) (.ifLtN 2473 2496 F (.seq ndC resProg))))

theorem ndNone_exec (c : Config) (hc : WordsBounded W c) {d m k : ℕ}
    (r04 : c.nreg 3004 = d) (r74 : c.nreg 2474 = m) (r75 : c.nreg 2475 = k)
    (r72 : c.nreg 2472 = 1) (hW : d + 5 * k + m + 4 ≤ W) (h5 : 5 ≤ W) :
    ∃ c' t, Exec I W ndNone c c' t ∧ t = 7 ∧ c'.nmem = upd c.nmem (d + 5 * k + m + 4) 1 ∧
      (∀ r, (r < 2483 ∨ 2484 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndNone
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r74, r75, r72]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r04, r74, r75, r72]
  · congr 1; omega
  · simp (disch := omega) only [upd_other]

theorem ndC_exec (c : Config) (hc : WordsBounded W c) {h k w : ℕ}
    (r64 : c.nreg 2464 = w) (r03 : c.nreg 3003 = h) (r75 : c.nreg 2475 = k)
    (hW : h + 10 * k ≤ W) (h10 : 10 ≤ W) :
    ∃ c' t, Exec I W ndC c c' t ∧ t = 12 ∧ c'.nreg 2950 = w ∧ c'.nreg 2951 = h ∧
      c'.nreg 2952 = h + k ∧ c'.nreg 2953 = h + 8 * k ∧ c'.nreg 2954 = h + 10 * k ∧
      c'.nreg 2955 = h + 2 * k ∧
      (∀ r, (r < 2483 ∨ (2484 < r ∧ r < 2950) ∨ 2955 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndC
  exec_block
  all_goals try ((try config_simp); (try simp only [r64, r03, r75]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r64, r03, r75])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- The cost of the node step without its full branch. -/
def ndCost (m k w : ℕ) : ℕ :=
  prepCost k + splitT k + (7 * m + 33) + wsCost k + 2 +
    (7 + ndBCost m k + 2 + 12 + (22 + rnCost m w + 6 + (7 * w + 2)))

/-- The room of the node step without its full branch. -/
def rNd (m k : ℕ) : ℕ := 46 * m + 10 * k + 31

/-- **The branch without an outcome**: a child without a feasible potential. -/
theorem nd_none_branch {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e bl el er : ℕ}
    {o₀ o₁ : Option (V → ℤ)} (c : Config) (hc : WordsBounded W c)
    (hin : InP g N ℓ L n P d e c)
    (hr0 : Res g N L (msplit g N P).1 o₀ (bl + 5) el c)
    (hr1 : Res g N L (msplit g N P).2 o₁ (el + 5) er c)
    (hp0 : PotOut (pg N (msplit g N P).1 ℓ) o₀) (hp1 : PotOut (pg N (msplit g N P).2 ℓ) o₁)
    (hf : 0 < c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) /
          c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) +
        c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)) /
          c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)))
    (r04 : c.nreg 3004 = d) (r74 : c.nreg 2474 = P.card) (r75 : c.nreg 2475 = ck N P)
    (r72 : c.nreg 2472 = 1) (hW : e ≤ W) (h5 : 5 ≤ W) :
    ∃ c' t, Exec I W ndNone c c' t ∧ t = 7 ∧ PotOut (pg N P ℓ) none ∧ Res g N L P none d e c' ∧
      (∀ a, (a < d + fin P.card (ck N P) ∨ d + fin P.card (ck N P) < a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2483 ∨ 2484 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have he := hin.en
  unfold fsz at he
  obtain ⟨c', t, ex, ht, hm, hn, hr, hrm, ho⟩ :=
    ndNone_exec (I := I) c hc r04 r74 r75 r72 (by omega) h5
  have hfin : d + fin P.card (ck N P) = d + 5 * ck N P + P.card + 4 := by unfold fin; omega
  have hpot : PotOut (pg N P ℓ) none := by
    rw [ind_eq, ind_eq] at hf
    have hP0 : (msplit g N P).1 ⊆ P := filter_subset _ _
    have hP1 : (msplit g N P).2 ⊆ P := filter_subset _ _
    by_cases h0 : c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) = 0
    · rw [if_pos h0] at hf
      have h1 : c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)) ≠ 0 := by
        intro h1; rw [if_pos h1] at hf; omega
      cases o₁ with
      | none => exact nd_none hP1 hp1
      | some f₁ => exact absurd hr1.2.1 h1
    · cases o₀ with
      | none => exact nd_none hP0 hp0
      | some f₀ => exact absurd hr0.2.1 h0
  refine ⟨c', t, ex, ht, hpot, ⟨hin.en, ?_⟩, fun a ha => ?_, hn, hr, hrm, ho⟩
  · show c'.nmem (d + fin P.card (ck N P)) ≠ 0
    rw [hm, hfin, upd_same]; omega
  · rw [hm, upd_other _ _ _ (by omega)]

set_option maxHeartbeats 4000000 in
/-- **The branch without shared vertices**: the combined potential, renormalized. -/
theorem nd_comb_branch {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e h w : ℕ} {f₀ f₁ : V → ℤ}
    {ν : ℕ → ℕ} (c : Config) (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c)
    (hp0 : (pg N (msplit g N P).1 ℓ).IsPot f₀) (hp1 : (pg N (msplit g N P).2 ℓ).IsPot f₁)
    (hb : bdry N (msplit g N P).1 (msplit g N P).2 = ∅)
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (r64 : c.nreg 2464 = w)
    (r75 : c.nreg 2475 = ck N P) (hwv : w = (verts N P).card)
    (P1 : ∀ x ∈ verts N P, ν (g.gv x) < w ∧
        gInv g N (c.nmem (h + 2 * ck N P + ν (g.gv x))) = x)
    (P2 : ∀ v < w, gInv g N (c.nmem (h + 2 * ck N P + v)) ∈ verts N P ∧
        ν (g.gv (gInv g N (c.nmem (h + 2 * ck N P + v)))) = v ∧
        c.nmem (h + 2 * ck N P + v) = g.gv (gInv g N (c.nmem (h + 2 * ck N P + v))))
    (hTn : ∀ a < P.card, c.nmem (h + a) = ν (g.gv (N.tail (cδ g N P a))))
    (hHn : ∀ a < P.card, c.nmem (h + ck N P + a) = ν (g.gv (N.head (cδ g N P a))))
    (hFv : ∀ v < w, c.nmem (h + 8 * ck N P + v) = (ndComb N (msplit g N P).1 f₀ f₁
          (gInv g N (c.nmem (h + 2 * ck N P + v))) + L).toNat ∧
        |ndComb N (msplit g N P).1 f₀ f₁ (gInv g N (c.nmem (h + 2 * ck N P + v)))| ≤ L)
    (hℓ : ∀ x ∈ P, |ℓ x| ≤ L) (hsumL : ∑ x ∈ P, |ℓ x| ≤ L) (heh : e ≤ h)
    (hW : h + 10 * ck N P + 31 * P.card + 9 ≤ W) (wV : 7 * L + 2 ≤ W) (h10 : 10 ≤ W) :
    ∃ c' t g', Exec I W (.seq ndC resProg) c c' t ∧
      t ≤ 12 + (22 + rnCost P.card w + 6 + (7 * w + 2)) ∧
      PotOut (pg N P ℓ) (some g') ∧ Res g N L P (some g') d e c' ∧
      (∀ a, (a < d + fin P.card (ck N P) ∨ e ≤ a) → a < h + 10 * ck N P →
        c'.nmem a = c.nmem a) ∧
      (∀ r, 2990 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hmk := ck_ge (N := N) P
  have hw2m : w ≤ 2 * P.card := hwv ▸ NTree.card_verts_le (N := N) P
  have he := hin.en
  unfold fsz at he
  obtain ⟨c₁, t₁, e₁, ht₁, s50, s51, s52, s53, s54, s55, sn₁, sm₁, sr₁, srm₁, so₁⟩ :=
    ndC_exec (I := I) c hc r64 r03 r75 (by omega) h10
  have hpot : (pg N P ℓ).IsPot (ndComb N (msplit g N P).1 f₀ f₁) := by
    have := nd_comb_pot hb hp0 hp1
    rwa [msplit_union] at this
  have hin₁ : InP g N ℓ L n P d e c₁ := inP_stab hin fun a _ _ => by rw [sm₁, srm₁]; simp
  obtain ⟨c₂, t₂, g', e₂, ht₂, hpo, hres, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ :=
    resProg_res (I := I) (g := g) (N := N) (f := ndComb N (msplit g N P).1 f₀ f₁)
      (ν := fun x => ν (g.gv x)) (ι := fun v => gInv g N (c.nmem (h + 2 * ck N P + v)))
      (w := w) (Tb := h) (HHb := h + ck N P) (Fb := h + 8 * ck N P) (Ab := h + 10 * ck N P)
      (Ib := h + 2 * ck N P) (Lf := L) c₁ e₁.wb_right hin₁ hpot
      (by rw [sn₁ _ (by omega)]; exact r04) s50 s51 s52 s53 s54 s55
      (fun x hx => P1 x hx) (fun v hv => ⟨(P2 v hv).1, (P2 v hv).2.1⟩) (by omega)
      (fun a ha => by rw [sm₁]; exact hTn a ha) (fun a ha => by rw [sm₁]; exact hHn a ha)
      (fun v hv => by
        rw [sm₁, (hFv v hv).1]
        have := abs_le.1 (hFv v hv).2
        exact Int.toNat_of_nonneg (by omega))
      (fun v hv => by rw [sm₁]; exact (P2 v hv).2.2) (fun v hv => (hFv v hv).2) hℓ hsumL
      (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by omega) (by omega)
  refine ⟨c₂, t₁ + t₂, g', .seq e₁ e₂, by omega, hpo, hres, fun a h1 h2 => ?_,
    fun r hr => ?_, by rw [hr₂, sr₁], by rw [hrm₂, srm₁], by rw [ho₂, so₁]⟩
  · rw [hm₂ a h1 (Or.inl h2), sm₁]
  · rw [hn₂ r hr, sn₁ r (by omega)]

set_option maxHeartbeats 16000000 in
/-- **The node step of the driver meets the field `node` of `NSpecR` with `GZ0`, given its full
branch** `F` in its own case (both children with an outcome, a shared vertex): cost
`ndCost m k w + ncF P₀ P₁`, room `rNd m k + rF P`. -/
theorem nodeS_exec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L Hb Gt : ℕ} (hHb : spWs (Fintype.card D) < Hb) (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |ℓ x| ≤ L) (hsumL : ∑ x, |ℓ x| ≤ L) (hWL : 7 * L + 2 ≤ W)
    (hW6 : 1000000 ≤ W) {Fs : Stmt} {ncF : Finset D → Finset D → ℕ} {rF : Finset D → ℕ}
    (hF : ∀ n P d e bl el er c f₀ f₁, GZ0 Hb c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rF P ≤ W → InPR g N ℓ L (n + 1) P d e c →
      Cnd (msplit g N) (n + 1) P →
      PotOut (pg N (msplit g N P).1 ℓ) (some f₀) → PotOut (pg N (msplit g N P).2 ℓ) (some f₁) →
      Res g N L (msplit g N P).1 (some f₀) (bl + 5) el c →
      Res g N L (msplit g N P).2 (some f₁) (el + 5) er c →
      (bdry N (msplit g N P).1 (msplit g N P).2).Nonempty →
      ∃ c' t o, Exec I W Fs c c' t ∧ t ≤ ncF (msplit g N P).1 (msplit g N P).2 ∧
        GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg N P ℓ) o ∧ Res g N L P o d e c') :
    ∀ n P d e bl el er c o₀ o₁, GZ0 Hb c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + (rNd P.card (ck N P) + rF P) ≤ W →
      InPR g N ℓ L (n + 1) P d e c → Cnd (msplit g N) (n + 1) P →
      PotOut (pg N (msplit g N P).1 ℓ) o₀ → PotOut (pg N (msplit g N P).2 ℓ) o₁ →
      Res g N L (msplit g N P).1 o₀ (bl + 5) el c →
      Res g N L (msplit g N P).2 o₁ (el + 5) er c →
      ∃ c' t o, Exec I W (nodeS Gt Fs) c c' t ∧
        t ≤ ndCost ((msplit g N P).1 ∪ (msplit g N P).2).card
            (ck N ((msplit g N P).1 ∪ (msplit g N P).2))
            (verts N ((msplit g N P).1 ∪ (msplit g N P).2)).card +
          ncF (msplit g N P).1 (msplit g N P).2 ∧
        GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg N P ℓ) o ∧ Res g N L P o d e c' := by
  intro n P d e bl el er c o₀ o₁ hg hc r04 r05 r06 r07 r08 r09 r03 b1 b2 b3 b4 b5 hroom hinR
    hcnd hp0 hp1 hr0 hr1
  obtain ⟨hPr, hin⟩ := hinR
  rw [msplit_union]
  have hcard := msplit_card (g := g) (N := N) P
  have hmk := ck_ge (N := N) P
  have hk2 : ck N P ≤ 2 * P.card := card_rcl_le P
  have hP0 : (msplit g N P).1 ⊆ P := filter_subset _ _
  have hP1 : (msplit g N P).2 ⊆ P := filter_subset _ _
  have hk0 : ck N (msplit g N P).1 ≤ 2 * (msplit g N P).1.card := card_rcl_le _
  have hk1 : ck N (msplit g N P).2 ≤ 2 * (msplit g N P).2.card := card_rcl_le _
  have hmD : P.card ≤ Fintype.card D := card_le_univ _
  have hws : spWs (ck N P) ≤ spWs (Fintype.card D) := spWs_mono (ck_le_card P)
  have hbig : 1000000 < P.card := hcnd.2.1
  have he := hin.en
  have hel := hr0.1
  have her := hr1.1
  unfold fsz at he hel her
  unfold rNd at hroom
  have hWe : er ≤ W := by omega
  -- the front
  obtain ⟨c₁, t₁, e₁, ht₁, f72, f73, f74, f75, f76, f79, f81, f82, f85, f86, fn₁, hg₁, fm₁, fr₁,
    frm₁, fo₁⟩ := ndFront_exec (I := I) hM hrot hface hPr c hc hg hin r04 r07 r09 (by omega)
      (by omega) b3 (by unfold fsz; omega) (by unfold fsz; omega) hWe (by omega) (by omega)
  have F1 : ∀ r, 3000 ≤ r → c₁.nreg r = c.nreg r := fun r hr => fn₁ r (by omega)
  have M1 : MemEq c c₁ Hb (W + 1) := fun a h1 _ => ⟨fm₁ a h1, by rw [frm₁]⟩
  have hin₁ : InP g N ℓ L (n + 1) P d e c₁ := inP_stab hin fun a h1 h2 => M1 a (by omega) (by omega)
  have hr0₁ := res_stab hr0 fun a h1 h2 => M1 a (by omega) (by omega)
  have hr1₁ := res_stab hr1 fun a h1 h2 => M1 a (by omega) (by omega)
  have hw₁ := e₁.wb_right
  by_cases hf : c₁.nreg 2473 < c₁.nreg 2486
  · -- a child without an outcome
    rw [f73, f86] at hf
    obtain ⟨c₂, t₂, e₂, ht₂, hpot, hres, m₂, n₂, r₂, rm₂, o₂⟩ :=
      nd_none_branch (I := I) c₁ hw₁ hin₁ hr0₁ hr1₁ hp0 hp1
        (by rw [fm₁ _ (by unfold fin; omega), fm₁ _ (by unfold fin; omega)]; exact hf)
        (by rw [F1 _ (by omega)]; exact r04) f74 f75 f72 (by omega) (by omega)
    refine ⟨c₂, t₁ + (t₂ + 1), none, .seq e₁ (.ifLtN_true (by rw [f73, f86]; exact hf) e₂), ?_,
      ?_, fun r hr => ?_, fun a h1 h2 h3 => ?_, by rw [o₂, fo₁], hpot, hres⟩
    · unfold ndCost; omega
    · refine ⟨fun r => by rw [r₂]; exact hg₁.1 r, fun a ha => by rw [rm₂]; exact hg₁.2.1 a ha,
        fun a ha => ?_⟩
      rw [m₂ a (Or.inl (by omega))]; exact hg₁.2.2 a ha
    · rw [n₂ r (by omega), F1 r hr]
    · refine ⟨?_, by rw [rm₂, frm₁]⟩
      rw [m₂ a (by unfold fin; omega), fm₁ a h1]
  · -- both children have an outcome
    rw [f73, f86] at hf
    rw [ind_eq, ind_eq] at hf
    have z0 : c.nmem (bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1)) = 0 := by
      by_contra h; rw [if_neg h] at hf; omega
    have z1 : c.nmem (el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2)) = 0 := by
      by_contra h; rw [if_neg h] at hf; omega
    obtain ⟨f₀, rfl⟩ : ∃ f₀, o₀ = some f₀ := by
      cases o₀ with
      | none => exact absurd z0 hr0.2
      | some f₀ => exact ⟨f₀, rfl⟩
    obtain ⟨f₁, rfl⟩ : ∃ f₁, o₁ = some f₁ := by
      cases o₁ with
      | none => exact absurd z1 hr1.2
      | some f₁ => exact ⟨f₁, rfl⟩
    have hcnd₁ : ¬ c₁.nreg 2473 < c₁.nreg 2486 := by
      rw [f73, f86, ind_eq, ind_eq, if_pos z0, if_pos z1]; omega
    -- the middle
    obtain ⟨c₂, t₂, w, ν, e₂, ht₂, g64, hwv, P1, P2, hTn, hHn, hFv, g96, -, -, m₂, n₂, r₂, rm₂,
      o₂⟩ := ndB_exec (I := I) Gt c₁ hw₁ hin₁ hr0₁ hr1₁ f72 f75 f79 f81 f82 f85
        (by rw [F1 _ (by omega)]; exact r04) (by rw [F1 _ (by omega)]; exact r03)
        (fun a ha => hg₁.2.2 _ (by omega)) (by omega) b3 b4 b5 le_rfl (by omega) (by omega)
        (by omega)
    have hw2m : w ≤ 2 * P.card := hwv ▸ NTree.card_verts_le (N := N) P
    have F2 : ∀ r, 3000 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
      rw [n₂ r (by omega), F1 r hr]
    have M2 : ∀ a, a < er → c₂.nmem a = c₁.nmem a := fun a ha => m₂ a (Or.inl ha)
    have hg₂ : GZ0 Hb c₂ := ⟨fun r => by rw [r₂]; exact hg₁.1 r,
      fun a ha => by rw [rm₂]; exact hg₁.2.1 a ha,
      fun a ha => by rw [M2 a (by omega)]; exact hg₁.2.2 a ha⟩
    have hw₂ := e₂.wb_right
    by_cases hb : c₂.nreg 2473 < c₂.nreg 2496
    · -- the full branch
      have hb' : (bdry N (msplit g N P).1 (msplit g N P).2).Nonempty := by
        rw [n₂ 2473 (by omega), f73, g96] at hb
        exact card_pos.1 hb
      obtain ⟨c₃, t₃, o, e₃, ht₃, hg₃, rk₃, hk₃, ho₃, hpo, hres⟩ :=
        hF n P d e bl el er c₂ f₀ f₁ hg₂ hw₂ ((F2 _ (by omega)).trans r04)
          ((F2 _ (by omega)).trans r05) ((F2 _ (by omega)).trans r06)
          ((F2 _ (by omega)).trans r07) ((F2 _ (by omega)).trans r08)
          ((F2 _ (by omega)).trans r09) ((F2 _ (by omega)).trans r03) b1 b2 b3 b4 b5
          (by omega) ⟨hPr, inP_stab hin₁ fun a h1 h2 => ⟨M2 a (by omega), by rw [rm₂]⟩⟩ hcnd
          hp0 hp1 (res_stab hr0₁ fun a h1 h2 => ⟨M2 a (by omega), by rw [rm₂]⟩)
          (res_stab hr1₁ fun a h1 h2 => ⟨M2 a (by omega), by rw [rm₂]⟩) hb'
      refine ⟨c₃, t₁ + (t₂ + (t₃ + 1) + 2), o,
        .seq e₁ (.ifLtN_false hcnd₁ (.seq e₂ (.ifLtN_true hb e₃))), ?_, hg₃,
        fun r hr => by rw [rk₃ r hr, F2 r hr], fun a h1 h2 h3 => ?_, by rw [ho₃, o₂, fo₁], hpo,
        hres⟩
      · unfold ndCost; omega
      · obtain ⟨x1, x2⟩ := hk₃ a h1 h2 h3
        exact ⟨by rw [x1, M2 a (by omega), fm₁ a h1], by rw [x2, rm₂, frm₁]⟩
    · -- no shared vertex: the combination
      have hb0 : bdry N (msplit g N P).1 (msplit g N P).2 = ∅ := by
        rw [n₂ 2473 (by omega), f73, g96] at hb
        exact card_eq_zero.1 (by omega)
      obtain ⟨c₃, t₃, g', e₃, ht₃, hpo, hres, m₃, n₃, r₃, rm₃, o₃⟩ :=
        nd_comb_branch (I := I) (f₀ := f₀) (f₁ := f₁) (ν := ν) c₂ hw₂
          (inP_stab hin₁ fun a h1 h2 => ⟨M2 a (by omega), by rw [rm₂]⟩) hp0 hp1 hb0
          ((F2 _ (by omega)).trans r04) ((F2 _ (by omega)).trans r03) g64
          (by rw [n₂ 2475 (by omega)]; exact f75) hwv P1 P2 hTn hHn hFv
          (fun x _ => hℓ x)
          ((sum_le_sum_of_subset_of_nonneg (subset_univ P) (fun _ _ _ => abs_nonneg _)).trans
            hsumL) (by omega) (by omega) hWL (by omega)
      refine ⟨c₃, t₁ + (t₂ + (t₃ + 2) + 2), some g',
        .seq e₁ (.ifLtN_false hcnd₁ (.seq e₂ (.ifLtN_false hb e₃))), ?_, ?_,
        fun r hr => by rw [n₃ r (by omega), F2 r hr], fun a h1 h2 h3 => ?_,
        by rw [o₃, o₂, fo₁], hpo, hres⟩
      · rw [← hwv]; unfold ndCost; omega
      · refine ⟨fun r => by rw [r₃]; exact hg₂.1 r, fun a ha => by rw [rm₃]; exact hg₂.2.1 a ha,
          fun a ha => ?_⟩
        rw [m₃ a (Or.inl (by unfold fin; omega)) (by omega)]; exact hg₂.2.2 a ha
      · refine ⟨?_, by rw [rm₃, rm₂, frm₁]⟩
        rw [m₃ a (by unfold fin; omega) (by omega), M2 a (by omega), fm₁ a h1]

end Frame

end NegSSSP

end PlanarFlow
