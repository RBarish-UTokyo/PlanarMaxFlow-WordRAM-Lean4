module

public import PlanarFlow.NegSSSP.SplitRunY
public import PlanarFlow.NegSSSP.DriverSplit
public import PlanarFlow.NegSSSP.Frame

/-!
# The machine's split as a function of the piece (`msplit`)

The driver runs on the decomposition `decM split` of a split **function** (`drive_split_mach`).
The split program's output depends on its whole configuration; it is a function of the piece
once the program runs on a **canonical configuration** of the piece: its registers named by
`splitProg` (all `< 972`, `splitProg_ok`) and its memory up to the word bound `spWs k` of the
split are those of `spCfg` (the rotation and the reversal of the canonical numbering of the
piece, `cα`, `cσ`, at `[0, 2k)`, everything else zero, the reals zero).

* `spB0`, `spWs`, `spU`, `spRegs`, `spMem`, `spCfg`, `spIn`, `spOrd` (the order of the darts on
  the machine), `spFin` (the end of the canonical run), **`msplit`** (the sides written by the
  canonical run at `spB0 k + 41 k + 4 + x`).
* `spFin_run`: the canonical run exists (`splitProg_splitM`) and ends in `spFin`.
* **`msplit_splitF`**: `SplitF N P (msplit P).1 (msplit P).2` for every piece `P ⊆ reps N` of more
  than `10⁶` darts (plane map): the hypothesis of `drive_split_mach`.
* **`msplit_run`**: **every** run of `splitProg` from a configuration agreeing with `spCfg` on
  the registers `< 972` and the memory up to `spWs k` (any word bound `≥ spWs k`, any input)
  writes the sides of `msplit P`: `side x = 0 ↔ cδ x ∈ (msplit P).1` (`exec_agree`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine BKMNW Driver PlanarSeparator PlanarSeparator.MillerProg

/-- The base of the split's work area for `k` half-edges. -/
def spB0 (k : ℕ) : ℕ := aEnd10 (3 * k) (3 * k) + 3 * k

/-- The word bound of the split (its whole work area). -/
def spWs (k : ℕ) : ℕ := spB0 k + 66 * k + 35

/-- The registers named by `splitProg`. -/
def spU : ℕ → Bool := fun r => decide (r < 972)

/-- **`splitProg` names only registers `< 972`**, reads no input, uses no randomness. -/
theorem splitProg_ok : splitProg.regsOK spU = true ∧ splitProg.noInp = true ∧
    splitProg.noRand = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The registers of the canonical configuration. -/
def spRegs (m k : ℕ) (r : ℕ) : ℕ :=
  if r = 10 then 1 else if r = 860 then m else if r = 861 then k else if r = 863 then k
  else if r = 865 then 2 * k else if r = 950 then spB0 k else 0

/-- The memory of the canonical configuration: the reversal at `[0, k)`, the rotation at
`[k, 2k)`. -/
def spMem (k : ℕ) (α σ : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a < k then α a else if a < 2 * k then σ (a - k) else 0

/-- **The canonical configuration of the split.** -/
def spCfg (m k : ℕ) (α σ : ℕ → ℕ) : Config :=
  { pc := 0, nreg := spRegs m k, rreg := fun _ => 0, nmem := spMem k α σ,
    rmem := fun _ => 0, output := [] }

/-- The input of the canonical run (none is read). -/
def spIn : Input := ⟨[], fun _ => 0⟩

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable (g : GIds D V) (N : CombMap D V F)

/-- The order of the darts of a piece on the machine. -/
def spOrd (Q : Finset D) : List D := (List.range Q.card).map (cδ g N Q)

/-- The canonical configuration of a piece. -/
noncomputable def spCfgP (P : Finset D) : Config := spCfg P.card (ck N P) (cα g N P) (cσ g N P)

open Classical in
/-- **The end of the canonical run of the split** of a piece. -/
noncomputable def spFin (P : Finset D) : Config :=
  if h : ∃ c' t, Exec spIn (spWs (ck N P)) splitProg (spCfgP g N P) c' t then
    Classical.choose h else spCfgP g N P

/-- **The split of the machine as a function of the piece**: the sides written by the canonical
run. -/
noncomputable def msplit (P : Finset D) : Finset D × Finset D :=
  (P.filter fun d => (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + (cL g P).idxOf d) = 0,
    P.filter fun d =>
      (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + (cL g P).idxOf d) ≠ 0)

variable {g N}

theorem idxOf_cδ {P : Finset D} {x : ℕ} (hx : x < P.card) : (cL g P).idxOf (cδ g N P x) = x := by
  have hx' : x < (cL g P).length := by rw [length_cL]; exact hx
  rw [cδ_lt hx, List.getD_eq_getElem _ _ hx']
  exact (cL_nodup P).idxOf_getElem x hx'

theorem cδ_idxOf {P : Finset D} {d : D} (hd : d ∈ P) :
    (cL g P).idxOf d < P.card ∧ cδ g N P ((cL g P).idxOf d) = d := by
  have hl : (cL g P).idxOf d < (cL g P).length := List.idxOf_lt_length_iff.2 (mem_cL.2 hd)
  refine ⟨by rw [← length_cL (g := g)]; exact hl, ?_⟩
  rw [cδ_lt (by rw [← length_cL (g := g)]; exact hl), List.getD_eq_getElem _ _ hl]
  exact List.getElem_idxOf hl

/-- **The sides of `msplit` are those written by the canonical run** (by definition). -/
theorem mem_msplit {P : Finset D} {x : ℕ} (hx : x < P.card) :
    cδ g N P x ∈ (msplit g N P).1 ↔
      (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) = 0 := by
  simp only [msplit, mem_filter, idxOf_cδ hx, cδ_memP hx, true_and]

theorem mem_msplit2 {P : Finset D} {x : ℕ} (hx : x < P.card) :
    cδ g N P x ∈ (msplit g N P).2 ↔
      (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) ≠ 0 := by
  simp only [msplit, mem_filter, idxOf_cδ hx, cδ_memP hx, true_and]

theorem spOrd_ok : ∀ Q : Finset D, ∀ d ∈ Q, d ∈ spOrd g N Q := fun Q d hd => by
  obtain ⟨h1, h2⟩ := cδ_idxOf (g := g) (N := N) hd
  exact List.mem_map.2 ⟨_, List.mem_range.2 h1, h2⟩

theorem spCfg_wb (P : Finset D) : WordsBounded (spWs (ck N P)) (spCfgP g N P) := by
  have he := penc_canon (g := g) (N := N) P
  have hk : P.card ≤ ck N P := ck_ge P
  constructor
  · intro r
    simp only [spCfgP, spCfg, spRegs, spWs, spB0]
    split_ifs <;> omega
  · intro a
    simp only [spCfgP, spCfg, spMem, spWs, spB0]
    split_ifs with h1 h2
    · have := he.α_lt a h1; unfold ck at *; omega
    · have := he.σ_lt (a - ck N P) (by unfold ck at *; omega); unfold ck at *; omega
    · omega

/-- The cut of one component changed in the canonical cut function still meets `CutsOK`. -/
theorem cutsOK_update (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K A₀ : Finset D} (hA : CutOK N K A₀) : CutsOK N (Function.update (cutC N) K A₀) :=
  fun K' hK' h0 hc => by
    by_cases hK : K' = K
    · subst hK; rw [Function.update_self]; exact hA
    · rw [Function.update_of_ne hK]; exact cutsOK_cutC hM hrot hface K' hK' h0 hc

/-- **The canonical run of the split exists**, ends in `spFin`, and writes the sides of the
split `splitM` of the machine's order for a cut function meeting `CutsOK`. -/
theorem spFin_run (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {P : Finset D}
    (hPr : P ⊆ reps N) :
    (∃ t, Exec spIn (spWs (ck N P)) splitProg (spCfgP g N P) (spFin g N P) t ∧
      t ≤ splitT (ck N P)) ∧
      (∃ cut, CutsOK N cut ∧ ∀ x < P.card,
        ((spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) = 0 ↔
          cδ g N P x ∈ (splitM N (spOrd g N) cut P).1)) ∧
      ∀ x < P.card, (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) ≤ 1 := by
  classical
  have he := penc_canon (g := g) (N := N) P
  have hk : P.card ≤ ck N P := ck_ge P
  have hB : aEnd10 (3 * ck N P) (3 * ck N P) ≤ spB0 (ck N P) := by unfold spB0; omega
  have hck : ck N P = (rcl N P).card := rfl
  have hB3 : 3 * ck N P ≤ spB0 (ck N P) := by unfold spB0; omega
  obtain ⟨c', t, ex, ht, -, -, hsides⟩ := splitProg_splitM (P := spIn) (W := spWs (ck N P))
    hM hrot hface hPr he (ord := spOrd g N) rfl (bα := 0) (bσ := ck N P) (bF := 2 * ck N P)
    (B₀ := spB0 (ck N P)) (spCfgP g N P) (spCfg_wb P)
    (by simp [spCfgP, spCfg, spRegs]) (by simp [spCfgP, spCfg, spRegs])
    (by simp [spCfgP, spCfg, spRegs, ck]) (by simp [spCfgP, spCfg, spRegs])
    (by simp [spCfgP, spCfg, spRegs, ck]) (by simp [spCfgP, spCfg, spRegs, ck])
    (by simp [spCfgP, spCfg, spRegs, ck])
    (fun h hh => by
      have hh' : h < ck N P := hh
      simp [spCfgP, spCfg, spMem, hh'])
    (fun h hh => by
      have hh' : h < ck N P := hh
      simp only [spCfgP, spCfg, spMem]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        Nat.add_sub_cancel_left])
    (by omega) (by omega) (by omega) (by omega) (by omega) hB le_rfl
    (fun a ha => by
      simp only [spCfgP, spCfg, spMem]
      split_ifs with h1 h2
      · have := he.α_lt a h1; unfold ck at *; unfold spB0; omega
      · have := he.σ_lt (a - ck N P) (by unfold ck at *; omega); unfold ck at *; unfold spB0
        omega
      · omega)
  have hex : ∃ c' t, Exec spIn (spWs (ck N P)) splitProg (spCfgP g N P) c' t := ⟨c', t, ex⟩
  have hfin : spFin g N P = c' := by
    unfold spFin
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨t', ex'⟩ := Classical.choose_spec hex
    exact (stmt_exec_det ex' ex).1
  refine ⟨⟨t, hfin ▸ ex, ht⟩, ?_⟩
  rw [hfin]
  simp only [← hck] at hsides
  rcases hsides with ⟨-, hs⟩ | ⟨x₀, -, -, A₀, hA, hs⟩
  · refine ⟨⟨cutC N, cutsOK_cutC hM hrot hface, fun x hx => ?_⟩, fun x hx => ?_⟩
    · rw [hs (cutC N) x hx]
      split_ifs with h <;> simp [h]
    · rw [hs (cutC N) x hx]; split_ifs <;> omega
  · refine ⟨⟨Function.update (cutC N) (pcomp N P x₀) A₀, cutsOK_update hM hrot hface hA,
      fun x hx => ?_⟩, fun x hx => ?_⟩
    · rw [(hs (Function.update (cutC N) (pcomp N P x₀) A₀) (Function.update_self _ _ _)).1 x hx]
      split_ifs with h <;> simp [h]
    · rw [(hs (Function.update (cutC N) (pcomp N P x₀) A₀) (Function.update_self _ _ _)).1 x hx]
      split_ifs <;> omega

/-- **The split of the machine meets `SplitF`** (the hypothesis of `drive_split_mach`). -/
theorem msplit_splitF (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) :
    SplitF N P (msplit g N P).1 (msplit g N P).2 := by
  obtain ⟨-, ⟨cut, hcut, hside⟩, -⟩ := spFin_run (g := g) hM hrot hface hPr
  have hS := splitM_splitF (spOrd_ok (g := g) (N := N)) hcut hPr hs
  obtain ⟨hu, hd, -⟩ := hS
  have e1 : (msplit g N P).1 = (splitM N (spOrd g N) cut P).1 := by
    ext d
    simp only [msplit, mem_filter]
    constructor
    · rintro ⟨hdP, h0⟩
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      have := (hside _ hx).1 h0
      rwa [hδ] at this
    · intro h
      have hdP : d ∈ P := hu ▸ mem_union_left _ h
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      exact ⟨hdP, (hside _ hx).2 (by rw [hδ]; exact h)⟩
  have e2 : (msplit g N P).2 = (splitM N (spOrd g N) cut P).2 := by
    ext d
    simp only [msplit, mem_filter]
    constructor
    · rintro ⟨hdP, h0⟩
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      have h1 : d ∉ (splitM N (spOrd g N) cut P).1 := fun h =>
        h0 ((hside _ hx).2 (by rw [hδ]; exact h))
      rw [← hu] at hdP
      rcases mem_union.1 hdP with h | h
      · exact absurd h h1
      · exact h
    · intro h
      have hdP : d ∈ P := hu ▸ mem_union_right _ h
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      refine ⟨hdP, fun h0 => ?_⟩
      have := (hside _ hx).1 h0
      rw [hδ] at this
      exact disjoint_left.1 hd this h
  rw [e1, e2]
  exact splitM_splitF (spOrd_ok (g := g) (N := N)) hcut hPr hs

/-- **Every run of the split from a configuration agreeing with the canonical one writes the
sides of `msplit`** (any input, any word bound `≥ spWs k`). -/
theorem msplit_run (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) {P' : Input} {W' : ℕ} {c₁ d' : Config} {t : ℕ}
    (hA : Agree spU (spWs (ck N P)) (spCfgP g N P) c₁) (h : Exec P' W' splitProg c₁ d' t)
    (hW : spWs (ck N P) ≤ W') :
    ∀ x < P.card, (d'.nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) = 0 ↔
      cδ g N P x ∈ (msplit g N P).1) ∧
      (d'.nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) ≠ 0 ↔
      cδ g N P x ∈ (msplit g N P).2) ∧ d'.nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) ≤ 1 := by
  obtain ⟨⟨t₀, ex₀, -⟩, -, hle⟩ := spFin_run (g := g) hM hrot hface hPr
  obtain ⟨hA', -, -⟩ := exec_agree ex₀ h splitProg_ok.1 splitProg_ok.2.1 splitProg_ok.2.2 hW hA
  intro x hx
  have hk : P.card ≤ ck N P := ck_ge P
  rw [hA'.nmem _ (by unfold spWs; omega), mem_msplit hx, mem_msplit2 hx]
  exact ⟨Iff.rfl, Iff.rfl, hle x hx⟩

end Frame

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW PlanarFlow.NegSSSP.Frame

universe w'

variable {I : Input} {W Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}

/-- **The recursion for negative lengths on the decomposition of the machine's own split**
(`msplit`, a function of the piece by the canonical run): `drive_split_mach` with
`split = msplit g M.dual`, the hypothesis `SplitF` discharged by `msplit_splitF`. -/
theorem drive_msplit_mach (C C₀ : ℕ) {D V F : Type w'} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} (g : GIds D F)
    (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans) (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
    {Res : Finset D → Option (F → ℤ) → ℕ → ℕ → Config → Prop}
    {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ}
    (hS : NSpec M.dual (minLen M.dual ℓ₀) (msplit g M.dual) I W Hb testS leafS splitS nodeS G
      InP Res tcP lcP scP ncP) (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card
        (bdry M.dual P₀ P₁).card P₀.card (verts M.dual P₀).card P₁.card
        (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hin : InP (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res (reps M.dual) o (Hb + 5) e c' ∧ G c' ∧
      c'.output = c.output :=
  drive_split_mach C C₀ (fun _ hP hs => msplit_splitF hM hrot hface hP hs) hneg hS hHb hl hn c
    hc hg r0 r1 r2 r3 m0 m1 m2 he hh hin

end Driver

end NegSSSP

end PlanarFlow
