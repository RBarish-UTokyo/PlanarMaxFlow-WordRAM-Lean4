module

public import PlanarFlow.NegSSSP.NodeNatB

/-!
# The node run on natural words: FR-Dijkstra of a part

`dijk_cmp_emb`: the run of `frProg` of a part inside the node (the setting of
`dijk_exec_emb`, `PlanarFlow/NegSSSP/NodeRunA.lean`) from a configuration with the invariant
`NInv W' L` (real memory `≤ W'` and the registers `500 … 519` bounded by `L`) compares within
`6 BB Pr L` and ends with `NInv W' (BB Pr L)` (`Pr = mkPrm (w + 1) 1 Dm p 0 Es`,
`BB Pr L = (w + 3) L`): `FR.frProg_good` on the truncation (the prices are feasible,
`feas_mkPrm`, as in `cNegMach_dij_exec_num`; the input bounded by `L` from the memory,
`xb_of_mem`), then `ExecCmp.lift_det`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine Monge.FR BKMNW Monge CmpAbs ModNat

/-- The input of FR-Dijkstra is bounded by the bound of the real memory. -/
theorem xb_of_mem {P : Prm} {c : Config} {L : ℕ} (hL : Lay P) (hDa : Data P c)
    (hM : MemB P.W L c) : XB P L := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hw' := hL.w
  have cv : ∀ (z : ℤ) (a : ℕ), a ≤ P.W → c.rmem a = (z : ℝ) → |z| ≤ (L : ℤ) := by
    intro z a ha h
    have := hM a ha
    rw [h] at this
    exact_mod_cast this
  refine ⟨fun i j hi hj => ?_, fun y hy => ?_, fun e he => ?_⟩
  · have : i * P.b + j < P.b * P.b :=
      calc i * P.b + j < i * P.b + P.b := by omega
        _ = (i + 1) * P.b := by ring
        _ ≤ P.b * P.b := Nat.mul_le_mul_right _ hi
    exact cv _ _ (by omega) (hDa.dmem i j hi hj)
  · exact cv _ _ (by omega) (hDa.pmem y hy)
  · exact cv _ _ (by omega) (hDa.lmem e he)

section Feas

variable {X : Type*} [DecidableEq X]

/-- **The prices of the arcs of a call are feasible** (the part of `cNegMach_dij_exec_num` that
does not depend on the run). -/
theorem feas_mkPrm (S : Finset X) (E : List (X × X × ℤ)) {r : X} (hr : r ∈ S)
    (hE : ∀ e ∈ E, e.1 ∈ S ∧ e.2.1 ∈ S) {φ : X → ℤ}
    (hpot : ((emptyDDG (F := X)).union E).IsPot φ) {n : ℕ} (idx : X → ℕ)
    (hidx : ∀ y ∈ S, idx y < n) (Es : List (ℕ × ℕ × ℤ))
    (hEs : ∀ a ∈ Es, ∃ a' ∈ E, (idx a'.1, idx a'.2.1, a'.2.2) = a) (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ)
    (hp : ∀ y ∈ S, p (idx y) = φ y) :
    Lay (mkPrm n 1 Dm p (idx r) Es) ∧ Feas (mkPrm n 1 Dm p (idx r) Es) ∧
      Monge.Crossing (mkPrm n 1 Dm p (idx r) Es).b (mkPrm n 1 Dm p (idx r) Es).D := by
  set Pr := mkPrm n 1 Dm p (idx r) Es with hPr
  have hn1 : 1 ≤ n := by have := hidx r hr; omega
  have hEsn : ∀ a ∈ Es, a.1 < n ∧ a.2.1 < n := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := hEs a ha
    exact ⟨hidx _ (hE a' ha').1, hidx _ (hE a' ha').2⟩
  have hL : Lay Pr := mkPrm_lay le_rfl hn1 (hidx r hr) fun a ha => (hEsn a ha).2
  have hfvv : ∀ {i : ℕ}, i < n → ((fv Pr hL.N_pos i : Fin Pr.N) : ℕ) = i := fun hi => fv_val hi
  have hlenEx : (exArcs Pr hL.N_pos).length = (arcList n Es).length :=
    length_exArcs_mkPrm hL.N_pos
  have hgetEx : ∀ t (ht : t < (exArcs Pr hL.N_pos).length), (exArcs Pr hL.N_pos)[t] =
      (fv Pr hL.N_pos ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).1,
        fv Pr hL.N_pos ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).2.1,
        ((arcList n Es)[t]'(by rw [← hlenEx]; exact ht)).2.2) := fun t ht =>
    exArcs_mkPrm_get hL.N_pos ht
  set Gm := (emptyDDG (F := Fin Pr.N)).union (exArcs Pr hL.N_pos)
  have hpm : Gm.IsPot (fun y => Pr.p y) := by
    rintro (⟨_, h, -⟩ | t)
    · simp [emptyDDG] at h
    · have ht : t.1 < (arcList n Es).length := lt_of_lt_of_eq t.2 hlenEx
      have hget := hgetEx t.1 t.2
      have ha : (arcList n Es)[t.1] ∈ Es := (mem_arcList.1 (List.getElem_mem ht)).1
      obtain ⟨a, ha', he'⟩ := hEs _ ha
      obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 ha'
      have hpj := hpot (.inr ⟨j, hj⟩)
      change φ E[j].2.1 ≤ φ E[j].1 + E[j].2.2 at hpj
      rw [hja] at hpj
      show p ((exArcs Pr hL.N_pos)[t.1]).2.1 ≤ p ((exArcs Pr hL.N_pos)[t.1]).1 +
        ((exArcs Pr hL.N_pos)[t.1]).2.2
      rw [hget, hfvv (by rw [← he']; exact hidx _ (hE _ ha').2),
        hfvv (by rw [← he']; exact hidx _ (hE _ ha').1), ← he']
      simp only
      rw [hp _ (hE _ ha').1, hp _ (hE _ ha').2]
      exact hpj
  have hb : Pr.b = 1 := rfl
  have hDc : Monge.Crossing Pr.b Pr.D := by
    intro i i' j j' hi _ hi' _ _; omega
  have hp' : ((faceDDG (fv Pr hL.N_pos) Pr.b Pr.D).union (exArcs Pr hL.N_pos)).IsPot
      (fun y => Pr.p y) := by
    rw [hb]; exact isPot_of_arcsIn (arcsIn_one_empty _ _ _) hpm
  exact ⟨hL, feas_of_isPot hL ((isPot_ddgPlus_iff (fv_inj_corner hL)).2 hp'), hDc⟩

end Feas

section Emb

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 1000000 in
/-- **FR-Dijkstra of a part inside the node is compare-bounded** (see the module docstring). -/
theorem dijk_cmp_emb {P₀ P₁ : Finset D}
    {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (h : NodeEnc N P₀ P₁ m w e ν ι)
    {X : Finset D} (hX : X ⊆ P₀ ∪ P₁) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) (hδ : (pg N X ℓ).IsPot δ) (Es : List (ℕ × ℕ × ℤ))
    (hEs : ∀ a ∈ Es, ∃ a' ∈ dijArcs N X ℓ (verts N X) (initLen B E δ),
      (numV ν a'.1, numV ν a'.2.1, a'.2.2) = a)
    (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (hp0 : p 0 = price B E δ none)
    (hpv : ∀ x ∈ verts N (P₀ ∪ P₁), p (ν x + 1) = δ x) (I : Input) {W' L : ℕ}
    (hW : (mkPrm (w + 1) 1 Dm p 0 Es).W ≤ W') (d : Config) (hd : WordsBounded W' d)
    (hin : Inp (mkPrm (w + 1) 1 Dm p 0 Es) d) (hDa : Data (mkPrm (w + 1) 1 Dm p 0 Es) d)
    (hrb : ∀ r < 372, d.nreg r ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W)
    (hmb : ∀ a ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W, d.nmem a ≤ (mkPrm (w + 1) 1 Dm p 0 Es).W)
    (hI : NInv W' L d) {d' : Config} {k : ℕ} (ex : Exec I W' frProg d d' k) :
    ExecCmp I W' (6 * BB (mkPrm (w + 1) 1 Dm p 0 Es) L) frProg d d' k ∧
      NInv W' (BB (mkPrm (w + 1) 1 Dm p 0 Es) L) d' := by
  classical
  set Pr := mkPrm (w + 1) 1 Dm p 0 Es with hPr
  -- the feasibility, as in `dijk_exec_num`
  have hsub : dijVerts N X ⊆ dijVerts N (P₀ ∪ P₁) :=
    insert_subset_insert _ (image_subset_image (verts_sub_of_sub hX))
  have hmemS : ∀ y ∈ dijVerts N (P₀ ∪ P₁), y = none ∨ ∃ x ∈ verts N (P₀ ∪ P₁), y = some x := by
    intro y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact Or.inl rfl
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact Or.inr ⟨x, hx, rfl⟩
  have hidx : ∀ y ∈ dijVerts N (P₀ ∪ P₁), numV ν y < w + 1 := by
    intro y hy
    rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩
    · simp [numV]
    · have := h.lt x hx; simp only [numV]; omega
  have hp : ∀ y ∈ dijVerts N (P₀ ∪ P₁), p (numV ν y) = price B E δ y := by
    intro y hy
    rcases hmemS y hy with rfl | ⟨x, hx, rfl⟩
    · exact hp0
    · exact hpv x hx
  obtain ⟨hL, hF, hDc⟩ := feas_mkPrm (dijVerts N (P₀ ∪ P₁))
    (dijArcs N X ℓ (verts N X) (initLen B E δ)) (r := none) (mem_insert_self _ _)
    (fun a ha => ⟨hsub (dijArcs_ends N ha).1, hsub (dijArcs_ends N ha).2⟩) (isPot_price hδ)
    (numV ν) hidx Es hEs Dm p hp
  -- the run on the truncation
  have hLw := lay_w hL
  set c := trunc frU Pr.W d with hcdef
  have hA := agree_trunc frU Pr.W d
  have hn : ∀ r < 372, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [frU, hr])).symm
  have hw : WordsBounded Pr.W c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [frU] using hr)) hmb
  have hinc : Inp Pr c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hn _ (by omega)]
    exacts [hin.r100, hin.r101, hin.r102, hin.r103, hin.r104, hin.r105, hin.r106, hin.r107,
      hin.r108, hin.r109]
  have hDac : Data Pr c :=
    hDa.congr hL (fun a ha => (hA.nmem a ha).symm) (fun a ha => (hA.rmem a ha).symm)
  have hMc : MemB Pr.W L c := fun a ha => by
    rw [← hA.rmem a ha]; exact hI.1 a (ha.trans hW)
  have hXB : XB Pr L := xb_of_mem hL hDac hMc
  have hLB : L ≤ BB Pr L := by unfold BB; exact Nat.le_mul_of_pos_left L (by omega)
  have hMBc : MemB Pr.W (BB Pr L) c := fun a ha => (hMc a ha).trans (by exact_mod_cast hLB)
  obtain ⟨c', kc, ec, -⟩ := frProg_exec (I := I) hL hDc hF c hw hinc hDac
  have hg := frProg_good (I := I) hL hXB hDc hF c hw hinc hDac
  have hMB' := hg.mem ec hMBc
  obtain ⟨hC, hA', hK⟩ := ((hg.toCmp hMBc).exec ec).lift_det frProg_regsOK frProg_noInp
    frProg_noRand hW hd ex
  refine ⟨hC, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · by_cases hab : a ≤ Pr.W
    · rw [hA'.rmem a hab]; exact hMB' a hab
    · rw [hK.rmem a (Nat.lt_of_not_le hab)]; exact (hI.1 a ha).trans (by exact_mod_cast hLB)
  · rw [hK.rreg r (by simp [frU]; omega)]; exact (hI.2 r h1 h2).trans (by exact_mod_cast hLB)

end Emb

end NegSSSP

end PlanarFlow
