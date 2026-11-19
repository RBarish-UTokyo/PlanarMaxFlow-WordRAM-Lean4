module

public import PlanarFlow.NegSSSP.NdCost
public import PlanarFlow.NegSSSP.SplitBig

/-!
# Towards the full branch of the node step

* **`msplit_eq`**: the machine's split of a piece of more than `10⁶` darts is the split
  `splitM N (spOrd g N) cut P` for a cut function with `CutsOK` (as in `msplit_splitF`).
* **`msplit_big`**: in the full branch (the parts share a vertex) the piece has a component of
  more than three quarters of its darts: the large case of the split (`bigProg`), so the
  machine's split exports the piece map, the cycle, the marks and the positions
  (`bigProg_spec''`); in the small case the parts are unions of components and share no vertex
  (`bdry_closed`).
* **`lg_lift_trunc`**: the logged run (`lg_lift`) from the truncation of a configuration, the
  form in which the fixed node program `nodeFullR` (word bound `WN`, registers `< 2920`) runs
  inside the driver with its stores logged.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- **The machine's split is `splitM` for a cut function with `CutsOK`.** -/
theorem msplit_eq (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) :
    ∃ cut, CutsOK N cut ∧ msplit g N P = splitM N (spOrd g N) cut P := by
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
  exact ⟨cut, hcut, Prod.ext e1 e2⟩

/-- **In the full branch the split is the large case**: if the parts of the machine's split
share a vertex, the piece has a component of more than three quarters of its darts. -/
theorem msplit_big (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card)
    (hb : (bdry N (msplit g N P).1 (msplit g N P).2).Nonempty) :
    ∃ x ∈ P, 3 * P.card / 4 < (pcomp N P x).card := by
  by_contra h
  push Not at h
  obtain ⟨cut, -, he⟩ := msplit_eq (g := g) hM hrot hface hPr hs
  rw [he, splitM_small cut h] at hb
  obtain ⟨hGP, hGc, -, -, -⟩ := grp_spec (N := N) (P := P) (by omega) h
    (((spOrd g N) P).filter (· ∈ P)) ∅ (empty_subset _) (fun _ h => absurd h (notMem_empty _))
    (by simp) (fun d hd => by simpa using (List.mem_filter.1 hd).2)
    (fun d hd => Or.inr (List.mem_filter.2 ⟨spOrd_ok (g := g) (N := N) P d hd, by simpa using hd⟩))
  rw [bdry_closed hGP hGc] at hb
  exact not_nonempty_empty hb

/-- **The canonical split in the large case exports the data of the piece map**: on a piece
with a component of more than three quarters of its darts, the end `spFin g N P` of the
canonical run meets `BigOut` (the conclusion of `bigProg_spec''`) for a dart `x₁` of the large
component; every run of the split stage agrees with `spFin` on `[0, spWs k]` and the registers
`< 972` (`exec_agree`, as in `msplit_run`). -/
theorem spFin_big (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {P : Finset D}
    (hPr : P ⊆ reps N) (hbig0 : ∃ x ∈ P, 3 * P.card / 4 < (pcomp N P x).card) :
    ∃ x₁ ∈ P, 3 * P.card / 4 < (pcomp N P x₁).card ∧
      BigOut N P P.card (ck N P) (cδ g N P) (spB0 (ck N P)) x₁ (spFin g N P) := by
  classical
  have he := penc_canon (g := g) (N := N) P
  have hk : P.card ≤ ck N P := ck_ge P
  have hB : PlanarSeparator.MillerProg.aEnd10 (3 * ck N P) (3 * ck N P) ≤ spB0 (ck N P) := by
    unfold spB0; omega
  have hck : ck N P = (rcl N P).card := rfl
  have hB3 : 3 * ck N P ≤ spB0 (ck N P) := by unfold spB0; omega
  obtain ⟨c', t, ex, -, -, -, hrest⟩ := splitProg_big (P := spIn) (W := spWs (ck N P))
    hM hrot hface hPr he (bα := 0) (bσ := ck N P) (bF := 2 * ck N P)
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
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left])
    (by omega) (by omega) (by omega) (by omega) (by omega) hB le_rfl
    (fun a ha => by
      simp only [spCfgP, spCfg, spMem]
      split_ifs with h1 h2
      · have := he.α_lt a h1; unfold ck at *; unfold spB0; omega
      · have := he.σ_lt (a - ck N P) (by unfold ck at *; omega); unfold ck at *; unfold spB0
        omega
      · omega) hbig0
  have hex : ∃ c' t, Exec spIn (spWs (ck N P)) splitProg (spCfgP g N P) c' t := ⟨c', t, ex⟩
  have hfin : spFin g N P = c' := by
    unfold spFin
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨t', ex'⟩ := Classical.choose_spec hex
    exact (stmt_exec_det ex' ex).1
  rw [hfin]
  exact hrest

end Frame

section Lift

open WordRAM WordRAM.Machine

variable {P P' : Input} {Ws W : ℕ}

/-- **The logged run from the truncation of a configuration**: a run of `s` (registers in `U`,
no input, no `rand`) with word bound `Ws` from `trunc U Ws d` gives a run of `lgS LP ONE s`
from `d` itself with word bound `W ≥ Ws`, the stores logged at `[p, p + j)` (`p = d.nreg LP`,
`Ws < p`, `p + k ≤ W`). -/
theorem lg_lift_trunc {s : Stmt} {c' : Config} {k : ℕ} {U : ℕ → Bool} {d : Config} {LP ONE : ℕ}
    (h : Exec P Ws s (trunc U Ws d) c' k) (hs : s.regsOK U = true) (hn : s.noInp = true)
    (hr : s.noRand = true) (hLP : U LP = false) (hONE : U ONE = false) (hne : LP ≠ ONE)
    (hWs : Ws ≤ W) (hd : WordsBounded W d) (h1 : d.nreg ONE = 1) (hp : Ws < d.nreg LP)
    (hpW : d.nreg LP + k ≤ W) :
    ∃ d' k' j, Exec P' W (lgS LP ONE s) d d' k' ∧ k' ≤ 3 * k ∧ j ≤ k ∧ Agree U Ws c' d' ∧
      LgKeep U Ws LP (d.nreg LP) j d d' ∧ d'.output = c'.output := by
  obtain ⟨d', k', j, e, hk, hj, hA, hK, L, o, o'⟩ :=
    lg_lift (P' := P') h hs hn hr hLP hONE hne hWs d (agree_trunc U Ws d) hd h1 hp hpW
  exact ⟨d', k', j, e, hk, hj, hA, hK, by rw [o', o]; rfl⟩

end Lift

end NegSSSP

end PlanarFlow
