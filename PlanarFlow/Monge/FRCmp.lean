module

public import PlanarFlow.Monge.CmpAbs
public import PlanarFlow.Monge.FRProg

/-!
# FR-Dijkstra: bounded comparisons

The reals of `PlanarFlow.Monge.FR.frProg` are integers; this file bounds every executed real
comparison of a run (`WordRAM.Machine.ModNat.CmpOK`), so that the run can be simulated on natural
words modulo `M` (`WordRAM.Machine.ModNat.CmpOK.toNat`).

With `L` bounding the inputs (`XB`: `|D|`, `|p|`, `|len| ≤ L`) and every real memory cell at the
start, the run keeps every real memory cell bounded by `BB P L = (N + 2) L`
(`PlanarFlow.Monge.CmpAbs.MemB`), stores only values bounded by `BB P L`, and compares only
values whose difference is at most `6 BB P L` (`PlanarFlow.Monge.CmpAbs.Good`):

* the distances of the ghost run are lengths of walks of fewer than `N` arcs: `|d i| ≤ N L`
  (`MRun.dist_le`); the stored distance `κ + p x` of a settled vertex is such a distance, the
  stored key `d x + len e - p y` and the stored item `d σ + F ρ σ` of a triplet are bounded by
  `(N + 2) L`;
* everything else is checked by the abstract interpretation `PlanarFlow.Monge.CmpAbs.absS`
  (`decide`): the compared reals are loads or sums of at most three loads.

This file: the bounds, `tPut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap CmpAbs

/-- The inputs are bounded by `L`. -/
structure XB (P : Prm) (L : ℕ) : Prop where
  D : ∀ i j, i < P.b → j < P.b → |P.D i j| ≤ (L : ℤ)
  p : ∀ y < P.N, |P.p y| ≤ (L : ℤ)
  len : ∀ e < P.m, |P.len e| ≤ (L : ℤ)

/-- The bound of the real memory cells. -/
def BB (P : Prm) (L : ℕ) : ℕ := (P.N + 2) * L

/-- The good statements of FR-Dijkstra: memory bounded by `BB P L`, comparisons by
`6 BB P L`. -/
abbrev FG (I : Input) (P : Prm) (L : ℕ) (s : Stmt) (c : Config) : Prop :=
  Good I P.W (BB P L) (6 * BB P L) s c

variable {P : Prm} {I : Input} {L : ℕ}

/-! ### Bounds -/

lemma XB.arc (hL : Lay P) (h : XB P L) {u y : ℕ} {ℓ : ℤ} (ha : IsArc P u y ℓ) : |ℓ| ≤ (L : ℤ) := by
  rcases ha with ⟨hu, hy, -, rfl⟩ | ⟨hu, e, h1, h2, -, rfl⟩
  · exact h.D u y hu hy
  · have := off_mono' hL (u + 1) P.N (by omega) le_rfl
    rw [hL.off_last] at this
    exact h.len e (by omega)

/-- The distances of a run of Dijkstra's algorithm: walks of at most `i` arcs. -/
lemma MRun.dist_le' (hL : Lay P) (hX : XB P L) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ}
    (hR : MRun P K v d) : ∀ i < K, |d i| ≤ (i * L : ℤ) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hR.root_d hi]; simp
    · obtain ⟨j, hj, ℓ, ha, hd⟩ := hR.parent i hpos hi
      have h1 := ih j hj (by omega)
      have h2 := hX.arc hL ha
      rw [hd]
      have h3 : (j * L : ℤ) + L ≤ i * L := by
        have : (j + 1 : ℤ) ≤ i := by exact_mod_cast hj
        nlinarith
      calc |d j + ℓ| ≤ |d j| + |ℓ| := abs_add_le _ _
        _ ≤ _ := by linarith

/-- A run of Dijkstra's algorithm settles at most `N` vertices. -/
lemma MRun.card_le {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} (hR : MRun P K v d)
    (hv : ∀ i < K, v i < P.N) : K ≤ P.N := by
  have := Fintype.card_le_of_injective (fun i : Fin K => (⟨v i, hv i i.2⟩ : Fin P.N))
    (fun i j h => Fin.ext (hR.inj i j i.2 j.2 (by simpa using congrArg Fin.val h)))
  simpa using this

lemma MRun.dist_le (hL : Lay P) (hX : XB P L) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ}
    (hR : MRun P K v d) (hv : ∀ i < K, v i < P.N) : ∀ i < K, |d i| ≤ (P.N * L : ℤ) := by
  intro i hi
  refine (hR.dist_le' hL hX i hi).trans ?_
  have := hR.card_le hv
  have : (i : ℤ) ≤ P.N := by exact_mod_cast (show i ≤ P.N by omega)
  have hL0 : (0 : ℤ) ≤ L := by positivity
  nlinarith

/-- The distance of a settled vertex. -/
lemma MSt.dV_le {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA : ℕ → ℕ → Prop} {xe : ℕ → Prop}
    {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ}
    (hS : MSt P K v d κ pA xe ex X nm rm) (hDB : ∀ i < K, |(d i : ℝ)| ≤ (P.N * L : ℝ)) {y : ℕ}
    (hy : y < P.N) (hs : sfV P nm y = 1) : |dV P rm y| ≤ (P.N * L : ℝ) := by
  obtain ⟨i, hi, rfl⟩ := (hS.gh.sf y hy).1 hs
  rw [hS.gh.dist i hi]; exact hDB i hi

/-- The distances of a run of Dijkstra's algorithm, as reals. -/
lemma MRun.dist_le_real (hL : Lay P) (hX : XB P L) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ}
    (hR : MRun P K v d) (hv : ∀ i < K, v i < P.N) : ∀ i < K, |(d i : ℝ)| ≤ (P.N * L : ℝ) := by
  intro i hi
  have := hR.dist_le hL hX hv i hi
  have h2 : ((|d i| : ℤ) : ℝ) ≤ ((P.N * L : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  exact h2

/-- An entry `F` of a half block. -/
lemma hbF_abs (hL : Lay P) (hX : XB P L) {s k ρ σ : ℕ} (hσ : sib k * s + σ < P.b) :
    |hbF P.b P.D P.p s k ρ σ| ≤ (2 * L : ℝ) := by
  unfold hbF
  have hb := hL.b_pos
  have hbN := hL.bN
  have hcl : cl P.b (k * s + ρ) < P.b := by unfold cl; omega
  have h1 := hX.D _ _ hσ hcl
  have h2 := hX.p _ (show cl P.b (k * s + ρ) < P.N by omega)
  have h3 : |P.D (sib k * s + σ) (cl P.b (k * s + ρ)) - P.p (cl P.b (k * s + ρ))| ≤ (2 * L : ℤ) :=
    (abs_sub _ _).trans (by linarith)
  have h4 : ((|P.D (sib k * s + σ) (cl P.b (k * s + ρ)) - P.p (cl P.b (k * s + ρ))| : ℤ) : ℝ) ≤
      ((2 * L : ℤ) : ℝ) := by exact_mod_cast h3
  push_cast at h4 ⊢
  first | exact h4 | skip

lemma BB_ge (L : ℕ) : (P.N * L + 2 * L : ℝ) ≤ (BB P L : ℝ) := by
  unfold BB; push_cast; nlinarith

/-- A register bounded by `BB P L`. -/
lemma regA_one {c : Config} {r : ℕ} (h : |c.rreg r| ≤ (BB P L : ℝ)) :
    RegA (BB P L) [(r, 1)] c := by
  intro r' j hj
  simp only [CmpAbs.get] at hj
  split_ifs at hj with h'
  simp only [Option.some.injEq] at hj; subst h' hj; simpa using h

/-- The abstract interpretation for FR-Dijkstra: `m = 6`, at most `8` rounds per loop. -/
theorem fg_abs {s : Stmt} {A : CmpAbs.AS} (h : (absS 6 8 s A).isSome = true) {c : Config}
    (hA : MemB P.W (BB P L) c → RegA (BB P L) A c) : FG I P L s c := good_abs' h hA

/-- The abstract interpretation from the empty state. -/
theorem fg_abs0 {s : Stmt} (h : (absS 6 8 s []).isSome = true) {c : Config} : FG I P L s c :=
  good_abs' h fun _ => regA_nil _

/-! ### Writing a triplet -/

/-- **`tPut` is good**: the stored item is `d σ + F ρ σ`. -/
theorem tPut_good (hL : Lay P) (hX : XB P L) {B T k σ j1 j2 : ℕ} {e : ℕ → ℝ}
    (c : Config) (hc : WordsBounded P.W c)
    (hE : Env P B (2 ^ T) k c) (hB : B + 8 * 2 ^ T ≤ P.W)
    (hR : QReady P B (2 ^ T) k c.nmem)
    (he : e σ = c.rmem (P.db + (sib k * 2 ^ T + σ))) (heB : |e σ| ≤ (P.N * L : ℝ))
    (h200 : c.nreg 200 = σ) (hσ : σ < hbNc P.b (2 ^ T) k) (h201 : c.nreg 201 = j1)
    (h202 : c.nreg 202 = j2) (hj : j1 < j2) (hj2 : j2 ≤ hbNr P.b (2 ^ T) k) :
    FG I P L tPut c := by
  unfold tPut
  refine Good.seq (fg_abs0 (by decide)) fun c₁ k₁ e₁ => ?_
  obtain ⟨c', k', e', -, hq, -⟩ :=
    rmq_exec (I := I) hL c hc hE hB rfl hR h200 hσ h201 h202 hj hj2
  obtain ⟨rfl, rfl⟩ := Exec.det e' e₁
  have hsσ : sib k * 2 ^ T + σ < P.b := by unfold hbNc at hσ; omega
  refine fg_abs (A := [(200, 1)]) (by decide) fun _ => regA_one ?_
  rw [hq.val, ← he]
  have h1 := hbF_abs (ρ := c'.nreg 203) hL hX hsσ
  calc |e σ + hbF P.b P.D P.p (2 ^ T) k (c'.nreg 203) σ|
      ≤ |e σ| + |hbF P.b P.D P.p (2 ^ T) k (c'.nreg 203) σ| := abs_add_le _ _
    _ ≤ P.N * L + 2 * L := add_le_add heB h1
    _ ≤ _ := BB_ge L

end FR

end Monge

end PlanarFlow
