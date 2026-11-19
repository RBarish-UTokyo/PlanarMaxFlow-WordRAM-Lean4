module

public import PlanarFlow.NegSSSP.Step
public import PlanarFlow.MSSP.Perturb

/-!
# Renormalized potentials: the semantics

The node of the recursion outputs a feasible potential `f` of its piece whose magnitude grows by
a factor `≈ 2b` per level of the recursion. Any feasible potential is a
valid outcome of the node (`NSpec` asks only `PotOut`), so the node may output instead the
**distances from a virtual source with zero-length arcs**: `g x = min_y dist (y, x)`, a feasible
potential with `−Σ_{d ∈ P} |ℓ d| ≤ g ≤ 0`, whatever the magnitude of `f`.

They are computed by Dijkstra on the reduced lengths `ℓ d + f (tail d) − f (head d) ≥ 0`, with a
virtual source `w` and an arc of length `Kz − f (ι v)` (`Kz ≥ f`) from the source to every vertex
`v` of the piece: `g x = D (ν x) + f x − Kz`.

* `RnArcs`: the arcs (`m` darts, then `w` source arcs), `RnReach` (the walks from the source,
  as `DkReach` of Dijkstra in memory), `rnG` (the digraph of the arcs).
* `RnReach.walk`, `rnReach_of_walk`: the walks from the source as lists of arcs.
* **`rn_pot`**: from the facts of Dijkstra (`D y` is the length of a walk from the source, and
  no walk is shorter), `g` is a **feasible potential** of the piece and
  **`−Σ_{d ∈ P} |ℓ d| ≤ g x ≤ 0`** on the vertices of the piece.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset MSSP

/-- **The arcs of the renormalization**: `m` darts (`a < m`: from `T a` to `H a`, length `R a`),
then `w` source arcs (`m + v`: from the source `w` to `v`, length `S v`). -/
structure RnArcs where
  m : ℕ
  w : ℕ
  T : ℕ → ℕ
  H : ℕ → ℕ
  R : ℕ → ℕ
  S : ℕ → ℕ

namespace RnArcs

variable (A : RnArcs)

/-- The tail of an arc. -/
def tk (a : ℕ) : ℕ := if a < A.m then A.T a else A.w

/-- The head of an arc. -/
def nh (a : ℕ) : ℕ := if a < A.m then A.H a else a - A.m

/-- The length of an arc. -/
def ln (a : ℕ) : ℕ := if a < A.m then A.R a else A.S (a - A.m)

end RnArcs

/-- **The walks from the source**: `RnReach A y L` if some walk from the source `w` to `y` has
length `L`. -/
inductive RnReach (A : RnArcs) : ℕ → ℕ → Prop
  | src : RnReach A A.w 0
  | step {u L a : ℕ} : RnReach A u L → a < A.m + A.w → A.tk a = u →
      RnReach A (A.nh a) (L + A.ln a)

/-- The digraph of the arcs. -/
def rnG (A : RnArcs) : Digraph ℕ (Fin (A.m + A.w)) where
  src a := A.tk a
  dst a := A.nh a
  len a := A.ln a

variable {A : RnArcs}

theorem RnReach.walk {y L : ℕ} (h : RnReach A y L) :
    ∃ l, LWalk (rnG A) A.w y l ∧ wlen (rnG A) l = L := by
  induction h with
  | src => exact ⟨[], .nil _, by simp⟩
  | @step u L a _ ha htk ih =>
    obtain ⟨l, hl, hlen⟩ := ih
    have h2 : LWalk (rnG A) A.w ((rnG A).dst ⟨a, ha⟩) (l ++ [⟨a, ha⟩]) :=
      hl.concat (show (rnG A).src ⟨a, ha⟩ = u from htk)
    refine ⟨l ++ [⟨a, ha⟩], ?_, ?_⟩
    · exact h2
    rw [wlen_append, hlen]
    simp [wlen, rnG]

theorem rnReach_of_walk {x y : ℕ} {l : List (Fin (A.m + A.w))} (h : LWalk (rnG A) x y l) :
    ∀ L, RnReach A x L → RnReach A y (L + (wlen (rnG A) l).toNat) := by
  induction h with
  | nil x => intro L hL; simpa [wlen] using hL
  | @cons a y l _ ih =>
    intro L hL
    have h1 := ih _ (RnReach.step hL a.2 rfl)
    have hnn : 0 ≤ wlen (rnG A) l := wlen_nonneg (fun _ => by simp [rnG]) l
    have e : (wlen (rnG A) (a :: l)).toNat = A.ln a + (wlen (rnG A) l).toNat := by
      rw [wlen_cons]
      have e' : (rnG A).len a = (A.ln a : ℤ) := rfl
      rw [e']; omega
    rw [e, ← Nat.add_assoc]; exact h1

/-- Telescoping along a walk: with `ln a = λ a + φ (tk a) − φ (nh a)` for every arc, the length
of a walk is the sum of `λ` plus the difference of `φ` at its ends. -/
theorem wlen_tele {φ : ℕ → ℤ} {lam : ℕ → ℤ}
    (hln : ∀ a : Fin (A.m + A.w), (A.ln a : ℤ) = lam a + φ (A.tk a) - φ (A.nh a))
    {x y : ℕ} {l : List (Fin (A.m + A.w))} (h : LWalk (rnG A) x y l) :
    wlen (rnG A) l = (l.map fun a : Fin (A.m + A.w) => lam (a : ℕ)).sum + φ x - φ y := by
  induction h with
  | nil x => simp
  | @cons a y l _ ih =>
    rw [wlen_cons, ih, List.map_cons, List.sum_cons]
    have := hln a
    have e1 : (rnG A).len a = (A.ln a : ℤ) := rfl
    have e2 : (rnG A).src a = A.tk a := rfl
    have e3 : (rnG A).dst a = A.nh a := rfl
    rw [e1, e2, e3]
    linarith

lemma neg_sum_abs_le {α : Type*} (g : α → ℤ) :
    ∀ l : List α, -(l.map fun a => |g a|).sum ≤ (l.map g).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := neg_abs_le (g a); have := neg_sum_abs_le g l; linarith

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The renormalized potential**: from the distances `D` of Dijkstra on the arcs built from a
potential `f` of the piece (feasible, since the reduced lengths `R` are natural) (`T`, `H`: the nodes of the tails and heads of the darts
`e a`, `R`: the reduced lengths, `S v = Kz − f (ι v)`), `g x = D (ν x) + f x − Kz` is a feasible
potential of the piece with `−Σ_{d ∈ P} |ℓ d| ≤ g ≤ 0` on its vertices. -/
theorem rn_pot {P : Finset D} {ℓ : D → ℤ} {f : V → ℤ}
    {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} {Kz : ℤ} {Dd : ℕ → ℕ}
    (he : ∀ a < A.m, e a ∈ P) (he_inj : ∀ a < A.m, ∀ b < A.m, e a = e b → a = b)
    (he_surj : ∀ d ∈ P, ∃ a < A.m, e a = d)
    (hν : ∀ x ∈ verts N P, ν x < A.w ∧ ι (ν x) = x)
    (hT : ∀ a < A.m, A.T a = ν (N.tail (e a))) (hH : ∀ a < A.m, A.H a = ν (N.head (e a)))
    (hR : ∀ a < A.m, (A.R a : ℤ) = ℓ (e a) + f (N.tail (e a)) - f (N.head (e a)))
    (hS : ∀ v < A.w, (A.S v : ℤ) = Kz - f (ι v))
    (hD1 : ∀ y < A.w, RnReach A y (Dd y)) (hD2 : ∀ y < A.w, ∀ L, RnReach A y L → Dd y ≤ L) :
    (pg N P ℓ).IsPot (fun x => (Dd (ν x) : ℤ) + f x - Kz) ∧
      ∀ x ∈ verts N P, -(∑ d ∈ P, |ℓ d|) ≤ (Dd (ν x) : ℤ) + f x - Kz ∧
        (Dd (ν x) : ℤ) + f x - Kz ≤ 0 := by
  refine ⟨fun ⟨d, hd⟩ => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · -- feasibility along a dart
    obtain ⟨a, ha, rfl⟩ := he_surj d hd
    have ht := hν _ (tail_mem_verts hd)
    have hh := hν _ (head_mem_verts hd)
    have r1 := hD1 _ ht.1
    have r2 := RnReach.step r1 (a := a) (by omega) (by simp [RnArcs.tk, ha, hT a ha])
    have e1 : A.nh a = ν (N.head (e a)) := by simp [RnArcs.nh, ha, hH a ha]
    have e2 : A.ln a = A.R a := by simp [RnArcs.ln, ha]
    rw [e1, e2] at r2
    have hle := hD2 _ hh.1 _ r2
    have hR' := hR a ha
    simp only [pg, MSSP.pieceGraph]
    have : ((Dd (ν (N.head (e a))) : ℕ) : ℤ) ≤ (Dd (ν (N.tail (e a))) : ℤ) + (A.R a : ℤ) := by
      exact_mod_cast hle
    linarith
  · -- the lower bound: a shortest walk without repeated vertex
    obtain ⟨hv, hιv⟩ := hν x hx
    obtain ⟨l, hl, hlen⟩ := (hD1 _ hv).walk
    obtain ⟨l', hl', hsub, hnd⟩ := exists_nodup_walk hl
    have hnn : ∀ a, 0 ≤ (rnG A).len a := fun _ => by simp [rnG]
    have hle1 : wlen (rnG A) l' ≤ wlen (rnG A) l := by
      unfold wlen
      exact List.Sublist.sum_le_sum (hsub.map _) (fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact hnn b)
    have hr := rnReach_of_walk hl' 0 .src
    have hle2 := hD2 _ hv _ hr
    have hnn' : 0 ≤ wlen (rnG A) l' := wlen_nonneg hnn l'
    have heq : (Dd (ν x) : ℤ) = wlen (rnG A) l' := by
      have : (Dd (ν x) : ℤ) ≤ wlen (rnG A) l' := by omega
      omega
    -- the telescoping potential
    let φ : ℕ → ℤ := fun u => if u < A.w then f (ι u) else Kz
    let lam : ℕ → ℤ := fun a => if a < A.m then ℓ (e a) else 0
    have hln : ∀ a : Fin (A.m + A.w), (A.ln a : ℤ) = lam a + φ (A.tk a) - φ (A.nh a) := by
      intro a
      by_cases ha : (a : ℕ) < A.m
      · have hd := he a ha
        have ht := hν _ (tail_mem_verts hd)
        have hh := hν _ (head_mem_verts hd)
        simp only [RnArcs.ln, RnArcs.tk, RnArcs.nh, ha, ite_true, lam, φ, hT a ha, hH a ha,
          ht.1, hh.1, ht.2, hh.2, hR a ha]
        try ring_nf
      · have hv' : (a : ℕ) - A.m < A.w := by omega
        simp only [RnArcs.ln, RnArcs.tk, RnArcs.nh, ha, ite_false, lam, φ, hv', lt_irrefl,
          hS _ hv']
        simp only [ite_true]
        ring
    have htele := wlen_tele hln hl'
    have eφw : φ A.w = Kz := by simp [φ]
    have eφx : φ (ν x) = f x := by simp [φ, hv, hιv]
    rw [eφw, eφx] at htele
    -- the sum of `lam` over a list without repeated arc
    have hnd' : l'.Nodup := List.Nodup.of_map _ hnd
    have hsum : -(∑ d ∈ P, |ℓ d|) ≤ (l'.map fun a : Fin (A.m + A.w) => lam (a : ℕ)).sum := by
      have h1 : -(∑ a : Fin (A.m + A.w), |lam a|) ≤ (l'.map fun a : Fin (A.m + A.w) => lam (a : ℕ)).sum := by
        have h2 : (l'.map fun a : Fin (A.m + A.w) => |lam (a : ℕ)|).sum ≤ ∑ a : Fin (A.m + A.w), |lam a| := by
          rw [← List.sum_toFinset _ hnd']
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
        have h3 := neg_sum_abs_le (fun a : Fin (A.m + A.w) => lam (a : ℕ)) l'
        linarith
      have h4 : ∑ a : Fin (A.m + A.w), |lam a| = ∑ d ∈ P, |ℓ d| := by
        rw [Fin.sum_univ_eq_sum_range (fun a => |lam a|)]
        rw [show A.m + A.w = A.m + A.w from rfl, sum_range_add]
        have h5 : ∑ x ∈ range A.w, |lam (A.m + x)| = 0 :=
          sum_eq_zero fun x _ => by simp [lam]
        rw [h5, add_zero]
        rw [sum_congr rfl (fun a ha => by
          rw [show |lam a| = |ℓ (e a)| by simp [lam, mem_range.1 ha]])]
        refine sum_nbij e (fun a ha => he a (mem_range.1 ha)) ?_ ?_ (fun _ _ => rfl)
        · intro a ha b hb hab
          exact he_inj a (mem_range.1 ha) b (mem_range.1 hb) hab
        · intro d hd
          obtain ⟨a, ha, rfl⟩ := he_surj d hd
          exact ⟨a, mem_coe.2 (mem_range.2 ha), rfl⟩
      linarith
    linarith
  · -- the upper bound: the source arc of `ν x`
    obtain ⟨hv, hιv⟩ := hν x hx
    have r := RnReach.step (A := A) .src (a := A.m + ν x) (by omega)
      (by simp [RnArcs.tk])
    have e1 : A.nh (A.m + ν x) = ν x := by simp [RnArcs.nh]
    have e2 : A.ln (A.m + ν x) = A.S (ν x) := by simp [RnArcs.ln]
    rw [e1, e2, Nat.zero_add] at r
    have hle := hD2 _ hv _ r
    have hS' := hS _ hv
    rw [hιv] at hS'
    have : (Dd (ν x) : ℤ) ≤ (A.S (ν x) : ℤ) := by exact_mod_cast hle
    linarith

end NegSSSP

end PlanarFlow
