module

public import Mathlib.Tactic

/-!
# The corner walk of `fixP`, as a function on naturals

FixConservationOnPath numbers the faces along a path by their first positions on the walk
around the path (`fixCorner`, `exists_fixCornersInj`). The program walks `N` steps; at step `n`
it sees the label `g n` of the face of the current dart and its index `tt n`; a mark array `mk`
holds `0` (not a face along the path), `1` (a face along the path not yet seen) or `x + 2`
(the corner number `x` of a face already seen). At a label marked `1` it records the corner:
`mk := cnt + 2`, `bt[cnt] := tt n`, `cnt := cnt + 1` (the step `st[cnt] := n` is a ghost).

* `CwSt`, `cwStep`, **`cwRun`** (the state after `n` steps);
* **`CwInv`** and `cwRun_inv` (the invariant after `n` steps);
* **`cw_final`**: for a walk of period `p ≤ N`, the corners are at increasing steps `< p`, each
  label marked `1` that occurs in the period is recorded exactly once (`mk = x + 2`), and the
  labels of the corners are distinct and first occurrences.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

/-- The state of the corner walk: the count, the marks, the corners (indices) and their steps. -/
structure CwSt where
  cnt : ℕ
  mks : ℕ → ℕ
  bt : ℕ → ℕ
  st : ℕ → ℕ

/-- One step of the corner walk at the label `f`, the index `t`, the step `n`. -/
def cwStep (f t n : ℕ) (s : CwSt) : CwSt :=
  if s.mks f = 1 then
    ⟨s.cnt + 1, fun a => if a = f then s.cnt + 2 else s.mks a,
      fun x => if x = s.cnt then t else s.bt x, fun x => if x = s.cnt then n else s.st x⟩
  else s

/-- **The corner walk** after `n` steps from the marks `mk0`. -/
def cwRun (g tt mk0 : ℕ → ℕ) : ℕ → CwSt
  | 0 => ⟨0, mk0, fun _ => 0, fun _ => 0⟩
  | n + 1 => cwStep (g n) (tt n) n (cwRun g tt mk0 n)

lemma cwRun_succ (g tt mk0 : ℕ → ℕ) (n : ℕ) :
    cwRun g tt mk0 (n + 1) = cwStep (g n) (tt n) n (cwRun g tt mk0 n) := rfl

/-- **The invariant of the corner walk** after `n` steps. -/
structure CwInv (g tt mk0 : ℕ → ℕ) (n : ℕ) (s : CwSt) : Prop where
  cnt_le : s.cnt ≤ n
  st_lt : ∀ x < s.cnt, s.st x < n ∧ s.bt x = tt (s.st x)
  mono : ∀ x y, x < y → y < s.cnt → s.st x < s.st y
  corner : ∀ x < s.cnt, s.mks (g (s.st x)) = x + 2 ∧ mk0 (g (s.st x)) = 1 ∧
    ∀ i < s.st x, g i ≠ g (s.st x)
  one : ∀ a, s.mks a = 1 ↔ (mk0 a = 1 ∧ ∀ i < n, g i ≠ a)
  keep : ∀ a, s.mks a = mk0 a ∨ (mk0 a = 1 ∧ 2 ≤ s.mks a)
  back : ∀ a, 2 ≤ s.mks a → s.mks a - 2 < s.cnt ∧ g (s.st (s.mks a - 2)) = a

lemma cwInv_zero (g tt mk0 : ℕ → ℕ) (h0 : ∀ a, mk0 a ≤ 1) :
    CwInv g tt mk0 0 (cwRun g tt mk0 0) where
  cnt_le := le_rfl
  st_lt x hx := absurd hx (Nat.not_lt_zero _)
  mono x y _ hy := absurd hy (Nat.not_lt_zero _)
  corner x hx := absurd hx (Nat.not_lt_zero _)
  one a := by simp [cwRun]
  keep a := Or.inl rfl
  back a ha := by have := h0 a; simp only [cwRun] at ha; omega

lemma cwInv_succ {g tt mk0 : ℕ → ℕ} {n : ℕ} {s : CwSt} (hs : CwInv g tt mk0 n s) :
    CwInv g tt mk0 (n + 1) (cwStep (g n) (tt n) n s) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hs
  unfold cwStep
  by_cases hf : s.mks (g n) = 1
  · simp only [hf, ↓reduceIte]
    have hfo := (i5 (g n)).1 hf
    refine ⟨by simp only; omega, fun x hx => ?_, fun x y hxy hy => ?_, fun x hx => ?_,
      fun a => ?_, fun a => ?_, fun a ha => ?_⟩
    · simp only at hx ⊢
      by_cases hxc : x = s.cnt
      · simp [hxc]
      · simp only [hxc, ↓reduceIte]
        have := i2 x (by omega); exact ⟨by omega, this.2⟩
    · simp only at hy ⊢
      by_cases hyc : y = s.cnt
      · simp only [hyc, ↓reduceIte, show x ≠ s.cnt by omega]
        exact (i2 x (by omega)).1
      · simp only [hyc, show x ≠ s.cnt by omega, ↓reduceIte]
        exact i3 x y hxy (by omega)
    · simp only at hx ⊢
      by_cases hxc : x = s.cnt
      · simp only [hxc, ↓reduceIte]
        exact ⟨by simp, hfo.1, fun i hi => hfo.2 i hi⟩
      · simp only [hxc, ↓reduceIte]
        obtain ⟨c1, c2, c3⟩ := i4 x (by omega)
        have hne : g (s.st x) ≠ g n := fun e => by rw [e, hf] at c1; omega
        simp only [hne, ↓reduceIte]
        exact ⟨c1, c2, c3⟩
    · simp only
      by_cases ha : a = g n
      · subst ha
        simp only [↓reduceIte]
        constructor
        · intro h; omega
        · rintro ⟨-, h⟩; exact absurd rfl (h n (by omega))
      · simp only [ha, ↓reduceIte]
        rw [i5 a]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact h2 i hi
          · exact fun e => ha e.symm
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 i (by omega)⟩
    · simp only
      by_cases ha : a = g n
      · subst ha; simp only [↓reduceIte]; exact Or.inr ⟨hfo.1, by omega⟩
      · simp only [ha, ↓reduceIte]; exact i6 a
    · simp only at ha ⊢
      by_cases hag : a = g n
      · subst hag
        simp only [↓reduceIte] at ha ⊢
        simp
      · simp only [hag, ↓reduceIte] at ha ⊢
        obtain ⟨b1, b2⟩ := i7 a ha
        refine ⟨by omega, ?_⟩
        simp only [show s.mks a - 2 ≠ s.cnt by omega, ↓reduceIte]
        exact b2
  · simp only [hf, ↓reduceIte]
    refine ⟨by omega, fun x hx => ?_, i3, i4, fun a => ?_, i6, i7⟩
    · have := i2 x hx; exact ⟨by omega, this.2⟩
    · rw [i5 a]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h2 i hi
        · intro e; subst e; exact hf ((i5 _).2 ⟨h1, h2⟩)
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 i (by omega)⟩

/-- **The invariant holds after every number of steps.** -/
theorem cwRun_inv (g tt mk0 : ℕ → ℕ) (h0 : ∀ a, mk0 a ≤ 1) :
    ∀ n, CwInv g tt mk0 n (cwRun g tt mk0 n)
  | 0 => cwInv_zero g tt mk0 h0
  | n + 1 => cwInv_succ (cwRun_inv g tt mk0 h0 n)

/-- **The corners of a periodic walk.** For a walk of period `p` (`g i = g (i % p)`, `0 < p`),
walked `N ≥ p` steps from the marks `mk0 ≤ 1`: the corners are at increasing steps `< p`, their
labels are first occurrences, marked `1` initially, distinct, with `mk = x + 2`; every label
marked `1` that occurs in the period is the label of a corner. -/
theorem cw_final (g tt mk0 : ℕ → ℕ) (h0 : ∀ a, mk0 a ≤ 1) {p N : ℕ} (hp : 0 < p) (hpN : p ≤ N)
    (hper : ∀ i, g i = g (i % p)) {s : CwSt} (hs : s = cwRun g tt mk0 N) :
    (∀ x < s.cnt, s.st x < p ∧ s.bt x = tt (s.st x) ∧ mk0 (g (s.st x)) = 1 ∧
      s.mks (g (s.st x)) = x + 2 ∧ ∀ i < s.st x, g i ≠ g (s.st x)) ∧
    (∀ x y, x < y → y < s.cnt → s.st x < s.st y) ∧
    (∀ a, mk0 a = 1 → (∃ i < p, g i = a) → 2 ≤ s.mks a ∧ s.mks a - 2 < s.cnt ∧
      g (s.st (s.mks a - 2)) = a) ∧
    (∀ a, mk0 a = 0 → s.mks a = 0) ∧ s.cnt ≤ N := by
  have hI : CwInv g tt mk0 N s := hs ▸ cwRun_inv g tt mk0 h0 N
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
  refine ⟨fun x hx => ?_, i3, fun a ha hex => ?_, fun a ha => ?_, i1⟩
  · obtain ⟨c1, c2, c3⟩ := i4 x hx
    obtain ⟨b1, b2⟩ := i2 x hx
    refine ⟨?_, b2, c2, c1, c3⟩
    by_contra hge
    push Not at hge
    have hlt : s.st x % p < s.st x := lt_of_lt_of_le (Nat.mod_lt _ hp) hge
    exact c3 _ hlt (hper (s.st x)).symm
  · obtain ⟨i, hi, hgi⟩ := hex
    have hne : s.mks a ≠ 1 := fun e => ((i5 a).1 e).2 i (by omega) hgi
    have h2 : 2 ≤ s.mks a := by rcases i6 a with e | ⟨-, e⟩ <;> omega
    exact ⟨h2, i7 a h2⟩
  · rcases i6 a with e | ⟨e, -⟩ <;> omega

/-- The labels of two corners are distinct. -/
theorem cw_labels_inj {g tt mk0 : ℕ → ℕ} {n : ℕ} {s : CwSt} (hs : CwInv g tt mk0 n s) {x y : ℕ}
    (hx : x < s.cnt) (hy : y < s.cnt) (e : g (s.st x) = g (s.st y)) : x = y := by
  have h1 := (hs.corner x hx).1
  have h2 := (hs.corner y hy).1
  rw [e] at h1; omega

end BKMNW

end PlanarFlow
