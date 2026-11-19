module

public import PlanarFlow.BKMNW.LsB2
public import PlanarFlow.BKMNW.LsG

/-!
# `sepL`: the path written by `lsB` is the certificate's (pure)

* `pathPD_congr` (`PathPD` from copied cells and an equal enumeration);
* **`pathPD_point`** (a one-vertex path `point x (tail x)` with `PD = [i₀ + 1, 0, …]`);
* `pick_eq_min` (a choice meeting `PkMin` with `gid` injective picks the first dart of an
  increasing enumeration), **`lsIs_dart`** (the empty case's dart index `lsIs` gives
  `if tail (pick) ∈ Q then rev pick else pick` on the piece map's first dart; `0` for `m = 0`);
* **`pemptyD_path`** (the path of `pemptyD` is a point at that dart), `core_sub_pdarts`,
  **`segsF_point_hole`** (a point inside a hole has no parts).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- `PathPD` from copied cells and an equal enumeration. -/
lemma pathPD_congr {e e' : ℕ → D} {n b b' : ℕ} {c c' : Config} {ρ : HPath M}
    (h : PathPD M e n b c ρ) (hm : ∀ j < n, c'.nmem (b' + j) = c.nmem (b + j))
    (he : ∀ i < n, e' i = e i) : PathPD M e' n b' c' ρ := by
  obtain ⟨hk, hd, hz⟩ := h
  refine ⟨hk, fun j hj => ?_, fun j hj hkj => by rw [hm j hj]; exact hz j hj hkj⟩
  obtain ⟨i, hi, h1, h2, h3⟩ := hd j hj
  exact ⟨i, hi, by rw [hm j (by omega)]; exact h1, by rw [he i hi]; exact h2, h3⟩

/-- **A one-vertex path on the machine**: `PD = [i₀ + 1, 0, …, 0]`. -/
lemma pathPD_point {e : ℕ → D} {n b i₀ : ℕ} {c : Config} {x : D} (hn : 1 ≤ n) (hi : i₀ < n)
    (hx : e i₀ = x) (h0 : c.nmem b = i₀ + 1) (hz : ∀ j, 0 < j → j < n → c.nmem (b + j) = 0) :
    PathPD M e n b c (SPath.point (M' := M) x (M.tail x)).toH := by
  refine ⟨hn, fun j hj => ?_, fun j hj hkj => hz j hkj hj⟩
  have hj0 : j = 0 := Nat.le_zero.1 hj
  subst hj0
  exact ⟨i₀, hi, by rw [Nat.add_zero]; exact h0, hx, rfl⟩

/-- A choice meeting `PkMin` (`gid` injective) picks the first dart of an increasing enumeration. -/
lemma pick_eq_min {gid : D → ℕ} (hgid : Injective gid) {pk : Finset D → D} (hpk : PkMin gid pk)
    {X : Finset D} {e : ℕ → D} {m : ℕ} (hm : 0 < m) (hmem : ∀ i < m, e i ∈ X)
    (hsurj : ∀ y ∈ X, ∃ i < m, e i = y) (hmono : ∀ i j, i < j → j < m → gid (e i) < gid (e j)) :
    pk X = e 0 := by
  obtain ⟨h1, h2⟩ := hpk X ⟨e 0, hmem 0 hm⟩
  obtain ⟨i, hi, hie⟩ := hsurj _ h1
  apply hgid
  have a1 := h2 _ (hmem 0 hm)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [hie]
  · have := hmono 0 i hpos hi
    rw [hie] at this
    omega

/-- **The index of the empty case's dart.** -/
lemma lsIs_dart {Q : Finset V} {ν : V → ℕ} (hQ : QPar Q ν) {g : ℕ → D} {f p : ℕ} {m : ℕ}
    (hm : 0 < m) (hp : g p = M.rev (g f)) :
    g (lsIs f (ν (M.tail (g f))) p m) =
      if M.tail (g f) ∈ Q then M.rev (g f) else g f := by
  have h1 : 1 - (1 - m) = 1 := by omega
  unfold lsIs
  rw [h1]
  by_cases hq : M.tail (g f) ∈ Q
  · have := (hQ _).1 hq
    rw [iteT hq, this]; simpa using hp
  · have : ν (M.tail (g f)) % 2 = 0 := (notMem_of_QPar hQ _).1 hq
    rw [iteF hq, this]; simp

lemma lsIs_zero (f v p : ℕ) : lsIs f v p 0 = 0 := by unfold lsIs; simp

/-- **The path of `pemptyD`** is a point at a dart. -/
lemma pemptyD_path (pc : PcChoice D V) (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) :
    (pemptyD M pc Q P Hs).2.1 = (SPath.point (M' := M)
      (if (pdarts M P Hs).Nonempty then
        (if M.tail (pc.pick (pdarts M P Hs)) ∈ Q then M.rev (pc.pick (pdarts M P Hs))
          else pc.pick (pdarts M P Hs)) else pc.pick P)
      (M.tail (if (pdarts M P Hs).Nonempty then
        (if M.tail (pc.pick (pdarts M P Hs)) ∈ Q then M.rev (pc.pick (pdarts M P Hs))
          else pc.pick (pdarts M P Hs)) else pc.pick P))).toH := by
  unfold pemptyD
  split_ifs <;> rfl

/-- The core's piece map is inside the piece map. -/
lemma core_sub_pdarts {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} :
    pdarts M (core M Q P) Hs ⊆ pdarts M P Hs := fun d hd => by
  rw [mem_pdarts] at hd ⊢
  exact ⟨(mem_core.1 hd.1).1, hd.2⟩

/-- **A point inside a hole has no parts.** -/
lemma segsF_point_hole {Hs : List (Finset V)} {x : D} (hx : M.tail x ∈ hunion Hs) :
    segsF (SPath.point (M' := M) x (M.tail x)).toH Hs = [] := by
  unfold segsF
  split_ifs with h
  · rw [HPath.runsF]
    have hk : ¬ (SPath.point (M' := M) x (M.tail x)).toH.k < 0 := by omega
    simp only [hk, ↓reduceDIte]
    have hp : (SPath.point (M' := M) x (M.tail x)).toH.p 0 ∈ hunion Hs := hx
    simp only [hp, ↓reduceDIte]
    exact HPath.runsF_of_lt _ h (by show 0 < 1; omega)
  · rfl

end MfDrv

end BKMNW

end PlanarFlow
