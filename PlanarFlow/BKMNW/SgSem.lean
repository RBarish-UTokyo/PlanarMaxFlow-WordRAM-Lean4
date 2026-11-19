module

public import PlanarFlow.BKMNW.SgX
public import PlanarFlow.BKMNW.SepSegs

/-!
# The parts of the separator with their start vertices (`SegsOut'`), and `sgProg`'s semantics

`SegsOut` stores only the darts of each part; a part with `k = 0` (a single vertex) is then
recorded nowhere. **`SegsOut'`** adds, after the darts, for each part `j` a frame dart index whose
tail is the part's start vertex `(π.segs[j]).p 0`:

* `mem (Gb + 1 + 2 s + L + j) = i` with `i < m` and `M.tail (en i) = (π.segs[j]).p 0`
  (`s = π.segs.length`, `L = Σ_j (π.segs[j]).k`), the block below `hi`.

* `SegsOut'`, `SegsOut'.congr`, `SegsOut'.mono`, `SegsOut'.toSegsOut`;
* **`segsOut'_sg`** (pure): the memory written by `sgProg` (`sgProg_exec`) is `SegsOut'` for a
  separator whose parts are `segsF ρ Hs` of a simple path `ρ` with its darts given by `PD`
  (`PathPD`-shaped), the core's darts `e' i = g (IX[i])`, the record's hole labels
  `HP[i] = hlab Hs (tail (g i))`, the frame `g (FX[f]) = en f`, and every core dart a frame dart.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The parts of the separator with their start vertices** (see the module docstring). -/
def SegsOut' (en : ℕ → D) (m : ℕ) (π : HSep M) (lo hi Gb : ℕ) (mem : ℕ → ℕ) : Prop :=
  SegsOut M en m π lo hi Gb mem ∧
    Gb + 1 + 3 * π.segs.length + (π.segs.map SPath.k).sum ≤ hi ∧
    ∀ (j : ℕ) (hj : j < π.segs.length),
      mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j) < m ∧
      M.tail (en (mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j))) =
        (π.segs[j]).p 0

lemma SegsOut'.toSegsOut {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem : ℕ → ℕ}
    (h : SegsOut' M en m π lo hi Gb mem) : SegsOut M en m π lo hi Gb mem := h.1

lemma SegsOut'.mono {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi hi' Gb : ℕ} {mem : ℕ → ℕ}
    (h : SegsOut' M en m π lo hi Gb mem) (hh : hi ≤ hi') : SegsOut' M en m π lo hi' Gb mem :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1.trans hh, h.1.2.2.2⟩, h.2.1.trans hh, h.2.2⟩

/-- `SegsOut'` depends only on the memory in `[Gb, hi)`. -/
lemma SegsOut'.congr {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem mem' : ℕ → ℕ}
    (h : SegsOut' M en m π lo hi Gb mem) (he : ∀ a, Gb ≤ a → a < hi → mem' a = mem a) :
    SegsOut' M en m π lo hi Gb mem' := by
  refine ⟨h.1.congr he, h.2.1, fun j hj => ?_⟩
  rw [he _ (by omega) (by have := h.2.1; omega)]
  exact h.2.2 j hj

/-- The data of the parts read from the list of the runs. -/
lemma segs_of_map {S : List (SPath M)} {R : List (ℕ × ℕ)} {d : ℕ → D} {p : ℕ → V}
    (h : S.map (fun σ => (σ.k, σ.d, σ.p)) =
      R.map (fun ab => (ab.2 - ab.1, fun i => d (ab.1 + i), fun i => p (ab.1 + i)))) :
    S.length = R.length ∧
    (∀ j (hj : j < S.length), (S[j]).k = sgLen R j ∧
      (∀ l, (S[j]).d l = d ((R.getD j (0, 0)).1 + l)) ∧
      (∀ l, (S[j]).p l = p ((R.getD j (0, 0)).1 + l))) ∧
    (∀ j, ((S.take j).map SPath.k).sum = sgOff R j) := by
  have hl : S.length = R.length := by
    have := congrArg List.length h; simpa using this
  refine ⟨hl, fun j hj => ?_, fun j => ?_⟩
  · have hjR : j < R.length := by omega
    have := congrArg (fun L => L[j]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjR,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    obtain ⟨h1, h2, h3⟩ := this
    refine ⟨?_, fun l => ?_, fun l => ?_⟩
    · unfold sgLen; rw [List.getD_eq_getElem _ _ hjR]; exact h1
    · rw [List.getD_eq_getElem _ _ hjR, h2]
    · rw [List.getD_eq_getElem _ _ hjR, h3]
  · have := congrArg (fun L => ((L.take j).map Prod.fst).sum) h
    simp only [← List.map_take, List.map_map] at this
    unfold sgOff
    exact this

/-- **`sgProg`'s output is `SegsOut'`** (see the module docstring). -/
theorem segsOut'_sg {ρ : HPath M} {Hs : List (Finset V)} (hρ : ρ.Simple Hs) {π : HSep M}
    (hπ : π.segs = segsF ρ Hs) {g en e' : ℕ → D} {n n' m : ℕ} {pd ix hp fx : ℕ → ℕ}
    (mem : ℕ → ℕ) {Gb lo hi : ℕ}
    (hk : ρ.k < n')
    (hPD : ∀ j ≤ ρ.k, ∃ i < n', pd j = i + 1 ∧ e' i = ρ.d j ∧ M.tail (ρ.d j) = ρ.p j)
    (hIX : ∀ i < n', ix i < n ∧ g (ix i) = e' i)
    (hHP : ∀ i < n, hp i = hlab Hs (M.tail (g i)))
    (hFX : ∀ f < m, fx f < n ∧ g (fx f) = en f)
    (hginj : ∀ i < n, ∀ j < n, g i = g j → i = j)
    (hcov : ∀ i < n', ∃ f < m, en f = e' i)
    (R : List (ℕ × ℕ)) (hRd : R = runIdx (fun j => decide (0 < hp (ix (pd j - 1)))) ρ.k 0)
    (mGb : mem Gb = R.length)
    (mOL : ∀ j < R.length, mem (Gb + 1 + j) = sgOff R j ∧ mem (Gb + 1 + R.length + j) = sgLen R j)
    (mD : ∀ j < R.length, ∀ l < sgLen R j, ∀ f < m,
      fx f = ix (pd ((R.getD j (0, 0)).1 + l) - 1) →
      mem (Gb + 1 + 2 * R.length + sgOff R j + l) = f)
    (mV : ∀ j < R.length, ∀ f < m, fx f = ix (pd (R.getD j (0, 0)).1 - 1) →
      mem (Gb + 1 + 2 * R.length + sgOff R R.length + j) = f)
    (hL : sgOff R R.length + 2 * R.length ≤ ρ.k + 2) (hlo : lo ≤ Gb) (hhi : Gb + 2 * n' + 3 ≤ hi) :
    SegsOut' M en m π lo hi Gb mem := by
  classical
  have hseg : π.segs = ρ.runsF hρ 0 := by rw [hπ, segsF]; exact dite_cond_eq_true (eq_true hρ)
  -- the flags of the path are the machine's
  have hfl : ∀ j ≤ ρ.k, pathFlags ρ Hs j = decide (0 < hp (ix (pd j - 1))) := fun j hj => by
    obtain ⟨i, hi, h1, h2, h3⟩ := hPD j hj
    obtain ⟨b1, b2⟩ := hIX i hi
    have e : hp (ix (pd j - 1)) = hlab Hs (ρ.p j) := by
      rw [h1, Nat.add_sub_cancel, hHP _ b1, b2, h2, h3]
    rw [e]
    cases hb : pathFlags ρ Hs j
    · have : ρ.p j ∉ hunion Hs := fun h' => by rw [pathFlags_iff.2 h'] at hb; cases hb
      exact (decide_eq_false fun h' => this (hlab_pos_iff.1 h')).symm
    · exact (decide_eq_true (hlab_pos_iff.2 (pathFlags_iff.1 hb))).symm
  have hmap := runsF_data ρ hρ 0
  rw [runIdx_congr hfl 0, ← hRd, ← hseg] at hmap
  obtain ⟨hlen, hjth, hsum⟩ := segs_of_map hmap
  have hsumT : (π.segs.map SPath.k).sum = sgOff R R.length := by
    rw [← hsum R.length, ← hlen, List.take_length]
  -- the frame index of a core dart
  have hfr : ∀ t ≤ ρ.k, ∃ f < m, fx f = ix (pd t - 1) ∧ en f = ρ.d t := fun t ht => by
    obtain ⟨i, hi, h1, h2, h3⟩ := hPD t ht
    obtain ⟨f, hf, hfe⟩ := hcov i hi
    obtain ⟨b1, b2⟩ := hIX i hi
    obtain ⟨c1, c2⟩ := hFX f hf
    refine ⟨f, hf, ?_, by rw [hfe, h2]⟩
    rw [h1, Nat.add_sub_cancel]
    exact hginj _ c1 _ b1 (by rw [c2, b2, hfe])
  have hrun : ∀ j < R.length, (R.getD j (0, 0)).1 ≤ (R.getD j (0, 0)).2 ∧
      (R.getD j (0, 0)).2 ≤ ρ.k := fun j hj => by
    rw [hRd] at hj ⊢; exact runIdx_getD_le _ _ hj
  refine ⟨⟨hlo, by rw [mGb, hlen], ?_, fun j hj => ?_⟩, ?_, fun j hj => ?_⟩
  · rw [hsumT, hlen]; omega
  · have hjR : j < R.length := by omega
    obtain ⟨k1, k2, k3⟩ := hjth j hj
    obtain ⟨o1, o2⟩ := mOL j hjR
    refine ⟨by rw [hsum j, o1], by rw [hlen, k1, o2], fun l hl => ?_⟩
    rw [k1] at hl
    have hr := hrun j hjR
    have ht : (R.getD j (0, 0)).1 + l ≤ ρ.k := by unfold sgLen at hl; omega
    obtain ⟨f, hf, hfx, hen⟩ := hfr _ ht
    have := mD j hjR l hl f hf hfx
    rw [hsum j, hlen, this, k2]
    exact ⟨hf, hen⟩
  · rw [hsumT, hlen]
    have : R.length ≤ ρ.k + 1 := by omega
    omega
  · have hjR : j < R.length := by omega
    obtain ⟨k1, k2, k3⟩ := hjth j hj
    have hr := hrun j hjR
    obtain ⟨f, hf, hfx, hen⟩ := hfr _ (hr.1.trans hr.2)
    have := mV j hjR f hf hfx
    rw [hsumT, hlen, this, k3, Nat.add_zero, hen]
    obtain ⟨i, hi, h1, h2, h3⟩ := hPD _ (hr.1.trans hr.2)
    exact ⟨hf, h3⟩

end MfDrv

end BKMNW

end PlanarFlow
