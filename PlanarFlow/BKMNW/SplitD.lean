module

public import PlanarFlow.BKMNW.ExistOracleD
public import PlanarFlow.BKMNW.DecA

/-!
# The split functions of the decomposition, made of explicit steps

The splits of `split_size` and `split_hole` as functions of the piece, given the choice functions
of the chain (`PcChoice`, a family of `ScChoice`, the rotation of the piece map of the core):

* `pcertF` (`pcertD` or `pemptyD`), **`pcert'`**;
* `splitD` (`splitOf` of the certificate, classes listed by `pc.ord`);
* `spSD`, `spHD` (the parameters `K`, `A` of `split_size`, `split_hole`), **`split_size'`**,
  **`split_hole'`**;
* **`splitFns_D`**: `SplitFns … (CInv M Q) (spSD …) (spHD …) (smC …)` for choices meeting their
  specifications; `exists_chainChoices`: such choices exist.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
open Classical in
/-- **The certificate of a piece, as a function**: `pcertD` if the piece map of the core is
nonempty, `pemptyD` otherwise. -/
noncomputable def pcertF (pc : PcChoice D V) (ch : ScChoice M) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) (K : ℕ) (σ : Perm D) : Option (Finset D × HPath M × Finset (Finset D)) :=
  if (pdarts M (core M Q P) Hs).Nonempty then pcertD M pc ch Q P Hs K σ
  else some (pemptyD M pc Q P Hs)

/-- **`pcert` as a function.** -/
theorem pcert' {S T Q : Finset V} (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hP0 : P.Nonempty) (K : ℕ) {A : ℕ}
    (hA : 2 * (P.card + K * nTouch M P Hs) + 2 + 9 * (6 * Nat.sqrt (2 * P.card) + 4) ≤ 3 * A)
    (hA2 : 2 ≤ A) {σ : Perm D} (hPM : PMap M (pdarts M (core M Q P) Hs) Hs σ)
    (pc : PcChoice D V) (hpc : pc.OK M Q P Hs) (ch : ScChoice M)
    (hch : ch.OK Hs A (P.card + K * nTouch M P Hs)) :
    ∃ c, pcertF M pc ch Q P Hs K σ = some c ∧
      PCertOf (M := M) Q P Hs K A (6 * Nat.sqrt (2 * P.card) + 4) c.1 c.2.1 c.2.2 := by
  unfold pcertF
  by_cases hne : (pdarts M (core M Q P) Hs).Nonempty
  · simp only [hne, ↓reduceIte]
    obtain ⟨ρ, I, h1, h2⟩ := pcert_of_core' hloopM hQdeg hQ5 hP hI hne K (by omega) hA hA2 hPM
      pc hpc ch hch
    exact ⟨_, h1, h2⟩
  · simp only [hne, ↓reduceIte]
    exact ⟨_, rfl, pcert_of_empty' hQdeg hQ5 hP hI hP0 (not_nonempty_iff_eq_empty.1 hne) K hA2
      (by omega) pc hpc⟩

variable (M) in
/-- **The split of a piece, as a function**: `splitOf` of the certificate `pcertF`, with the
classes listed by `pc.ord`. -/
noncomputable def splitD (pc : PcChoice D V) (ch : ScChoice M) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) (K A : ℕ) (σ : Perm D) : SplitAns M :=
  (pcertF M pc ch Q P Hs K σ).map fun c =>
    splitOf M P Hs K A c.1 c.2.1 (pc.ord (P.image (clsF M P c.1 Hs K c.2.1)))

/-- The bound `L = 6 √(2 #P) + 4` on the vertices of the separator. -/
def lS (P : Finset D) : ℕ := 6 * Nat.sqrt (2 * P.card) + 4

/-- The weight bound of the splits by size. -/
def aS (P : Finset D) : ℕ := (2 * P.card + 2 + 9 * lS P) / 3 + 1

/-- The weight of a hole in the splits by holes. -/
def kH (P : Finset D) : ℕ := P.card + 3 * lS P + 2

/-- The weight bound of the splits by holes. -/
def aH (P : Finset D) : ℕ := (2 * (P.card + 6 * kH P) + 2 + 9 * lS P) / 3 + 1

variable (M) in
/-- **The split by size, as a function** (`K = 0`, `A = aS P`). -/
noncomputable def spSD (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (σf : Finset D → List (Finset V) → Perm D) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) : SplitAns M :=
  splitD M pc (sc Hs (aS P) (P.card + 0 * nTouch M P Hs)) Q P Hs 0 (aS P) (σf P Hs)

variable (M) in
/-- **The split by holes, as a function** (`K = kH P`, `A = aH P`). -/
noncomputable def spHD (pc : PcChoice D V) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (σf : Finset D → List (Finset V) → Perm D) (Q : Finset V) (P : Finset D)
    (Hs : List (Finset V)) : SplitAns M :=
  splitD M pc (sc Hs (aH P) (P.card + kH P * nTouch M P Hs)) Q P Hs (kH P) (aH P) (σf P Hs)

/-- **`split_size` for the explicit function `spSD`.** -/
theorem split_size' {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hs : 100000 < P.card)
    (ht : nTouch M P Hs ≤ 5) (pc : PcChoice D V) (hpc : pc.OK M Q P Hs)
    (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset D → List (Finset V) → Perm D)
    (hσf : PMap M (pdarts M (core M Q P) Hs) Hs (σf P Hs)) :
    ∃ l r π, spSD M pc sc σf Q P Hs = some (l, r, π) ∧ SplitOK M S T 9 6 P Hs l r π ∧
      CInv M Q l (childHoles Hs π.path.mverts) ∧ CInv M Q r (childHoles Hs π.path.mverts) ∧
      4 * l.card ≤ 3 * P.card ∧ 4 * r.card ≤ 3 * P.card := by
  have hb := sqrt_bound hs
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  have hA : aS P = (2 * P.card + 2 + 9 * lS P) / 3 + 1 := rfl
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨c, hcD, hc⟩ := pcert' hloopM hQdeg hQ5 hP hI hP0 0 (A := aS P)
    (by simp only [zero_mul]; omega) (by omega) hσf pc hpc _ (hsc Hs _ _)
  obtain ⟨h1, h2, h3, h4, h5⟩ := exists_split_of_pcert' (κ := 9) hSTQ hP hI hc (hpc.ord _)
    (by omega) (fun h => absurd rfl h) (by simp only [zero_mul]; omega) (by omega)
    (fun _ => by omega) (fun h => absurd rfl h) (fun k hk => short_bound hs hk)
  rw [hw_eq, zero_mul, add_zero] at h4 h5
  refine ⟨_, _, _, ?_, h1, h2, h3, by omega, by omega⟩
  simp only [spSD, splitD, hcD, Option.map_some]

/-- **`split_hole` for the explicit function `spHD`.** -/
theorem split_hole' {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hs : 100000 < P.card)
    (ht : nTouch M P Hs = 6) (pc : PcChoice D V) (hpc : pc.OK M Q P Hs)
    (sc : List (Finset V) → ℕ → ℕ → ScChoice M) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset D → List (Finset V) → Perm D)
    (hσf : PMap M (pdarts M (core M Q P) Hs) Hs (σf P Hs)) :
    ∃ l r π, spHD M pc sc σf Q P Hs = some (l, r, π) ∧ SplitOK M S T 9 6 P Hs l r π ∧
      CInv M Q l (childHoles Hs π.path.mverts) ∧ CInv M Q r (childHoles Hs π.path.mverts) ∧
      nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
      nTouch M r (childHoles Hs π.path.mverts) ≤ 5 := by
  have hb := sqrt_bound hs
  have hL : lS P = 6 * Nat.sqrt (2 * P.card) + 4 := rfl
  have hK : kH P = P.card + 3 * lS P + 2 := rfl
  have hA : aH P = (2 * (P.card + 6 * kH P) + 2 + 9 * lS P) / 3 + 1 := rfl
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨c, hcD, hc⟩ := pcert' hloopM hQdeg hQ5 hP hI hP0 (kH P) (A := aH P)
    (by rw [ht]; omega) (by omega) hσf pc hpc _ (hsc Hs _ _)
  have hK0 : kH P ≠ 0 := by omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := exists_split_of_pcert' (κ := 9) hSTQ hP hI hc (hpc.ord _)
    (by omega) (fun _ => by omega) (by rw [ht]; omega) (by omega) (fun h => absurd h hK0)
    (fun _ => ⟨ht, by omega⟩) (fun k hk => short_bound hs hk)
  have hfew : ∀ X : Finset D, hw M (kH P) Hs c.2.1.mverts X ≤ aH P →
      nTouch M X (childHoles Hs c.2.1.mverts) ≤ 5 := by
    intro X hX
    refine (nTouch_ch_le hP.disj X).trans ?_
    rw [hw_eq] at hX
    by_contra h
    have h' : 5 ≤ (tH M Hs c.2.1.mverts X).card := by omega
    have := Nat.mul_le_mul_left (kH P) h'
    have : aH P < 5 * kH P := by omega
    linarith
  refine ⟨_, _, _, ?_, h1, h2, h3, hfew _ h4, hfew _ h5⟩
  simp only [spHD, splitD, hcD, Option.map_some]

/-- **The explicit split functions meet `SplitFns`** (with the invariant `CInv M Q`, `κ = 9`,
`s = 100000`, and the small pieces by `smC`), for choice functions meeting their specifications:
`pc.OK` on every piece, `(sc Hs A W).OK Hs A W`, and `σf P Hs` a rotation of the piece map of the
core of every piece meeting `CInv`. -/
theorem splitFns_D (hloop : ∀ d, M.head d ≠ M.tail d) {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (pc : PcChoice D V)
    (hpc : ∀ P Hs, pc.OK M Q P Hs) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) (σf : Finset D → List (Finset V) → Perm D)
    (hσf : ∀ P Hs, CInv M Q P Hs → PMap M (pdarts M (core M Q P) Hs) Hs (σf P Hs)) :
    SplitFns M S T 9 100000 (CInv M Q) (spSD M pc sc σf Q) (spHD M pc sc σf Q)
      (smC M S T 9 100000) := by
  refine ⟨(splitFns_choose (CInv M Q)
    (fun P Hs hP hs ht => exists_decOK_small (by norm_num) (by norm_num) hloop
      (fun t ht => hQdeg t (hSTQ ht)) _ P Hs rfl hP hs ht)
    (fun _ _ hP hI hs ht => split_size hSTQ hloop hQdeg hQ5 hP hI hs ht)
    (fun _ _ hP hI hs ht => split_hole hSTQ hloop hQdeg hQ5 hP hI hs ht)).small,
    fun P Hs hP hI hs ht => ?_, fun P Hs hP hI hs ht => ?_⟩
  · exact split_size' hSTQ hloop hQdeg hQ5 hP hI hs ht pc (hpc P Hs) sc hsc σf (hσf P Hs hI)
  · exact split_hole' hSTQ hloop hQdeg hQ5 hP hI hs ht pc (hpc P Hs) sc hsc σf (hσf P Hs hI)

open Classical in
/-- **Choice functions meeting the specifications of `splitFns_D` exist** (on a map without loops
with a dart). -/
theorem exists_chainChoices [Nonempty D] (hloop : ∀ d, M.head d ≠ M.tail d) (Q : Finset V) :
    (∃ pc : PcChoice D V, ∀ P Hs, pc.OK M Q P Hs) ∧
    (∃ sc : List (Finset V) → ℕ → ℕ → ScChoice M, ∀ Hs A W, (sc Hs A W).OK Hs A W) ∧
    (∃ σf : Finset D → List (Finset V) → Perm D,
      ∀ P Hs, CInv M Q P Hs → PMap M (pdarts M (core M Q P) Hs) Hs (σf P Hs)) := by
  refine ⟨⟨⟨fun E => if h : E.Nonempty then h.choose else Classical.arbitrary D,
      fun P Hs d => if h : ∃ b ∈ pdarts M (core M Q P) Hs, HRel Hs (M.tail b) (avQ M Q d) then
        h.choose else Classical.arbitrary D,
      fun P Hs H => if h : ∃ b ∈ pdarts M (core M Q P) Hs, M.tail b ∈ H then
        h.choose else Classical.arbitrary D,
      fun X => X.toList,
      fun X => if h : X.Nonempty then h.choose else Classical.arbitrary D⟩,
      fun P Hs => ⟨fun d => ?_, fun d h => ?_, fun H h => ?_, fun X => ⟨nodup_toList X, by simp⟩,
        fun X h => ?_⟩⟩, ⟨fun Hs A W => (exists_scChoice_ok (Hs := Hs) hloop A W).choose,
      fun Hs A W => (exists_scChoice_ok (Hs := Hs) hloop A W).choose_spec⟩,
      ⟨fun P Hs => if h : ∃ σ, PMap M (pdarts M (core M Q P) Hs) Hs σ then h.choose else 1,
        fun P Hs hI => ?_⟩⟩
  · have hne : ({d, M.rev d} : Finset D).Nonempty := ⟨d, by simp⟩
    have := hne.choose_spec
    simp only [hne, ↓reduceDIte]
    simpa [mem_insert, mem_singleton] using this
  · simp only [h, ↓reduceDIte]; exact h.choose_spec
  · simp only [h, ↓reduceDIte]; exact h.choose_spec
  · simp only [h, ↓reduceDIte]; exact h.choose_spec
  · have h := pmap_of_cinv hI
    simp only [h, ↓reduceDIte]; exact h.choose_spec

end BKMNW

end PlanarFlow
