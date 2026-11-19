module

public import PlanarFlow.NegSSSP.KEncNatT

/-!
# The distances from the first source, on natural words: Bellman–Ford in memory

`tpProg_tpar` (`KEncNatT.lean`) writes the shortest-path tree of the first source `u` from the
distances `(dist G u x).toNat` of the reached vertices (`G = pieceGraph M S ℓ`). Here a
Bellman–Ford pass on **natural words only**, in memory, computes them:

* `bfProg`: `D[y] := Inf` for the `n` nodes, `D[ιv u] := 0`, then `R` rounds, each relaxing
  every dart `j` of the piece (`S[j] > 0`) whose tail value `D[NT[j]]` is finite (`< Inf`):
  `D[NH[j]] := D[NT[j]] + L[j]` when smaller. `bfProg_natOnly`.
* `bf_step`: one relaxation keeps the invariant (`BFInv`: every finite value is the length of a
  walk from `u`, and is at most the length of every walk of at most `r` arcs; `BArc`: the darts
  already relaxed in the round).
* `bfProg_dist`: **with `R ≥ #V` rounds, `R · Lmax < Inf` (`Lmax` bounding the lengths, `> 0`
  on `S`) and `Inf + Lmax ≤ W`, at the end `D[ιv x] = (dist G u x).toNat` for every reached
  `x` and `D[ιv x] = Inf` otherwise**, within `R (24 nD + 6) + 5 n + 10` steps
  (`O(#V · #D)`, **weaker** than the `O(q log q)` of a heap Dijkstra; the program of
  `PlanarFlow/Dijkstra/` reads its graph from the input tape and keeps its arrays at fixed
  addresses, so it cannot be reused in memory as it is). A shortest walk can be taken with
  distinct tails (`MSSP.exists_nodup_walk`), hence with at most `#V` arcs.
* `spTreeProg := bfProg ; tpProg`, `spTreeProg_tpar`: **the parents of the shortest-path tree
  of `u` in memory** (`PAR[ιv x] = σ a` for `tpar G u x = some a`) from the arrays by darts and
  the reach bits, with `UniqTight G`.

Registers: natural `2400 … 2409` (inputs `nD`, `Sb`, `NTb`, `NHb`, `Lb`, `Db`, `n`, `R`, `Inf`,
`ιv u`), `2410 … 2421` (scratch). Natural memory is written only in `[Db, Db + n)`; no real
register or real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- `D[y] := Inf` (`y < n`), `D[u₀] := 0`, the constants `1`, `0` and the round counter. -/
def bfInit : Stmt :=
  .seq (block [.constN 2410 1, .constN 2411 0, .constN 2412 0])
    (.seq (.whileLtN 2412 2406 (block [.addN 2414 2405 2412, .storeN 2414 2408,
        .addN 2412 2412 2410]))
      (block [.addN 2414 2405 2409, .storeN 2414 2411, .constN 2413 0]))

/-- The loads of the dart `j = r2412`: `S[j]` (`2414`), `t = NT[j]` (`2415`), `h = NH[j]`
(`2416`), `D[t]` (`2417`), `D[h]` (`2418`), `L[j]` (`2419`), the address `Db + h` (`2420`). -/
def bfLoad : Stmt :=
  block [.addN 2414 2401 2412, .loadN 2414 2414, .addN 2415 2402 2412, .loadN 2415 2415,
    .addN 2416 2403 2412, .loadN 2416 2416, .addN 2417 2405 2415, .loadN 2417 2417,
    .addN 2418 2405 2416, .loadN 2418 2418, .addN 2419 2404 2412, .loadN 2419 2419,
    .addN 2420 2405 2416]

/-- The relaxation of the dart. -/
def bfTest : Stmt :=
  .ifLtN 2411 2414
    (.ifLtN 2417 2408
      (.seq (.instr (.addN 2421 2417 2419)) (.ifLtN 2421 2418 (.instr (.storeN 2420 2421)) .skip))
      .skip)
    .skip

/-- The body of a round. -/
def bfBody : Stmt := .seq bfLoad (.seq bfTest (block [.addN 2412 2412 2410]))

/-- A round. -/
def bfRound : Stmt :=
  .seq (block [.constN 2412 0]) (.seq (.whileLtN 2412 2400 bfBody) (block [.addN 2413 2413 2410]))

/-- **Bellman–Ford in memory, on natural words.** -/
def bfProg : Stmt := .seq bfInit (.whileLtN 2413 2407 bfRound)

/-- **`bfProg` has no real instruction** (checked by the kernel). -/
theorem bfProg_natOnly : Klein.natOnly bfProg = true := by kernel_rfl

/-! ### The relaxation of one dart on the machine -/

theorem bfTest_exec (c : Config) (hc : WordsBounded W c) (h11 : c.nreg 2411 = 0)
    (hW : 0 < c.nreg 2414 → c.nreg 2417 < c.nreg 2408 → c.nreg 2417 + c.nreg 2419 ≤ W) :
    ∃ c' t, Exec P W bfTest c c' t ∧ t ≤ 8 ∧
      c'.nmem = (if 0 < c.nreg 2414 ∧ c.nreg 2417 < c.nreg 2408 ∧
          c.nreg 2417 + c.nreg 2419 < c.nreg 2418 then
        upd c.nmem (c.nreg 2420) (c.nreg 2417 + c.nreg 2419) else c.nmem) ∧
      (∀ r, r ≠ 2421 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold bfTest
  by_cases h1 : 0 < c.nreg 2414
  · refine spec_ifLtN_true (by rw [h11]; exact h1) ?_
    by_cases h2 : c.nreg 2417 < c.nreg 2408
    · refine spec_ifLtN_true h2 ?_
      refine spec_seq ?_
      refine spec_instr (Exec.addN hc 2421 2417 2419 (hW h1 h2)) fun hw₁ => ?_
      by_cases h3 : c.nreg 2417 + c.nreg 2419 < c.nreg 2418
      · refine spec_ifLtN_true (by config_simp; exact h3) ?_
        refine spec_instr (Exec.storeN hw₁ _ _) fun _ => ⟨by omega, ?_, fun r hr => ?_, rfl, rfl,
          rfl⟩
        · config_simp
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2, h3⟩)]
        · config_simp; rw [upd_other _ _ _ hr]
      · refine spec_ifLtN_false (by config_simp; exact h3) (spec_skip hw₁ ⟨by omega, ?_,
          fun r hr => ?_, rfl, rfl, rfl⟩)
        · config_simp
          rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h3 h.2.2)]
        · config_simp; rw [upd_other _ _ _ hr]
    · refine spec_ifLtN_false h2 (spec_skip hc ⟨by omega, ?_, fun r _ => rfl, rfl, rfl, rfl⟩)
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h2 h.2.1)]
  · refine spec_ifLtN_false (by rw [h11]; exact h1) (spec_skip hc ⟨by omega, ?_, fun r _ => rfl,
      rfl, rfl, rfl⟩)
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h1 h.1)]

/-! ### The invariant of the rounds -/

section Math

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

lemma wlen_le_length {Lmax : ℕ} (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax) (hpos : ∀ d ∈ S, 0 < ℓ d)
    (l : List {d // d ∈ S}) : MSSP.wlen (MSSP.pieceGraph M S ℓ) l ≤ (l.length * Lmax : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [MSSP.wlen_cons, List.length_cons, add_mul, one_mul]
    have h1 := hL a.1 a.2
    have h2 := Int.toNat_of_nonneg (hpos a.1 a.2).le
    have e : (MSSP.pieceGraph M S ℓ).len a = ℓ a.1 := rfl
    rw [e]
    push_cast at ih ⊢
    omega

/-- **The invariant after `r` rounds**: every finite value is the length of a walk from `u`;
every value is at most the length of every walk of at most `r` arcs, and at most `Inf`. -/
def BFInv (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) (u : V) (ιv : V → ℕ) (Db Inf r : ℕ)
    (m : ℕ → ℕ) : Prop :=
  (∀ x, m (Db + ιv x) < Inf → ∃ l, MSSP.LWalk (MSSP.pieceGraph M S ℓ) u x l ∧
    MSSP.wlen (MSSP.pieceGraph M S ℓ) l = (m (Db + ιv x) : ℤ)) ∧
  (∀ x l, MSSP.LWalk (MSSP.pieceGraph M S ℓ) u x l → l.length ≤ r →
    (m (Db + ιv x) : ℤ) ≤ MSSP.wlen (MSSP.pieceGraph M S ℓ) l) ∧
  (∀ x, m (Db + ιv x) ≤ Inf)

/-- **The darts already relaxed in the current round** (numbers `< i`): the value at the head is
at most that of a walk of at most `r` arcs to the tail, plus the length. -/
def BArc (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) (u : V) (ιv : V → ℕ) {nD : ℕ}
    (σ : D ≃ Fin nD) (Db r i : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ (a : {d // d ∈ S}) (l : List {d // d ∈ S}),
    MSSP.LWalk (MSSP.pieceGraph M S ℓ) u (M.tail a.1) l → l.length ≤ r → (σ a.1 : ℕ) < i →
      (m (Db + ιv (M.head a.1)) : ℤ) ≤ MSSP.wlen (MSSP.pieceGraph M S ℓ) l + ℓ a.1

/-- The memory after the relaxation of the dart `d`. -/
def bfRelax (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) (ιv : V → ℕ) (Db Inf : ℕ) (d : D)
    (m : ℕ → ℕ) : ℕ → ℕ :=
  if d ∈ S ∧ m (Db + ιv (M.tail d)) < Inf ∧
      m (Db + ιv (M.tail d)) + (ℓ d).toNat < m (Db + ιv (M.head d)) then
    upd m (Db + ιv (M.head d)) (m (Db + ιv (M.tail d)) + (ℓ d).toNat) else m

/-- **One relaxation keeps the invariant.** -/
theorem bf_step {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {nD : ℕ} {σ : D ≃ Fin nD}
    {Db Inf Lmax r i : ℕ} (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hr : r * Lmax < Inf) {m : ℕ → ℕ} (hI : BFInv M S ℓ u ιv Db Inf r m)
    (hA : BArc M S ℓ u ιv σ Db r i m) {d : D} (hd : (σ d : ℕ) = i) :
    BFInv M S ℓ u ιv Db Inf r (bfRelax M S ℓ ιv Db Inf d m) ∧
      BArc M S ℓ u ιv σ Db r (i + 1) (bfRelax M S ℓ ιv Db Inf d m) := by
  obtain ⟨W1, W2, W3⟩ := hI
  have hinj' : ∀ x y, Db + ιv x = Db + ιv y ↔ x = y := fun x y =>
    ⟨fun h => hinj (by omega), fun h => by rw [h]⟩
  -- the value of the tail is finite along a short walk
  have hfin : ∀ l, MSSP.LWalk (MSSP.pieceGraph M S ℓ) u (M.tail d) l → l.length ≤ r →
      m (Db + ιv (M.tail d)) < Inf := fun l hl hlen => by
    have h1 := W2 _ l hl hlen
    have h2 := wlen_le_length (M := M) hL hpos l
    have h3 : l.length * Lmax ≤ r * Lmax := Nat.mul_le_mul_right _ hlen
    have : (m (Db + ιv (M.tail d)) : ℤ) < Inf := by
      have : ((l.length * Lmax : ℕ) : ℤ) ≤ ((r * Lmax : ℕ) : ℤ) := by exact_mod_cast h3
      have : ((r * Lmax : ℕ) : ℤ) < Inf := by exact_mod_cast hr
      omega
    exact_mod_cast this
  by_cases hc : d ∈ S ∧ m (Db + ιv (M.tail d)) < Inf ∧
      m (Db + ιv (M.tail d)) + (ℓ d).toNat < m (Db + ιv (M.head d))
  · obtain ⟨hS, hT, hlt⟩ := hc
    have e : bfRelax M S ℓ ιv Db Inf d m =
        upd m (Db + ιv (M.head d)) (m (Db + ιv (M.tail d)) + (ℓ d).toNat) := by
      unfold bfRelax; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hS, hT, hlt⟩)]
    have hv : ∀ x, bfRelax M S ℓ ιv Db Inf d m (Db + ιv x) =
        if x = M.head d then m (Db + ιv (M.tail d)) + (ℓ d).toNat else m (Db + ιv x) := by
      intro x
      rw [e, upd_apply]
      by_cases hx : x = M.head d
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ((hinj' x _).2 hx)),
          ite_eq_left_of_eq_true _ _ (eq_true hx)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hx ((hinj' x _).1 h)),
          ite_eq_right_of_eq_false _ _ (eq_false hx)]
    have hdec : ∀ x, bfRelax M S ℓ ιv Db Inf d m (Db + ιv x) ≤ m (Db + ιv x) := fun x => by
      rw [hv]; split_ifs with hx
      · subst hx; omega
      · exact le_rfl
    have hℓ := Int.toNat_of_nonneg (hpos d hS).le
    refine ⟨⟨fun x hx => ?_, fun x l hl hlen => ?_, fun x => (hdec x).trans (W3 x)⟩,
      fun a l hl hlen ha => ?_⟩
    · rw [hv] at hx ⊢
      split_ifs with hxe
      · subst hxe
        obtain ⟨l, hl, hw⟩ := W1 _ hT
        have hw' : MSSP.LWalk (MSSP.pieceGraph M S ℓ) u (M.head d) (l ++ [⟨d, hS⟩]) :=
          MSSP.LWalk.concat (G := MSSP.pieceGraph M S ℓ) (a := (⟨d, hS⟩ : {d // d ∈ S})) hl rfl
        refine ⟨l ++ [⟨d, hS⟩], hw', ?_⟩
        rw [MSSP.wlen_append, hw]
        simp only [MSSP.wlen_cons, MSSP.wlen_nil, add_zero]
        change _ + ℓ d = _
        push_cast; rw [hℓ]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hxe)] at hx; exact W1 x hx
    · have := W2 x l hl hlen
      have := hdec x
      push_cast at *; omega
    · by_cases hai : (σ a.1 : ℕ) = i
      · have had : a.1 = d := σ.injective (Fin.ext (hai.trans hd.symm))
        obtain ⟨a, haS⟩ := a
        simp only at had hl ⊢
        subst had
        rw [hv, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        have := W2 _ l hl hlen
        push_cast; rw [hℓ]; omega
      · have := hA a l hl hlen (by omega)
        have := hdec (M.head a.1)
        push_cast at *; omega
  · have e : bfRelax M S ℓ ιv Db Inf d m = m := by
      unfold bfRelax; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rw [e]
    refine ⟨⟨W1, W2, W3⟩, fun a l hl hlen ha => ?_⟩
    by_cases hai : (σ a.1 : ℕ) = i
    · have had : a.1 = d := σ.injective (Fin.ext (hai.trans hd.symm))
      obtain ⟨a, haS⟩ := a
      simp only at had hl ⊢
      subst had
      have hT := hfin l hl hlen
      have h1 := W2 _ l hl hlen
      have hℓ := Int.toNat_of_nonneg (hpos a haS).le
      have : ¬ m (Db + ιv (M.tail a)) + (ℓ a).toNat < m (Db + ιv (M.head a)) :=
        fun h => hc ⟨haS, hT, h⟩
      omega
    · exact hA a l hl hlen (by omega)

/-- **The end of a round**: all the darts relaxed, the invariant holds for one more arc. -/
theorem bfInv_succ {u : V} {ιv : V → ℕ} {nD : ℕ} {σ : D ≃ Fin nD} {Db Inf r : ℕ}
    {m : ℕ → ℕ} (hI : BFInv M S ℓ u ιv Db Inf r m) (hA : BArc M S ℓ u ιv σ Db r nD m) :
    BFInv M S ℓ u ιv Db Inf (r + 1) m := by
  obtain ⟨W1, W2, W3⟩ := hI
  refine ⟨W1, fun x l hl hlen => ?_, W3⟩
  by_cases hle : l.length ≤ r
  · exact W2 x l hl hle
  · rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
    · simp at hle
    · rw [List.concat_eq_append] at hl hle hlen ⊢
      obtain ⟨hl', hx⟩ := MSSP.LWalk.concat_iff.1 hl
      simp only [List.length_append, List.length_singleton] at hle hlen
      have := hA a l' hl' (by omega) (σ a.1).2
      have hx' : M.head a.1 = x := hx
      rw [hx'] at this
      rw [MSSP.wlen_append]
      simp only [MSSP.wlen_cons, MSSP.wlen_nil, add_zero]
      exact this

/-- **After `R ≥ #V` rounds the values are the distances.** -/
theorem bfInv_dist {u : V} {ιv : V → ℕ} {Db Inf R Lmax : ℕ} (hpos : ∀ d ∈ S, 0 < ℓ d)
    (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax) (hR : Fintype.card V ≤ R) (hRL : R * Lmax < Inf)
    {m : ℕ → ℕ} (hI : BFInv M S ℓ u ιv Db Inf R m) :
    (∀ x, MSSP.Reach (MSSP.pieceGraph M S ℓ) u x →
      m (Db + ιv x) = (MSSP.dist (MSSP.pieceGraph M S ℓ) u x).toNat) ∧
    (∀ x, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x → m (Db + ιv x) = Inf) := by
  classical
  obtain ⟨W1, W2, W3⟩ := hI
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨l, hl, hw⟩ := MSSP.exists_walk_dist hnn hx
    obtain ⟨l', hl', hsub, hnd⟩ := MSSP.exists_nodup_walk hl
    have hlen : l'.length ≤ R := by
      have := hnd.length_le_card
      rw [List.length_map] at this
      omega
    have hw' : MSSP.wlen (MSSP.pieceGraph M S ℓ) l' ≤ MSSP.wlen (MSSP.pieceGraph M S ℓ) l :=
      List.Sublist.sum_le_sum (hsub.map _) (fun a ha => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact hnn b)
    have h1 := W2 x l' hl' hlen
    have h2 := wlen_le_length (M := M) hL hpos l'
    have h3 : l'.length * Lmax ≤ R * Lmax := Nat.mul_le_mul_right _ hlen
    have hlt : m (Db + ιv x) < Inf := by
      have : ((l'.length * Lmax : ℕ) : ℤ) ≤ ((R * Lmax : ℕ) : ℤ) := by exact_mod_cast h3
      have : ((R * Lmax : ℕ) : ℤ) < Inf := by exact_mod_cast hRL
      have : (m (Db + ιv x) : ℤ) < Inf := by omega
      exact_mod_cast this
    obtain ⟨l₀, hl₀, hw₀⟩ := W1 x hlt
    have h4 := MSSP.dist_le hnn hl₀
    have h5 := MSSP.dist_nonneg hnn hx
    omega
  · have h1 := W3 x
    by_contra hne
    obtain ⟨l, hl, -⟩ := W1 x (by omega)
    exact hx ⟨l, hl⟩

end Math

/-! ### The rounds on the machine -/

section Run

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

/-- The layout of `bfProg`: the arrays by darts (`nD` words) and the values (`n` words) below
`W`, the values apart from the arrays. -/
structure BFLay (nD n Sb NTb NHb Lb Db Inf Lmax W : ℕ) : Prop where
  one : 1 ≤ W
  wS : Sb + nD ≤ W
  wT : NTb + nD ≤ W
  wH : NHb + nD ≤ W
  wL : Lb + nD ≤ W
  wD : Db + n ≤ W
  wI : Inf + Lmax ≤ W
  dS : Sb + nD ≤ Db ∨ Db + n ≤ Sb
  dT : NTb + nD ≤ Db ∨ Db + n ≤ NTb
  dH : NHb + nD ≤ Db ∨ Db + n ≤ NHb
  dL : Lb + nD ≤ Db ∨ Db + n ≤ Lb

/-- The inputs of `bfProg` in memory, by the numbering `σ` and the nodes `ιv`. -/
structure BFIn (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ} (σ : D ≃ Fin nD)
    (ιv : V → ℕ) (Sb NTb NHb Lb : ℕ) (c : Config) : Prop where
  fl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S
  nt : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d)
  nh : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d)
  ln : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat

lemma BFIn.frame {nD : ℕ} {σ : D ≃ Fin nD} {ιv : V → ℕ} {Sb NTb NHb Lb Db n Inf Lmax : ℕ}
    (hL : BFLay nD n Sb NTb NHb Lb Db Inf Lmax W) {c c' : Config}
    (h : BFIn M S ℓ σ ιv Sb NTb NHb Lb c)
    (hm : ∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) : BFIn M S ℓ σ ιv Sb NTb NHb Lb c' := by
  have := hL.dS; have := hL.dT; have := hL.dH; have := hL.dL
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d hd => ?_⟩
  · rw [hm _ (by have := (σ d).2; omega)]; exact h.fl d
  · rw [hm _ (by have := (σ d).2; omega)]; exact h.nt d
  · rw [hm _ (by have := (σ d).2; omega)]; exact h.nh d
  · rw [hm _ (by have := (σ d).2; omega)]; exact h.ln d hd

theorem bfInit_exec {Db n Inf u₀ : ℕ} (hu : u₀ < n) (hW : Db + n ≤ W) (h1 : 1 ≤ W)
    (c : Config) (hc : WordsBounded W c) (h05 : c.nreg 2405 = Db) (h06 : c.nreg 2406 = n)
    (h08 : c.nreg 2408 = Inf) (h09 : c.nreg 2409 = u₀) :
    ∃ c' t, Exec P W bfInit c c' t ∧ t ≤ 5 * n + 10 ∧
      ((∀ y < n, c'.nmem (Db + y) = if y = u₀ then 0 else Inf) ∧
        (∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 2410 = 1 ∧ c'.nreg 2411 = 0 ∧ c'.nreg 2413 = 0 ∧
        (∀ r, r < 2410 ∨ 2422 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold bfInit
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < i, c'.nmem (Db + y) = Inf) ∧ (∀ a, a < Db ∨ Db + i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2412 → r ≠ 2414 → c'.nreg r = (upd (upd c.nreg 2410 1) 2411 0) r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 2412) (bR := 2406)
    (body := block [.addN 2414 2405 2412, .storeN 2414 2408, .addN 2412 2412 2410]) J (K := 3)
    (n := n) _ ‹_› (by config_simp) (by config_simp; exact h06) ?_
    (fun i c₁ hi hw ha hb ⟨g, gnm, gn, gr, grm, go⟩ => by
      have e05 : c₁.nreg 2405 = Db := by rw [gn _ (by omega) (by omega)]; config_simp; exact h05
      have e08 : c₁.nreg 2408 = Inf := by rw [gn _ (by omega) (by omega)]; config_simp; exact h08
      have e10 : c₁.nreg 2410 = 1 := by rw [gn _ (by omega) (by omega)]; config_simp
      exec_block
      all_goals try ((try config_simp); (try simp only [e05, e08, e10, ha]); omega)
      refine ⟨by omega, by config_simp; rw [ha, e10], by config_simp; exact hb, fun y hy => ?_,
        fun a ha' => ?_, fun r h1 h2 => ?_, gr, grm, go⟩
      all_goals config_simp
      all_goals try simp only [e05, e08, e10, ha]
      · rw [upd_apply]; split_ifs with h
        · rfl
        · exact g y (by omega)
      · rw [upd_other _ _ _ (by omega)]; exact gnm a (by omega)
      · rw [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact gn r h1 h2)) ?_
  · refine ⟨fun y hy => absurd hy (by omega), fun a _ => rfl, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    config_simp; rw [upd_other _ _ _ h1]
  rintro c₂ k₂ hk₂ hw₂ ⟨_, g, gnm, gn, gr, grm, go⟩
  have e05 : c₂.nreg 2405 = Db := by rw [gn _ (by omega) (by omega)]; config_simp; exact h05
  have e09 : c₂.nreg 2409 = u₀ := by rw [gn _ (by omega) (by omega)]; config_simp; exact h09
  have e10 : c₂.nreg 2410 = 1 := by rw [gn _ (by omega) (by omega)]; config_simp
  have e11 : c₂.nreg 2411 = 0 := by rw [gn _ (by omega) (by omega)]; config_simp
  exec_block
  all_goals try ((try config_simp); (try simp only [e05, e09]); omega)
  refine ⟨by omega, fun y hy => ?_, fun a ha => ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  all_goals config_simp
  all_goals try simp only [e05, e09, e10, e11]
  · rw [upd_apply]
    by_cases h : y = u₀
    · subst h; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact g y hy
  · rw [upd_other _ _ _ (by omega)]; exact gnm a ha
  · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), gn _ (by omega) (by omega)]
    simp (disch := omega) only [upd_other]
  · exact gr
  · exact grm
  · exact go

set_option maxHeartbeats 4000000 in
/-- **One round on the machine** keeps the invariant for one more arc. -/
theorem bfRound_exec {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {n : ℕ}
    (hιn : ∀ x, ιv x < n) {nD : ℕ} (σ : D ≃ Fin nD) {Sb NTb NHb Lb Db Inf Lmax r R : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hLay : BFLay nD n Sb NTb NHb Lb Db Inf Lmax W) (hrR : r < R) (hRL : R * Lmax < Inf)
    (hRW : R ≤ W)
    (c : Config) (hc : WordsBounded W c) (hIn : BFIn M S ℓ σ ιv Sb NTb NHb Lb c)
    (hI : BFInv M S ℓ u ιv Db Inf r c.nmem)
    (h00 : c.nreg 2400 = nD) (h01 : c.nreg 2401 = Sb) (h02 : c.nreg 2402 = NTb)
    (h03 : c.nreg 2403 = NHb) (h04 : c.nreg 2404 = Lb) (h05 : c.nreg 2405 = Db)
    (h08 : c.nreg 2408 = Inf) (h10 : c.nreg 2410 = 1) (h11 : c.nreg 2411 = 0)
    (h13 : c.nreg 2413 = r) :
    ∃ c' t, Exec P W bfRound c c' t ∧ t ≤ 24 * nD + 4 ∧
      (BFInv M S ℓ u ιv Db Inf (r + 1) c'.nmem ∧ c'.nreg 2413 = r + 1 ∧
        (∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ q, q < 2412 ∨ 2422 ≤ q → c'.nreg q = c.nreg q) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hLay.one; have := hLay.wS; have := hLay.wT; have := hLay.wH; have := hLay.wL
  have := hLay.wD; have := hLay.wI; have := hLay.dS; have := hLay.dT; have := hLay.dH
  have := hLay.dL
  have hrL : r * Lmax < Inf := lt_of_le_of_lt (Nat.mul_le_mul_right _ hrR.le) hRL
  unfold bfRound
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    BFInv M S ℓ u ιv Db Inf r c'.nmem ∧ BArc M S ℓ u ιv σ Db r i c'.nmem ∧
      (∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2412 ∨ q = 2413 ∨ 2422 ≤ q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 2412) (bR := 2400) (body := bfBody) J (K := 22)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact h00) ?_
    (fun i c₁ hi hw ha hb ⟨gI, gA, gnm, gn, gr, grm, go⟩ => by
      have e01 : c₁.nreg 2401 = Sb := (gn 2401 (by omega)).trans h01
      have e02 : c₁.nreg 2402 = NTb := (gn 2402 (by omega)).trans h02
      have e03 : c₁.nreg 2403 = NHb := (gn 2403 (by omega)).trans h03
      have e04 : c₁.nreg 2404 = Lb := (gn 2404 (by omega)).trans h04
      have e05 : c₁.nreg 2405 = Db := (gn 2405 (by omega)).trans h05
      have e08 : c₁.nreg 2408 = Inf := (gn 2408 (by omega)).trans h08
      have e10 : c₁.nreg 2410 = 1 := (gn 2410 (by omega)).trans h10
      have e11 : c₁.nreg 2411 = 0 := (gn 2411 (by omega)).trans h11
      have hIn₁ := hIn.frame hLay gnm
      set d := σ.symm ⟨i, hi⟩ with hd
      have hσd : (σ d : ℕ) = i := by rw [hd]; simp
      have xf : (0 < c₁.nmem (Sb + i)) ↔ d ∈ S := by rw [← hσd]; exact hIn₁.fl d
      have xt : c₁.nmem (NTb + i) = ιv (M.tail d) := by rw [← hσd]; exact hIn₁.nt d
      have xh : c₁.nmem (NHb + i) = ιv (M.head d) := by rw [← hσd]; exact hIn₁.nh d
      have xl : d ∈ S → c₁.nmem (Lb + i) = (ℓ d).toNat := fun h => by
        rw [← hσd]; exact hIn₁.ln d h
      have tlt := hιn (M.tail d)
      have hlt := hιn (M.head d)
      obtain ⟨c₂, k₂, e₂, hk₂, p14, p17, p18, p19, p20, p10, p11, p12, pn, pnm, pr, prm, po⟩ :
          ∃ c₂ k₂, Exec P W bfLoad c₁ c₂ k₂ ∧ k₂ ≤ 13 ∧
            c₂.nreg 2414 = c₁.nmem (Sb + i) ∧
            c₂.nreg 2417 = c₁.nmem (Db + ιv (M.tail d)) ∧
            c₂.nreg 2418 = c₁.nmem (Db + ιv (M.head d)) ∧
            c₂.nreg 2419 = c₁.nmem (Lb + i) ∧ c₂.nreg 2420 = Db + ιv (M.head d) ∧
            c₂.nreg 2410 = 1 ∧ c₂.nreg 2411 = 0 ∧ c₂.nreg 2412 = i ∧
            (∀ q, q < 2414 ∨ 2421 ≤ q → c₂.nreg q = c₁.nreg q) ∧ c₂.nmem = c₁.nmem ∧
            c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        unfold bfLoad
        exec_block
        all_goals try ((try config_simp); (try simp only [e01, e02, e03, e04, e05, ha, xt, xh]); omega)
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [e01, e02, e03, e04, e05, e10, e11, ha, xt, xh]
        simp (disch := omega) only [upd_other]
      have hW' : 0 < c₂.nreg 2414 → c₂.nreg 2417 < c₂.nreg 2408 →
          c₂.nreg 2417 + c₂.nreg 2419 ≤ W := fun h1 h2 => by
        rw [p14] at h1
        have hS := xf.1 h1
        rw [p17, p19, xl hS]
        rw [p17, pn 2408 (by omega), e08] at h2
        have := hL d hS
        omega
      obtain ⟨c₃, k₃, e₃, hk₃, qm, qn, qr, qrm, qo⟩ := bfTest_exec (P := P) c₂ e₂.wb_right p11 hW'
      have hrel : c₃.nmem = bfRelax M S ℓ ιv Db Inf d c₁.nmem := by
        rw [qm, p14, p17, p18, p19, p20, pn _ (by omega), e08, pnm]
        unfold bfRelax
        by_cases hS : d ∈ S
        · rw [xl hS]
          simp only [xf.2 hS, hS, true_and]
        · have h0 : ¬ 0 < c₁.nmem (Sb + i) := fun h => hS (xf.1 h)
          simp only [h0, hS, false_and, ↓reduceIte]
      obtain ⟨hI', hA'⟩ := bf_step hinj hpos hL hrL gI gA hσd
      have hw₃ := e₃.wb_right
      have e₄ := Exec.addN (P := P) hw₃ 2412 2412 2410 (by rw [qn _ (by omega), qn _ (by omega), p12, p10]; omega)
      refine ⟨_, _, Exec.seq e₂ (Exec.seq e₃ (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right))),
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · config_simp; rw [qn _ (by omega), qn _ (by omega), p12, p10]
      · config_simp; rw [qn _ (by omega), pn _ (by omega), hb]
      · config_simp; rw [hrel]; exact hI'
      · config_simp; rw [hrel]; exact hA'
      · intro a ha'
        config_simp
        rw [hrel]
        unfold bfRelax
        split_ifs
        · rw [upd_other _ _ _ (by have := hιn (M.head d); omega)]; exact gnm a ha'
        · exact gnm a ha'
      · intro q hq
        config_simp
        rw [upd_other _ _ _ (by omega), qn _ (by omega), pn _ (by omega)]
        exact gn q hq
      · config_simp; rw [qr, pr, gr]
      · config_simp; rw [qrm, prm, grm]
      · config_simp; rw [qo, po, go])) ?_
  · refine ⟨hI, fun a l _ _ ha => absurd ha (by omega), fun a _ => rfl, fun q hq => ?_, rfl, rfl,
      rfl⟩
    config_simp; rw [upd_other _ _ _ (by omega)]
  rintro c₂ k₂ hk₂ hw₂ ⟨_, gI, gA, gnm, gn, gr, grm, go⟩
  have e13 : c₂.nreg 2413 = r := (gn 2413 (by omega)).trans h13
  have e10 : c₂.nreg 2410 = 1 := (gn 2410 (by omega)).trans h10
  exec_block
  all_goals try ((try config_simp); (try simp only [e13, e10]); omega)
  refine ⟨by omega, ?_, ?_, fun a ha => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  all_goals config_simp
  · exact bfInv_succ gI gA
  · rw [e13, e10]
  · exact gnm a ha
  · rw [upd_other _ _ _ (by omega)]; exact gn q (by omega)
  · exact gr
  · exact grm
  · exact go

set_option maxHeartbeats 2000000 in
/-- **The distances from `u` by Bellman–Ford in memory** (see the module docstring). -/
theorem bfProg_dist {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {n : ℕ}
    (hιn : ∀ x, ιv x < n) {nD : ℕ} (σ : D ≃ Fin nD) {Sb NTb NHb Lb Db Inf Lmax R : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hLay : BFLay nD n Sb NTb NHb Lb Db Inf Lmax W) (hR : Fintype.card V ≤ R)
    (hRL : R * Lmax < Inf) (hRW : R ≤ W)
    (c : Config) (hc : WordsBounded W c) (hIn : BFIn M S ℓ σ ιv Sb NTb NHb Lb c)
    (h00 : c.nreg 2400 = nD) (h01 : c.nreg 2401 = Sb) (h02 : c.nreg 2402 = NTb)
    (h03 : c.nreg 2403 = NHb) (h04 : c.nreg 2404 = Lb) (h05 : c.nreg 2405 = Db)
    (h06 : c.nreg 2406 = n) (h07 : c.nreg 2407 = R) (h08 : c.nreg 2408 = Inf)
    (h09 : c.nreg 2409 = ιv u) :
    ∃ c' t, Exec P W bfProg c c' t ∧ t ≤ R * (24 * nD + 6) + 5 * n + 12 ∧
      (∀ x, MSSP.Reach (MSSP.pieceGraph M S ℓ) u x →
        c'.nmem (Db + ιv x) = (MSSP.dist (MSSP.pieceGraph M S ℓ) u x).toNat) ∧
      (∀ x, ¬ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x → c'.nmem (Db + ιv x) = Inf) ∧
      (∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2410 ∨ 2422 ≤ q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.one; have := hLay.wD
  obtain ⟨c₁, t₁, e₁, ht₁, hD₁, hm₁, a10, a11, a13, an₁, ar₁, arm₁, ao₁⟩ :=
    bfInit_exec (P := P) (hιn u) hLay.wD hLay.one c hc h05 h06 h08 h09
  have hIn₁ := hIn.frame hLay hm₁
  have hI₀ : BFInv M S ℓ u ιv Db Inf 0 c₁.nmem := by
    refine ⟨fun x hx => ?_, fun x l hl hlen => ?_, fun x => ?_⟩
    · rw [hD₁ _ (hιn x)] at hx ⊢
      split_ifs at hx ⊢ with h
      · have hx' : x = u := hinj h
        subst hx'
        exact ⟨[], .nil _, by simp⟩
      · omega
    · have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      have := MSSP.LWalk.nil_iff.1 hl
      subst this
      rw [hD₁ _ (hιn u), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      simp
    · rw [hD₁ _ (hιn x)]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun r c' =>
    BFInv M S ℓ u ιv Db Inf r c'.nmem ∧ (∀ a, a < Db ∨ Db + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2412 ∨ 2422 ≤ q → c'.nreg q = c₁.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2413) (bR := 2407)
    (body := bfRound) J (K := 24 * nD + 4) (n := R) c₁ e₁.wb_right a13
    (by rw [an₁ _ (by omega), h07]) ⟨hI₀, hm₁, fun _ _ => rfl, ar₁, arm₁, ao₁⟩
    (fun r c₃ hr hw ha hb ⟨gI, gnm, gn, gr, grm, go⟩ => by
      have hIn₃ := hIn.frame hLay gnm
      have k : ∀ q, q < 2410 → c₃.nreg q = c.nreg q := fun q hq => by
        rw [gn q (by omega), an₁ q (by omega)]
      obtain ⟨c₄, t₄, e₄, ht₄, hI₄, h13, hm₄, hn₄, hr₄, hrm₄, ho₄⟩ :=
        bfRound_exec (P := P) hinj hιn σ hpos hL hLay hr hRL hRW c₃ hw hIn₃ gI
          ((k _ (by omega)).trans h00) ((k _ (by omega)).trans h01) ((k _ (by omega)).trans h02)
          ((k _ (by omega)).trans h03) ((k _ (by omega)).trans h04) ((k _ (by omega)).trans h05)
          ((k _ (by omega)).trans h08) ((gn _ (by omega)).trans a10)
          ((gn _ (by omega)).trans a11) ha
      refine ⟨c₄, t₄, e₄, ht₄, h13, by rw [hn₄ _ (by omega), hb], hI₄,
        fun a ha' => (hm₄ a ha').trans (gnm a ha'), fun q hq => (hn₄ q hq).trans (gn q hq),
        hr₄.trans gr, hrm₄.trans grm, ho₄.trans go⟩)
  obtain ⟨hIR, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ := hJ
  obtain ⟨hd₁, hd₂⟩ := bfInv_dist hpos hL hR hRL hIR
  refine ⟨c₂, t₁ + t₂, Exec.seq e₁ e₂, ?_, hd₁, hd₂, hm₂, fun q hq => ?_, hr₂, hrm₂, ho₂⟩
  · have : (24 * nD + 4 + 2) * R = R * (24 * nD + 6) := by ring
    omega
  · rw [hn₂ q (by omega), an₁ q hq]

/-- **Bellman–Ford, then the tight-arc pass.** -/
def spTreeProg : Stmt := .seq bfProg tpProg

/-- **`spTreeProg` has no real instruction** (checked by the kernel). -/
theorem spTreeProg_natOnly : Klein.natOnly spTreeProg = true := by kernel_rfl

set_option maxHeartbeats 1000000 in
/-- **The parents of the shortest-path tree of `u`, on natural words, in memory**: `bfProg`
(the distances at `Db`) then `tpProg` (reading them, the reach bits at `Rb` and the same arrays
by darts), with `UniqTight G` (a field of `MSSP.Hyp`): `PAR[ιv x] = σ a` whenever
`tpar G u x = some a`, within `R (24 nD + 6) + 5 n + 29 nD + 17` steps. -/
theorem spTreeProg_tpar {u : V} {ιv : V → ℕ} (hinj : Function.Injective ιv) {n : ℕ}
    (hιn : ∀ x, ιv x < n) {nD : ℕ} (σ : D ≃ Fin nD) {Sb NTb NHb Lb Db Rb Pb Inf Lmax R : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hU : MSSP.UniqTight (MSSP.pieceGraph M S ℓ))
    (hLay : BFLay nD n Sb NTb NHb Lb Db Inf Lmax W)
    (hTP : TPLay nD n Sb NTb NHb Lb Rb Db Pb W) (hRb : Rb + n ≤ Db ∨ Db + n ≤ Rb)
    (hR : Fintype.card V ≤ R) (hRL : R * Lmax < Inf) (hRW : R ≤ W)
    (c : Config) (hc : WordsBounded W c) (hIn : BFIn M S ℓ σ ιv Sb NTb NHb Lb c)
    (hrb : ∀ x, 0 < c.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x)
    (h00 : c.nreg 2400 = nD) (h01 : c.nreg 2401 = Sb) (h02 : c.nreg 2402 = NTb)
    (h03 : c.nreg 2403 = NHb) (h04 : c.nreg 2404 = Lb) (h05 : c.nreg 2405 = Db)
    (h06 : c.nreg 2406 = n) (h07 : c.nreg 2407 = R) (h08 : c.nreg 2408 = Inf)
    (h09 : c.nreg 2409 = ιv u)
    (g00 : c.nreg 2300 = nD) (g01 : c.nreg 2301 = Sb) (g02 : c.nreg 2302 = NTb)
    (g03 : c.nreg 2303 = NHb) (g04 : c.nreg 2304 = Lb) (g05 : c.nreg 2305 = Rb)
    (g06 : c.nreg 2306 = Db) (g07 : c.nreg 2307 = Pb) :
    ∃ c' t, Exec P W spTreeProg c c' t ∧ t ≤ R * (24 * nD + 6) + 5 * n + 29 * nD + 17 ∧
      (∀ x a, Klein.tpar (MSSP.pieceGraph M S ℓ) u x = some a → c'.nmem (Pb + ιv x) = σ a.1) ∧
      (∀ a, (a < Db ∨ Db + n ≤ a) → (a < Pb ∨ Pb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hd₁, -, hm₁, hn₁, hr₁, hrm₁, ho₁⟩ :=
    bfProg_dist (P := P) hinj hιn σ hpos hL hLay hR hRL hRW c hc hIn h00 h01 h02 h03 h04 h05 h06
      h07 h08 h09
  have hIn₁ := hIn.frame hLay hm₁
  have := hTP.dR
  have := hTP.dD
  obtain ⟨c₂, t₂, e₂, ht₂, hP, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    tpProg_tpar (P := P) hpos hU σ hinj hιn u hTP c₁ e₁.wb_right
      ((hn₁ _ (by omega)).trans g00) ((hn₁ _ (by omega)).trans g01)
      ((hn₁ _ (by omega)).trans g02) ((hn₁ _ (by omega)).trans g03)
      ((hn₁ _ (by omega)).trans g04) ((hn₁ _ (by omega)).trans g05)
      ((hn₁ _ (by omega)).trans g06) ((hn₁ _ (by omega)).trans g07) hIn₁.fl hIn₁.nt hIn₁.nh
      hIn₁.ln (fun x => by rw [hm₁ _ (by have := hιn x; omega)]; exact hrb x)
      (fun x hx => hd₁ x hx)
  refine ⟨c₂, t₁ + t₂, Exec.seq e₁ e₂, by omega, hP, fun a ha ha' => ?_, hr₂.trans hr₁,
    hrm₂.trans hrm₁, ho₂.trans ho₁⟩
  rw [hm₂ a ha', hm₁ a ha]

end Run

end NegSSSP

end PlanarFlow
