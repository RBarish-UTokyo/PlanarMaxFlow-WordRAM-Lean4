module

public import PlanarFlow.NegSSSP.LinGlue
public import PlanarFlow.Monge.FRLayout
public import Mathlib.Data.List.GetD

/-!
# The layout of the explicit arcs of FR-Dijkstra by a counting sort

The machine program `PlanarFlow.Monge.FR.frProg` reads its explicit arcs in compressed-row form
(`PlanarFlow.Monge.FR.mkPrm`): the offsets `off x = (FR.pre Es x).length` (`x ≤ N`), and the
heads and lengths of `FR.arcList N Es`, the arcs listed tail by tail, in the order of `Es`
within a tail. `csProg` lays out a list of arcs given as arrays (tails `T`, heads `H`, lengths
`Lz`, and keep flags `K`: the arcs `i < M` with `K i ≠ 0`, in order, `csList`) by a **stable
counting sort**: clear the counts, count the arcs per tail, prefix sums (the offsets), copy the
offsets to a cursor array, place every arc at the cursor of its tail. `csProg_exec`: within
`csCost M N = 35 M + 21 N + 23` steps the offsets `(pre (csList …) x).length` at `Ob + x`
(`x ≤ N`), and the head and the length of the `e`-th arc of `arcList N (csList …)` at `Db + e`
(natural memory) and `Rb + e` (real memory); `csProg_mkPrm`: at the bases of `mkPrm`, the
fields `omem`, `emem`, `lmem` of `Monge.FR.Data`.

The proof of stability: `csList (i + 1)` is `csList i` with at most one arc appended, so the
arcs of a tail among the first `i` (`blk (csList i) x`) are a prefix of those of all
(`blk_csList_prefix`), and the `e`-th arc of `pre Es N` is the `j`-th of the block of its tail
`x`, `e = (pre Es x).length + j` (`pre_getElem`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.FR

/-! ### The lists -/

/-- The arcs `i' < i` with `K i' ≠ 0`, in order. -/
def csList (T H K : ℕ → ℕ) (Lz : ℕ → ℤ) : ℕ → List (ℕ × ℕ × ℤ)
  | 0 => []
  | i + 1 => csList T H K Lz i ++ if K i = 0 then [] else [(T i, H i, Lz i)]

section Lists

variable {T H K : ℕ → ℕ} {Lz : ℕ → ℤ}

lemma blk_append (l : List (ℕ × ℕ × ℤ)) (a : ℕ × ℕ × ℤ) (x : ℕ) :
    blk (l ++ [a]) x = blk l x ++ if a.1 = x then [a] else [] := by
  unfold blk
  rw [List.filter_append]
  congr 1
  by_cases h : a.1 = x <;> simp [h]

lemma blk_nil (x : ℕ) : blk [] x = [] := rfl

lemma blk_csList_succ (i x : ℕ) : blk (csList T H K Lz (i + 1)) x =
    blk (csList T H K Lz i) x ++
      if K i ≠ 0 ∧ T i = x then [(T i, H i, Lz i)] else [] := by
  simp only [csList]
  by_cases hK : K i = 0
  · simp [hK]
  · simp only [hK, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    rw [blk_append]

lemma csList_prefix {i j : ℕ} (h : i ≤ j) : csList T H K Lz i <+: csList T H K Lz j := by
  induction j with
  | zero => rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact (ih (by omega)).trans (List.prefix_append _ _)
    · rw [show i = j + 1 by omega]

lemma blk_csList_prefix {i j : ℕ} (h : i ≤ j) (x : ℕ) :
    blk (csList T H K Lz i) x <+: blk (csList T H K Lz j) x :=
  (csList_prefix h).filter _

lemma length_csList_le (i : ℕ) : (csList T H K Lz i).length ≤ i := by
  induction i with
  | zero => simp [csList]
  | succ i ih => simp only [csList, List.length_append]; split_ifs <;> simp <;> omega

lemma length_pre_succ (L : List (ℕ × ℕ × ℤ)) (x : ℕ) :
    (pre L (x + 1)).length = (pre L x).length + (blk L x).length := by
  rw [pre_succ, List.length_append]

/-- **The `e`-th arc of `pre L n` is the `j`-th of the block of its tail.** -/
lemma pre_getElem (L : List (ℕ × ℕ × ℤ)) :
    ∀ n e (he : e < (pre L n).length), ∃ x < n, ∃ j, ∃ hj : j < (blk L x).length,
      e = (pre L x).length + j ∧ (pre L n)[e] = (blk L x)[j] := by
  intro n
  induction n with
  | zero => intro e he; simp [pre] at he
  | succ n ih =>
    intro e he
    have hl := length_pre_succ L n
    by_cases h : e < (pre L n).length
    · obtain ⟨x, hx, j, hj, rfl, hg⟩ := ih e h
      refine ⟨x, by omega, j, hj, rfl, ?_⟩
      have : (pre L (n + 1))[(pre L x).length + j] =
          (pre L n ++ blk L n)[(pre L x).length + j]'(by rw [← pre_succ]; exact he) := by
        simp only [pre_succ]
      rw [this, List.getElem_append_left h, hg]
    · refine ⟨n, by omega, e - (pre L n).length, by omega, by omega, ?_⟩
      have : (pre L (n + 1))[e] = (pre L n ++ blk L n)[e]'(by rw [← pre_succ]; exact he) := by
        simp only [pre_succ]
      rw [this, List.getElem_append_right (by omega)]

/-- The tails of the arcs of `blk L x` are `x`. -/
lemma blk_getElem_fst {L : List (ℕ × ℕ × ℤ)} {x j : ℕ} (hj : j < (blk L x).length) :
    ((blk L x)[j]).1 = x := by
  have h := (List.mem_filter.1 (List.getElem_mem hj)).2
  simpa using h

end Lists

/-! ### The program -/

/-- Clear the counts `Ob[x] := 0`, `x ≤ N` (`r411` the counter, `r412 = N + 1`). -/
def csClear : Stmt := .seq (block [.constN 410 1, .constN 411 0, .addN 412 401 410, .constN 413 0])
  (.whileLtN 411 412 (block [.addN 414 405 411, .storeN 414 413, .addN 411 411 410]))

/-- Count the kept arcs per tail at `Ob + T i + 1`. -/
def csCountBody : Stmt :=
  .seq (block [.addN 414 404 411, .loadN 415 414]) <|
  .seq (.ifLtN 415 410 .skip (block [.addN 414 402 411, .loadN 416 414, .addN 414 405 416,
    .addN 414 414 410, .loadN 417 414, .addN 417 417 410, .storeN 414 417]))
    (block [.addN 411 411 410])

/-- The prefix sums `Ob[x + 1] += Ob[x]`. -/
def csPrefBody : Stmt := block [.addN 414 405 411, .loadN 415 414, .addN 414 414 410,
  .loadN 416 414, .addN 416 416 415, .storeN 414 416, .addN 411 411 410]

/-- The cursors `Cb[x] := Ob[x]`. -/
def csCopyBody : Stmt := block [.addN 414 405 411, .loadN 415 414, .addN 414 406 411,
  .storeN 414 415, .addN 411 411 410]

/-- Place the kept arc `i` at the cursor of its tail. -/
def csPlaceBody : Stmt :=
  .seq (block [.addN 414 404 411, .loadN 415 414]) <|
  .seq (.ifLtN 415 410 .skip (block [.addN 414 402 411, .loadN 416 414, .addN 414 406 416,
    .loadN 417 414, .addN 419 403 411, .loadN 420 419, .addN 419 409 417, .storeN 419 420,
    .addN 419 408 411, .loadR 400 419, .addN 419 407 417, .storeR 419 400, .addN 417 417 410,
    .storeN 414 417]))
    (block [.addN 411 411 410])

/-- **The counting sort.** -/
def csProg : Stmt :=
  .seq csClear <|
  .seq (.instr (.constN 411 0)) <| .seq (.whileLtN 411 400 csCountBody) <|
  .seq (.instr (.constN 411 0)) <| .seq (.whileLtN 411 401 csPrefBody) <|
  .seq (.instr (.constN 411 0)) <| .seq (.whileLtN 411 401 csCopyBody) <|
  .seq (.instr (.constN 411 0)) (.whileLtN 411 400 csPlaceBody)

/-- The data of `csProg`: `M` arcs (tails at `Tb`, heads at `Hb`, keep flags at `Kb`, natural
memory; lengths at `Lb`, real memory), `N` vertices; the offsets at `Ob`, the cursors at `Cb`,
the heads at `Db` (natural), the lengths at `Rb` (real). -/
structure CsIn (M N Tb Hb Kb Ob Cb Rb Lb Db : ℕ) (T H K : ℕ → ℕ) (Lz : ℕ → ℤ) (c : Config) :
    Prop where
  r400 : c.nreg 400 = M
  r401 : c.nreg 401 = N
  r402 : c.nreg 402 = Tb
  r403 : c.nreg 403 = Hb
  r404 : c.nreg 404 = Kb
  r405 : c.nreg 405 = Ob
  r406 : c.nreg 406 = Cb
  r407 : c.nreg 407 = Rb
  r408 : c.nreg 408 = Lb
  r409 : c.nreg 409 = Db
  tl : ∀ i < M, c.nmem (Tb + i) = T i
  hd : ∀ i < M, c.nmem (Hb + i) = H i
  kp : ∀ i < M, c.nmem (Kb + i) = K i
  ln : ∀ i < M, c.rmem (Lb + i) = Lz i

/-- The layout of `csProg`: the kept tails below `N`, the regions written apart from each other
and from the arrays read, the addresses below the word bound. -/
structure CsLay (M N Tb Hb Kb Ob Cb Rb Lb Db W : ℕ) (T H K : ℕ → ℕ) : Prop where
  tlt : ∀ i < M, K i ≠ 0 → T i < N
  oT : Ob + N + 1 ≤ Tb ∨ Tb + M ≤ Ob
  oH : Ob + N + 1 ≤ Hb ∨ Hb + M ≤ Ob
  oK : Ob + N + 1 ≤ Kb ∨ Kb + M ≤ Ob
  cT : Cb + N ≤ Tb ∨ Tb + M ≤ Cb
  cH : Cb + N ≤ Hb ∨ Hb + M ≤ Cb
  cK : Cb + N ≤ Kb ∨ Kb + M ≤ Cb
  dT : Db + M ≤ Tb ∨ Tb + M ≤ Db
  dH : Db + M ≤ Hb ∨ Hb + M ≤ Db
  dK : Db + M ≤ Kb ∨ Kb + M ≤ Db
  oc : Ob + N + 1 ≤ Cb ∨ Cb + N ≤ Ob
  od : Ob + N + 1 ≤ Db ∨ Db + M ≤ Ob
  cd : Cb + N ≤ Db ∨ Db + M ≤ Cb
  rl : Rb + M ≤ Lb ∨ Lb + M ≤ Rb
  wT : Tb + M ≤ W
  wH : Hb + M ≤ W
  wK : Kb + M ≤ W
  wL : Lb + M ≤ W
  wO : Ob + N + 1 ≤ W
  wC : Cb + N ≤ W
  wD : Db + M ≤ W
  wR : Rb + M ≤ W
  wM : M + 1 ≤ W
  wN : N + 1 ≤ W

/-! ### The phases -/

variable {P : Input} {W : ℕ} {M N Tb Hb Kb Ob Cb Rb Lb Db : ℕ} {T H K : ℕ → ℕ} {Lz : ℕ → ℤ}

theorem csClear_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c) :
    ∃ c' k, Exec P W csClear c c' k ∧ k ≤ 5 * N + 11 ∧
      ((∀ x ≤ N, c'.nmem (Ob + x) = 0) ∧
        (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.wN
  unfold csClear
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r401]); omega)
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Ob + x) = 0) ∧ (∀ a, (a < Ob ∨ Ob + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧ c'.nreg 413 = 0 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 411) (bR := 412)
    (body := block [.addN 414 405 411, .storeN 414 413, .addN 411 411 410]) J (K := 3)
    (n := N + 1) _ ‹_› (by config_simp) (by config_simp; rw [hI.r401]) ?_
    (fun i c₁ hi hw ha hb ⟨g0, gm, gn, g410, g413, gr, grm, go⟩ => by
      have e405 : c₁.nreg 405 = Ob := (gn 405 (by omega)).trans hI.r405
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, ha, g410, g413]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (intro x hx; simp only [upd_apply]; split_ifs
           · rfl
           · exact g0 x (by omega))
        | (intro a ha'; simp only [upd_apply]
           rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact gm a (by omega))
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr))) ?_
  · refine ⟨fun x hx => absurd hx (by omega), fun a _ => ?_, fun r hr => ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g0, gm, gn, g410, -, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, fun x hx => g0 x (by omega), gm, gn, g410, gr, grm, go⟩

lemma length_blk_succ (i x : ℕ) : (blk (csList T H K Lz (i + 1)) x).length =
    (blk (csList T H K Lz i) x).length + if K i ≠ 0 ∧ T i = x then 1 else 0 := by
  rw [blk_csList_succ, List.length_append]; split_ifs <;> simp

lemma length_blk_le (i x : ℕ) : (blk (csList T H K Lz i) x).length ≤ i :=
  (List.length_filter_le _ _).trans (length_csList_le i)

theorem csCount_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c)
    (h410 : c.nreg 410 = 1) (h411 : c.nreg 411 = 0) (h0 : ∀ x ≤ N, c.nmem (Ob + x) = 0) :
    ∃ c' k, Exec P W (.whileLtN 411 400 csCountBody) c c' k ∧ k ≤ 14 * M + 2 ∧
      ((∀ x < N, c'.nmem (Ob + (x + 1)) = (blk (csList T H K Lz M) x).length) ∧
        c'.nmem Ob = 0 ∧ (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.wN; have := hL.wM; have := hL.wK; have := hL.wT
  have := hL.oK; have := hL.oT
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < N, c'.nmem (Ob + (x + 1)) = (blk (csList T H K Lz i) x).length) ∧
      c'.nmem Ob = 0 ∧ (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 411) (bR := 400) (body := csCountBody) J (K := 12)
    (n := M) c hc h411 hI.r400 ⟨fun x hx => by rw [h0 _ (by omega)]; rfl,
      by simpa using h0 0 (by omega), fun _ _ => rfl, fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨gc, g0, gm, gn, g410, gr, grm, go⟩ => by
      have e404 : c₁.nreg 404 = Kb := (gn 404 (by omega)).trans hI.r404
      have e402 : c₁.nreg 402 = Tb := (gn 402 (by omega)).trans hI.r402
      have e405 : c₁.nreg 405 = Ob := (gn 405 (by omega)).trans hI.r405
      have eK : c₁.nmem (Kb + i) = K i := by rw [gm _ (by omega)]; exact hI.kp i hi
      have eT : c₁.nmem (Tb + i) = T i := by rw [gm _ (by omega)]; exact hI.tl i hi
      unfold csCountBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e404, ha]); omega)
      refine spec_seq ?_
      by_cases hk : K i = 0
      · refine spec_ifLtN_true (by config_simp; simp only [e404, ha, eK, hk, g410]; omega) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, g410]); omega)
        dsimp only [J]
        config_simp
        simp only [ha, g410]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, g0, gm, fun r hr => ?_, trivial, gr, grm,
          go⟩
        · rw [gc x hx, length_blk_succ]; simp [hk]
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · have htN := hL.tlt i hi hk
        have hcnt := gc (T i) htN
        have hle := length_blk_le (T := T) (H := H) (K := K) (Lz := Lz) i (T i)
        refine spec_ifLtN_false (by config_simp; simp only [e404, ha, eK, g410]; omega) ?_
        have hcnt' : c₁.nmem (Ob + T i + 1) = (blk (csList T H K Lz i) (T i)).length := by
          rw [Nat.add_assoc]; exact hcnt
        exec_block
        all_goals try ((try config_simp); (try simp only [e404, e402, ha, eK, eT, g410]); omega)
        all_goals try ((try config_simp); (try simp only [e405, e402, ha, eT, hcnt', g410]); omega)
        dsimp only [J]
        config_simp
        simp only [e404, e402, e405, ha, eK, eT, g410]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, ?_, fun a ha' => ?_, fun r hr => ?_, trivial,
          gr, grm, go⟩
        · simp only [upd_apply]
          rw [length_blk_succ]
          by_cases hx' : x = T i
          · subst hx'
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), hcnt']
            simp [hk]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gc x hx]
            simp [Ne.symm hx']
        · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), g0]
        · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gc, g0, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gc, g0, gm, gn, g410, gr, grm, go⟩

lemma length_pre_csList_le (L : List (ℕ × ℕ × ℤ)) (hL : L = csList T H K Lz M) (x : ℕ) :
    (pre L x).length ≤ M := by
  subst hL; exact (length_pre_le _ x).trans (length_csList_le M)

theorem csPref_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c)
    (h410 : c.nreg 410 = 1) (h411 : c.nreg 411 = 0) (hc0 : c.nmem Ob = 0)
    (hcnt : ∀ x < N, c.nmem (Ob + (x + 1)) = (blk (csList T H K Lz M) x).length) :
    ∃ c' k, Exec P W (.whileLtN 411 401 csPrefBody) c c' k ∧ k ≤ 9 * N + 2 ∧
      ((∀ x ≤ N, c'.nmem (Ob + x) = (pre (csList T H K Lz M) x).length) ∧
        (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.wN; have := hL.wM
  set L := csList T H K Lz M with hLd
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x ≤ j, c'.nmem (Ob + x) = (pre L x).length) ∧
      (∀ x, j < x → x < N + 1 → c'.nmem (Ob + x) = (blk L (x - 1)).length) ∧
      (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 411) (bR := 401) (body := csPrefBody) J (K := 7)
    (n := N) c hc h411 hI.r401 ⟨fun x hx => by
      rw [show x = 0 by omega, Nat.add_zero, hc0]; simp [pre],
      fun x hx hx' => by
        have := hcnt (x - 1) (by omega); rwa [show x - 1 + 1 = x by omega] at this,
      fun _ _ => rfl, fun _ _ => rfl, h410, rfl, rfl, rfl⟩
    (fun j c₁ hj hw ha hb ⟨gp, gb, gm, gn, g410, gr, grm, go⟩ => by
      have e405 : c₁.nreg 405 = Ob := (gn 405 (by omega)).trans hI.r405
      have hpj := gp j le_rfl
      have hbj : c₁.nmem (Ob + j + 1) = (blk L j).length := by
        rw [Nat.add_assoc, gb (j + 1) (by omega) (by omega), Nat.add_sub_cancel]
      have hps := length_pre_succ L j
      have hpM := length_pre_csList_le L hLd (j + 1)
      unfold csPrefBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, ha, g410, hpj, hbj]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, ha, g410, hpj, hbj]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx hx' => ?_, fun a ha' => ?_,
        fun r hr => ?_, trivial, gr, grm, go⟩
      · simp only [upd_apply]
        by_cases hxj : x = j + 1
        · subst hxj; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; omega
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gp x (by omega)]
      · simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gb x (by omega) hx']
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gp, -, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gp, gm, gn, g410, gr, grm, go⟩

theorem csCopy_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c)
    (h410 : c.nreg 410 = 1) (h411 : c.nreg 411 = 0) :
    ∃ c' k, Exec P W (.whileLtN 411 401 csCopyBody) c c' k ∧ k ≤ 7 * N + 2 ∧
      ((∀ x < N, c'.nmem (Cb + x) = c.nmem (Ob + x)) ∧
        (∀ a, (a < Cb ∨ Cb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.wN; have := hL.wC; have := hL.oc
  let J : ℕ → Config → Prop := fun j c' =>
    (∀ x < j, c'.nmem (Cb + x) = c.nmem (Ob + x)) ∧
      (∀ a, (a < Cb ∨ Cb + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 411) (bR := 401) (body := csCopyBody) J (K := 5)
    (n := N) c hc h411 hI.r401 ⟨fun x hx => absurd hx (by omega), fun _ _ => rfl, fun _ _ => rfl,
      h410, rfl, rfl, rfl⟩
    (fun j c₁ hj hw ha hb ⟨gp, gm, gn, g410, gr, grm, go⟩ => by
      have e405 : c₁.nreg 405 = Ob := (gn 405 (by omega)).trans hI.r405
      have e406 : c₁.nreg 406 = Cb := (gn 406 (by omega)).trans hI.r406
      have hoj : c₁.nmem (Ob + j) = c.nmem (Ob + j) := gm _ (by omega)
      unfold csCopyBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e405, e406, ha, g410]); omega)
      dsimp only [J]
      config_simp
      simp only [e405, e406, ha, g410, hoj]
      refine ⟨by omega, trivial, hb, fun x hx => ?_, fun a ha' => ?_, fun r hr => ?_, trivial, gr,
        grm, go⟩
      · simp only [upd_apply]
        by_cases hxj : x = j
        · subst hxj; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gp x (by omega)]
      · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a ha']
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, gp, gm, gn, g410, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, gp, gm, gn, g410, gr, grm, go⟩

lemma length_blk_csList_le {i : ℕ} (hi : i ≤ M) (x : ℕ) :
    (blk (csList T H K Lz i) x).length ≤ (blk (csList T H K Lz M) x).length :=
  (blk_csList_prefix hi x).length_le

theorem csPlace_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c)
    (h410 : c.nreg 410 = 1) (h411 : c.nreg 411 = 0)
    (hcur : ∀ x < N, c.nmem (Cb + x) = (pre (csList T H K Lz M) x).length) :
    ∃ c' k, Exec P W (.whileLtN 411 400 csPlaceBody) c c' k ∧ k ≤ 21 * M + 2 ∧
      ((∀ x < N, ∀ j < (blk (csList T H K Lz M) x).length,
          c'.nmem (Db + ((pre (csList T H K Lz M) x).length + j)) =
            ((blk (csList T H K Lz M) x).getD j (0, 0, 0)).2.1 ∧
          c'.rmem (Rb + ((pre (csList T H K Lz M) x).length + j)) =
            (((blk (csList T H K Lz M) x).getD j (0, 0, 0)).2.2 : ℝ)) ∧
        (∀ a, (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ a, (a < Rb ∨ Rb + M ≤ a) → c'.rmem a = c.rmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
        (∀ r, r ≠ 400 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have := hL.wN; have := hL.wM; have := hL.wC; have := hL.wD; have := hL.wR; have := hL.wT
  have := hL.wH; have := hL.wK; have := hL.wL
  have := hL.cT; have := hL.cH; have := hL.cK; have := hL.dT; have := hL.dH; have := hL.dK
  have := hL.cd; have := hL.rl
  set L := csList T H K Lz M with hLd
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < N, c'.nmem (Cb + x) = (pre L x).length + (blk (csList T H K Lz i) x).length) ∧
      (∀ x < N, ∀ j < (blk (csList T H K Lz i) x).length,
        c'.nmem (Db + ((pre L x).length + j)) =
          ((blk (csList T H K Lz i) x).getD j (0, 0, 0)).2.1 ∧
        c'.rmem (Rb + ((pre L x).length + j)) =
          (((blk (csList T H K Lz i) x).getD j (0, 0, 0)).2.2 : ℝ)) ∧
      (∀ a, (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Rb ∨ Rb + M ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 410 = 1 ∧
      (∀ r, r ≠ 400 → c'.rreg r = c.rreg r) ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 411) (bR := 400) (body := csPlaceBody) J (K := 19)
    (n := M) c hc h411 hI.r400 ⟨fun x hx => by rw [hcur x hx]; simp [csList, blk],
      fun x _ j hj => by simp [csList, blk] at hj, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, h410, fun _ _ => rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨gA, gB, gm, grm, gn, g410, gr, go⟩ => by
      have e402 : c₁.nreg 402 = Tb := (gn 402 (by omega)).trans hI.r402
      have e403 : c₁.nreg 403 = Hb := (gn 403 (by omega)).trans hI.r403
      have e404 : c₁.nreg 404 = Kb := (gn 404 (by omega)).trans hI.r404
      have e406 : c₁.nreg 406 = Cb := (gn 406 (by omega)).trans hI.r406
      have e407 : c₁.nreg 407 = Rb := (gn 407 (by omega)).trans hI.r407
      have e408 : c₁.nreg 408 = Lb := (gn 408 (by omega)).trans hI.r408
      have e409 : c₁.nreg 409 = Db := (gn 409 (by omega)).trans hI.r409
      have eK : c₁.nmem (Kb + i) = K i := by rw [gm _ (by omega) (by omega)]; exact hI.kp i hi
      have eT : c₁.nmem (Tb + i) = T i := by rw [gm _ (by omega) (by omega)]; exact hI.tl i hi
      have eH : c₁.nmem (Hb + i) = H i := by rw [gm _ (by omega) (by omega)]; exact hI.hd i hi
      have eL : c₁.rmem (Lb + i) = Lz i := by rw [grm _ (by omega)]; exact hI.ln i hi
      unfold csPlaceBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e404, ha]); omega)
      refine spec_seq ?_
      by_cases hk : K i = 0
      · refine spec_ifLtN_true (by config_simp; simp only [e404, ha, eK, hk, g410]; omega) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, g410]); omega)
        dsimp only [J]
        config_simp
        simp only [ha, g410]
        have hbl : ∀ x, blk (csList T H K Lz (i + 1)) x = blk (csList T H K Lz i) x := fun x => by
          rw [blk_csList_succ]; simp [hk]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx j hj => ?_, gm, grm,
          fun r hr => ?_, trivial, gr, go⟩
        · rw [hbl]; exact gA x hx
        · rw [hbl] at hj ⊢; exact gB x hx j hj
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · -- the arc `i` is kept, with tail `t < N`
        have htN := hL.tlt i hi hk
        set t := T i with htd
        have hpos := gA t htN
        have hsucc := length_blk_succ (T := T) (H := H) (K := K) (Lz := Lz) i t
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hk, rfl⟩)] at hsucc
        have hpre1 := length_blk_csList_le (T := T) (H := H) (K := K) (Lz := Lz) (M := M)
          (show i + 1 ≤ M by omega) t
        rw [← hLd] at hpre1
        have hps := length_pre_succ L t
        have hmono := length_pre_mono L (show t + 1 ≤ N by omega)
        have hNM := length_pre_csList_le L hLd N
        refine spec_ifLtN_false (by config_simp; simp only [e404, ha, eK, g410]; omega) ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e402, e403, e404, e406, e407, e408,
          e409, ha, eT, g410, hpos]); omega)
        dsimp only [J]
        config_simp
        simp only [e402, e403, e404, e406, e407, e408, e409, ha, eT, eH, eL, g410, hpos]
        refine ⟨by omega, trivial, hb, fun x hx => ?_, fun x hx j hj => ?_, fun a h1 h2 => ?_,
          fun a h1 => ?_, fun r hr => ?_, trivial, fun r hr => ?_, go⟩
        · simp only [upd_apply]
          by_cases hxt : x = t
          · subst hxt; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]; omega
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gA x hx, length_blk_succ]
            rw [← htd]; simp [Ne.symm hxt]
        · rw [blk_csList_succ, ← htd] at hj ⊢
          simp only [upd_apply]
          by_cases hxt : x = t
          · subst hxt
            simp only [ne_eq, hk, not_false_eq_true, true_and, ↓reduceIte, List.length_append,
              List.length_singleton] at hj ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · obtain ⟨b1, b2⟩ := gB _ hx j hj'
              rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
                ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
                ite_eq_right_of_eq_false _ _ (eq_false (by omega)), List.getD_append _ _ _ _ hj',
                b1, b2]
              exact ⟨rfl, rfl⟩
            · subst hj'
              rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
                ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
                ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
                List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
              exact ⟨rfl, rfl⟩
          · have hne : ¬ (K i ≠ 0 ∧ t = x) := fun h => hxt h.2.symm
            simp only [hne, ↓reduceIte, List.append_nil] at hj ⊢
            have hx1 := length_blk_csList_le (T := T) (H := H) (K := K) (Lz := Lz) (M := M)
              (show i ≤ M by omega) x
            rw [← hLd] at hx1
            have hpx := length_pre_succ L x
            have hfar : (pre L x).length + j < (pre L t).length +
                (blk (csList T H K Lz i) t).length ∨
                (pre L t).length + (blk (csList T H K Lz i) t).length < (pre L x).length + j := by
              rcases Nat.lt_or_gt_of_ne hxt with h | h
              · have := length_pre_mono L (show x + 1 ≤ t by omega); omega
              · have := length_pre_mono L (show t + 1 ≤ x by omega); omega
            obtain ⟨b1, b2⟩ := gB x hx j hj
            have := length_pre_mono L (show x + 1 ≤ N by omega)
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega)), b1, b2]
            exact ⟨rfl, rfl⟩
        · simp only [upd_apply]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
            ite_eq_right_of_eq_false _ _ (eq_false (by omega)), gm a h1 h2]
        · simp only [upd_apply]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), grm a h1]
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
        · simp only [upd_apply]; rw [ite_eq_right_of_eq_false _ _ (eq_false hr), gr r hr])) ?_
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, -, gB, gm, grm, gn, g410, gr, go⟩ := hJ₂
  exact ⟨by omega, gB, gm, grm, gn, g410, gr, go⟩

/-! ### The counting sort -/

lemma CsIn.mono (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) {c c' : Config}
    (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c)
    (hn : ∀ r, r < 410 → c'.nreg r = c.nreg r)
    (hm : ∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) →
      c'.nmem a = c.nmem a)
    (hr : ∀ a, (a < Rb ∨ Rb + M ≤ a) → c'.rmem a = c.rmem a) :
    CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c' := by
  have := hL.oT; have := hL.oH; have := hL.oK; have := hL.cT; have := hL.cH; have := hL.cK
  have := hL.dT; have := hL.dH; have := hL.dK; have := hL.rl
  exact ⟨(hn 400 (by omega)).trans hI.r400, (hn 401 (by omega)).trans hI.r401,
    (hn 402 (by omega)).trans hI.r402, (hn 403 (by omega)).trans hI.r403,
    (hn 404 (by omega)).trans hI.r404, (hn 405 (by omega)).trans hI.r405,
    (hn 406 (by omega)).trans hI.r406, (hn 407 (by omega)).trans hI.r407,
    (hn 408 (by omega)).trans hI.r408, (hn 409 (by omega)).trans hI.r409,
    fun i hi => by rw [hm _ (by omega) (by omega) (by omega)]; exact hI.tl i hi,
    fun i hi => by rw [hm _ (by omega) (by omega) (by omega)]; exact hI.hd i hi,
    fun i hi => by rw [hm _ (by omega) (by omega) (by omega)]; exact hI.kp i hi,
    fun i hi => by rw [hr _ (by omega)]; exact hI.ln i hi⟩

/-- The cost bound of `csProg`. -/
def csCost (M N : ℕ) : ℕ := 35 * M + 21 * N + 23

/-- **The counting sort on the machine.** From `CsIn` (with `CsLay`), `csProg` writes the
offsets `(pre L x).length` (`x ≤ N`) at `Ob + x`, and the head and the length of the `e`-th arc
of `arcList N L` at `Db + e` and `Rb + e`, `L = csList T H K Lz M` the kept arcs in order, within
`csCost M N` steps; the memory changes only in `[Ob, Ob + N]`, `[Cb, Cb + N)`, `[Db, Db + M)`
(natural) and `[Rb, Rb + M)` (real). -/
theorem csProg_exec (hL : CsLay M N Tb Hb Kb Ob Cb Rb Lb Db W T H K) (c : Config)
    (hc : WordsBounded W c) (hI : CsIn M N Tb Hb Kb Ob Cb Rb Lb Db T H K Lz c) :
    ∃ c' k, Exec P W csProg c c' k ∧ k ≤ csCost M N ∧
      ((∀ x ≤ N, c'.nmem (Ob + x) = (pre (csList T H K Lz M) x).length) ∧
        (∀ e < (arcList N (csList T H K Lz M)).length,
          c'.nmem (Db + e) = ((arcList N (csList T H K Lz M)).getD e (0, 0, 0)).2.1 ∧
          c'.rmem (Rb + e) = (((arcList N (csList T H K Lz M)).getD e (0, 0, 0)).2.2 : ℝ)) ∧
        (∀ a, (a < Ob ∨ Ob + N + 1 ≤ a) → (a < Cb ∨ Cb + N ≤ a) → (a < Db ∨ Db + M ≤ a) →
          c'.nmem a = c.nmem a) ∧
        (∀ a, (a < Rb ∨ Rb + M ≤ a) → c'.rmem a = c.rmem a) ∧
        (∀ r, r < 410 ∨ 420 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 400 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have := hL.oc; have := hL.od; have := hL.cd; have := hL.wO; have := hL.wC
  unfold csProg
  -- clear
  refine spec_seq ?_
  refine spec_use (csClear_exec (P := P) hL c hc hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨z₁, m₁, n₁, r410₁, rr₁, rm₁, o₁⟩
  have hI₁ := hI.mono hL (fun r hr => n₁ r (by omega)) (fun a h _ _ => m₁ a h)
    (fun a _ => by rw [rm₁])
  -- count
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 411 0 (by omega)) fun hw₂ => ?_
  refine spec_seq ?_
  refine spec_use (csCount_exec (P := P) hL _ hw₂
    (hI₁.mono hL (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₁) (by config_simp) (by config_simp; exact z₁)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨cnt₃, z₃, m₃, n₃, r410₃, rr₃, rm₃, o₃⟩
  config_simp at m₃
  config_simp at n₃
  config_simp at rr₃
  config_simp at rm₃
  config_simp at o₃
  have hI₃ := hI₁.mono hL (fun r hr => by rw [n₃ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun a h _ _ => m₃ a h) (fun a _ => by rw [rm₃])
  -- prefix sums
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₃ 411 0 (by omega)) fun hw₄ => ?_
  refine spec_seq ?_
  refine spec_use (csPref_exec (P := P) hL _ hw₄
    (hI₃.mono hL (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₃) (by config_simp) (by config_simp; exact z₃)
    (by config_simp; exact cnt₃)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨pre₅, m₅, n₅, r410₅, rr₅, rm₅, o₅⟩
  config_simp at m₅
  config_simp at n₅
  config_simp at rr₅
  config_simp at rm₅
  config_simp at o₅
  have hI₅ := hI₃.mono hL (fun r hr => by rw [n₅ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun a h _ _ => m₅ a h) (fun a _ => by rw [rm₅])
  -- the cursors
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₅ 411 0 (by omega)) fun hw₆ => ?_
  refine spec_seq ?_
  refine spec_use (csCopy_exec (P := P) hL _ hw₆
    (hI₅.mono hL (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₅) (by config_simp)) ?_
  intro c₇ k₇ hk₇ hw₇ ⟨cur₇, m₇, n₇, r410₇, rr₇, rm₇, o₇⟩
  config_simp at cur₇
  config_simp at m₇
  config_simp at n₇
  config_simp at rr₇
  config_simp at rm₇
  config_simp at o₇
  have hI₇ := hI₅.mono hL (fun r hr => by rw [n₇ r (by omega)]; exact upd_other _ _ _ (by omega))
    (fun a _ h _ => m₇ a h) (fun a _ => by rw [rm₇])
  -- place
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₇ 411 0 (by omega)) fun hw₈ => ?_
  have hcur : ∀ x < N, ({ c₇ with nreg := upd c₇.nreg 411 0 } : Config).nmem (Cb + x) =
      (pre (csList T H K Lz M) x).length := by
    intro x hx; config_simp; rw [cur₇ x hx, pre₅ x (by omega)]
  refine spec_use (csPlace_exec (P := P) hL _ hw₈
    (hI₇.mono hL (fun r hr => upd_other _ _ _ (by omega)) (fun _ _ _ _ => rfl) (fun _ _ => rfl))
    (by config_simp; exact r410₇) (by config_simp) hcur) ?_
  intro c₉ k₉ hk₉ hw₉ ⟨B₉, m₉, rm₉, n₉, r410₉, rr₉, o₉⟩
  config_simp at m₉
  config_simp at rm₉
  config_simp at n₉
  config_simp at rr₉
  config_simp at o₉
  refine ⟨?_, fun x hx => ?_, fun e he => ?_, fun a h1 h2 h3 => ?_, fun a h => ?_,
    fun r hr => ?_, fun r hr => ?_, ?_⟩
  · unfold csCost; omega
  · rw [m₉ _ (by omega) (by omega), m₇ _ (by omega), pre₅ x hx]
  · obtain ⟨x, hx, j, hj, rfl, hg⟩ := pre_getElem _ N e he
    have hgd : (arcList N (csList T H K Lz M)).getD ((pre (csList T H K Lz M) x).length + j)
        (0, 0, 0) = (blk (csList T H K Lz M) x).getD j (0, 0, 0) := by
      rw [List.getD_eq_getElem _ _ he, List.getD_eq_getElem _ _ hj]; exact hg
    rw [hgd]
    exact B₉ x hx j hj
  · rw [m₉ a h2 h3, m₇ a h2, m₅ a h1, m₃ a h1, m₁ a h1]
  · rw [rm₉ a h, rm₇, rm₅, rm₃, rm₁]
  · rw [n₉ r hr, upd_other _ _ _ (by omega), n₇ r hr, upd_other _ _ _ (by omega), n₅ r hr,
      upd_other _ _ _ (by omega), n₃ r hr, upd_other _ _ _ (by omega), n₁ r hr]
  · rw [rr₉ r hr, rr₇, rr₅, rr₃, rr₁]
  · rw [o₉, o₇, o₅, o₃, o₁]

/-- **The counting sort lays out the explicit arcs of `frProg`**: with the bases of
`mkPrm N 1 Dm p r L` (`L = csList T H K Lz M`, the offsets at `ob`, the heads at `ob + N + 1`,
the lengths at `lb`), the run of `csProg` leaves the fields `omem`, `emem`, `lmem` of
`Monge.FR.Data`, within `csCost M N` steps. -/
theorem csProg_mkPrm {Dm : ℕ → ℕ → ℤ} {p : ℕ → ℤ} {r : ℕ}
    (hL : CsLay M N Tb Hb Kb (mkPrm N 1 Dm p r (csList T H K Lz M)).ob Cb
      (mkPrm N 1 Dm p r (csList T H K Lz M)).lb Lb
      ((mkPrm N 1 Dm p r (csList T H K Lz M)).ob + N + 1) W T H K) (c : Config)
    (hc : WordsBounded W c)
    (hI : CsIn M N Tb Hb Kb (mkPrm N 1 Dm p r (csList T H K Lz M)).ob Cb
      (mkPrm N 1 Dm p r (csList T H K Lz M)).lb Lb
      ((mkPrm N 1 Dm p r (csList T H K Lz M)).ob + N + 1) T H K Lz c) :
    ∃ c' k, Exec P W csProg c c' k ∧ k ≤ csCost M N ∧
      (∀ x ≤ (mkPrm N 1 Dm p r (csList T H K Lz M)).N,
        c'.nmem ((mkPrm N 1 Dm p r (csList T H K Lz M)).ob + x) =
          (mkPrm N 1 Dm p r (csList T H K Lz M)).off x) ∧
      (∀ e < (mkPrm N 1 Dm p r (csList T H K Lz M)).m,
        c'.nmem ((mkPrm N 1 Dm p r (csList T H K Lz M)).ob +
          (mkPrm N 1 Dm p r (csList T H K Lz M)).N + 1 + e) =
          (mkPrm N 1 Dm p r (csList T H K Lz M)).dst e) ∧
      (∀ e < (mkPrm N 1 Dm p r (csList T H K Lz M)).m,
        c'.rmem ((mkPrm N 1 Dm p r (csList T H K Lz M)).lb + e) =
          (mkPrm N 1 Dm p r (csList T H K Lz M)).len e) := by
  obtain ⟨c', k, he, hk, ho, ha, -⟩ := csProg_exec (P := P) hL c hc hI
  exact ⟨c', k, he, hk, fun x hx => ho x hx, fun e he' => (ha e he').1,
    fun e he' => (ha e he').2⟩

end NegSSSP

end PlanarFlow
