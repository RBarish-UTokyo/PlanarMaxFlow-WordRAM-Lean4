module

public import PlanarFlow.NegSSSP.Enc.RnSem
public import PlanarFlow.NegSSSP.Enc.DkRun
public import PlanarFlow.NegSSSP.KEncOut
public import PlanarFlow.NegSSSP.LinGlue

/-!
# Renormalized potentials on the machine: the program and its phases

`rnProg` (registers `2966 … 2990`, plus `osProg`'s `1500 … 1520` and `dkProg`'s
`2500 … 2547`) reads `m` darts (tails `T[a] < w` at `Tb`, heads `H[a] < w` at `Hb`, lengths in the
offset encoding `LL[a]` at `LLb`) and `w` potentials `F[v]` (at `Fb`) and writes, at `OUTb`,
`OUT[v] = D v + F v + L − K` where `K = max F` and `D` are the distances by Dijkstra from a
virtual source `w` on the arcs `RnArcs` (`rnArcs`): the darts with the lengths
`LL[a] + F[T a] − (F[H a] + L)` and the source arcs of lengths `K − F v`. Phases:

1. `rnSetup`; the maximum `K` (`rnMax`, `rnK`);
2. the arc arrays `TK`, `KP` (all `1`), `NH`, `LN` of the `M = m + w` arcs (`rnArcBody`);
3. the out-lists by `osProg` (`osProg_lists`: the generic form of its out-lists);
4. Dijkstra in memory (`dkProg`), from the source `w`, `Inf = K + 1`;
5. the output (`rnOutBody`).

The scratch is `[Ab, Ab + 5 M + 8 N + 1)`, `N = w + 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap Monge.FR

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- Constants and the bases of the arc arrays (`r2966 = m`, `r2967 = w`, `r2974 = Ab`). -/
def rnSetup : Stmt := block [.constN 2979 1, .addN 2975 2966 2967, .addN 2976 2967 2979,
  .constN 2977 0, .constN 2978 0, .copyN 2980 2974, .addN 2981 2980 2975,
  .addN 2982 2981 2975, .addN 2983 2982 2975]

/-- One step of the maximum: `K := max K F[i]`. -/
def rnMaxBody : Stmt :=
  .seq (block [.addN 2984 2971 2978, .loadN 2984 2984])
    (.seq (.ifLtN 2977 2984 (.instr (.copyN 2977 2984)) .skip) (.instr (.addN 2978 2978 2979)))

/-- A dart arc: `r2985 = T[i]`, `r2986 = H[i]`, `r2989 = LL[i] + F[T i] − (F[H i] + L)`. -/
def rnDart : Stmt := block [.addN 2984 2968 2978, .loadN 2985 2984, .addN 2984 2969 2978,
  .loadN 2986 2984, .addN 2984 2971 2985, .loadN 2987 2984, .addN 2984 2971 2986,
  .loadN 2988 2984, .addN 2984 2970 2978, .loadN 2989 2984, .addN 2989 2989 2987,
  .addN 2988 2988 2972, .subN 2989 2989 2988]

/-- A source arc: `r2985 = w`, `r2986 = i − m`, `r2989 = K − F[i − m]`. -/
def rnSrc : Stmt := block [.subN 2986 2978 2966, .copyN 2985 2967, .addN 2984 2971 2986,
  .loadN 2988 2984, .subN 2989 2977 2988]

/-- The four arrays at `i`: `TK[i] := r2985`, `KP[i] := 1`, `NH[i] := r2986`,
`LN[i] := r2989`. -/
def rnTail : Stmt := block [.addN 2984 2980 2978, .storeN 2984 2985, .addN 2984 2981 2978,
  .storeN 2984 2979, .addN 2984 2982 2978, .storeN 2984 2986, .addN 2984 2983 2978,
  .storeN 2984 2989, .addN 2978 2978 2979]

/-- One arc. -/
def rnArcBody : Stmt := .seq (.ifLtN 2978 2966 rnDart rnSrc) rnTail

/-- The registers of `osProg`. -/
def rnOsSet : Stmt := block [.copyN 1500 2975, .copyN 1501 2976, .copyN 1502 2980,
  .copyN 1504 2981, .addN 1505 2983 2975, .addN 1506 1505 2976, .addN 1506 1506 2979,
  .addN 1507 1506 2976, .addN 1508 1507 2976, .addN 1509 1508 2976]

/-- The registers of `dkProg` (and the base of its distances kept in `r2990`). -/
def rnDkSet : Stmt := block [.copyN 2500 2976, .addN 2501 1509 2975, .addN 2502 2501 2976,
  .copyN 2504 1507, .copyN 2505 1508, .copyN 2506 1509, .copyN 2507 2982, .copyN 2508 2983,
  .addN 2509 2977 2979, .copyN 2510 2967, .copyN 2990 2501]

/-- One output: `OUT[i] := D[i] + F[i] + L − K`. -/
def rnOutBody : Stmt := block [.addN 2984 2990 2978, .loadN 2985 2984, .addN 2984 2971 2978,
  .loadN 2986 2984, .addN 2985 2985 2986, .addN 2985 2985 2972, .subN 2985 2985 2977,
  .addN 2984 2973 2978, .storeN 2984 2985, .addN 2978 2978 2979]

/-- The first part of `rnProg`. -/
def rnFront : Stmt :=
  .seq rnSetup <| .seq (.whileLtN 2978 2967 rnMaxBody) <|
    .seq (.instr (.constN 2978 0)) (.whileLtN 2978 2975 rnArcBody)

/-- The middle part: the out-lists. -/
def rnMid : Stmt := .seq rnOsSet osProg

/-- The last part: Dijkstra and the output. -/
def rnBack : Stmt :=
  .seq rnDkSet <| .seq dkProg <| .seq (.instr (.constN 2978 0)) (.whileLtN 2978 2967 rnOutBody)

/-- **The renormalization** (`r2966 = m`, `r2967 = w`, `r2968 = Tb`, `r2969 = Hb`,
`r2970 = LLb`, `r2971 = Fb`, `r2972 = L`, `r2973 = OUTb`, `r2974 = Ab`). -/
def rnProg : Stmt := .seq rnFront (.seq rnMid rnBack)

theorem rnProg_natOnly : Klein.natOnly rnProg = true := by kernel_rfl

/-! ### The values -/

/-- The maximum of the first `i` potentials (and `0`). -/
def rnK (mem : ℕ → ℕ) (Fb : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => max (rnK mem Fb i) (mem (Fb + i))

lemma le_rnK {mem : ℕ → ℕ} {Fb : ℕ} : ∀ {i v : ℕ}, v < i → mem (Fb + v) ≤ rnK mem Fb i
  | i + 1, v, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact (le_rnK h).trans (le_max_left _ _)
    · exact le_max_right _ _

lemma rnK_le {mem : ℕ → ℕ} {Fb Fm : ℕ} : ∀ {i : ℕ}, (∀ v < i, mem (Fb + v) ≤ Fm) →
    rnK mem Fb i ≤ Fm
  | 0, _ => Nat.zero_le _
  | i + 1, h => max_le (rnK_le fun v hv => h v (by omega)) (h i (by omega))

/-- **The arcs read from the memory.** -/
def rnArcs (mem : ℕ → ℕ) (m w Tb Hb LLb Fb L : ℕ) : RnArcs where
  m := m
  w := w
  T a := mem (Tb + a)
  H a := mem (Hb + a)
  R a := mem (LLb + a) + mem (Fb + mem (Tb + a)) - (mem (Fb + mem (Hb + a)) + L)
  S v := rnK mem Fb w - mem (Fb + v)

/-! ### The phases -/

theorem rnSetup_exec (c : Config) (hc : WordsBounded W c) {m w Ab : ℕ}
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r74 : c.nreg 2974 = Ab)
    (hW : Ab + 4 * (m + w) + 1 ≤ W) :
    ∃ c' k, Exec P W rnSetup c c' k ∧ k = 9 ∧ c'.nreg 2975 = m + w ∧ c'.nreg 2976 = w + 1 ∧
      c'.nreg 2977 = 0 ∧ c'.nreg 2978 = 0 ∧ c'.nreg 2979 = 1 ∧ c'.nreg 2980 = Ab ∧
      c'.nreg 2981 = Ab + (m + w) ∧ c'.nreg 2982 = Ab + (m + w) + (m + w) ∧
      c'.nreg 2983 = Ab + (m + w) + (m + w) + (m + w) ∧
      (∀ r, r < 2975 ∨ 2983 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnSetup
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r67, r74]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r67, r74])
  simp only [upd_apply]; split_ifs <;> omega

theorem rnMaxBody_exec (c : Config) (hc : WordsBounded W c) {Fb K i : ℕ}
    (r71 : c.nreg 2971 = Fb) (r77 : c.nreg 2977 = K) (r78 : c.nreg 2978 = i)
    (r79 : c.nreg 2979 = 1) (w1 : Fb + i ≤ W) (w2 : i + 1 ≤ W) :
    ∃ c' k, Exec P W rnMaxBody c c' k ∧ k ≤ 5 ∧ c'.nreg 2977 = max K (c.nmem (Fb + i)) ∧
      c'.nreg 2978 = i + 1 ∧ (∀ r, r ≠ 2977 → r ≠ 2978 → r ≠ 2984 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnMaxBody
  obtain ⟨c₁, k₁, e₁, hk₁, g84, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 2984 2971 2978, .loadN 2984 2984]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2984 = c.nmem (Fb + i) ∧ (∀ r, r ≠ 2984 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r71, r78]); omega)
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r71, r78]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q77 : c₁.nreg 2977 = K := by rw [gn₁ _ (by omega), r77]
  obtain ⟨c₂, k₂, e₂, hk₂, g77, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (.ifLtN 2977 2984 (.instr (.copyN 2977 2984)) .skip) c₁ c₂ k₂ ∧ k₂ ≤ 2 ∧
      c₂.nreg 2977 = max K (c.nmem (Fb + i)) ∧ (∀ r, r ≠ 2977 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases h : K < c.nmem (Fb + i)
    · have hlt : c₁.nreg 2977 < c₁.nreg 2984 := by rw [q77, g84]; exact h
      have e := Exec.copyN (P := P) hw₁ 2977 2984
      refine ⟨_, 1 + 1, .ifLtN_true hlt e, by omega, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [g84]; omega
      · config_simp; rw [upd_other _ _ _ hr]
    · have hlt : ¬ c₁.nreg 2977 < c₁.nreg 2984 := by rw [q77, g84]; exact h
      refine ⟨c₁, 0 + 2, .ifLtN_false hlt (.skip hw₁), by omega, ?_, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      rw [q77]; omega
  have hw₂ := e₂.wb_right
  have q78 : c₂.nreg 2978 = i := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r78]
  have q79 : c₂.nreg 2979 = 1 := by rw [gn₂ _ (by omega), gn₁ _ (by omega), r79]
  have e₃ := Exec.addN (P := P) hw₂ 2978 2978 2979 (by rw [q78, q79]; omega)
  refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [gm₂, gm₁], by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · config_simp; exact g77
  · config_simp; rw [q78, q79]
  · config_simp; simp only [upd_apply, h2, ite_false]; rw [gn₂ r h1, gn₁ r h3]

/-- **The maximum of the potentials.** -/
theorem rnMax_exec (c : Config) (hc : WordsBounded W c) {w Fb : ℕ}
    (r67 : c.nreg 2967 = w) (r71 : c.nreg 2971 = Fb) (r77 : c.nreg 2977 = 0)
    (r78 : c.nreg 2978 = 0) (r79 : c.nreg 2979 = 1) (w1 : Fb + w + 1 ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 2978 2967 rnMaxBody) c c' k ∧ k ≤ 7 * w + 2 ∧
      c'.nreg 2977 = rnK c.nmem Fb w ∧
      (∀ r, r ≠ 2977 → r ≠ 2978 → r ≠ 2984 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 2977 = rnK c.nmem Fb i ∧
      (∀ r, r ≠ 2977 → r ≠ 2978 → r ≠ 2984 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2978) (bR := 2967)
    (body := rnMaxBody) J (K := 5) (n := w) c hc r78 r67
    ⟨r77, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j77, jn, jm, jr, jrm, jo⟩ := hJ
      obtain ⟨c'', k, ex, hk, h77, h78, hn, hm, hr, hrm, ho⟩ := rnMaxBody_exec (P := P) (Fb := Fb) c' hw
        (by rw [jn _ (by omega) (by omega) (by omega)]; exact r71) j77 ha
        (by rw [jn _ (by omega) (by omega) (by omega)]; exact r79) (by omega) (by omega)
      refine ⟨c'', k, ex, hk, h78, (hn _ (by omega) (by omega) (by omega)).trans hb,
        ?_, fun r h1 h2 h3 => by rw [hn r h1 h2 h3, jn r h1 h2 h3], by rw [hm, jm],
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      rw [h77, jm]; rfl)
  obtain ⟨j77, jn, jm, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, hk₂, j77, jn, jm, jr, jrm, jo⟩

theorem rnDart_exec (c : Config) (hc : WordsBounded W c) {Tb Hb LLb Fb L i : ℕ}
    (r68 : c.nreg 2968 = Tb) (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb)
    (r71 : c.nreg 2971 = Fb) (r72 : c.nreg 2972 = L) (r78 : c.nreg 2978 = i)
    (w1 : Tb + i ≤ W) (w2 : Hb + i ≤ W) (w3 : Fb + c.nmem (Tb + i) ≤ W)
    (w4 : Fb + c.nmem (Hb + i) ≤ W) (w5 : LLb + i ≤ W)
    (w6 : c.nmem (LLb + i) + c.nmem (Fb + c.nmem (Tb + i)) ≤ W)
    (w7 : c.nmem (Fb + c.nmem (Hb + i)) + L ≤ W) :
    ∃ c' k, Exec P W rnDart c c' k ∧ k = 13 ∧ c'.nreg 2985 = c.nmem (Tb + i) ∧
      c'.nreg 2986 = c.nmem (Hb + i) ∧
      c'.nreg 2989 = c.nmem (LLb + i) + c.nmem (Fb + c.nmem (Tb + i)) -
        (c.nmem (Fb + c.nmem (Hb + i)) + L) ∧
      (∀ r, r < 2984 ∨ 2989 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnDart
  exec_block
  all_goals try ((try config_simp); (try simp only [r68, r69, r70, r71, r72, r78]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r68, r69, r70, r71, r72, r78])
  simp only [upd_apply]; split_ifs <;> omega

theorem rnSrc_exec (c : Config) (hc : WordsBounded W c) {m w Fb K i : ℕ}
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r71 : c.nreg 2971 = Fb)
    (r77 : c.nreg 2977 = K) (r78 : c.nreg 2978 = i) (w1 : Fb + (i - m) ≤ W) :
    ∃ c' k, Exec P W rnSrc c c' k ∧ k = 5 ∧ c'.nreg 2985 = w ∧ c'.nreg 2986 = i - m ∧
      c'.nreg 2989 = K - c.nmem (Fb + (i - m)) ∧
      (∀ r, r < 2984 ∨ 2989 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnSrc
  exec_block
  all_goals try ((try config_simp); (try simp only [r66, r67, r71, r77, r78]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r66, r67, r71, r77, r78])
  simp only [upd_apply]; split_ifs <;> omega

theorem rnTail_exec (c : Config) (hc : WordsBounded W c) {B0 B1 B2 B3 i x y z : ℕ}
    (r80 : c.nreg 2980 = B0) (r81 : c.nreg 2981 = B1) (r82 : c.nreg 2982 = B2)
    (r83 : c.nreg 2983 = B3) (r78 : c.nreg 2978 = i) (r79 : c.nreg 2979 = 1)
    (r85 : c.nreg 2985 = x) (r86 : c.nreg 2986 = y) (r89 : c.nreg 2989 = z)
    (w0 : B0 + i ≤ W) (w1 : B1 + i ≤ W) (w2 : B2 + i ≤ W) (w3 : B3 + i ≤ W)
    (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W rnTail c c' k ∧ k = 9 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (B0 + i) x) (B1 + i) 1) (B2 + i) y) (B3 + i) z ∧
      c'.nreg 2978 = i + 1 ∧ (∀ r, r ≠ 2978 → r ≠ 2984 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnTail
  exec_block
  all_goals try ((try config_simp); (try simp only [r80, r81, r82, r83, r78, r79]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r80, r81, r82, r83, r78, r79, r85, r86, r89])
  simp only [upd_apply]; split_ifs <;> omega

/-- The tail of an arc read from the memory. -/
def rnTkV (mem : ℕ → ℕ) (m w Tb i : ℕ) : ℕ := if i < m then mem (Tb + i) else w

/-- The head of an arc read from the memory. -/
def rnNhV (mem : ℕ → ℕ) (m Hb i : ℕ) : ℕ := if i < m then mem (Hb + i) else i - m

/-- The length of an arc read from the memory. -/
def rnLnV (mem : ℕ → ℕ) (m Tb Hb LLb Fb L K i : ℕ) : ℕ :=
  if i < m then mem (LLb + i) + mem (Fb + mem (Tb + i)) - (mem (Fb + mem (Hb + i)) + L)
  else K - mem (Fb + (i - m))

theorem rnArcBody_exec (c : Config) (hc : WordsBounded W c)
    {m w Tb Hb LLb Fb L K i B0 B1 B2 B3 : ℕ}
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r68 : c.nreg 2968 = Tb)
    (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r77 : c.nreg 2977 = K) (r78 : c.nreg 2978 = i)
    (r79 : c.nreg 2979 = 1) (r80 : c.nreg 2980 = B0) (r81 : c.nreg 2981 = B1)
    (r82 : c.nreg 2982 = B2) (r83 : c.nreg 2983 = B3)
    (hd : i < m → Tb + i ≤ W ∧ Hb + i ≤ W ∧ Fb + c.nmem (Tb + i) ≤ W ∧
      Fb + c.nmem (Hb + i) ≤ W ∧ LLb + i ≤ W ∧
      c.nmem (LLb + i) + c.nmem (Fb + c.nmem (Tb + i)) ≤ W ∧
      c.nmem (Fb + c.nmem (Hb + i)) + L ≤ W)
    (hs : m ≤ i → Fb + (i - m) ≤ W)
    (w0 : B0 + i ≤ W) (w1 : B1 + i ≤ W) (w2 : B2 + i ≤ W) (w3 : B3 + i ≤ W)
    (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W rnArcBody c c' k ∧ k ≤ 23 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (B0 + i) (rnTkV c.nmem m w Tb i)) (B1 + i) 1) (B2 + i)
        (rnNhV c.nmem m Hb i)) (B3 + i) (rnLnV c.nmem m Tb Hb LLb Fb L K i) ∧
      c'.nreg 2978 = i + 1 ∧
      (∀ r, r ≠ 2978 → (r < 2984 ∨ 2989 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnArcBody
  obtain ⟨c₁, k₁, e₁, hk₁, g85, g86, g89, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (.ifLtN 2978 2966 rnDart rnSrc) c c₁ k₁ ∧ k₁ ≤ 14 ∧
      c₁.nreg 2985 = rnTkV c.nmem m w Tb i ∧ c₁.nreg 2986 = rnNhV c.nmem m Hb i ∧
      c₁.nreg 2989 = rnLnV c.nmem m Tb Hb LLb Fb L K i ∧
      (∀ r, r < 2984 ∨ 2989 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    by_cases h : i < m
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hd h
      obtain ⟨c₁, k₁, e₁, hk₁, g85, g86, g89, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
        rnDart_exec (P := P) c hc r68 r69 r70 r71 r72 r78 d1 d2 d3 d4 d5 d6 d7
      refine ⟨c₁, k₁ + 1, .ifLtN_true (by rw [r78, r66]; exact h) e₁, by omega, ?_, ?_, ?_,
        gn₁, gm₁, gr₁, grm₁, go₁⟩
      · rw [g85]; simp [rnTkV, h]
      · rw [g86]; simp [rnNhV, h]
      · rw [g89]; simp [rnLnV, h]
    · obtain ⟨c₁, k₁, e₁, hk₁, g85, g86, g89, gn₁, gm₁, gr₁, grm₁, go₁⟩ :=
        rnSrc_exec (P := P) c hc r66 r67 r71 r77 r78 (hs (by omega))
      refine ⟨c₁, k₁ + 2, .ifLtN_false (by rw [r78, r66]; exact h) e₁, by omega, ?_, ?_, ?_,
        gn₁, gm₁, gr₁, grm₁, go₁⟩
      · rw [g85]; simp [rnTkV, h]
      · rw [g86]; simp [rnNhV, h]
      · rw [g89]; simp [rnLnV, h]
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, gm₂, g78, gn₂, gr₂, grm₂, go₂⟩ := rnTail_exec (P := P) c₁ hw₁
    (by rw [gn₁ _ (by omega)]; exact r80) (by rw [gn₁ _ (by omega)]; exact r81)
    (by rw [gn₁ _ (by omega)]; exact r82) (by rw [gn₁ _ (by omega)]; exact r83)
    (by rw [gn₁ _ (by omega)]; exact r78) (by rw [gn₁ _ (by omega)]; exact r79)
    g85 g86 g89 w0 w1 w2 w3 w4
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by rw [gm₂, gm₁], g78, fun r h1 h2 => ?_,
    by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  rw [gn₂ r h1 (by omega), gn₁ r h2]

/-- **The arc arrays**: `TK` at `Ab`, `KP` at `Ab + M`, `NH` at `Ab + 2M`, `LN` at `Ab + 3M`
(`M = m + w`), the arcs `rnArcs` of the memory at the start. -/
theorem rnArcLoop_exec (c : Config) (hc : WordsBounded W c)
    {m w Tb Hb LLb Fb L Ab Fm Lm : ℕ}
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r68 : c.nreg 2968 = Tb)
    (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r75 : c.nreg 2975 = m + w) (r77 : c.nreg 2977 = rnK c.nmem Fb w)
    (r78 : c.nreg 2978 = 0) (r79 : c.nreg 2979 = 1) (r80 : c.nreg 2980 = Ab)
    (r81 : c.nreg 2981 = Ab + (m + w)) (r82 : c.nreg 2982 = Ab + (m + w) + (m + w))
    (r83 : c.nreg 2983 = Ab + (m + w) + (m + w) + (m + w))
    (hT : ∀ a < m, c.nmem (Tb + a) < w) (hH : ∀ a < m, c.nmem (Hb + a) < w)
    (hF : ∀ v < w, c.nmem (Fb + v) ≤ Fm) (hLL : ∀ a < m, c.nmem (LLb + a) ≤ Lm)
    (lT : Tb + m ≤ Ab) (lH : Hb + m ≤ Ab) (lL : LLb + m ≤ Ab) (lF : Fb + w ≤ Ab)
    (wE : Ab + 4 * (m + w) + 1 ≤ W) (wV : Fm + Lm + L ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 2978 2975 rnArcBody) c c' k ∧ k ≤ 25 * (m + w) + 2 ∧
      (∀ a < m + w,
        c'.nmem (Ab + a) = (rnArcs c.nmem m w Tb Hb LLb Fb L).tk a ∧
        c'.nmem (Ab + (m + w) + a) = 1 ∧
        c'.nmem (Ab + (m + w) + (m + w) + a) = (rnArcs c.nmem m w Tb Hb LLb Fb L).nh a ∧
        c'.nmem (Ab + (m + w) + (m + w) + (m + w) + a) =
          (rnArcs c.nmem m w Tb Hb LLb Fb L).ln a) ∧
      (∀ x, x < Ab ∨ Ab + 4 * (m + w) ≤ x → c'.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 2978 → (r < 2984 ∨ 2989 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A := rnArcs c.nmem m w Tb Hb LLb Fb L with hA
  set M := m + w with hM
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ a < i, c'.nmem (Ab + a) = A.tk a ∧ c'.nmem (Ab + M + a) = 1 ∧
        c'.nmem (Ab + M + M + a) = A.nh a ∧ c'.nmem (Ab + M + M + M + a) = A.ln a) ∧
      (∀ x, x < Ab ∨ Ab + 4 * M ≤ x → c'.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 2978 → (r < 2984 ∨ 2989 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2978) (bR := 2975)
    (body := rnArcBody) J (K := 23) (n := M) c hc r78 r75
    ⟨fun a ha => absurd ha (by omega), fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q : ∀ r, r ≠ 2978 → (r < 2984 ∨ 2989 < r) → ∀ v, c.nreg r = v → c'.nreg r = v :=
        fun r h1 h2 v h => (jn r h1 h2).trans h
      -- the inputs are unchanged
      have eT : i < m → c'.nmem (Tb + i) = c.nmem (Tb + i) := fun h => j2 _ (by omega)
      have eH : i < m → c'.nmem (Hb + i) = c.nmem (Hb + i) := fun h => j2 _ (by omega)
      have eL : i < m → c'.nmem (LLb + i) = c.nmem (LLb + i) := fun h => j2 _ (by omega)
      have eF : ∀ v < w, c'.nmem (Fb + v) = c.nmem (Fb + v) := fun v h => j2 _ (by omega)
      have eFT : i < m → c'.nmem (Fb + c'.nmem (Tb + i)) = c.nmem (Fb + c.nmem (Tb + i)) :=
        fun h => by rw [eT h]; exact eF _ (hT i h)
      have eFH : i < m → c'.nmem (Fb + c'.nmem (Hb + i)) = c.nmem (Fb + c.nmem (Hb + i)) :=
        fun h => by rw [eH h]; exact eF _ (hH i h)
      obtain ⟨c'', k, ex, hk, hm, h78, hn, hr, hrm, ho⟩ := rnArcBody_exec (P := P)
        (m := m) (w := w) (Tb := Tb) (Hb := Hb) (LLb := LLb) (Fb := Fb) (L := L)
        (K := rnK c.nmem Fb w) (B0 := Ab) (B1 := Ab + M) (B2 := Ab + M + M)
        (B3 := Ab + M + M + M) c' hw
        (q _ (by omega) (by omega) _ r66) (q _ (by omega) (by omega) _ r67)
        (q _ (by omega) (by omega) _ r68) (q _ (by omega) (by omega) _ r69)
        (q _ (by omega) (by omega) _ r70) (q _ (by omega) (by omega) _ r71)
        (q _ (by omega) (by omega) _ r72) (q _ (by omega) (by omega) _ r77) ha
        (q _ (by omega) (by omega) _ r79) (q _ (by omega) (by omega) _ r80)
        (q _ (by omega) (by omega) _ r81) (q _ (by omega) (by omega) _ r82)
        (q _ (by omega) (by omega) _ r83)
        (fun h => by
          have := hT i h; have := hH i h; have := hLL i h
          have := hF _ (hT i h); have := hF _ (hH i h)
          rw [eFT h, eFH h, eT h, eH h, eL h]
          refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
        (fun h => by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have vT : rnTkV c'.nmem m w Tb i = A.tk i := by
        unfold rnTkV; simp only [hA, RnArcs.tk, rnArcs]
        split_ifs with h
        · exact eT h
        · rfl
      have vH : rnNhV c'.nmem m Hb i = A.nh i := by
        unfold rnNhV; simp only [hA, RnArcs.nh, rnArcs]
        split_ifs with h
        · exact eH h
        · rfl
      have vL : rnLnV c'.nmem m Tb Hb LLb Fb L (rnK c.nmem Fb w) i = A.ln i := by
        unfold rnLnV; simp only [hA, RnArcs.ln, rnArcs]
        split_ifs with h
        · rw [eL h, eFT h, eFH h]
        · rw [eF _ (by omega)]
      rw [vT, vH, vL] at hm
      refine ⟨c'', k, ex, hk, h78, (hn _ (by omega) (by omega)).trans hb, fun a ha' => ?_,
        fun x hx => ?_, fun r h1 h2 => (hn r h1 h2).trans (jn r h1 h2), by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha' with ha' | rfl
        · obtain ⟨t1, t2, t3, t4⟩ := j1 a ha'
          simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega
        · simp only [upd_apply]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega
      · rw [hm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j2 x hx)
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, k₂, e₂, by omega, fun a ha => ?_, fun x hx => j2 x (by omega), jn, jr, jrm, jo⟩
  exact j1 a ha

/-! ### The out-lists and Dijkstra -/

/-- The indices `i < M` kept (`K i ≠ 0`) with key `T i = u`, in order. -/
def osFl (T K : ℕ → ℕ) (M u : ℕ) : List ℕ :=
  (List.range M).filter (fun i => decide (K i ≠ 0 ∧ T i = u))

lemma sum_length_blk (L : List (ℕ × ℕ × ℤ)) :
    ∀ n, ∑ u ∈ range n, (blk L u).length = (pre L n).length
  | 0 => by simp [pre]
  | n + 1 => by rw [sum_range_succ, sum_length_blk L n, length_pre_succ]

/-- **The out-lists of `osProg` in generic form**: for every key `u < N`, the words
`OL[OB[u] + j]`, `j < OE[u] − OB[u]`, are the kept indices of key `u` in order (`osFl`); the
lists have `M` entries at most in all. -/
theorem osProg_lists {M N Tb Kb Ob Cb OBb OEb Db : ℕ} {T K : ℕ → ℕ}
    (hL : OsLay M N Tb Kb Ob Cb OBb OEb Db W T K) (c : Config)
    (hc : WordsBounded W c) (hI : OsIn M N Tb Kb Ob Cb OBb OEb Db T K c) :
    ∃ c' k, Exec P W osProg c c' k ∧ k ≤ osCost M N ∧
      (∀ u < N, c'.nmem (OEb + u) = c'.nmem (OBb + u) + (osFl T K M u).length ∧
        c'.nmem (OEb + u) ≤ M ∧
        ∀ j < (osFl T K M u).length, c'.nmem (Db + (c'.nmem (OBb + u) + j)) =
          (osFl T K M u).getD j 0) ∧
      (∑ u ∈ range N, (c'.nmem (OEb + u) - c'.nmem (OBb + u)) ≤ M) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * N + 1 ≤ a) → (a < OBb ∨ Db + M ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1510 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hOB, hOL, hm, hn, hr, hrm, ho⟩ := osProg_exec (P := P) hL c hc hI
  set L := csList T id K (fun _ => 0) M with hLd
  have hbl : ∀ u, (blk L u).length = (osFl T K M u).length := fun u => by
    have := congrArg List.length (blk_map_csList T K (fun _ => 0) u M)
    simpa [osFl] using this
  refine ⟨c', k, ex, hk, fun u hu => ?_, ?_, hm, hn, hr, hrm, ho⟩
  · obtain ⟨hb, he⟩ := hOB u hu
    refine ⟨by rw [he, hb, length_pre_succ, hbl], ?_, fun j hj => ?_⟩
    · rw [he]; exact length_pre_csList_le L hLd _
    · have hj' : j < (blk L u).length := by rw [hbl]; exact hj
      have hlt : (pre L u).length + j < (pre L N).length := by
        have := length_pre_mono L (show u + 1 ≤ N by omega)
        rw [length_pre_succ] at this; omega
      rw [hb, hOL _ hlt, pre_getD_blk L hu hj']
      have h := List.getElem_of_eq (blk_map_csList T K (fun _ => 0) u M) (i := j)
        (by simpa using hj')
      simp only [List.getElem_map] at h
      rw [h, List.getD_eq_getElem _ _ (by simpa [osFl] using hj)]
      rfl
  · have e : ∀ u ∈ range N, c'.nmem (OEb + u) - c'.nmem (OBb + u) = (blk L u).length :=
      fun u hu => by
        obtain ⟨hb, he⟩ := hOB u (mem_range.1 hu)
        rw [he, hb, length_pre_succ]; omega
    rw [sum_congr rfl e, sum_length_blk]
    exact length_pre_csList_le L hLd _

/-- **Dijkstra's walks are the walks of the arcs**: if the out-lists of the nodes `u < A.w + 1`
are the arcs of tail `u` (`osFl` with all flags `1`), the heads and lengths read by Dijkstra are
those of the arcs, and the source is `A.w`, then `DkReach` and `RnReach` agree. -/
theorem dk_rn {p : DkP} {A : RnArcs} (hs : p.s = A.w)
    (hl : ∀ u < p.n, p.oe u = p.ob u + (osFl A.tk (fun _ => 1) (A.m + A.w) u).length ∧
      ∀ j < (osFl A.tk (fun _ => 1) (A.m + A.w) u).length,
        p.ol (p.ob u + j) = (osFl A.tk (fun _ => 1) (A.m + A.w) u).getD j 0)
    (hnh : ∀ a < A.m + A.w, p.nh a = A.nh a) (hln : ∀ a < A.m + A.w, p.ln a = A.ln a)
    (htk : ∀ a < A.m + A.w, A.tk a < p.n) :
    (∀ y L, DkReach p y L → RnReach A y L) ∧ (∀ y L, RnReach A y L → DkReach p y L) := by
  constructor
  · intro y L h
    induction h with
    | src => rw [hs]; exact .src
    | @step u L i _ hu h1 h2 ih =>
      obtain ⟨he, hol⟩ := hl u hu
      have hj : i - p.ob u < (osFl A.tk (fun _ => 1) (A.m + A.w) u).length := by omega
      have e := hol _ hj
      rw [show p.ob u + (i - p.ob u) = i by omega] at e
      have hmem : p.ol i ∈ osFl A.tk (fun _ => 1) (A.m + A.w) u := by
        rw [e, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      simp only [osFl, List.mem_filter, List.mem_range, ne_eq, one_ne_zero,
        not_false_eq_true, true_and, decide_eq_true_eq] at hmem
      rw [hnh _ hmem.1, hln _ hmem.1]
      exact .step ih hmem.1 hmem.2
  · intro y L h
    induction h with
    | src => rw [← hs]; exact .src
    | @step u L a _ ha htk' ih =>
      have hu : u < p.n := htk' ▸ htk a ha
      obtain ⟨he, hol⟩ := hl u hu
      have hmem : a ∈ osFl A.tk (fun _ => 1) (A.m + A.w) u := by
        simp only [osFl, List.mem_filter, List.mem_range, ne_eq, one_ne_zero,
          not_false_eq_true, true_and, decide_eq_true_eq]
        exact ⟨ha, htk'⟩
      obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 hmem
      have e := hol j hj
      rw [List.getD_eq_getElem _ _ hj, hja] at e
      have := DkReach.step ih hu (i := p.ob u + j) (by omega) (by omega)
      rw [e, hnh _ ha, hln _ ha] at this
      exact this

/-! ### The register blocks and the output -/

theorem rnOsSet_exec (c : Config) (hc : WordsBounded W c) {M N Ab B3 : ℕ}
    (r75 : c.nreg 2975 = M) (r76 : c.nreg 2976 = N) (r79 : c.nreg 2979 = 1)
    (r80 : c.nreg 2980 = Ab) (r81 : c.nreg 2981 = Ab + M) (r83 : c.nreg 2983 = B3)
    (hW : B3 + M + 4 * N + 1 ≤ W) :
    ∃ c' k, Exec P W rnOsSet c c' k ∧ k = 10 ∧ c'.nreg 1500 = M ∧ c'.nreg 1501 = N ∧
      c'.nreg 1502 = Ab ∧ c'.nreg 1504 = Ab + M ∧ c'.nreg 1505 = B3 + M ∧
      c'.nreg 1506 = B3 + M + N + 1 ∧ c'.nreg 1507 = B3 + M + N + 1 + N ∧
      c'.nreg 1508 = B3 + M + N + 1 + N + N ∧ c'.nreg 1509 = B3 + M + N + 1 + N + N + N ∧
      (∀ r, r < 1500 ∨ 1509 < r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnOsSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r75, r76, r79, r80, r81, r83]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r75, r76, r79, r80, r81, r83])
  simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 1600000 in
theorem rnDkSet_exec (c : Config) (hc : WordsBounded W c) {M N w K Ol OB OE NHb LNb : ℕ}
    (r75 : c.nreg 2975 = M) (r76 : c.nreg 2976 = N) (r67 : c.nreg 2967 = w)
    (r77 : c.nreg 2977 = K) (r79 : c.nreg 2979 = 1) (r82 : c.nreg 2982 = NHb)
    (r83 : c.nreg 2983 = LNb) (r07 : c.nreg 1507 = OB) (r08 : c.nreg 1508 = OE)
    (r09 : c.nreg 1509 = Ol) (hW : Ol + M + N ≤ W) (hK : K + 1 ≤ W) :
    ∃ c' k, Exec P W rnDkSet c c' k ∧ k = 11 ∧ c'.nreg 2500 = N ∧ c'.nreg 2501 = Ol + M ∧
      c'.nreg 2502 = Ol + M + N ∧ c'.nreg 2504 = OB ∧ c'.nreg 2505 = OE ∧
      c'.nreg 2506 = Ol ∧ c'.nreg 2507 = NHb ∧ c'.nreg 2508 = LNb ∧ c'.nreg 2509 = K + 1 ∧
      c'.nreg 2510 = w ∧ c'.nreg 2990 = Ol + M ∧
      (∀ r, (r < 2500 ∨ 2510 < r) → r ≠ 2990 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnDkSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r75, r76, r67, r77, r79, r82, r83, r07, r08, r09]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals config_simp
  all_goals try (simp only [r75, r76, r67, r77, r79, r82, r83, r07, r08, r09])
  simp only [upd_apply]; split_ifs <;> omega

theorem rnOutBody_exec (c : Config) (hc : WordsBounded W c) {Db Fb L OUTb K i : ℕ}
    (r90 : c.nreg 2990 = Db) (r71 : c.nreg 2971 = Fb) (r72 : c.nreg 2972 = L)
    (r73 : c.nreg 2973 = OUTb) (r77 : c.nreg 2977 = K) (r78 : c.nreg 2978 = i)
    (r79 : c.nreg 2979 = 1) (w1 : Db + i ≤ W) (w2 : Fb + i ≤ W)
    (w3 : c.nmem (Db + i) + c.nmem (Fb + i) + L ≤ W) (w4 : OUTb + i ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c' k, Exec P W rnOutBody c c' k ∧ k = 10 ∧
      c'.nmem = upd c.nmem (OUTb + i) (c.nmem (Db + i) + c.nmem (Fb + i) + L - K) ∧
      c'.nreg 2978 = i + 1 ∧
      (∀ r, r ≠ 2978 → r ≠ 2984 → r ≠ 2985 → r ≠ 2986 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rnOutBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r71, r72, r73, r77, r78, r79]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r90, r71, r72, r73, r77, r78, r79])
  simp only [upd_apply]; split_ifs <;> omega

/-- **The output loop.** -/
theorem rnOut_exec (c : Config) (hc : WordsBounded W c) {w Db Fb L OUTb K : ℕ}
    (r67 : c.nreg 2967 = w) (r90 : c.nreg 2990 = Db) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r73 : c.nreg 2973 = OUTb) (r77 : c.nreg 2977 = K)
    (r78 : c.nreg 2978 = 0) (r79 : c.nreg 2979 = 1) (w1 : Db + w ≤ W) (w2 : Fb + w ≤ W)
    (w4 : OUTb + w + 1 ≤ W) (dD : OUTb + w ≤ Db ∨ Db + w ≤ OUTb)
    (dF : OUTb + w ≤ Fb ∨ Fb + w ≤ OUTb)
    (w3 : ∀ v < w, c.nmem (Db + v) + c.nmem (Fb + v) + L ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 2978 2967 rnOutBody) c c' k ∧ k ≤ 12 * w + 2 ∧
      (∀ v < w, c'.nmem (OUTb + v) = c.nmem (Db + v) + c.nmem (Fb + v) + L - K) ∧
      (∀ a, a < OUTb ∨ OUTb + w ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2978 → r ≠ 2984 → r ≠ 2985 → r ≠ 2986 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (OUTb + v) = c.nmem (Db + v) + c.nmem (Fb + v) + L - K) ∧
      (∀ a, a < OUTb ∨ OUTb + i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2978 → r ≠ 2984 → r ≠ 2985 → r ≠ 2986 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2978) (bR := 2967)
    (body := rnOutBody) J (K := 10) (n := w) c hc r78 r67
    ⟨fun v hv => absurd hv (by omega), fun _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q : ∀ r, r ≠ 2978 → r ≠ 2984 → r ≠ 2985 → r ≠ 2986 → ∀ v, c.nreg r = v →
          c'.nreg r = v := fun r h1 h2 h3 h4 v h => (jn r h1 h2 h3 h4).trans h
      have eD : c'.nmem (Db + i) = c.nmem (Db + i) := j2 _ (by omega)
      have eF : c'.nmem (Fb + i) = c.nmem (Fb + i) := j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h78, hn, hr, hrm, ho⟩ := rnOutBody_exec (P := P) (K := K)
        (Db := Db) (Fb := Fb) (L := L) (OUTb := OUTb) c' hw
        (q _ (by omega) (by omega) (by omega) (by omega) _ r90)
        (q _ (by omega) (by omega) (by omega) (by omega) _ r71)
        (q _ (by omega) (by omega) (by omega) (by omega) _ r72)
        (q _ (by omega) (by omega) (by omega) (by omega) _ r73)
        (q _ (by omega) (by omega) (by omega) (by omega) _ r77) ha
        (q _ (by omega) (by omega) (by omega) (by omega) _ r79) (by omega) (by omega)
        (by rw [eD, eF]; exact w3 i hi) (by omega) (by omega)
      rw [eD, eF] at hm
      refine ⟨c'', k, ex, by omega, h78,
        (hn _ (by omega) (by omega) (by omega) (by omega)).trans hb, fun v hv => ?_,
        fun a h => ?_, fun r h1 h2 h3 h4 => (hn r h1 h2 h3 h4).trans (jn r h1 h2 h3 h4),
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 v hv
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₂, e₂, hk₂, j1, j2, jn, jr, jrm, jo⟩

/-! ### The first part: the maximum and the arc arrays -/


theorem rnFront_exec (c : Config) (hc : WordsBounded W c)
    {m w Tb Hb LLb Fb L Ab Fm Lm : ℕ}
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r68 : c.nreg 2968 = Tb)
    (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r74 : c.nreg 2974 = Ab)
    (hT : ∀ a < m, c.nmem (Tb + a) < w) (hH : ∀ a < m, c.nmem (Hb + a) < w)
    (hF : ∀ v < w, c.nmem (Fb + v) ≤ Fm) (hLL : ∀ a < m, c.nmem (LLb + a) ≤ Lm)
    (lT : Tb + m ≤ Ab) (lH : Hb + m ≤ Ab) (lL : LLb + m ≤ Ab) (lF : Fb + w ≤ Ab)
    (wE : Ab + 4 * (m + w) + 1 ≤ W) (wV : Fm + Lm + L ≤ W) :
    ∃ c' k, Exec P W rnFront c c' k ∧ k ≤ 7 * w + 25 * (m + w) + 16 ∧
      (∀ a < m + w,
        c'.nmem (Ab + a) = (rnArcs c.nmem m w Tb Hb LLb Fb L).tk a ∧
        c'.nmem (Ab + (m + w) + a) = 1 ∧
        c'.nmem (Ab + (m + w) + (m + w) + a) = (rnArcs c.nmem m w Tb Hb LLb Fb L).nh a ∧
        c'.nmem (Ab + (m + w) + (m + w) + (m + w) + a) =
          (rnArcs c.nmem m w Tb Hb LLb Fb L).ln a) ∧
      (∀ x, x < Ab ∨ Ab + 4 * (m + w) ≤ x → c'.nmem x = c.nmem x) ∧
      c'.nreg 2975 = m + w ∧ c'.nreg 2976 = w + 1 ∧ c'.nreg 2977 = rnK c.nmem Fb w ∧
      c'.nreg 2979 = 1 ∧ c'.nreg 2980 = Ab ∧
      c'.nreg 2981 = Ab + (m + w) ∧ c'.nreg 2982 = Ab + (m + w) + (m + w) ∧
      c'.nreg 2983 = Ab + (m + w) + (m + w) + (m + w) ∧
      (∀ r, r < 2975 ∨ 2989 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, s75, s76, s77, s78, s79, s80, s81, s82, s83, sn, sm, sr, srm, so⟩ :=
    rnSetup_exec (P := P) c hc r66 r67 r74 wE
  have hw₁ := e₁.wb_right
  have q₁ : ∀ r, r < 2975 → ∀ v, c.nreg r = v → c₁.nreg r = v :=
    fun r hr v h => (sn r (Or.inl hr)).trans h
  obtain ⟨c₂, k₂, e₂, hk₂, t77, tn, tm, tr, trm, tout⟩ := rnMax_exec (P := P) c₁ hw₁
    (q₁ _ (by omega) _ r67) (q₁ _ (by omega) _ r71) s77 s78 s79 (by omega)
  have hw₂ := e₂.wb_right
  have e₃ := Exec.constN (P := P) hw₂ 2978 0 (by omega)
  have hw₃ := e₃.wb_right
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 2978 0 } with hc₃
  have q₃ : ∀ r, r ≠ 2977 → r ≠ 2978 → r ≠ 2984 → c₃.nreg r = c₁.nreg r := fun r h1 h2 h3 => by
    simp only [hc₃, upd_apply, h2, ite_false]; exact tn r h1 h2 h3
  have m₃ : c₃.nmem = c.nmem := by simp only [hc₃]; rw [tm, sm]
  obtain ⟨c₄, k₄, e₄, hk₄, a₄, f₄, n₄, r₄, rm₄, o₄⟩ := rnArcLoop_exec (P := P)
    (Fm := Fm) (Lm := Lm) c₃ hw₃
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r66)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r67)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r68)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r69)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r70)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r71)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact q₁ _ (by omega) _ r72)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s75)
    (by simp only [hc₃, upd_apply]; rw [t77, m₃, sm]; simp)
    (by simp only [hc₃, upd_apply, ite_true])
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s79)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s80)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s81)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s82)
    (by rw [q₃ _ (by omega) (by omega) (by omega)]; exact s83)
    (by rw [m₃]; exact hT) (by rw [m₃]; exact hH) (by rw [m₃]; exact hF)
    (by rw [m₃]; exact hLL) lT lH lL lF wE wV
  rw [m₃] at a₄ f₄
  have q₄ : ∀ r, r ≠ 2978 → (r < 2984 ∨ 2989 < r) → c₄.nreg r = c₃.nreg r := n₄
  refine ⟨c₄, k₁ + (k₂ + (1 + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, a₄, f₄,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s75
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s76
  · rw [q₄ _ (by omega) (by omega)]; simp only [hc₃, upd_apply]; rw [t77, sm]; simp
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s79
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s80
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s81
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s82
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]; exact s83
  · rw [q₄ _ (by omega) (by omega), q₃ _ (by omega) (by omega) (by omega)]
    exact sn r (by omega)
  · rw [r₄]; simp only [hc₃]; rw [tr, sr]
  · rw [rm₄]; simp only [hc₃]; rw [trm, srm]
  · rw [o₄]; simp only [hc₃]; rw [tout, so]

end NegSSSP

end PlanarFlow
