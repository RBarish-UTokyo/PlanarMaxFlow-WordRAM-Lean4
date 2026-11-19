module

public import PlanarFlow.NegSSSP.NodeRunA
public import PlanarFlow.NegSSSP.DijGlue

/-!
# The run of one part of a node: the arithmetic, the arcs, FR-Dijkstra, the flags

A node in the plain encoding (`NegSSSP.NodeEnc`) is held in a configuration **above** the work
space of FR-Dijkstra: with `M₀ = m + w + 1`, the slot `k` is `Σ + k M₀`, and `Σ` lies above the
bound `loB m w = 4 m + 18 w + 175` of the word bound of every layout of FR-Dijkstra of the node
(`mkPrm_one`). The slots: `0` tails, `1` heads, `2` sides (natural), `3` lengths, `4`, `5` the
potentials `δ₀`, `δ₁` at the vertex numbers (real), `6` the vertex numbers of the boundary
(natural), `7` the values `E` of Bellman–Ford on the boundary (real), `8 … 15` scratch, `16 … 19`
the normalized flags and the distances of the two parts, `20` the output, `21` the lowering `C`.
The registers `803 + k` hold the slots, `800`, `801`, `802` the sizes `m`, `w`, `b`, `825` the
bound `loB m w` (`NCtx`).

`partProg` (one program for both parts; `r830` the side `s`, `r831` the base of `δₛ`, `r832`,
`r833` the bases of the flags and the distances it writes):

1. `clrProg`: the natural memory below `loB m w` cleared;
2. `pProg`: the initial lengths and the prices of the part (`C` read from the slot `21`);
3. `aProg`: the candidate arcs of the part;
4. `csProg`: the arcs sorted by tail, the offsets in the layout `mkPrm` of FR-Dijkstra;
5. `cpyProg`: the heads and the lengths copied into that layout (their number `m'` read from the
   last offset);
6. the registers `< 372` cleared, the input registers of `frProg` set, `D 0 0 = 0`;
7. `frProg` (`dijk_exec_emb`);
8. `nrmProg`: the flags normalized, the distances copied up.

* `part_exec`: the run of `partProg` within `cNegMach.dij (w + 1) (m + w) + 100 m + 200 w +
  20 b + 1300` steps; at the end the flags and the distances at `r832`, `r833` are the data of
  `minProg` (`NegSSSP.minIn_of_run`) for the call `dijk` of the part, with the boundary values
  lowered by `C`; the registers `800 … 899` and the memory above `Σ` outside the scratch slots
  and the two written rows are kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW

variable {P : Input} {W : ℕ}

/-! ### The layout of FR-Dijkstra with one corner -/

theorem mkPrm_one (N : ℕ) (Dm : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (r : ℕ) (Es : List (ℕ × ℕ × ℤ)) :
    (mkPrm N 1 Dm p r Es).W = 14 * N + 4 * (arcList N Es).length + 160 ∧
    (mkPrm N 1 Dm p r Es).lb = 2 * N + 2 + (arcList N Es).length ∧
    (mkPrm N 1 Dm p r Es).pb = 1 ∧ (mkPrm N 1 Dm p r Es).ob = N + 1 ∧
    (mkPrm N 1 Dm p r Es).sb = 2 * N + 2 + 2 * (arcList N Es).length ∧
    (mkPrm N 1 Dm p r Es).db = 3 * N + 2 + 2 * (arcList N Es).length ∧
    (mkPrm N 1 Dm p r Es).wb = 4 * N + 2 + 2 * (arcList N Es).length := by
  simp only [mkPrm, lvOf]
  norm_num
  omega

/-- The bound of the work space of FR-Dijkstra at a node of `m` darts and `w` vertex numbers. -/
def loB (m w : ℕ) : ℕ := 4 * m + 18 * w + 175

/-! ### The setup blocks -/

/-- Before `clrProg`: the bound. -/
def clrSet : Stmt := block [.copyN 900 825]

/-- Before `pProg`. -/
def pSet : Stmt := block [.copyN 947 824, .loadR 500 947, .copyN 500 802, .copyN 501 810,
  .copyN 502 809, .copyN 505 801, .copyN 506 831, .copyN 507 811, .constN 508 1]

/-- Before `aProg`. -/
def aSet : Stmt := block [.copyN 700 800, .copyN 701 801, .copyN 702 803, .copyN 703 804,
  .copyN 704 805, .copyN 705 806, .copyN 706 811, .copyN 707 812, .copyN 708 813, .copyN 709 814,
  .copyN 710 815, .copyN 711 830]

/-- Before `csProg`. -/
def csSet : Stmt := block [.constN 949 1, .addN 400 800 801, .addN 401 801 949, .copyN 402 812,
  .copyN 403 813, .copyN 404 814, .addN 405 401 949, .copyN 406 816, .copyN 407 818,
  .copyN 408 815, .copyN 409 817]

/-- Before `cpyProg`: `N = w + 1` (`r940`), `ob = w + 2` (`r941`), the number of arcs `m'`
(`r942`, the last offset), the base of the lengths `lb` (`r943`). -/
def cpSet : Stmt := block [.constN 949 1, .addN 940 801 949, .addN 941 940 949,
  .addN 947 941 940, .loadN 942 947, .addN 911 947 949, .addN 943 911 942, .copyN 910 942,
  .copyN 912 817, .copyN 913 943, .copyN 914 818]

/-- Before `frProg`: the input registers, `D 0 0 = 0`. -/
def inpBlk : Stmt := block [.addN 944 943 942, .addN 945 944 940, .addN 946 945 940,
  .copyN 100 940, .constN 101 1, .constN 102 0, .constN 103 1, .copyN 104 941, .copyN 105 943,
  .constN 106 0, .copyN 107 944, .copyN 108 945, .copyN 109 946, .constR 948 0, .constN 947 0,
  .storeR 947 948]

/-- Before `nrmProg`. -/
def nSet : Stmt := block [.constN 949 1, .copyN 600 801, .addN 601 944 949, .addN 602 945 949,
  .copyN 603 832, .copyN 604 833]

/-- **The run of one part.** -/
def partProg : Stmt :=
  .seq clrSet <| .seq clrProg <| .seq pSet <| .seq pProg <| .seq aSet <| .seq aProg <|
  .seq csSet <| .seq csProg <| .seq cpSet <| .seq cpyProg <| .seq (zeroRegs lowRegs) <|
  .seq inpBlk <| .seq frProg <| .seq nSet nrmProg

theorem clrSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W clrSet c c' k ∧ k = 1 ∧ c'.nreg 900 = c.nreg 825 ∧
      (∀ r, r ≠ 900 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clrSet
  exec_block
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

theorem pSet_exec (c : Config) (hc : WordsBounded W c) (h1 : 1 ≤ W) :
    ∃ c' k, Exec P W pSet c c' k ∧ k = 9 ∧ c'.nreg 500 = c.nreg 802 ∧
      c'.nreg 501 = c.nreg 810 ∧ c'.nreg 502 = c.nreg 809 ∧ c'.nreg 505 = c.nreg 801 ∧
      c'.nreg 506 = c.nreg 831 ∧ c'.nreg 507 = c.nreg 811 ∧ c'.nreg 508 = 1 ∧
      c'.rreg 500 = c.rmem (c.nreg 824) ∧
      (∀ r, (r < 500 ∨ 508 < r) → r ≠ 947 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pSet
  exec_block
  all_goals try omega
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

set_option maxHeartbeats 1600000 in
theorem aSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W aSet c c' k ∧ k = 12 ∧ c'.nreg 700 = c.nreg 800 ∧
      c'.nreg 701 = c.nreg 801 ∧ c'.nreg 702 = c.nreg 803 ∧ c'.nreg 703 = c.nreg 804 ∧
      c'.nreg 704 = c.nreg 805 ∧ c'.nreg 705 = c.nreg 806 ∧ c'.nreg 706 = c.nreg 811 ∧
      c'.nreg 707 = c.nreg 812 ∧ c'.nreg 708 = c.nreg 813 ∧ c'.nreg 709 = c.nreg 814 ∧
      c'.nreg 710 = c.nreg 815 ∧ c'.nreg 711 = c.nreg 830 ∧
      (∀ r, (r < 700 ∨ 711 < r) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold aSet
  exec_block
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

theorem csSet_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 800 + c.nreg 801 ≤ W)
    (h2 : c.nreg 801 + 2 ≤ W) :
    ∃ c' k, Exec P W csSet c c' k ∧ k = 11 ∧ c'.nreg 400 = c.nreg 800 + c.nreg 801 ∧
      c'.nreg 401 = c.nreg 801 + 1 ∧ c'.nreg 402 = c.nreg 812 ∧ c'.nreg 403 = c.nreg 813 ∧
      c'.nreg 404 = c.nreg 814 ∧ c'.nreg 405 = c.nreg 801 + 1 + 1 ∧
      c'.nreg 406 = c.nreg 816 ∧ c'.nreg 407 = c.nreg 818 ∧ c'.nreg 408 = c.nreg 815 ∧
      c'.nreg 409 = c.nreg 817 ∧
      (∀ r, (r < 400 ∨ 409 < r) → r ≠ 949 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold csSet
  exec_block
  all_goals try (config_simp; omega)
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

set_option maxHeartbeats 1600000 in
theorem cpSet_exec (c : Config) (hc : WordsBounded W c)
    (h1 : 2 * c.nreg 801 + 4 + c.nmem (2 * c.nreg 801 + 3) ≤ W) :
    ∃ c' k, Exec P W cpSet c c' k ∧ k = 11 ∧ c'.nreg 940 = c.nreg 801 + 1 ∧
      c'.nreg 941 = c.nreg 801 + 2 ∧ c'.nreg 942 = c.nmem (2 * c.nreg 801 + 3) ∧
      c'.nreg 943 = 2 * c.nreg 801 + 4 + c.nmem (2 * c.nreg 801 + 3) ∧
      c'.nreg 910 = c.nmem (2 * c.nreg 801 + 3) ∧ c'.nreg 911 = 2 * c.nreg 801 + 4 ∧
      c'.nreg 912 = c.nreg 817 ∧ c'.nreg 913 = 2 * c.nreg 801 + 4 + c.nmem (2 * c.nreg 801 + 3) ∧
      c'.nreg 914 = c.nreg 818 ∧
      (∀ r, r < 900 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e : c.nreg 801 + 1 + 1 + (c.nreg 801 + 1) = 2 * c.nreg 801 + 3 := by omega
  unfold cpSet
  exec_block
  all_goals try (config_simp; omega)
  · config_simp; rw [e]; omega
  config_simp
  rw [e]
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

set_option maxHeartbeats 1600000 in
theorem inpBlk_exec (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 943 + c.nreg 942 + c.nreg 940 + c.nreg 940 ≤ W) (h2 : 1 ≤ W) :
    ∃ c' k, Exec P W inpBlk c c' k ∧ k = 16 ∧ c'.nreg 944 = c.nreg 943 + c.nreg 942 ∧
      c'.nreg 945 = c.nreg 943 + c.nreg 942 + c.nreg 940 ∧
      c'.nreg 946 = c.nreg 943 + c.nreg 942 + c.nreg 940 + c.nreg 940 ∧
      c'.nreg 100 = c.nreg 940 ∧ c'.nreg 101 = 1 ∧ c'.nreg 102 = 0 ∧ c'.nreg 103 = 1 ∧
      c'.nreg 104 = c.nreg 941 ∧ c'.nreg 105 = c.nreg 943 ∧ c'.nreg 106 = 0 ∧
      c'.nreg 107 = c.nreg 943 + c.nreg 942 ∧
      c'.nreg 108 = c.nreg 943 + c.nreg 942 + c.nreg 940 ∧
      c'.nreg 109 = c.nreg 943 + c.nreg 942 + c.nreg 940 + c.nreg 940 ∧
      (∀ r, (r < 100 ∨ 109 < r) → r < 944 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem 0 = 0 ∧ (∀ a, a ≠ 0 → c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  unfold inpBlk
  exec_block
  all_goals try (config_simp; omega)
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp

theorem nSet_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 944 + 1 ≤ W)
    (h2 : c.nreg 945 + 1 ≤ W) :
    ∃ c' k, Exec P W nSet c c' k ∧ k = 6 ∧ c'.nreg 600 = c.nreg 801 ∧
      c'.nreg 601 = c.nreg 944 + 1 ∧ c'.nreg 602 = c.nreg 945 + 1 ∧
      c'.nreg 603 = c.nreg 832 ∧ c'.nreg 604 = c.nreg 833 ∧
      (∀ r, (r < 600 ∨ 604 < r) → r ≠ 949 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nSet
  exec_block
  all_goals try (config_simp; omega)
  config_simp
  and_intros
  all_goals first
    | (intro r h1 h2; simp (disch := omega) only [upd_other]; done)
    | (intro r h1; simp (disch := omega) only [upd_other]; done)
    | omega
    | simp



open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR BKMNW

/-! ### The context of a node in the registers -/

/-- The registers of the context: the sizes `m`, `w`, `b` (`r800 … r802`), the slots
`Z + k M₀` (`r803 + k`, `k < 22`), the bound `loB m w` (`r825`). -/
structure NCtx (m w b Z M₀ : ℕ) (c : Config) : Prop where
  r800 : c.nreg 800 = m
  r801 : c.nreg 801 = w
  r802 : c.nreg 802 = b
  slot : ∀ k < 22, c.nreg (803 + k) = Z + k * M₀
  r825 : c.nreg 825 = loB m w

theorem NCtx.of {m w b Z M₀ : ℕ} {c c' : Config} (h : NCtx m w b Z M₀ c)
    (hr : ∀ r, 800 ≤ r → r < 900 → c'.nreg r = c.nreg r) : NCtx m w b Z M₀ c' :=
  ⟨(hr 800 (by omega) (by omega)).trans h.r800, (hr 801 (by omega) (by omega)).trans h.r801,
    (hr 802 (by omega) (by omega)).trans h.r802,
    fun k hk => (hr (803 + k) (by omega) (by omega)).trans (h.slot k hk),
    (hr 825 (by omega) (by omega)).trans h.r825⟩

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

open Classical in
/-- The lengths of the candidate arcs of a part as integers: the darts, then the arcs from the
root (the initial length at a vertex number, the potential elsewhere). -/
noncomputable def lzF (N : CombMap D V F) (P₀ P₁ : Finset D) (m : ℕ) (e : ℕ → D) (ν : V → ℕ)
    (ι : ℕ → V) (ℓ : D → ℤ) (B : Finset V) (E δ : V → ℤ) (i : ℕ) : ℤ :=
  if i < m then ℓ (e i)
  else if ∃ x ∈ verts N (P₀ ∪ P₁), ν x = i - m then initLen B E δ (ι (i - m)) else δ (ι (i - m))

/-- **The initial lengths of `pProg` are the lengths `lzF` of the arcs from the root.** -/
theorem lzF_init {P₀ P₁ : Finset D} {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {β : ℕ → V} (hβ : IsEnum b β (bdry N P₀ P₁))
    (ℓ : D → ℤ) (E δ : V → ℤ) (Cz : ℤ) (Iv : ℕ → ℝ)
    (hb : ∀ i < b, Iv (ν (β i)) = (E (β i) : ℝ) - Cz)
    (ho : ∀ v < w, (∀ i < b, ν (β i) ≠ v) → Iv v = δ (ι v)) {v : ℕ} (hv : v < w) :
    Iv v = (lzF N P₀ P₁ m e ν ι ℓ (bdry N P₀ P₁) (fun y => E y - Cz) δ (m + v) : ℝ) := by
  unfold lzF
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]
  by_cases hB : ∃ i < b, ν (β i) = v
  · obtain ⟨i, hi, rfl⟩ := hB
    have hx : β i ∈ verts N (P₀ ∪ P₁) := bdry_sub_verts (hβ.mem i hi)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨β i, hx, rfl⟩), h.inv _ hx, hb i hi]
    unfold initLen
    rw [ite_eq_left_of_eq_true _ _ (eq_true (hβ.mem i hi))]
    push_cast; rfl
  · rw [ho v hv fun i hi e' => hB ⟨i, hi, e'⟩]
    by_cases hx : ∃ x ∈ verts N (P₀ ∪ P₁), ν x = v
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx)]
      obtain ⟨x, hx, rfl⟩ := hx
      rw [h.inv x hx]
      unfold initLen
      have : x ∉ bdry N P₀ P₁ := by
        intro hxB
        obtain ⟨i, hi, rfl⟩ := hβ.surj x hxB
        exact hB ⟨i, hi, rfl⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]

/-- **The arcs of the counting sort of a part are the arcs of the call of Dijkstra**: the
hypotheses `hEs`, `hEs'`, `hhd` of `dijk_exec_emb` for the list `csList` of the candidate arcs
written by `aProg` with the lengths `lzF`. -/
theorem arcs_part {P₀ P₁ : Finset D} {m w : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}
    (h : NodeEnc N P₀ P₁ m w e ν ι) {s : ℕ} (hs : s ≤ 1) (ℓ : D → ℤ) (B : Finset V)
    (E δ : V → ℤ) (Tq Hq K : ℕ → ℕ)
    (hT : ∀ i < m, Tq i = encT N e ν i + 1 ∧ Hq i = encH N e ν i + 1 ∧
      (K i ≠ 0 ↔ encS P₀ e i = s))
    (hV : ∀ v < w, Tq (m + v) = 0 ∧ Hq (m + v) = v + 1 ∧
      (K (m + v) ≠ 0 ↔ InSide (encT N e ν) (encH N e ν) (encS P₀ e) m s v)) :
    (∀ a ∈ csList Tq Hq K (lzF N P₀ P₁ m e ν ι ℓ B E δ) (m + w),
        ∃ a' ∈ dijArcs N (partOf P₀ P₁ s) ℓ (verts N (partOf P₀ P₁ s)) (initLen B E δ),
          (numV ν a'.1, numV ν a'.2.1, a'.2.2) = a) ∧
      (∀ a' ∈ dijArcs N (partOf P₀ P₁ s) ℓ (verts N (partOf P₀ P₁ s)) (initLen B E δ),
        (numV ν a'.1, numV ν a'.2.1, a'.2.2) ∈
          csList Tq Hq K (lzF N P₀ P₁ m e ν ι ℓ B E δ) (m + w)) ∧
      (∀ a ∈ csList Tq Hq K (lzF N P₀ P₁ m e ν ι ℓ B E δ) (m + w), a.2.1 < w + 1) := by
  classical
  have hends := enc_ends h
  let LzD : ℕ → ℤ := fun i => if i < m then ℓ (e i) else initLen B E δ (ι (i - m))
  have heq : csList Tq Hq K (lzF N P₀ P₁ m e ν ι ℓ B E δ) (m + w) =
      csList Tq Hq K LzD (m + w) := by
    refine csList_congr _ fun i hi hK => ?_
    simp only [lzF, LzD]
    by_cases him : i < m
    · simp [him]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false him), ite_eq_right_of_eq_false _ _ (eq_false him)]
      obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by omega⟩
      have hv : v < w := by omega
      obtain ⟨d, hd, -, hdv⟩ := (hV v hv).2.2.1 hK
      refine ite_eq_left_of_eq_true _ _ (eq_true ?_)
      rw [Nat.add_sub_cancel_left]
      rcases hdv with hdv | hdv
      · exact ⟨N.tail (e d), mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inl rfl⟩, hdv⟩
      · exact ⟨N.head (e d), mem_verts.2 ⟨e d, h.enum.mem d hd, Or.inr rfl⟩, hdv⟩
  rw [heq]
  obtain ⟨h1, h2⟩ := csList_dijArcs h hs ℓ B E δ Tq Hq K LzD
    (fun i hi => ⟨(hT i hi).1, (hT i hi).2.1, (hT i hi).2.2, by simp [LzD, hi]⟩)
    (fun v hv => ⟨(hV v hv).1, (hV v hv).2.1, (hV v hv).2.2, by simp [LzD]⟩)
  refine ⟨h1, h2, fun a ha => ?_⟩
  obtain ⟨i, hi, -, rfl⟩ := (mem_csList _).1 ha
  by_cases him : i < m
  · rw [(hT i him).2.1]; have := (hends i him).2.1; simp only; omega
  · obtain ⟨v, rfl⟩ : ∃ v, i = m + v := ⟨i - m, by omega⟩
    rw [(hV v (by omega)).2.1]; simp only; omega

end Node

end NegSSSP

end PlanarFlow

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine

/-! ### The layouts of the glue programs in the slots -/

/-- The numeric hypotheses of the slots. -/
structure SlotH (m w b Z M₀ W' : ℕ) : Prop where
  hM : M₀ = m + w + 1
  hZ : 4 * m + 18 * w + 175 ≤ Z
  hW : Z + 22 * M₀ ≤ W'
  hb : b ≤ w

theorem pLay_slot {m w b Z M₀ W' δb : ℕ} (H : SlotH m w b Z M₀ W') {n : ℕ → ℕ}
    (hδb : δb = Z + 4 * M₀ ∨ δb = Z + 5 * M₀) (hlt : ∀ i < b, n i < w)
    (hinj : ∀ i < b, ∀ j < b, n i = n j → i = j) :
    PLay b w (Z + 7 * M₀) (Z + 6 * M₀) δb (Z + 8 * M₀) 1 W' n := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨hlt, hinj, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

theorem aLay_slot {m w b Z M₀ W' s : ℕ} (H : SlotH m w b Z M₀ W') {T Hd S : ℕ → ℕ}
    (hends : ∀ d < m, T d < w ∧ Hd d < w ∧ S d ≤ 1) (hs : s ≤ 1) :
    ALay m w s (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) (Z + 3 * M₀) (Z + 8 * M₀)
      (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (Z + 12 * M₀) W' T Hd S := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨hends, hs, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem csLay_slot {m w b Z M₀ W' : ℕ} (H : SlotH m w b Z M₀ W') {T Hd K : ℕ → ℕ}
    (htl : ∀ i < m + w, K i ≠ 0 → T i < w + 1) :
    CsLay (m + w) (w + 1) (Z + 9 * M₀) (Z + 10 * M₀) (Z + 11 * M₀) (w + 2)
      (Z + 13 * M₀) (Z + 15 * M₀) (Z + 12 * M₀) (Z + 14 * M₀) W' T Hd K := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨htl, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem cpyLay_slot {m w b Z M₀ W' m' : ℕ} (H : SlotH m w b Z M₀ W') (hm' : m' ≤ m + w) :
    CpyLay m' (2 * w + 4) (Z + 14 * M₀) (2 * w + 4 + m') (Z + 15 * M₀) W' := by
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end NegSSSP

end PlanarFlow
