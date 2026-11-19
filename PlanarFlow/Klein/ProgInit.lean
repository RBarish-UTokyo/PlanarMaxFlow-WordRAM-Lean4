module

public import PlanarFlow.Klein.ProgWeight
public import PlanarFlow.Klein.InitList

/-!
# Klein's algorithm on the machine: the initialisation

**What is given.** The machine has no conversion from naturals to reals, and the shortest-path
tree from the first root is computed by Dijkstra's algorithm, whose machine interface does not
fit this program. So the program starts from a configuration in which:

* the input (besides `KInput`, `KBnd`, `KOut`) holds the initial spanning tree `T` and a cotree
  `C` of it, by orders of their vertices and faces (`KInit`): the nodes of the vertices (`IV`),
  the parent darts of the vertices other than the root by nondecreasing depth (`IT`), the nodes
  of the faces (`IF`), the parent darts of the faces other than the root by nondecreasing depth
  (`IC`), and the four lengths (`HD`);
* the real memory holds the weights `WT` of the first move (these are the reach bits from the
  first target), the weights `PH`, and the constants `tripL` (`TL`), the threshold
  `tripL - 2 #V tripW` (`TH`) and the value `H₀` at the nodes of the faces (`H0`) (`KConst`).

The caller (the maximum-flow algorithm) computes these in its own registers; their cost is the
separate term `dijkCost` of `tripCost`.

**The program** `inS`: from the empty forest, the operations `treeOpsL` storing `T` (the values of
the nodes of the vertices and of the edges, then the links), the parent darts `TP` of `T`, the
values `val d = wt d + psum (tail d) - psum (head d)` into the real array `VL` at `2 nD` (two
queries `regQueryS` per dart: the path sums are the labels of `T`, `lct_label`), then the
operations `cotOpsL` storing `C` with the values `VL` and `H₀`.

* `listLoop_orun`: **a loop over a list**, the body performing the operations of one element, is
  an `ORun` performing the operations of the list.
* `in_orun`: **the initialisation on the machine**: the operations of `init_storedL`, at most
  `6 (#V + #F)`, counted `6 (#V + #F) + 2 nD` operations and `92 (#V + #F) + 32 nD + 60` further
  steps; the forest stores the data at the start of the first move with the value `H₀` at the
  nodes of the faces, `TP` holds `T`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### The layout -/

/-- The offset of the array `IV` (the nodes of the vertices). -/
def iIV (nD n k : ℕ) : ℕ := 9 * nD + 3 * n + k
/-- The offset of the array `IT` (the parent darts of the spanning tree). -/
def iIT (nD n k : ℕ) : ℕ := iIV nD n k + n
/-- The offset of the array `IF` (the nodes of the faces). -/
def iIF (nD n k : ℕ) : ℕ := iIV nD n k + 2 * n
/-- The offset of the array `IC` (the parent darts of the cotree). -/
def iIC (nD n k : ℕ) : ℕ := iIV nD n k + 3 * n
/-- The offset of the four lengths `HD`. -/
def iHD (nD n k : ℕ) : ℕ := iIV nD n k + 4 * n

/-- The real array `VL` (the values of the darts). -/
def aVL (nD : ℕ) : ℕ := 2 * nD
/-- The real word holding the threshold `tripL - 2 #V tripW`. -/
def aTH (nD : ℕ) : ℕ := 3 * nD + 1
/-- The real word holding the value `H₀` at the nodes of the faces. -/
def aH0 (nD : ℕ) : ℕ := 3 * nD + 2

/-! ### A loop over a list -/

section
variable {P : Input} {W B n : ℕ}

lemma flatMap_take_succ {α β : Type*} (xs : List α) (f : α → List β) {i : ℕ}
    (hi : i < xs.length) : (xs.take (i + 1)).flatMap f = (xs.take i).flatMap f ++ f xs[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]; simp

/-- **A loop over a list** `xs` (the index in `r ra`, from `0` to `r rb = |xs|`): if the body
performs the operations `opsOf xs[i]` of the element `i` (counted `mb` operations and `hb`
further steps), keeping a property `Q`, the loop performs the operations `xs.flatMap opsOf`,
counted `mb |xs|` operations and `(hb + 2) |xs| + 2` further steps. -/
theorem listLoop_orun {α : Type*} {body : Stmt} {ra rb : ℕ} (xs : List α)
    (opsOf : α → List EOp) {F₀ : Forest} (hv : ValidOpsE n F₀ (xs.flatMap opsOf))
    (Q : ℕ → Config → Prop) {mb hb : ℕ}
    (hbody : ∀ i (hi : i < xs.length) (c : Config) (G : List VT), Q i c → WordsBounded W c →
      LCTE B n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 G c → c.nreg ra = i →
      c.nreg rb = xs.length →
      ValidOpsE n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) →
      ∃ c' G', ORun P W B n body c (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 G c'
        (opsOf xs[i]) G' mb hb ∧ Q (i + 1) c' ∧ c'.nreg ra = i + 1 ∧ c'.nreg rb = xs.length)
    {c : Config} (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₀ G c) (hQ : Q 0 c)
    (h0 : c.nreg ra = 0) (hlen : c.nreg rb = xs.length) :
    ∃ c' G', ORun P W B n (.whileLtN ra rb body) c F₀ G c' (xs.flatMap opsOf) G'
        (mb * xs.length) ((hb + 2) * xs.length + 2) ∧ Q xs.length c' := by
  have hvi : ∀ i (hi : i < xs.length),
      ValidOpsE n (runOpsE n F₀ ((xs.take i).flatMap opsOf)).1 (opsOf xs[i]) := by
    intro i hi
    have e : xs.flatMap opsOf = ((xs.take i).flatMap opsOf ++ opsOf xs[i]) ++
        (xs.drop (i + 1)).flatMap opsOf := by
      rw [← flatMap_take_succ xs opsOf hi, ← List.flatMap_append, List.take_append_drop]
    rw [e] at hv
    exact ((validOpsE_append_iff n _ _ _).1 ((validOpsE_append_iff n _ _ _).1 hv).1).2
  obtain ⟨i, os, c', G', hrun, ⟨hos, hile, hS', hc', hra, hrb, hQ'⟩, ht, -, -⟩ :=
    ORun.whileLtN (α := ℕ) (P := P) (W := W) (B := B) (n := n) (a := ra) (b := rb)
    (body := body) F₀
    (fun i hs G₁ c₁ => hs = (xs.take i).flatMap opsOf ∧ i ≤ xs.length ∧
      LCTE B n (runOpsE n F₀ hs).1 G₁ c₁ ∧ WordsBounded W c₁ ∧ c₁.nreg ra = i ∧
      c₁.nreg rb = xs.length ∧ Q i c₁) (fun i => mb * i) (fun i => (hb + 2) * (xs.length - i))
    (fun i hs G₁ c₁ h _ => ⟨h.2.2.1, h.2.2.2.1⟩)
    (fun i hs G₁ c₁ h _ ht => by
      obtain ⟨rfl, hile, hS₁, hc₁, hra, hrb, hQ₁⟩ := h
      have hi : i < xs.length := by rw [hra, hrb] at ht; exact ht
      obtain ⟨c₂, G₂, o, hQ₂, hra₂, hrb₂⟩ := hbody i hi c₁ G₁ hQ₁ hc₁ hS₁ hra hrb (hvi i hi)
      refine ⟨i + 1, c₂, opsOf xs[i], G₂, mb, hb, o, ⟨(flatMap_take_succ xs opsOf hi).symm,
        hi, ?_, o.2.wb, hra₂, hrb₂, hQ₂⟩, by ring, ?_⟩
      · rw [runOpsE_fst_append]
        exact o.2.lcte
      · have : xs.length - i = xs.length - (i + 1) + 1 := by omega
        rw [this]; ring_nf; omega)
    (x := 0) (hs := []) ⟨by simp, Nat.zero_le _, hS, hc, h0, hlen, hQ⟩ trivial
  have hik : i = xs.length := by rw [hra, hrb] at ht; omega
  subst hik
  rw [List.take_length] at hos
  simp only [List.nil_append] at hos
  subst hos
  refine ⟨c', G', hrun.mono (by omega) (by simp), hQ'⟩

end

/-! ### The bodies of the loops -/

/-- The frame of the bodies: the registers below `r120` and `r121`, the output and the memory
outside the structure are kept. -/
def IFr (B n : ℕ) (c c' : Config) : Prop :=
  (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c.nreg r) ∧ (∀ r, r < 120 → c'.rreg r = c.rreg r) ∧
    c'.output = c.output ∧
    ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a

lemma IFr.refl (B n : ℕ) (c : Config) : IFr B n c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

lemma IFr.trans {B n : ℕ} {c c' c'' : Config} (h : IFr B n c c') (h' : IFr B n c' c'') :
    IFr B n c c'' :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), fun r hr => (h'.2.1 r hr).trans (h.2.1 r hr),
    h'.2.2.1.trans h.2.2.1, fun a ha => ⟨(h'.2.2.2 a ha).1.trans (h.2.2.2 a ha).1,
      (h'.2.2.2 a ha).2.trans (h.2.2.2 a ha).2⟩⟩

/-- The increment of the index `r120`. -/
def incI : List Instr := [.constN 127 1, .addN 120 120 127]

/-- **The values of the nodes of a list** (`IV`, `IF`): `add` and `add2` of the real `r rz` at
the node `off[r120]`. -/
def bodyNV (B off rz : ℕ) : Stmt :=
  .seq (block [.constN 122 off, .addN 122 122 120, .readIn 122 122]) <|
  .seq (ropsS B [.add 122 rz, .add2 122 rz]) (block incI)

/-- **The values of the nodes of the edges of a list of darts** (`IT`, `IC`): the dart `d`
from `off[r120]`, its node from `oN`, the reals `A[d]`, `A[rev d]` from the real array at `aA`,
then `ops`. -/
def bodyDV (B nD off oN aA : ℕ) (ops : List ROp) : Stmt :=
  .seq (block [.constN 122 off, .addN 122 122 120, .readIn 122 122,
    .constN 123 oN, .addN 123 123 122, .readIn 123 123,
    .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124,
    .constN 125 aA, .addN 125 125 122, .loadR 132 125,
    .constN 125 aA, .addN 125 125 124, .loadR 133 125]) <|
  .seq (ropsS B ops) (block incI)

/-- **The links of the edges of a list of darts** (`IT`, `IC`): the dart `d` from `off[r120]`,
the node of its edge from `oN`, the nodes of the two ends from `oF` at `d` and at `rev d`. -/
def bodyLK (B nD off oN oF : ℕ) : Stmt :=
  .seq (block [.constN 122 off, .addN 122 122 120, .readIn 122 122,
    .constN 123 oN, .addN 123 123 122, .readIn 123 123,
    .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124,
    .constN 125 oF, .addN 125 125 122, .readIn 125 125,
    .constN 126 oF, .addN 126 126 124, .readIn 126 126]) <|
  .seq (ropsS B [.link 123 125, .link 126 123]) (block incI)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD}

section
variable {P : Input} {W B n : ℕ}

lemma incI_exec {c : Config} (hc : WordsBounded W c) {i : ℕ} (h120 : c.nreg 120 = i)
    (hi : i + 1 ≤ W) :
    ∃ c' k', Exec P W (block incI) c c' k' ∧ k' = 2 ∧ c'.nreg 120 = i + 1 ∧
      GFr 120 128 c c' ∧ (∀ r, r ≠ 120 → r ≠ 127 → c'.nreg r = c.nreg r) := by
  unfold incI
  exec_block
  · omega
  · config_simp; rw [h120]; omega
  · refine ⟨rfl, by config_simp; rw [h120], ⟨fun r hr => ⟨?_, rfl⟩, rfl, rfl, rfl⟩,
      fun r h1 h2 => ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    · config_simp; rw [upd_other _ _ _ h1, upd_other _ _ _ h2]

/-- **The values of the nodes of a list**: the body `bodyNV` performs `add`, `add2` of `z` at
the node of the element `i`. -/
theorem bodyNV_orun (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W) {α : Type*}
    {off rz : ℕ} {xs : List α} {ιN : α → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = ιN xs[i])
    (hoff : off + xs.length ≤ W) {z : ℤ} {i : ℕ} (hi : i < xs.length) {c : Config}
    (hc : WordsBounded W c) {F : Forest} {G : List VT} (hS : LCTE B n F G c)
    (h120 : c.nreg 120 = i) (hz : c.rreg rz = z) (hrz : rz < 120)
    (hv : ValidOpsE n F [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z]) :
    ∃ c' G', ORun P W B n (bodyNV B off rz) c F G c' [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z]
        G' 2 5 ∧ c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, p122, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122]) c c' k' ∧ k' = 3 ∧ c'.nreg 122 = ιN xs[i] ∧
      GFr 122 123 c c' := by
    exec_block
    · omega
    · config_simp; rw [h120]; omega
    · exact hP _
    · refine ⟨rfl, by config_simp; rw [h120, hxs i hi], by gfr_tac⟩
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  have hz₁ : c₁.rreg rz = z := by rw [(g₁.1 rz (by omega)).2, hz]
  have hops : [ROp.add 122 rz, ROp.add2 122 rz].map (ROp.eop c₁ fun _ => z) =
      [.add (ιN xs[i]) z, .add2 (ιN xs[i]) z] := by
    simp [ROp.eop, p122]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orun (P := P) hW (fun _ => z)
    [ROp.add 122 rz, ROp.add2 122 rz] e₁.wb_right o₁.2.lcte (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by norm_num, by omega, hz₁⟩) (by rw [hops]; exact hv)
  rw [hops] at o₂
  have hc₂ := o₂.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  refine ⟨c₃, G₂, o.mono (by simp) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)

/-- The operations of `bodyDV`: on the first values `A[d]` (`sw = false`) or `A[rev d]`. -/
def opsDV (sw : Bool) : List ROp :=
  if sw then [.add 123 133, .add2 123 132] else [.add 123 132, .add2 123 133]

/-- The operations performed by `bodyDV`. -/
def eopsDV (sw : Bool) (u : ℕ) (a a' : ℤ) : List EOp :=
  if sw then [.add u a', .add2 u a] else [.add u a, .add2 u a']

/-- **The values of the nodes of the edges of a list of darts**: the body `bodyDV` performs
`eopsDV` at the node of the edge of the dart of the element `i`, with the values `A d`,
`A (rev d)` read from the real memory. -/
theorem bodyDV_orun (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hK : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)) {Y : Type*}
    {off oN aA : ℕ} {xs : List Y} {pd : Y → D} {ιE : D → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = σ (pd xs[i]))
    (hoff : off + xs.length ≤ W) (hN : ∀ d, P.data.getD (oN + σ d) 0 = ιE d)
    (hoN : oN + nD ≤ W) (haA : aA + nD ≤ W) {A : D → ℤ} (sw : Bool)
    {i : ℕ} (hi : i < xs.length) {c : Config} (hc : WordsBounded W c) {F : Forest}
    {G : List VT} (hS : LCTE B n F G c) (h120 : c.nreg 120 = i)
    (hA : ∀ d, c.rmem (aA + σ d) = A d)
    (hv : ValidOpsE n F (eopsDV sw (ιE (pd xs[i])) (A (pd xs[i])) (A (M.rev (pd xs[i]))))) :
    ∃ c' G', ORun P W B n (bodyDV B nD off oN aA (opsDV sw)) c F G c'
        (eopsDV sw (ιE (pd xs[i])) (A (pd xs[i])) (A (M.rev (pd xs[i])))) G' 2 17 ∧
      c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  set d := pd xs[i] with hd
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσd := hσ d
  have hσr := hσ (M.rev d)
  obtain ⟨c₁, k₁, e₁, hk₁, p123, p132, p133, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122, .constN 123 oN, .addN 123 123 122, .readIn 123 123,
      .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124, .constN 125 aA,
      .addN 125 125 122, .loadR 132 125, .constN 125 aA, .addN 125 125 124,
      .loadR 133 125]) c c' k' ∧ k' = 15 ∧ c'.nreg 123 = ιE d ∧ c'.rreg 132 = A d ∧
      c'.rreg 133 = A (M.rev d) ∧ GFr 122 134 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; rw [h120]; omega)
      | (config_simp; rw [h120, hxs i hi]; omega)
      | (config_simp; rw [h120, hxs i hi, hK]; omega)
      | (simp only [iRV]; omega)
      | (config_simp; rw [h120, hxs i hi]; simp only [iRV]; omega))
    refine ⟨rfl, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, hxs i hi, hN]
    · config_simp; rw [h120, hxs i hi, hA]
    · config_simp; rw [h120, hxs i hi, hK, hA]
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  set zr : ℕ → ℤ := fun r => if r = 132 then A d else A (M.rev d) with hzr
  have w132 : c₁.rreg 132 = zr 132 := by rw [p132]; simp [hzr]
  have w133 : c₁.rreg 133 = zr 133 := by rw [p133]; simp [hzr]
  have hops : (opsDV sw).map (ROp.eop c₁ zr) = eopsDV sw (ιE d) (A d) (A (M.rev d)) := by
    cases sw <;> simp [opsDV, eopsDV, ROp.eop, p123, hzr]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orun (P := P) hW zr (opsDV sw) e₁.wb_right o₁.2.lcte
    (fun o ho => by
      cases sw <;> simp only [opsDV, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at ho <;>
        rcases ho with rfl | rfl
      · exact ⟨by norm_num, by norm_num, w132⟩
      · exact ⟨by norm_num, by norm_num, w133⟩
      · exact ⟨by norm_num, by norm_num, w133⟩
      · exact ⟨by norm_num, by norm_num, w132⟩) (by rw [hops]; exact hv)
  rw [hops] at o₂
  have hc₂ := o₂.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  have hl : (opsDV sw).length = 2 := by cases sw <;> rfl
  refine ⟨c₃, G₂, o.mono (by omega) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)

/-- **The links of the edges of a list of darts**: the body `bodyLK` links the node of the edge
of the dart `d` of the element `i` below the node `F1 d` of one end, then the node `F1 (rev d)`
of the other end below it. -/
theorem bodyLK_orun (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hK : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)) {Y : Type*}
    {off oN oF : ℕ} {xs : List Y} {pd : Y → D} {ιE F1 : D → ℕ}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (off + i) 0 = σ (pd xs[i]))
    (hoff : off + xs.length ≤ W) (hN : ∀ d, P.data.getD (oN + σ d) 0 = ιE d)
    (hoN : oN + nD ≤ W) (hF : ∀ d, P.data.getD (oF + σ d) 0 = F1 d) (hoF : oF + nD ≤ W)
    {i : ℕ} (hi : i < xs.length) {c : Config} (hc : WordsBounded W c) {F : Forest}
    {G : List VT} (hS : LCTE B n F G c) (h120 : c.nreg 120 = i)
    (hv : ValidOpsE n F [.link (ιE (pd xs[i])) (F1 (pd xs[i])),
      .link (F1 (M.rev (pd xs[i]))) (ιE (pd xs[i]))]) :
    ∃ c' G', ORun P W B n (bodyLK B nD off oN oF) c F G c'
        [.link (ιE (pd xs[i])) (F1 (pd xs[i])), .link (F1 (M.rev (pd xs[i]))) (ιE (pd xs[i]))]
        G' 2 17 ∧ c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  set d := pd xs[i] with hd
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσd := hσ d
  have hσr := hσ (M.rev d)
  obtain ⟨c₁, k₁, e₁, hk₁, p123, p125, p126, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 off,
      .addN 122 122 120, .readIn 122 122, .constN 123 oN, .addN 123 123 122, .readIn 123 123,
      .constN 124 (iRV nD), .addN 124 124 122, .readIn 124 124, .constN 125 oF,
      .addN 125 125 122, .readIn 125 125, .constN 126 oF, .addN 126 126 124,
      .readIn 126 126]) c c' k' ∧ k' = 15 ∧ c'.nreg 123 = ιE d ∧ c'.nreg 125 = F1 d ∧
      c'.nreg 126 = F1 (M.rev d) ∧ GFr 122 127 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (config_simp; rw [h120]; omega)
      | (config_simp; rw [h120, hxs i hi]; omega)
      | (config_simp; rw [h120, hxs i hi, hK]; omega)
      | (simp only [iRV]; omega)
      | (config_simp; rw [h120, hxs i hi]; simp only [iRV]; omega))
    refine ⟨rfl, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, hxs i hi, hN]
    · config_simp; rw [h120, hxs i hi, hF]
    · config_simp; rw [h120, hxs i hi, hK, hF]
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  have hops : [ROp.link 123 125, ROp.link 126 123].map (ROp.eop c₁ fun _ => 0) =
      [.link (ιE d) (F1 d), .link (F1 (M.rev d)) (ιE d)] := by
    simp [ROp.eop, p123, p125, p126]
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orun (P := P) hW (fun _ => 0)
    [ROp.link 123 125, ROp.link 126 123] e₁.wb_right o₁.2.lcte (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩) (by rw [hops]; exact hv)
  rw [hops] at o₂
  have hc₂ := o₂.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  refine ⟨c₃, G₂, o.mono (by simp) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)

/-- **The parent darts of the spanning tree** into `TP`: for the dart `d = IT[r120]`,
`TP[NH[d]] := d`. -/
def bodyTP (nD n k : ℕ) : List Instr :=
  [.constN 122 (iIT nD n k), .addN 122 122 120, .readIn 122 122,
    .constN 123 (iNH nD), .addN 123 123 122, .readIn 123 123,
    .constN 124 aTP, .addN 124 124 123, .storeN 124 122] ++ incI

/-- **The values of the darts** into `VL`: for the dart number `i = r120`,
`VL[i] := WT[i] + psum (NT[i]) - psum (NH[i])` (two queries). -/
def bodyVL (B nD : ℕ) : Stmt :=
  .seq (block [.constN 122 (iNT nD), .addN 122 122 120, .readIn 122 122,
    .constN 123 (iNH nD), .addN 123 123 120, .readIn 123 123]) <|
  .seq (regQueryS B 122) <| .seq (.instr (.copyR 134 196)) <|
  .seq (regQueryS B 123) <| .seq (.instr (.copyR 135 196)) <|
  block ([.constN 124 aWT, .addN 124 124 120, .loadR 136 124, .addR 136 136 134,
    .subR 136 136 135, .constN 125 (aVL nD), .addN 125 125 120, .storeR 125 136] ++ incI)

theorem bodyTP_exec (hP : ∀ i, P.data.getD i 0 ≤ W) {k : ℕ} {ιv : V → ℕ}
    (hlt : ∀ x, ιv x < n) (hNH : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d))
    (hWa : iNH nD + nD ≤ W) {xs : List V} {pd : V → D}
    (hxs : ∀ i (h : i < xs.length), P.data.getD (iIT nD n k + i) 0 = σ (pd xs[i]))
    (hoff : iIT nD n k + xs.length ≤ W) {i : ℕ} (hi : i < xs.length) {c : Config}
    (hc : WordsBounded W c) (h120 : c.nreg 120 = i) (hnW : n ≤ W) :
    ∃ c' k', Exec P W (block (bodyTP nD n k)) c c' k' ∧ k' = 11 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, (r < 120 ∨ r = 121 ∨ r = 151) → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = upd c.nmem (aTP + ιv (M.head (pd xs[i]))) (σ (pd xs[i])) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hσd := (σ (pd xs[i])).2
  have hln := hlt (M.head (pd xs[i]))
  unfold bodyTP incI
  exec_block
  all_goals try (first
    | exact hP _
    | omega
    | (config_simp; rw [h120]; omega)
    | (config_simp; rw [h120, hxs i hi]; omega)
    | (unfold aTP; omega)
    | (config_simp; rw [h120, hxs i hi, hNH]; unfold aTP; omega))
  refine ⟨rfl, by config_simp; rw [h120], fun r hr => ?_, rfl, ?_, rfl, rfl⟩
  · config_simp
    simp only [upd_other _ _ _ (show r ≠ 120 by omega), upd_other _ _ _ (show r ≠ 127 by omega),
      upd_other _ _ _ (show r ≠ 124 by omega), upd_other _ _ _ (show r ≠ 123 by omega),
      upd_other _ _ _ (show r ≠ 122 by omega)]
  · config_simp; rw [h120, hxs i hi, hNH]

/-- **The value of one dart** into `VL`: two queries of path sums. -/
theorem bodyVL_orun (hW : B + 16 * (n + 1) ≤ W) (hP : ∀ i, P.data.getD i 0 ≤ W) {ιv : V → ℕ}
    (hlt : ∀ x, ιv x < n) (hNT : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d))
    (hNH : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)) (hWa : 6 * nD ≤ W)
    (hB : 3 * nD ≤ B) {d : D} {i : ℕ} (hd : (σ d : ℕ) = i) {c : Config}
    (hc : WordsBounded W c) {F : Forest} {G : List VT} (hS : LCTE B n F G c)
    (h120 : c.nreg 120 = i) :
    ∃ c' G', ORun P W B n (bodyVL B nD) c F G c' [] G' 2 18 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aVL nD + i → c'.rmem a = c.rmem a) ∧
      c'.rmem (aVL nD + i) = c.rmem (aWT + i) + pathSum F n (ιv (M.tail d)) -
        pathSum F n (ιv (M.head d)) := by
  have hσd := (σ d).2
  obtain ⟨c₁, k₁, e₁, hk₁, p122, p123, g₁⟩ : ∃ c' k', Exec P W (block [.constN 122 (iNT nD),
      .addN 122 122 120, .readIn 122 122, .constN 123 (iNH nD), .addN 123 123 120,
      .readIn 123 123]) c c' k' ∧ k' = 6 ∧ c'.nreg 122 = ιv (M.tail d) ∧
      c'.nreg 123 = ιv (M.head d) ∧ GFr 122 124 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iNT, iNH]; omega)
      | (config_simp; rw [h120]; simp only [iNT, iNH]; omega))
    refine ⟨rfl, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, ← hd, hNT]
    · config_simp; rw [h120, ← hd, hNH]
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, G₂, o₂, -, -, -, s₂, -, m₂, f₂⟩ := regQuery_orun (P := P) hW e₁.wb_right
    o₁.2.lcte p122 (hlt _)
  have e₃ := Exec.copyR (P := P) o₂.2.wb 134 196
  have g₃ : GFr 134 135 c₂ { c₂ with rreg := upd c₂.rreg 134 (c₂.rreg 196) } := by gfr_tac
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  obtain ⟨c₄, G₄, o₄, -, -, -, s₄, -, m₄, f₄⟩ := regQuery_orun (P := P) hW e₃.wb_right
    o₃.2.lcte (v := ιv (M.head d))
    (by rw [(g₃.1 123 (by omega)).1, f₂.1 123 (by omega), p123]) (hlt _)
  have e₅ := Exec.copyR (P := P) o₄.2.wb 135 196
  have g₅ : GFr 135 136 c₄ { c₄ with rreg := upd c₄.rreg 135 (c₄.rreg 196) } := by gfr_tac
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  set c₅ := { c₄ with rreg := upd c₄.rreg 135 (c₄.rreg 196) } with hc₅
  have hc₅w : WordsBounded W c₅ := e₅.wb_right
  have q120 : c₅.nreg 120 = i := by
    rw [(g₅.1 120 (by omega)).1, f₄.1 120 (by omega), (g₃.1 120 (by omega)).1,
      f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]
  have q134 : c₅.rreg 134 = pathSum F n (ιv (M.tail d)) := by
    rw [(g₅.1 134 (by omega)).2, f₄.2.1 134 (by omega)]; config_simp; exact s₂
  have q135 : c₅.rreg 135 = pathSum F n (ιv (M.head d)) := by
    rw [hc₅]; config_simp; exact s₄
  have hmem : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₅.nmem a = c.nmem a ∧
      c₅.rmem a = c.rmem a := fun a ha => by
    have h2 := m₂ a ha
    have h4 := m₄ a ha
    simp only [DynTree.mem] at h2 h4
    rw [hc₅]
    simp only
    rw [h4.1, h4.2, g₃.2.1, g₃.2.2.1, h2.1, h2.2, g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩
  have hw : c₅.rmem (aWT + i) = c.rmem (aWT + i) :=
    (hmem _ (Or.inl (by unfold aWT; omega))).2
  obtain ⟨c₆, k₆, e₆, hk₆, t120, tn, tr, tm, tnm, tout⟩ : ∃ c' k', Exec P W
      (block ([.constN 124 aWT, .addN 124 124 120, .loadR 136 124, .addR 136 136 134,
        .subR 136 136 135, .constN 125 (aVL nD), .addN 125 125 120, .storeR 125 136] ++ incI))
      c₅ c' k' ∧ k' = 10 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, r ≠ 120 → r ≠ 124 → r ≠ 125 → r ≠ 127 → c'.nreg r = c₅.nreg r) ∧
      (∀ r, r ≠ 136 → c'.rreg r = c₅.rreg r) ∧
      c'.rmem = upd c₅.rmem (aVL nD + i) (c.rmem (aWT + i) + pathSum F n (ιv (M.tail d)) -
        pathSum F n (ιv (M.head d))) ∧ c'.nmem = c₅.nmem ∧ c'.output = c₅.output := by
    unfold incI
    exec_block
    all_goals try (first
      | omega
      | (unfold aWT; omega)
      | (unfold aVL; omega)
      | (config_simp; rw [q120]; unfold aWT; omega)
      | (config_simp; rw [q120]; unfold aVL; omega)
      | (config_simp; rw [q120]; omega))
    refine ⟨rfl, by config_simp; rw [q120], fun r h1 h2 h3 h4 => ?_, fun r h1 => ?_, ?_, rfl,
      rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
        upd_other _ _ _ h4]
    · config_simp; simp only [upd_other _ _ _ h1]
    · config_simp; rw [q120, q134, q135, hw]
  have o₆ : ORun P W B n _ c₅ F G₄ c₆ [] G₄ 0 k₆ := ORun.glue e₆ o₅.2.lcte
    (fun a ha _ => ⟨by rw [tnm], by rw [tm, upd_other _ _ _ (by unfold aVL; omega)]⟩)
    (tn 151 (by omega) (by omega) (by omega) (by omega))
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hreg : ∀ r, r < 120 → c₅.nreg r = c.nreg r ∧ c₅.rreg r = c.rreg r := fun r hr => by
    rw [(g₅.1 r (by omega)).1, (g₅.1 r (by omega)).2, f₄.1 r (by omega), f₄.2.1 r (by omega),
      (g₃.1 r (by omega)).1, (g₃.1 r (by omega)).2, f₂.1 r (by omega), f₂.2.1 r (by omega),
      (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]; exact ⟨rfl, rfl⟩
  refine ⟨c₆, G₄, o.mono (by omega) (by omega), t120, fun r hr => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha hne => ?_, ?_⟩
  · rw [tn r (by omega) (by omega) (by omega) (by omega)]
    rcases hr with hr | rfl
    · exact (hreg r hr).1
    · rw [(g₅.1 121 (by omega)).1, f₄.1 121 (by omega), (g₃.1 121 (by omega)).1,
        f₂.1 121 (by omega), (g₁.1 121 (by omega)).1]
  · rw [tr r (by omega)]; exact (hreg r hr).2
  · rw [tout, hc₅]; simp only; rw [f₄.2.2, g₃.2.2.2, f₂.2.2, g₁.2.2.2]
  · rw [tnm]; exact (hmem a ha).1
  · rw [tm, upd_other _ _ _ hne]; exact (hmem a ha).2
  · rw [tm, upd_same]

end

/-! ### The input of the initialisation and the program -/

variable (M σ) in
/-- **The initial trees in the input**: the orders `vs`, `ts` of the spanning tree `T` and `fs`,
`cs` of the cotree `C` (`Orders`), in the arrays `IV`, `IT`, `IF`, `IC`, and their lengths in
`HD`. -/
structure KInit (ιv : V → ℕ) (ιf : F → ℕ) (n k : ℕ) (T : DTree M.dual) (C : DTree M)
    (vs ts : List V) (fs cs : List F) (P : Input) : Prop where
  oT : Orders T vs ts
  oC : Orders C fs cs
  iv : ∀ i (h : i < vs.length), P.data.getD (iIV nD n k + i) 0 = ιv vs[i]
  it : ∀ i (h : i < ts.length), P.data.getD (iIT nD n k + i) 0 = σ (T.par ts[i])
  if_ : ∀ i (h : i < fs.length), P.data.getD (iIF nD n k + i) 0 = ιf fs[i]
  ic : ∀ i (h : i < cs.length), P.data.getD (iIC nD n k + i) 0 = σ (C.par cs[i])
  l0 : P.data.getD (iHD nD n k) 0 = vs.length
  l1 : P.data.getD (iHD nD n k + 1) 0 = ts.length
  l2 : P.data.getD (iHD nD n k + 2) 0 = fs.length
  l3 : P.data.getD (iHD nD n k + 3) 0 = cs.length

/-- The bounds of a loop over the list of length `HD[off]`. -/
def ldI (off : ℕ) : List Instr := [.constN 120 0, .constN 121 off, .readIn 121 121]

/-- **The spanning tree**: the values of the nodes of the vertices and of the edges, the links. -/
def inTS (B nD n k : ℕ) : Stmt :=
  .seq (block (.constR 110 0 :: ldI (iHD nD n k))) <|
  .seq (.whileLtN 120 121 (bodyNV B (iIV nD n k) 110)) <|
  .seq (block (ldI (iHD nD n k + 1))) <|
  .seq (.whileLtN 120 121 (bodyDV B nD (iIT nD n k) (iNG nD) (aPH nD) (opsDV false))) <|
  .seq (block (ldI (iHD nD n k + 1))) <|
  .whileLtN 120 121 (bodyLK B nD (iIT nD n k) (iNG nD) (iNT nD))

/-- **The parent darts** `TP` of the spanning tree. -/
def inPS (nD n k : ℕ) : Stmt :=
  .seq (block (ldI (iHD nD n k + 1))) (.whileLtN 120 121 (block (bodyTP nD n k)))

/-- **The values of the darts** `VL`. -/
def inVS (B nD : ℕ) : Stmt :=
  .seq (block [.constN 120 0, .constN 121 nD]) (.whileLtN 120 121 (bodyVL B nD))

/-- **The cotree**: the values of the nodes of the faces (`H₀`) and of the edges (`VL`), the
links. -/
def inCS (B nD n k : ℕ) : Stmt :=
  .seq (block ([.constN 122 (aH0 nD), .loadR 111 122] ++ ldI (iHD nD n k + 2))) <|
  .seq (.whileLtN 120 121 (bodyNV B (iIF nD n k) 111)) <|
  .seq (block (ldI (iHD nD n k + 3))) <|
  .seq (.whileLtN 120 121 (bodyDV B nD (iIC nD n k) (iNE nD) (aVL nD) (opsDV true))) <|
  .seq (block (ldI (iHD nD n k + 3))) <|
  .whileLtN 120 121 (bodyLK B nD (iIC nD n k) (iNE nD) (iNF nD))

/-- **The initialisation.** -/
def inS (B nD n k : ℕ) : Stmt := .seq (inTS B nD n k) (.seq (inPS nD n k) (.seq (inVS B nD)
  (inCS B nD n k)))

lemma treeOpsL_eq {ιv : V → ℕ} {ιg : D → ℕ} (T : DTree M.dual) (φ : D → ℤ) {vs ts : List V}
    (hO : Orders T vs ts) : treeOpsL T ιv ιg φ vs ts =
      (vs.flatMap fun y => [.add (ιv y) 0, .add2 (ιv y) 0]) ++
      (ts.flatMap fun y => eopsDV false (ιg (T.par y)) (φ (T.par y)) (φ (M.rev (T.par y)))) ++
      (ts.flatMap fun y => [.link (ιg (T.par y)) (ιv (M.tail (T.par y))),
        .link (ιv (M.tail (M.rev (T.par y)))) (ιg (T.par y))]) := by
  unfold treeOpsL buildOpsL setOps treeValsL linkOps
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1
    exact List.flatMap_congr fun y _ => by
      simp only [eopsDV, Bool.false_eq_true, ↓reduceIte]
      change [EOp.add _ (φ (M.rev (M.rev _))), _] = _
      rw [M.rev_rev]
  · exact List.flatMap_congr fun y hy => by
      have h := T.head_par y ((hO.ymem y).1 hy)
      change [EOp.link _ (ιv (M.tail _)), EOp.link (ιv y) _] =
        [_, EOp.link (ιv (M.dual.face (M.dual.rev (T.par y)))) _]
      rw [h]

lemma cotOpsL_eq {ιf : F → ℕ} {ιe : D → ℕ} (C : DTree M) (val : D → ℤ) (H₀ : ℤ)
    {fs cs : List F} (hO : Orders C fs cs) : cotOpsL C ιf ιe val H₀ fs cs =
      (fs.flatMap fun y => [.add (ιf y) H₀, .add2 (ιf y) H₀]) ++
      (cs.flatMap fun y => eopsDV true (ιe (C.par y)) (val (C.par y)) (val (M.rev (C.par y)))) ++
      (cs.flatMap fun y => [.link (ιe (C.par y)) (ιf (M.face (C.par y))),
        .link (ιf (M.face (M.rev (C.par y)))) (ιe (C.par y))]) := by
  unfold cotOpsL buildOpsL setOps treeValsL linkOps
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  congr 1
  · exact List.flatMap_congr fun y hy => by
      have h := C.head_par y ((hO.ymem y).1 hy)
      change [EOp.link _ _, EOp.link (ιf y) _] = [_, EOp.link (ιf (M.face (M.rev (C.par y)))) _]
      rw [h]

section
variable {P : Input} {W B n : ℕ}

lemma ldI_exec {c : Config} (hc : WordsBounded W c) (hP : ∀ i, P.data.getD i 0 ≤ W)
    {off : ℕ} (hoff : off ≤ W) :
    ∃ c' k', Exec P W (block (ldI off)) c c' k' ∧ k' = 3 ∧ c'.nreg 120 = 0 ∧
      c'.nreg 121 = P.data.getD off 0 ∧ GFr 120 122 c c' := by
  unfold ldI
  exec_block
  · omega
  · exact hoff
  · config_simp; exact hP _
  · exact ⟨rfl, by config_simp, by config_simp, by gfr_tac⟩

lemma IFr.ofGFr {B n lo hi : ℕ} {c c' : Config} (h : GFr lo hi c c') (hlo : 120 ≤ lo)
    (hhi : 122 ≤ lo ∨ hi ≤ 121) : IFr B n c c' :=
  ⟨fun r hr => (h.1 r (by omega)).1, fun r hr => (h.1 r (by omega)).2, h.2.2.2,
    fun a _ => by rw [h.2.1, h.2.2.1]; exact ⟨rfl, rfl⟩⟩

/-- The frame of the parts of the initialisation: the registers below `r110`, the output and
the memory outside the structure are kept. -/
def IFr0 (B n : ℕ) (c c' : Config) : Prop :=
  (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
    ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a

lemma IFr0.trans {B n : ℕ} {c c' c'' : Config} (h : IFr0 B n c c') (h' : IFr0 B n c' c'') :
    IFr0 B n c c'' :=
  ⟨fun r hr => ⟨(h'.1 r hr).1.trans (h.1 r hr).1, (h'.1 r hr).2.trans (h.1 r hr).2⟩,
    h'.2.1.trans h.2.1, fun a ha => ⟨(h'.2.2 a ha).1.trans (h.2.2 a ha).1,
      (h'.2.2 a ha).2.trans (h.2.2 a ha).2⟩⟩

lemma IFr.to0 {B n : ℕ} {c c' : Config} (h : IFr B n c c') : IFr0 B n c c' :=
  ⟨fun r hr => ⟨h.1 r (by omega), h.2.1 r (by omega)⟩, h.2.2.1, h.2.2.2⟩

lemma GFr.to0 {B n lo hi : ℕ} {c c' : Config} (h : GFr lo hi c c') (hlo : 110 ≤ lo) :
    IFr0 B n c c' :=
  ⟨fun r hr => h.1 r (by omega), h.2.2.2, fun a _ => by rw [h.2.1, h.2.2.1]; exact ⟨rfl, rfl⟩⟩

/-- **The spanning tree stored on the machine**: `inTS` performs `treeOpsL`, counted `6 #V`
operations and `45 #V + 16` further steps. -/
theorem inT_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {φ : D → ℤ}
    (hv : ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d) :
    ∃ c' G', ORun P W B n (inTS B nD n k) c (Forest.init n) G c' (treeOpsL T ιv ιg φ vs ts)
        G' (6 * Fintype.card V) (45 * Fintype.card V + 16) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a := by
  have hvl := hI.oT.flen
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [treeOpsL_eq T φ hI.oT] at hv ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  -- the values of the nodes of the vertices
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p110, g₁⟩ : ∃ c' k', Exec P W
      (block (.constR 110 0 :: ldI (iHD nD n k))) c c' k' ∧ k' = 4 ∧ c'.nreg 120 = 0 ∧
      c'.nreg 121 = vs.length ∧ c'.rreg 110 = ((0 : ℤ) : ℝ) ∧ GFr 110 122 c c' := by
    unfold ldI
    exec_block
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l0, by config_simp, by gfr_tac⟩
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) vs (fun y => [EOp.add (ιv y) 0, .add2 (ιv y) 0]) hvA (fun _ c' => IFr B n c₁ c')
    (body := bodyNV B (iIV nD n k) 110) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orun hW hP hI.iv (by unfold iIV; omega) hi hc' hS'
        h120 (z := 0) (by rw [hQ.2.1 110 (by omega), p110]) (by omega) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have hph₃ : ∀ d, c₃.rmem (aPH nD + σ d) = φ d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, g₁.2.2.1, hph]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => eopsDV false (ιg (T.par y)) (φ (T.par y)) (φ (M.rev (T.par y))))
    hvB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIT nD n k) (iNG nD) (aPH nD)
      (opsDV false)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orun (aA := aPH nD) (A := φ) hW hP hK.rv
        hI.it (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega)
        (by unfold aPH; omega) false hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aPH; omega))).2, hph₃]) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l1]⟩)
    e₃.wb_right o₃.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l1])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.2.wb hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => [EOp.link (ιg (T.par y)) (ιv (M.tail (T.par y))),
      .link (ιv (M.tail (M.rev (T.par y)))) (ιg (T.par y))])
    hvC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIT nD n k) (iNG nD) (iNT nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orun hW hP hK.rv hI.it
        (by unfold iIT iIV; omega) hK.ng (by unfold iNG; omega) hK.nt (by unfold iNT; omega)
        hi hc' hS' h120 hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l1]⟩)
    e₅.wb_right o₅.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l1])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr.1, hfr.2.1, hfr.2.2⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

/-- **The cotree stored on the machine**: `inCS` performs `cotOpsL` (the values from `VL` and
`H0`), counted `6 #F` operations and `45 #F + 17` further steps. -/
theorem inC_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {val : D → ℤ} {H₀ : ℤ}
    {F₁ : Forest} (hv : ValidOpsE n F₁ (cotOpsL C ιf ιe val H₀ fs cs)) {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n F₁ G c)
    (hvl : ∀ d, c.rmem (aVL nD + σ d) = val d) (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G', ORun P W B n (inCS B nD n k) c F₁ G c' (cotOpsL C ιf ιe val H₀ fs cs) G'
        (6 * Fintype.card F) (45 * Fintype.card F + 17) ∧ IFr0 B n c c' := by
  have hfl := hI.oC.flen
  have hcl := hI.oC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  rw [cotOpsL_eq C val H₀ hI.oC] at hv ⊢
  obtain ⟨hvAB, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  obtain ⟨hvA, hvB⟩ := (validOpsE_append_iff n _ _ _).1 hvAB
  rw [runOpsE_fst_append] at hvC
  -- the values of the nodes of the faces
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, p111, g₁⟩ : ∃ c' k', Exec P W
      (block ([.constN 122 (aH0 nD), .loadR 111 122] ++ ldI (iHD nD n k + 2))) c c' k' ∧
      k' = 5 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = fs.length ∧ c'.rreg 111 = (H₀ : ℝ) ∧
      GFr 111 123 c c' := by
    unfold ldI
    exec_block
    · unfold aH0; omega
    · omega
    · unfold iHD iIV; omega
    · config_simp; exact hP _
    · exact ⟨rfl, by config_simp, by config_simp; exact hI.l2, by config_simp; exact hH0,
        by gfr_tac⟩
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  obtain ⟨c₂, G₂, o₂, q₂⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) fs (fun y => [EOp.add (ιf y) H₀, .add2 (ιf y) H₀]) hvA
    (fun _ c' => IFr B n c₁ c') (body := bodyNV B (iIF nD n k) 111) (mb := 2) (hb := 5)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyNV_orun hW hP hI.if_ (by unfold iIF iIV; omega) hi hc'
        hS' h120 (z := H₀) (by rw [hQ.2.1 111 (by omega), p111]) (by omega) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), p121]⟩)
    e₁.wb_right o₁.2.lcte (IFr.refl _ _ _) p120 p121
  -- the values of the nodes of the edges
  obtain ⟨c₃, k₃, e₃, hk₃, s120, s121, g₃⟩ := ldI_exec (P := P) o₂.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₃ := ORun.ofGFr e₃ o₂.2.lcte g₃ (by omega)
  have hvl₃ : ∀ d, c₃.rmem (aVL nD + σ d) = val d := fun d => by
    have := hσ d
    rw [g₃.2.2.1, (q₂.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, g₁.2.2.1, hvl]
  obtain ⟨c₄, G₄, o₄, q₄⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => eopsDV true (ιe (C.par y)) (val (C.par y)) (val (M.rev (C.par y))))
    hvB (fun _ c' => IFr B n c₃ c') (body := bodyDV B nD (iIC nD n k) (iNE nD) (aVL nD)
      (opsDV true)) (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyDV_orun (aA := aVL nD) (A := val) hW hP hK.rv
        hI.ic (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega)
        (by unfold aVL; omega) true hi hc' hS' h120 (fun d => by
          have := hσ d
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aVL; omega))).2, hvl₃]) hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), s121,
        hI.l3]⟩)
    e₃.wb_right o₃.2.lcte (IFr.refl _ _ _) s120 (by rw [s121, hI.l3])
  -- the links
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, g₅⟩ := ldI_exec (P := P) o₄.2.wb hP
    (off := iHD nD n k + 3) (by unfold iHD iIV; omega)
  have o₅ := ORun.ofGFr e₅ o₄.2.lcte g₅ (by omega)
  obtain ⟨c₆, G₆, o₆, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) cs (fun y => [EOp.link (ιe (C.par y)) (ιf (M.face (C.par y))),
      .link (ιf (M.face (M.rev (C.par y)))) (ιe (C.par y))])
    hvC (fun _ c' => IFr B n c₅ c') (body := bodyLK B nD (iIC nD n k) (iNE nD) (iNF nD))
    (mb := 2) (hb := 17)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := bodyLK_orun hW hP hK.rv hI.ic
        (by unfold iIC iIV; omega) hK.ne (by unfold iNE; omega) hK.nf (by unfold iNF; omega)
        hi hc' hS' h120 hvi
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega), t121,
        hI.l3]⟩)
    e₅.wb_right o₅.2.lcte (IFr.refl _ _ _) t120 (by rw [t121, hI.l3])
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hfr : IFr0 B n c c₆ := (((((g₁.to0 (by omega)).trans q₂.to0).trans
    (g₃.to0 (by omega))).trans q₄.to0).trans (g₅.to0 (by omega))).trans q₆.to0
  refine ⟨c₆, G₆, ?_, hfr⟩
  rw [List.append_assoc]; exact o.mono (by omega) (by omega)

lemma flatMap_nil' {α : Type*} (l : List α) : l.flatMap (fun _ => ([] : List EOp)) = [] := by
  simp

/-- **The parent darts of the spanning tree into `TP`** (no operation). -/
theorem inP_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {S : Finset D} {ℓ : D → ℤ}
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) :
    ∃ c' G', ORun P W B n (inPS nD n k) c Fo G c' [] G' 0 (13 * Fintype.card V + 5) ∧
      (∀ x, x ≠ T.root → c'.nmem (aTP + ιv x) = σ (T.par x)) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      c'.rmem = c.rmem ∧ (∀ a, n ≤ a → c'.nmem a = c.nmem a) := by
  have htl := hI.oT.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hvn := hL.prim.f_lt
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ := ldI_exec (P := P) hc hP
    (off := iHD nD n k + 1) (by unfold iHD iIV; omega)
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  have hhd : ∀ i (h : i < ts.length), M.head (T.par ts[i]) = ts[i] := fun i h =>
    tpar_head T ((hI.oT.ymem _).1 (List.getElem_mem h))
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n)
    (ra := 120) (rb := 121) ts (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121 ∨ r = 151) → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, (∀ x : V, a ≠ aTP + ιv x) → c'.nmem a = c₁.nmem a) ∧
      ∀ i' (h : i' < ts.length), i' < i → c'.nmem (aTP + ιv ts[i']) = σ (T.par ts[i']))
    (body := block (bodyTP nD n k)) (mb := 0) (hb := 11)
    (fun i hi c' G' hQ hc' hS' h120 _ _ => by
      obtain ⟨c₃, k₃, e₃, hk₃, q120, qn, qr, qm, qrm, qout⟩ := bodyTP_exec (P := P) hP hvn hK.nh
        (by unfold iNH; omega) hI.it (by unfold iIT iIV; omega) hi hc' h120 (by omega)
      rw [hhd i hi] at qm
      subst hk₃
      refine ⟨c₃, G', ORun.glue e₃ hS' (fun a ha _ => ⟨?_, by rw [qrm]⟩) (qn 151 (by omega)),
        ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr, by rw [qr]; exact hQ.2.1,
          by rw [qrm]; exact hQ.2.2.1, by rw [qout]; exact hQ.2.2.2.1, fun a ha => ?_,
          fun i' h hi' => ?_⟩, q120, by rw [qn 121 (by omega), hQ.1 121 (by omega), p121,
          hI.l1]⟩
      · rw [qm, upd_other _ _ _ (by have := hvn ts[i]; unfold aTP; omega)]
      · rw [qm, upd_other _ _ _ (ha _)]; exact hQ.2.2.2.2.1 a ha
      · rw [qm]
        rcases Nat.lt_or_ge i' i with h' | h'
        · have hne : ts[i'] ≠ ts[i] := fun h'' => by
            have := (List.Nodup.getElem_inj_iff hI.oT.ynd).1 h''; omega
          rw [upd_other _ _ _ (fun h'' => hne (hL.prim.f_inj (by unfold aTP at h''; omega)))]
          exact hQ.2.2.2.2.2 i' h h'
        · obtain rfl : i' = i := by omega
          rw [upd_same])
    e₁.wb_right o₁.2.lcte ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hI.l1])
  rw [flatMap_nil'] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by simp) (by omega), fun x hx => ?_, fun r hr => ?_, ?_, ?_,
    fun a ha => ?_⟩
  · obtain ⟨i', h, rfl⟩ := List.getElem_of_mem ((hI.oT.ymem x).2 hx)
    exact q₆ i' h h
  · rw [q₁ r (by omega), q₂, (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]; exact ⟨rfl, rfl⟩
  · rw [q₄, g₁.2.2.2]
  · rw [q₃, g₁.2.2.1]
  · rw [q₅ a (fun x h => by have := hvn x; unfold aTP at h; omega), g₁.2.1]

/-- **The values of the darts into `VL`**: two queries per dart (no operation). -/
theorem inV_orun (hW : B + 16 * (n + 1) ≤ W) (hWa : 6 * nD ≤ W) (hB3 : 3 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) {ιv : V → ℕ} (hvn : ∀ x, ιv x < n)
    (hNT : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d))
    (hNH : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) :
    ∃ c' G', ORun P W B n (inVS B nD) c Fo G c' [] G' (2 * nD) (20 * nD + 4) ∧
      (∀ d, c'.rmem (aVL nD + σ d) = c.rmem (aWT + σ d) + pathSum Fo n (ιv (M.tail d)) -
        pathSum Fo n (ιv (M.head d))) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ : ∃ c' k', Exec P W (block [.constN 120 0,
      .constN 121 nD]) c c' k' ∧ k' = 2 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = nD ∧
      GFr 120 122 c c' := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by gfr_tac⟩
  have o₁ := ORun.ofGFr e₁ hS g₁ (by omega)
  have hlen : (List.range nD).length = nD := List.length_range
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := listLoop_orun (P := P) (W := W) (B := B) (n := n)
    (ra := 120) (rb := 121) (List.range nD) (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c₁.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c₁.rreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + i ≤ a) →
        c'.rmem a = c₁.rmem a) ∧
      ∀ d : D, (σ d : ℕ) < i → c'.rmem (aVL nD + σ d) = c₁.rmem (aWT + σ d) +
        pathSum Fo n (ιv (M.tail d)) - pathSum Fo n (ιv (M.head d)))
    (body := bodyVL B nD) (mb := 2) (hb := 18)
    (fun i hi c' G' hQ hc' hS' h120 h121 _ => by
      rw [flatMap_nil'] at hS' ⊢
      have hi' : i < nD := by rw [hlen] at hi; exact hi
      set d := σ.symm ⟨i, hi'⟩ with hd
      have hσd : (σ d : ℕ) = i := by rw [hd, Equiv.apply_symm_apply]
      obtain ⟨c₃, G₃, o, q120, qn, qr, qout, qnm, qrm, qv⟩ := bodyVL_orun hW hP hvn hNT hNH hWa
        (by omega) hσd hc' hS' h120
      have hwt : c'.rmem (aWT + i) = c₁.rmem (aWT + i) :=
        hQ.2.2.2.2.1 _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aVL; omega))
      refine ⟨c₃, G₃, o, ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr,
        fun r hr => by rw [qr r hr]; exact hQ.2.1 r hr, by rw [qout]; exact hQ.2.2.1,
        fun a ha => by rw [qnm a ha]; exact hQ.2.2.2.1 a ha, fun a ha ha' => ?_,
        fun d' hd' => ?_⟩, q120, by rw [qn 121 (by omega), h121]⟩
      · rw [qrm a ha (by omega)]; exact hQ.2.2.2.2.1 a ha (by omega)
      · rcases Nat.lt_or_ge (σ d' : ℕ) i with h' | h'
        · rw [qrm _ (Or.inl (by unfold aVL; omega)) (by omega)]
          exact hQ.2.2.2.2.2 d' h'
        · have : d' = d := σ.injective (Fin.ext (by omega))
          subst this
          rw [hσd, qv, hwt]; rfl)
    e₁.wb_right o₁.2.lcte ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hlen])
  rw [flatMap_nil', hlen] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by omega) (by omega), fun d => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha ha' => ?_⟩
  · rw [q₆ d (by rw [hlen]; exact (σ d).2), g₁.2.2.1]
  · rw [q₁ r (by omega), q₂ r (by omega), (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [q₃, g₁.2.2.2]
  · rw [q₄ a ha, g₁.2.1]
  · rw [q₅ a ha (by rw [hlen]; exact ha'), g₁.2.2.1]

/-- **The initialisation on the machine.** From the empty forest stored at `B` (and `r151 = n`),
the input holding the map (`KInput`) and the initial trees (`KInit`, the cotree `C` with its
parent darts off `T`), the real memory holding weights `wt` in `WT`, `φ` in `PH` and `H₀` in
`H0`, the program `inS` performs the operations `treeOpsL ++ cotOpsL` of `init_storedL` (at most
`6 (#V + #F)`), counted `6 (#V + #F) + 2 nD` operations and `60 (#V + #F) + 20 nD + 42` further
steps; the forest stores `T` with the weights `φ` and `C` with the values
`wt d + psum (tail d) - psum (head d)` and `H₀` at the nodes of the faces, and `TP`, `WT`, `PH`
hold `T`, `wt`, `φ` (`KMem`). It keeps the registers below `r110`, the output, the natural
memory outside the structure from `n` on, and the real memory outside the structure and `VL`. -/
theorem in_orun (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 9 * nD + 7 * n + k + 4 ≤ W)
    (hB : n + 2 * nD ≤ B) (hB3 : 3 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    {S : Finset D} {ℓ : D → ℤ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}
    (hL : Layout M n ιv ιg ιf ιe) (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {T : DTree M.dual}
    {C : DTree M} {vs ts : List V} {fs cs : List F} (hI : KInit M σ ιv ιf n k T C vs ts fs cs P)
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) {wt φ : D → ℤ} {H₀ : ℤ} {c : Config}
    (hc : WordsBounded W c) {G : List VT} (hS : LCTE B n (Forest.init n) G c)
    (hwt : ∀ d, c.rmem (aWT + σ d) = wt d) (hph : ∀ d, c.rmem (aPH nD + σ d) = φ d)
    (hH0 : c.rmem (aH0 nD) = H₀) :
    ∃ c' G' os, ORun P W B n (inS B nD n k) c (Forest.init n) G c' os G'
        (6 * (Fintype.card V + Fintype.card F) + 2 * nD)
        (60 * (Fintype.card V + Fintype.card F) + 20 * nD + 42) ∧
      os.length ≤ 6 * (Fintype.card V + Fintype.card F) ∧
      (runOpsE n (Forest.init n) os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ C.root H₀ (runOpsE n (Forest.init n) os).1 T
        (fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d)) ∧
      KMem M σ ιv T wt φ c' ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aVL nD ∨ aVL nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  set val : D → ℤ := fun d => wt d + T.psum φ (M.tail d) - T.psum φ (M.head d) with hval
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨hlen, hv, ho, hSt⟩ := init_storedL hL hoff φ val H₀ hI.oT hI.oC
  obtain ⟨-, hvT, -, hRT, -, -, -⟩ := tree_storedL (ιf := ιf) (ιe := ιe) hL φ hI.oT
  obtain ⟨-, hvC⟩ := (validOpsE_append_iff n _ _ _).1 hv
  set F1 := (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 with hF1
  -- the spanning tree
  obtain ⟨c₁, G₁, o₁, r₁, out₁, m₁⟩ := inT_orun hW hWa hB hP hL hK hI hvT hc hS hph
  -- its parent darts
  obtain ⟨c₂, G₂, o₂, tp₂, r₂, out₂, rm₂, nm₂⟩ := inP_orun hW hWa hB hP hL hK hI o₁.2.wb
    o₁.2.lcte
  -- the values of the darts
  obtain ⟨c₃, G₃, o₃, vl₃, r₃, out₃, nm₃, rm₃⟩ := inV_orun (P := P) (σ := σ) hW (by omega) hB3 hP
    hL.prim.f_lt hK.nt hK.nh o₂.2.wb o₂.2.lcte
  have hvl : ∀ d, c₃.rmem (aVL nD + σ d) = ((val d : ℤ) : ℝ) := fun d => by
    have hd := hσ d
    rw [vl₃, rm₂, (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
    change (wt d : ℝ) + pathSum F1 n _ - pathSum F1 n _ = _
    rw [lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv,
      lct_label hRT hL.prim.f_lt hL.prim.e_lt hL.hv]
    simp only [hval]; push_cast; ring
  have hH0₃ : c₃.rmem (aH0 nD) = H₀ := by
    rw [rm₃ _ (Or.inl (by unfold aH0; omega)) (Or.inr (by unfold aH0 aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aH0; omega))).2, hH0]
  -- the cotree
  obtain ⟨c₄, G₄, o₄, f₄⟩ := inC_orun hW hWa hB3 hP hL hK hI hvC o₃.2.wb o₃.2.lcte hvl hH0₃
  have o := o₁.seq (o₂.seq (o₃.seq o₄))
  simp only [List.nil_append] at o
  refine ⟨c₄, G₄, _, o.mono (by omega) (by omega), hlen, ho, hSt, ⟨fun x hx => ?_, fun d => ?_,
    fun d => ?_⟩, fun r hr => ?_, ?_, fun a ha han => ?_, fun a ha ha' => ?_⟩
  · have := hL.prim.f_lt x
    rw [(f₄.2.2 _ (Or.inl (by unfold aTP; omega))).1, nm₃ _ (Or.inl (by unfold aTP; omega))]
    exact tp₂ x hx
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aWT; omega))).2,
      rm₃ _ (Or.inl (by unfold aWT; omega)) (Or.inl (by unfold aWT aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aWT; omega))).2, hwt]
  · have := hσ d
    rw [(f₄.2.2 _ (Or.inl (by unfold aPH; omega))).2,
      rm₃ _ (Or.inl (by unfold aPH; omega)) (Or.inl (by unfold aPH aVL; omega)), rm₂,
      (m₁ _ (Or.inl (by unfold aPH; omega))).2, hph]
  · rw [(f₄.1 r hr).1, (f₄.1 r hr).2, (r₃ r hr).1, (r₃ r hr).2, (r₂ r hr).1, (r₂ r hr).2]
    exact r₁ r hr
  · rw [f₄.2.1, out₃, out₂, out₁]
  · rw [(f₄.2.2 a ha).1, nm₃ a ha, nm₂ a han, (m₁ a ha).1]
  · rw [(f₄.2.2 a ha).2, rm₃ a ha ha', rm₂, (m₁ a ha).2]

end

end Klein

end PlanarFlow
