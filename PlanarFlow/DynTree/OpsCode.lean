module

public import PlanarFlow.DynTree.AccessCode
public import PlanarFlow.DynTree.Evert

/-!
# Dynamic trees: the operations on the machine (the embeddable interface)

The state of the structure at base `B` is `LCT B n F G c`: the memory of `c` stores a virtual
forest `G` representing the forest `F` on `0, …, n-1`, with `n` in `r151`. Operands are passed in
`r193` (`v`), `r194` (`w`) and the real `r193` (`δ`); the answers are left in `r195` (a node)
and the real `r195` (a value). Every operation keeps the registers below `r160` and from `r200`
on, the real registers outside `r160 … r199`, the output, and the memory outside the structure.

* `opRootS`: `r195 := findRoot F n v`;
* `opParentS`: `r195 := F.par v`;
* `opMinS`: `r195 := (pathMin F n v).2`, real `r195 := (pathMin F n v).1`;
* `opSumS`: real `r195 := pathSum F n v`;
* `opAddS`: `F := addPath F n v δ`;
* `opCutS`: `F := cut F n v` (`v` not a root);
* `opLinkS`: `F := link F v w` (`v` a root, `w` not in the tree of `v`).

Each costs at most `16400 · (Φ - Φ') + 311600 ⌊log₂ n⌋ + 42100` steps, `Φ = potL G` the rank
potential of the virtual forest.

**Evert.** `LCTE B n F G c` is the same state without the invariant on the field `fpar` (which
`evert` does not keep); the access, the queries, the additions to both values, cut and link work
on it as well (`…_execE`), and so do

* `opEvertS`: `F := evert F n v` (`opEvert_exec`);
* `opQuery2S`: the queries on the second values;
* `opAdd2S`: `F := addPath2 F n v δ`;
* `opParentAccS`: `r195 := F.par v`, read from the access (the `fpar` field is not used).
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-- The state of the link-cut tree at base `B`: the memory stores `G`, which represents `F`. -/
structure LCT (B n : ℕ) (F : Forest) (G : List VT) (c : Config) : Prop where
  inv : Inv B n (mem c) G
  rep : Rep B n (mem c) G F
  bnd : Bnd B n (mem c)
  hn : c.nreg 151 = n

/-- The state of the evertable link-cut tree: as `LCT`, without the field `fpar`. -/
structure LCTE (B n : ℕ) (F : Forest) (G : List VT) (c : Config) : Prop where
  inv : Inv B n (mem c) G
  rep : RepE B n (mem c) G F
  bnd : Bnd B n (mem c)
  hn : c.nreg 151 = n

lemma LCT.toE {B n : ℕ} {F : Forest} {G : List VT} {c : Config} (h : LCT B n F G c) :
    LCTE B n F G c := ⟨h.inv, h.rep.toRepE, h.bnd, h.hn⟩

section
variable {P : Input} {W : ℕ}

/-- The access in the form used by the operations: the accessed tree first. -/
theorem access_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 189 = v)
    (hvn : v < n) {gb ga : List VT} {T0 : VT} (hG : G = gb ++ T0 :: ga) (hvT : v ∈ nodes T0) :
    ∃ c' k l dv, Exec P W (accessS B) c c' k ∧
      LCTE B n F (node l v leaf dv :: (gb ++ ga)) c' ∧ MemFrame B n (mem c) (mem c') ∧
      FrK 193 c c' ∧ c'.nreg 189 = v ∧
      k + 16400 * potL (node l v leaf dv :: (gb ++ ga)) ≤
        16400 * potL G + 147600 * Nat.log 2 n + 21000 ∧
      (∀ u, fpar B (mem c') u = fpar B (mem c) u) ∧ rv B (mem c') v = false := by
  obtain ⟨c', k, l, dv, e, I, R, hb, hmf, hfr, h189, h151, hk, hfp, hrv⟩ :=
    accessS_execE (P := P) B n hc hW hS.hn hS.bnd hS.inv hS.rep hv hvn hG hvT
  have hp : (gb ++ node l v leaf dv :: ga).Perm (node l v leaf dv :: (gb ++ ga)) :=
    List.perm_middle
  exact ⟨c', k, l, dv, e, ⟨I.perm B n hp, R.perm B n hp, hb, h151⟩, hmf, hfr, h189,
    by rw [← potL_perm hp]; exact hk, hfp, hrv⟩

theorem access_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v : ℕ} (hv : c.nreg 189 = v)
    (hvn : v < n) {gb ga : List VT} {T0 : VT} (hG : G = gb ++ T0 :: ga) (hvT : v ∈ nodes T0) :
    ∃ c' k l dv, Exec P W (accessS B) c c' k ∧
      LCT B n F (node l v leaf dv :: (gb ++ ga)) c' ∧ MemFrame B n (mem c) (mem c') ∧
      FrK 193 c c' ∧ c'.nreg 189 = v ∧
      k + 16400 * potL (node l v leaf dv :: (gb ++ ga)) ≤
        16400 * potL G + 147600 * Nat.log 2 n + 21000 ∧ rv B (mem c') v = false := by
  obtain ⟨c', k, l, dv, e, hS', hmf, hfr, h189, hk, hfp, hrv⟩ :=
    access_execE (P := P) B n hc hW hS.toE hv hvn hG hvT
  exact ⟨c', k, l, dv, e, ⟨hS'.inv, ⟨hS'.rep, fun u hu => by rw [hfp]; exact hS.rep.fpar u hu⟩,
    hS'.bnd, hS'.hn⟩, hmf, hfr, h189, hk, hrv⟩

/-- Every node `v < n` lies in one of the trees of `G`. -/
lemma LCTE.split {B n : ℕ} {F : Forest} {G : List VT} {c : Config} (hS : LCTE B n F G c)
    {v : ℕ} (hvn : v < n) : ∃ gb ga T0, G = gb ++ T0 :: ga ∧ v ∈ nodes T0 := by
  obtain ⟨T, hT, hu⟩ := mem_nodesL_iff.mp ((hS.inv.cover v).mpr hvn)
  obtain ⟨gb, ga, rfl⟩ := List.append_of_mem hT
  exact ⟨gb, ga, T, rfl, hu⟩

lemma LCT.split {B n : ℕ} {F : Forest} {G : List VT} {c : Config} (hS : LCT B n F G c) {v : ℕ}
    (hvn : v < n) : ∃ gb ga T0, G = gb ++ T0 :: ga ∧ v ∈ nodes T0 := by
  obtain ⟨T, hT, hu⟩ := mem_nodesL_iff.mp ((hS.inv.cover v).mpr hvn)
  obtain ⟨gb, ga, rfl⟩ := List.append_of_mem hT
  exact ⟨gb, ga, T, rfl, hu⟩

end

/-! ### Queries -/

/-- The queries at `v = r193`: `r195 := findRoot v`, `r196 := ` the argmin and real
`r195 := ` the minimum on the root path, real `r196 := pathSum v`. -/
def opQueryS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  block (ld B 195 189 5 ++ ld B 196 189 3 ++ ldR B 195 189 2 ++ ldR B 197 189 1 ++ [.addR 195 195 197] ++
    ldR B 196 189 3 ++ ldR B 198 189 4 ++ [.mulR 198 197 198, .addR 196 196 198])

section
variable {P : Input} {W : ℕ}

theorem opQuery_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opQueryS B) c c' k ∧ LCTE B n F G' c' ∧
      c'.nreg 195 = findRoot F n v ∧ c'.nreg 196 = (pathMin F n v).2 ∧
      c'.rreg 195 = (pathMin F n v).1 ∧ c'.rreg 196 = pathSum F n v ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 ∧
      ∀ u, fpar B (mem c') u = fpar B (mem c) u := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  obtain ⟨hroot, hmin, hsum, -, -⟩ := query_top B n hS2.inv hS2.rep rfl
  have hb := hS2.bnd
  obtain ⟨-, -, -, -, -, -⟩ := hb.get hvn.le
  have hblk : ∃ c3 k3, Exec P W (block (ld B 195 189 5 ++ ld B 196 189 3 ++ ldR B 195 189 2 ++
      ldR B 197 189 1 ++ [.addR 195 195 197] ++ ldR B 196 189 3 ++ ldR B 198 189 4 ++
      [.mulR 198 197 198, .addR 196 196 198])) c2 c3 k3 ∧ k3 ≤ 40 ∧ mem c3 = mem c2 ∧
      c3.nreg 195 = lm B (mem c2) v ∧ c3.nreg 196 = am B (mem c2) v ∧
      c3.rreg 195 = minA B (mem c2) v ∧ c3.rreg 196 = sumA B (mem c2) v ∧ FrK 197 c2 c3 ∧
      c3.nreg 193 = c2.nreg 193 ∧ c3.nreg 194 = c2.nreg 194 ∧ c3.nreg 151 = c2.nreg 151 := by
    have hw2 := e2.wb_right
    simp only [ld, ldR, ad, List.cons_append, List.nil_append, List.append_assoc]
    exec_block
    any_goals (config_simp; (try simp only [h189]); omega)
    refine ⟨by omega, rfl, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_, ?_, ?_⟩
    · config_simp; rw [h189]; rfl
    · config_simp; rw [h189]; rfl
    · config_simp; rw [h189]; rfl
    · config_simp; rw [h189]; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      exact ⟨trivial, trivial⟩
    · omega
    · config_simp
    · config_simp
    · config_simp
  obtain ⟨c3, k3, e3, hk3, m3, r195, r196, q195, q196, f3, s193, s194, s151⟩ := hblk
  refine ⟨c3, 1 + (k2 + k3), _, .seq e1 (.seq e2 e3), ⟨m3 ▸ hS2.inv, m3 ▸ hS2.rep, m3 ▸ hS2.bnd,
    by rw [s151]; exact hS2.hn⟩, by rw [r195, hroot], by rw [r196, hmin],
    by rw [q195, hmin], by rw [q196, hsum], m3 ▸ hmf2, ?_, ?_, ?_, by omega,
    fun u => by rw [m3, hfp2]; rfl⟩
  · have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    exact g1.trans ((hfr2.mono (by omega)).trans f3)
  · rw [s193, hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  · rw [s194, hfr2.2.1 194 (by omega) (by omega)]; config_simp

theorem opQuery_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opQueryS B) c c' k ∧ LCT B n F G' c' ∧
      c'.nreg 195 = findRoot F n v ∧ c'.nreg 196 = (pathMin F n v).2 ∧
      c'.rreg 195 = (pathMin F n v).1 ∧ c'.rreg 196 = pathSum F n v ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 := by
  obtain ⟨c', k, G', e, hS', h1, h2, h3, h4, h5, h6, h7, h8, h9, hfp⟩ :=
    opQuery_execE (P := P) B n hc hW hS.toE hv hvn
  exact ⟨c', k, G', e, ⟨hS'.inv, ⟨hS'.rep, fun u hu => by rw [hfp]; exact hS.rep.fpar u hu⟩,
    hS'.bnd, hS'.hn⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end

/-! ### Parent and addition -/

/-- `r195 := F.par v`, `v = r193`. -/
def opParentS (B : ℕ) : Stmt := block (ld B 195 193 4)

/-- `F := addPath F n v δ`, `v = r193`, `δ = ` real `r200`. -/
def opAddS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  block (ldR B 197 189 (tgf false) ++ [.addR 197 197 200] ++ stR B 189 (tgf false) 197)

section
variable {P : Input} {W : ℕ}

theorem opParent_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k, Exec P W (opParentS B) c c' k ∧ k ≤ 5 ∧ LCT B n F G c' ∧ c'.nreg 195 = F.par v ∧
      mem c' = mem c ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = c.nreg 194 := by
  unfold opParentS
  simp only [ld, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hv]); omega)
  refine ⟨by omega, ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩, ?_, rfl,
    ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩, by config_simp; exact hv, by config_simp⟩
  · config_simp; rw [hv]; exact hS.rep.fpar v hvn
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]

/-- `F := addPath2 F n v δ`, `v = r193`, `δ = ` real `r200`. -/
def opAdd2S (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  block (ldR B 197 189 6 ++ [.addR 197 197 200] ++ stR B 189 6 197)

/-- The addition of `δ = ` real `r200` to channel `k` at the accessed `v = r189`. -/
lemma addBlock_exec (B n : ℕ) (k : Bool) {c2 : Config} (hw2 : WordsBounded W c2)
    (hW : B + 16 * (n + 1) ≤ W) {v : ℕ} (h189 : c2.nreg 189 = v) (hvn : v < n) :
    ∃ c3 k3, Exec P W (block (ldR B 197 189 (tgf k) ++ [.addR 197 197 200] ++
      stR B 189 (tgf k) 197)) c2 c3 k3 ∧ k3 ≤ 12 ∧
      mem c3 = addTagC B k v (c2.rreg 200) (mem c2) ∧
      FrK 197 c2 c3 ∧ c3.nreg 193 = c2.nreg 193 ∧ c3.nreg 194 = c2.nreg 194 ∧
      c3.nreg 151 = c2.nreg 151 := by
  have hk : tgf k < 16 := by cases k <;> simp [tgf]
  simp only [ldR, stR, ad, List.cons_append, List.nil_append, List.append_assoc]
  exec_block
  any_goals (config_simp; (try simp only [h189]); omega)
  refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩, by config_simp,
    by config_simp, by config_simp⟩
  · simp only [mem, addTagC]; config_simp; rw [h189]
    cases k <;> rfl
  · config_simp
    simp (disch := omega) only [upd_out _ _ _ hr]
    try exact ⟨trivial, trivial⟩

/-- The addition to channel `k` on the root path of `v = r193`. -/
theorem opAddC_execE (B n : ℕ) (k : Bool) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ}
    (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k' G', Exec P W (.seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
      block (ldR B 197 189 (tgf k) ++ [.addR 197 197 200] ++ stR B 189 (tgf k) 197)) c c' k' ∧
      LCTE B n (addPathC F n v (c.rreg 200) k) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k' + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 ∧
      ∀ u, fpar B (mem c') u = fpar B (mem c) u := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  have hδ : c2.rreg 200 = c.rreg 200 := by
    rw [(hfr2.1 200 (by omega)).2]
  obtain ⟨I3, R3, F3, P3⟩ := addPath_okE B n hS2.inv hS2.rep rfl k (c.rreg 200)
  obtain ⟨c3, k3, e3, hk3, m3, f3, s193, s194, s151⟩ :=
    addBlock_exec (P := P) B n k e2.wb_right hW h189 hvn
  rw [hδ] at m3
  refine ⟨c3, 1 + (k2 + k3), _, .seq e1 (.seq e2 e3), ⟨m3 ▸ I3, m3 ▸ R3, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    by omega, fun u => by rw [m3, P3, hfp2]; rfl⟩
  · rw [m3]; exact hS2.bnd
  · rw [s151]; exact hS2.hn
  · rw [m3]; exact hmf2.trans B n F3
  · have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    exact g1.trans ((hfr2.mono (by omega)).trans f3)
  · rw [s193, hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  · rw [s194, hfr2.2.1 194 (by omega) (by omega)]; config_simp

theorem opAdd_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opAddS B) c c' k ∧ LCT B n (addPath F n v (c.rreg 200)) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 := by
  obtain ⟨c', k, G', e, hS', h1, h2, h3, h4, h5, hfp⟩ :=
    opAddC_execE (P := P) B n false hc hW hS.toE hv hvn
  exact ⟨c', k, G', e, ⟨hS'.inv, ⟨hS'.rep, fun u hu => by rw [hfp]; exact hS.rep.fpar u hu⟩,
    hS'.bnd, hS'.hn⟩, h1, h2, h3, h4, h5⟩

theorem opAdd2_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opAdd2S B) c c' k ∧ LCTE B n (addPath2 F n v (c.rreg 200)) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 :=
  let ⟨c', k, G', e, hS', h1, h2, h3, h4, h5, _⟩ := opAddC_execE (P := P) B n true hc hW hS hv hvn
  ⟨c', k, G', e, hS', h1, h2, h3, h4, h5⟩

end

/-! ### Cut -/

/-- `F := cut F n v`, `v = r193` not a root. -/
def opCutS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  .seq (block (ld B 192 189 1 ++ st B 189 1 151 ++ st B 192 0 151 ++ st B 189 4 151 ++
    ldR B 197 192 1 ++ ldR B 198 189 1 ++ ldR B 199 192 6 ++ ldR B 196 189 6 ++
    [.addR 197 197 198, .addR 199 199 196] ++ stR B 192 1 197 ++ stR B 192 6 199 ++
    [.copyN 170 189])) (recompS B)

section
variable {P : Input} {W : ℕ}

/-- After the access of a non-root `v`, its left subtree is not empty. -/
lemma left_ne_leaf {B n : ℕ} {M : Mem} {F : Forest} {l : VT} {v : ℕ} {dv : List VT}
    {G : List VT} (hR : RepE B n M (node l v leaf dv :: G) F) (hp : F.par v < n) : l ≠ leaf := by
  rintro rfl
  have := hR.par v n (by simp)
  omega

theorem opCut_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n)
    (hp : F.par v < n) :
    ∃ c' k G', Exec P W (opCutS B) c c' k ∧ LCTE B n (cut F n v) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21500 ∧
      ∀ u, fpar B (mem c') u = if u = v then n else fpar B (mem c) u := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, hrv2⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  have hl := left_ne_leaf hS2.rep hp
  obtain ⟨I3, R3, F3, hpot3, P3⟩ := cut_okE B n hS2.inv hS2.rep rfl hl hrv2
  have hb2 := hS2.bnd
  obtain ⟨-, la, ra, -, -, -⟩ := hb2.get hvn.le
  have hblk : ∃ c3 k3, Exec P W (block (ld B 192 189 1 ++ st B 189 1 151 ++ st B 192 0 151 ++
      st B 189 4 151 ++ ldR B 197 192 1 ++ ldR B 198 189 1 ++ ldR B 199 192 6 ++
      ldR B 196 189 6 ++ [.addR 197 197 198, .addR 199 199 196] ++ stR B 192 1 197 ++
      stR B 192 6 199 ++ [.copyN 170 189])) c2 c3 k3 ∧ k3 ≤ 80 ∧
      mem c3 = ⟨upd (upd (upd (mem c2).nm (adr B v 1) n) (adr B (lc B (mem c2) v) 0) n)
        (adr B v 4) n, upd (upd (mem c2).rm (adr B (lc B (mem c2) v) 1)
          (tg B (mem c2) (lc B (mem c2) v) + tg B (mem c2) v)) (adr B (lc B (mem c2) v) 6)
          (tg2 B (mem c2) (lc B (mem c2) v) + tg2 B (mem c2) v)⟩ ∧
      FrK 193 c2 c3 ∧ c3.nreg 170 = v ∧ c3.nreg 193 = c2.nreg 193 ∧
      c3.nreg 194 = c2.nreg 194 := by
    have hw2 := e2.wb_right
    have hn2 := hS2.hn
    simp only [lc, mem, adr] at la
    simp only [ld, ldR, st, stR, ad, List.cons_append, List.nil_append, List.append_assoc]
    exec_block
    any_goals (config_simp; (try simp only [h189, hn2]); omega)
    refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, by config_simp; exact h189,
      by config_simp, by config_simp⟩
    · simp only [mem, lc, tg, tg2]; config_simp; rw [h189, hn2]; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · config_simp; simp (disch := omega) only [upd_ne_of]
  obtain ⟨c3, k3, e3, hk3, m3, f3, s170, s193, s194⟩ := hblk
  have hb3 : Bnd B n (mem c3) := by
    rw [m3]; refine hb2.of fun a => ?_
    simp only [upd_apply]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr le_rfl
  obtain ⟨-, l3, r3, -, -, -⟩ := hb3.get hvn.le
  obtain ⟨c4, k4, e4, hk4, m4, f4, s4, t4⟩ := recompS_exec (P := P) B n e3.wb_right hW s170
    (by rw [(f3.1 151 (by omega)).1]; exact hS2.hn) hvn.le l3 r3
  have hm4 : mem c4 = cutM B n v (mem c2) := by rw [m4, m3]; rfl
  have h151 : c4.nreg 151 = n := by
    rw [(f4.1 151 (by omega)).1, (f3.1 151 (by omega)).1]; exact hS2.hn
  have hb4 : Bnd B n (mem c4) := by rw [m4]; exact hb3.recomp hvn.le
  refine ⟨c4, 1 + (k2 + (k3 + k4)), _, .seq e1 (.seq e2 (.seq e3 e4)), ⟨hm4 ▸ I3, hm4 ▸ R3,
    hb4, h151⟩, by rw [hm4]; exact hmf2.trans B n F3, ?_, ?_, ?_, by omega, fun u => ?_⟩
  · have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    exact g1.trans ((hfr2.mono (by omega)).trans ((f3.mono (by omega)).trans (f4.mono (by omega))))
  · rw [f4.2.1 193 (by omega) (by omega), s193, hfr2.2.1 193 (by omega) (by omega)]; config_simp
    exact hv
  · rw [f4.2.1 194 (by omega) (by omega), s194, hfr2.2.1 194 (by omega) (by omega)]; config_simp
  · rw [hm4, P3, hfp2]; rfl

theorem opCut_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n)
    (hp : F.par v < n) :
    ∃ c' k G', Exec P W (opCutS B) c c' k ∧ LCT B n (cut F n v) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21500 := by
  obtain ⟨c', k, G', e, hS', h1, h2, h3, h4, h5, hfp⟩ :=
    opCut_execE (P := P) B n hc hW hS.toE hv hvn hp
  refine ⟨c', k, G', e, ⟨hS'.inv, ⟨hS'.rep, fun u hu => ?_⟩, hS'.bnd, hS'.hn⟩, h1, h2, h3, h4, h5⟩
  rw [hfp]; simp only [cut]; split_ifs
  · rfl
  · exact hS.rep.fpar u hu

end

/-! ### Link -/

/-- `F := link F v w`, `v = r193` a root, `w = r194` not in the tree of `v`. -/
def opLinkS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <| .seq (.instr (.copyN 189 194)) <|
  .seq (accessS B) (block (st B 193 0 194 ++ st B 193 4 194))

lemma rootPath_root {F : Forest} {n v : ℕ} (hvn : v < n) (hp : F.par v = n) :
    rootPath F n v = [v] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [rootPath, upPath, hvn, hp, upPath_nil]

section
variable {P : Input} {W : ℕ}

theorem opLink_execE (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v w : ℕ} (hv : c.nreg 193 = v)
    (hw : c.nreg 194 = w) (hvn : v < n) (hwn : w < n) (hp : F.par v = n)
    (hroot : findRoot F n w ≠ v) :
    ∃ c' k G', Exec P W (opLinkS B) c c' k ∧ LCTE B n (link F v w) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = w ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 311600 * Nat.log 2 n + 42100 ∧
      ∀ u, fpar B (mem c') u = if u = v then w else fpar B (mem c) u := by
  -- access `v`
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, lv, dv, e2, hS2, hmf2, hfr2, h189, hk2, hfp2, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  generalize hrest : gb ++ ga = rest1 at hS2 hk2
  -- the tree of `v` is the single node `v`
  have hlv : lv = leaf := by
    have h := rootPath_top B n hS2.inv hS2.rep (gb := []) (ga := rest1) rfl
      (xs := seq lv) (v := v) (by simp)
    rw [rootPath_root hvn hp] at h
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons.injEq, true_and, List.reverse_eq_nil_iff] at h
    exact seq_eq_nil.mp (List.reverse_eq_nil_iff.mp h.symm)
  subst hlv
  have h193 : c2.nreg 193 = v := by
    rw [hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  have h194 : c2.nreg 194 = w := by
    rw [hfr2.2.1 194 (by omega) (by omega)]; config_simp; exact hw
  have e3 := Exec.copyN (P := P) e2.wb_right 189 194
  have hS3 : LCTE B n F (node leaf v leaf dv :: rest1)
      { c2 with nreg := upd c2.nreg 189 (c2.nreg 194) } :=
    ⟨hS2.inv, hS2.rep, hS2.bnd, by config_simp; exact hS2.hn⟩
  -- `w` is not in the tree of `v`
  have hwv : w ∉ nodes (node leaf v leaf dv) := by
    intro hm
    obtain ⟨c', k', lw, dw, -, hS', -, -, -, -, -, -⟩ := access_execE (P := P) B n e3.wb_right hW hS3
      (by config_simp; exact h194) hwn (gb := []) (ga := rest1) rfl hm
    have hperm := nodes_perm_of_inv B n (gb := []) (ga := rest1) hS3.inv hS'.inv
    have hvT' : v ∈ nodes (node lw w leaf dw) := hperm.mem_iff.mpr (by simp)
    have hh := top_root B n hS'.inv hS'.rep hvT' hp
    have hrp := rootPath_top B n hS'.inv hS'.rep (gb := []) (ga := [] ++ rest1) rfl
      (xs := seq lw) (v := w) (by simp)
    apply hroot
    rw [findRoot, hrp]
    simp only [seq_node, seq_leaf] at hh
    rcases hq : seq lw with _ | ⟨a, L⟩
    · rw [hq] at hh; simp at hh; simp [hh]
    · rw [hq] at hh; simp at hh; simp [hh, List.getLastD, List.getLast?_reverse]
  -- access `w` in its own tree
  obtain ⟨gb', ga', T1, hG1, hwT⟩ : ∃ gb' ga' T1, rest1 = gb' ++ T1 :: ga' ∧ w ∈ nodes T1 := by
    have hm : w ∈ nodesL (node leaf v leaf dv :: rest1) := (hS2.inv.cover w).mpr hwn
    simp only [nodesL_cons, List.mem_append] at hm
    rcases hm with hm | hm
    · exact absurd hm hwv
    · obtain ⟨T, hT, hu⟩ := mem_nodesL_iff.mp hm
      obtain ⟨gb', ga', rfl⟩ := List.append_of_mem hT
      exact ⟨gb', ga', T, rfl, hu⟩
  obtain ⟨c4, k4, lw, dw, e4, hS4, hmf4, hfr4, h189', hk4, hfp4, -⟩ := access_execE (P := P) B n
    e3.wb_right hW hS3 (by config_simp; exact h194) hwn (gb := node leaf v leaf dv :: gb') (ga := ga')
    (by rw [hG1]; rfl) hwT
  have hp4 : (node lw w leaf dw :: ((node leaf v leaf dv :: gb') ++ ga')).Perm
      (node lw w leaf dw :: node leaf v leaf dv :: (gb' ++ ga')) := List.Perm.refl _
  obtain ⟨I5, R5, F5, hpot5, P5⟩ := link_okE B n hS4.inv hS4.rep rfl rfl
  have h193' : c4.nreg 193 = v := by
    rw [hfr4.2.1 193 (by omega) (by omega)]; config_simp; exact h193
  have h194' : c4.nreg 194 = w := by
    rw [hfr4.2.1 194 (by omega) (by omega)]; config_simp; exact h194
  have hblk : ∃ c5 k5, Exec P W (block (st B 193 0 194 ++ st B 193 4 194)) c4 c5 k5 ∧ k5 ≤ 10 ∧
      mem c5 = linkM B v w (mem c4) ∧ FrK 197 c4 c5 ∧ c5.nreg 193 = v ∧ c5.nreg 194 = w ∧
      c5.nreg 151 = c4.nreg 151 := by
    have hw4 := e4.wb_right
    simp only [st, ad, List.cons_append, List.nil_append, List.append_assoc]
    exec_block
    any_goals (config_simp; (try simp only [h193']); omega)
    refine ⟨by omega, ?_, ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩,
      by config_simp; exact h193', by config_simp; exact h194', by config_simp⟩
    · simp only [mem, linkM, setFpar]; config_simp; rw [h193', h194']; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
  obtain ⟨c5, k5, e5, hk5, m5, f5, s193, s194, s151⟩ := hblk
  have hb5 : Bnd B n (mem c5) := by
    rw [m5]; refine hS4.bnd.of fun a => ?_
    simp only [linkM, setFpar, upd_apply]
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr hwn.le
  refine ⟨c5, 1 + (k2 + (1 + (k4 + k5))), _, .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    ⟨m5 ▸ I5, m5 ▸ R5, hb5, by rw [s151]; exact hS4.hn⟩,
    by rw [m5]; exact (hmf2.trans B n hmf4).trans B n F5, ?_, s193, s194, ?_, fun u => ?_⟩
  · have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    have g3 : FrK 197 c2 { c2 with nreg := upd c2.nreg 189 (c2.nreg 194) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    exact g1.trans ((hfr2.mono (by omega)).trans (g3.trans ((hfr4.mono (by omega)).trans f5)))
  · simp only [List.cons_append] at hk4
    simp only [List.append_eq] at hpot5 ⊢
    omega
  · rw [m5, P5, hfp4]
    have : fpar B (mem { c2 with nreg := upd c2.nreg 189 (c2.nreg 194) }) u = fpar B (mem c2) u := rfl
    rw [this, hfp2]; rfl

theorem opLink_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCT B n F G c) {v w : ℕ} (hv : c.nreg 193 = v)
    (hw : c.nreg 194 = w) (hvn : v < n) (hwn : w < n) (hp : F.par v = n)
    (hroot : findRoot F n w ≠ v) :
    ∃ c' k G', Exec P W (opLinkS B) c c' k ∧ LCT B n (link F v w) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = w ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 311600 * Nat.log 2 n + 42100 := by
  obtain ⟨c', k, G', e, hS', h1, h2, h3, h4, h5, hfp⟩ :=
    opLink_execE (P := P) B n hc hW hS.toE hv hw hvn hwn hp hroot
  refine ⟨c', k, G', e, ⟨hS'.inv, ⟨hS'.rep, fun u hu => ?_⟩, hS'.bnd, hS'.hn⟩, h1, h2, h3, h4, h5⟩
  rw [hfp]; simp only [link]; split_ifs
  · rfl
  · exact hS.rep.fpar u hu

end

/-! ### Evert, the queries on the second values, and the parent from the access -/

/-- `F := evert F n v`, `v = r193`: the access of `v`, then the flip of `v`. -/
def opEvertS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <| .seq (block [.copyN 173 189]) (flipS B)

/-- The queries on the second values at `v = r193`: `r196 := ` the argmin and real `r195 := ` the
minimum of the second values on the root path, real `r196 := pathSum2 v`. -/
def opQuery2S (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  block (ld B 196 189 8 ++ ldR B 195 189 7 ++ ldR B 197 189 6 ++ [.addR 195 195 197] ++
    ldR B 196 189 8 ++ ldR B 198 189 4 ++ [.mulR 198 197 198, .addR 196 196 198])

/-- `r195 := F.par v`, `v = r193`, read from the access: the rightmost node of the left subtree
of `v` (`n` if there is none). -/
def opParentAccS (B : ℕ) : Stmt :=
  .seq (.instr (.copyN 189 193)) <| .seq (accessS B) <|
  .seq (block (ld B 192 189 1 ++ [.copyN 195 151])) <|
  .ifLtN 192 151 (block (ld B 195 192 6)) .skip

section
variable {P : Input} {W : ℕ}

/-- **Evert on the machine.** -/
theorem opEvert_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opEvertS B) c c' k ∧ LCTE B n (evert F n v) G' c' ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧
      c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21300 := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, -, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  obtain ⟨I3, R3, F3, hpot3⟩ := evert_okE B n hS2.inv hS2.rep rfl
  have e3 := Exec.copyN (P := P) e2.wb_right 173 189
  have e3b := Exec.block_cons e3 (Exec.block_nil e3.wb_right)
  obtain ⟨c4, k4, e4, hk4, m4, f4, s173, -⟩ := flipS_exec (P := P) B n e3b.wb_right hW (u := v)
    (by config_simp; exact h189) hvn.le
  have hm4 : mem c4 = evertM B v (mem c2) := m4
  have g3 : FrK 197 c2 { c2 with nreg := upd c2.nreg 173 (c2.nreg 189) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by config_simp; rw [upd_ne_of _ _ _ (by omega)], rfl⟩
  have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by omega, rfl⟩
  have fr : FrK 197 c c4 := g1.trans ((hfr2.mono (by omega)).trans (g3.trans (f4.mono (by omega))))
  refine ⟨c4, 1 + (k2 + (1 + k4)), _, .seq e1 (.seq e2 (.seq e3b e4)),
    ⟨hm4 ▸ I3, hm4 ▸ R3, hm4 ▸ hS2.bnd.flipM hvn.le, ?_⟩, ?_, fr, ?_, ?_, ?_⟩
  · rw [(fr.1 151 (by omega)).1]; exact hS.hn
  · rw [hm4]; exact hmf2.trans B n F3
  · rw [f4.2.1 193 (by omega) (by omega)]; config_simp
    rw [hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  · rw [f4.2.1 194 (by omega) (by omega)]; config_simp
    rw [hfr2.2.1 194 (by omega) (by omega)]; config_simp
  · rw [hpot3]; omega

theorem opQuery2_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ} (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opQuery2S B) c c' k ∧ LCTE B n F G' c' ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.rreg 196 = pathSum2 F n v ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, -, -⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  obtain ⟨-, -, -, hmin2, hsum2⟩ := query_top B n hS2.inv hS2.rep rfl
  have hblk : ∃ c3 k3, Exec P W (block (ld B 196 189 8 ++ ldR B 195 189 7 ++ ldR B 197 189 6 ++
      [.addR 195 195 197] ++ ldR B 196 189 8 ++ ldR B 198 189 4 ++
      [.mulR 198 197 198, .addR 196 196 198])) c2 c3 k3 ∧ k3 ≤ 40 ∧ mem c3 = mem c2 ∧
      c3.nreg 196 = am2 B (mem c2) v ∧
      c3.rreg 195 = minA2 B (mem c2) v ∧ c3.rreg 196 = sumA2 B (mem c2) v ∧ FrK 197 c2 c3 ∧
      c3.nreg 193 = c2.nreg 193 ∧ c3.nreg 194 = c2.nreg 194 ∧ c3.nreg 151 = c2.nreg 151 := by
    have hw2 := e2.wb_right
    simp only [ld, ldR, ad, List.cons_append, List.nil_append, List.append_assoc]
    exec_block
    any_goals (config_simp; (try simp only [h189]); omega)
    refine ⟨by omega, rfl, ?_, ?_, ?_, ⟨fun r hr => ?_, fun r h1 h2 => ?_, rfl⟩, ?_, ?_, ?_⟩
    · config_simp; rw [h189]; rfl
    · config_simp; rw [h189]; rfl
    · config_simp; rw [h189]; rfl
    · config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
      try exact ⟨trivial, trivial⟩
    · omega
    · config_simp
    · config_simp
    · config_simp
  obtain ⟨c3, k3, e3, hk3, m3, r196, q195, q196, f3, s193, s194, s151⟩ := hblk
  refine ⟨c3, 1 + (k2 + k3), _, .seq e1 (.seq e2 e3), ⟨m3 ▸ hS2.inv, m3 ▸ hS2.rep, m3 ▸ hS2.bnd,
    by rw [s151]; exact hS2.hn⟩, by rw [r196, hmin2], by rw [q195, hmin2], by rw [q196, hsum2],
    m3 ▸ hmf2, ?_, ?_, ?_, by omega⟩
  · have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
      ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
        fun r h1 h2 => by omega, rfl⟩
    exact g1.trans ((hfr2.mono (by omega)).trans f3)
  · rw [s193, hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  · rw [s194, hfr2.2.1 194 (by omega) (by omega)]; config_simp

theorem opParentAcc_exec (B n : ℕ) {c : Config} (hc : WordsBounded W c)
    (hW : B + 16 * (n + 1) ≤ W) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {v : ℕ}
    (hv : c.nreg 193 = v) (hvn : v < n) :
    ∃ c' k G', Exec P W (opParentAccS B) c c' k ∧ LCTE B n F G' c' ∧ c'.nreg 195 = F.par v ∧
      MemFrame B n (mem c) (mem c') ∧ FrK 197 c c' ∧ c'.nreg 193 = v ∧ c'.nreg 194 = c.nreg 194 ∧
      k + 16400 * potL G' ≤ 16400 * potL G + 147600 * Nat.log 2 n + 21100 := by
  have e1 := Exec.copyN (P := P) hc 189 193
  obtain ⟨gb, ga, T0, hG, hvT⟩ := hS.split hvn
  have hS1 : LCTE B n F G { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨hS.inv, hS.rep, hS.bnd, by config_simp; exact hS.hn⟩
  obtain ⟨c2, k2, l, dv, e2, hS2, hmf2, hfr2, h189, hk2, -, hrv⟩ := access_execE (P := P) B n
    e1.wb_right hW hS1 (by config_simp; exact hv) hvn hG hvT
  have hpar := parent_top B n hS2.inv hS2.rep rfl hrv
  have hb2 := hS2.bnd
  obtain ⟨-, la, -, -, -, -⟩ := hb2.get hvn.le
  have la' := la
  simp only [lc, mem, adr] at la'
  have hn2 := hS2.hn
  have hrest : ∃ c' k, Exec P W (.seq (block (ld B 192 189 1 ++ [.copyN 195 151]))
      (.ifLtN 192 151 (block (ld B 195 192 6)) .skip)) c2 c' k ∧ k ≤ 20 ∧ mem c' = mem c2 ∧
      c'.nreg 195 = F.par v ∧ FrK 197 c2 c' ∧ c'.nreg 151 = n ∧ c'.nreg 193 = c2.nreg 193 ∧
      c'.nreg 194 = c2.nreg 194 := by
    have hw2 := e2.wb_right
    refine spec_seq ?_
    simp only [ld, ad, List.cons_append, List.nil_append]
    exec_block
    any_goals (config_simp; (try simp only [h189]); omega)
    refine spec_gen fun c3 hc3 => ?_
    have hw3 : WordsBounded W c3 := hc3 ▸ ‹WordsBounded W _›
    have m3 : mem c3 = mem c2 := by rw [hc3]; rfl
    have r192 : c3.nreg 192 = lc B (mem c2) v := by rw [hc3]; config_simp; rw [h189]; rfl
    have r195 : c3.nreg 195 = n := by rw [hc3]; config_simp; exact hn2
    have r151 : c3.nreg 151 = n := by rw [hc3]; config_simp; exact hn2
    have f3 : FrK 197 c2 c3 := by
      rw [hc3]
      refine ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩
      config_simp
      simp (disch := omega) only [upd_out _ _ _ hr]
    have r193 : c3.nreg 193 = c2.nreg 193 := by rw [hc3]; config_simp
    have r194 : c3.nreg 194 = c2.nreg 194 := by rw [hc3]; config_simp
    clear hc3
    by_cases hl : lc B (mem c2) v < n
    · refine spec_ifLtN_true (by rw [r192, r151]; exact hl) ?_
      have hl' : c2.nmem (v * 16 + (B + 1)) < n := hl
      exec_block
      any_goals (config_simp; (try simp only [r192]); (try simp only [lc, mem, adr]); omega)
      refine ⟨by omega, m3, ?_, ?_, by config_simp; exact r151, by config_simp; exact r193,
        by config_simp; exact r194⟩
      · config_simp; rw [r192, hpar, ite_of_pos hl, ← m3]; rfl
      · refine f3.trans ⟨fun r hr => ?_, fun r h1 h2 => by omega, rfl⟩
        config_simp
        simp (disch := omega) only [upd_out _ _ _ hr]
    · refine spec_ifLtN_false (by rw [r192, r151]; exact hl) (spec_skip hw3 ?_)
      exact ⟨by omega, m3, by rw [r195, hpar, ite_of_neg hl], f3, r151, r193, r194⟩
  obtain ⟨c3, k3, e3, hk3, m3, r195, f3, r151, r193, r194⟩ := hrest
  have g1 : FrK 197 c { c with nreg := upd c.nreg 189 (c.nreg 193) } :=
    ⟨fun r hr => by config_simp; rw [upd_out _ _ _ hr (by omega)],
      fun r h1 h2 => by omega, rfl⟩
  have fr3 : FrK 197 c c3 := g1.trans ((hfr2.mono (by omega)).trans f3)
  refine ⟨c3, 1 + (k2 + k3), _, .seq e1 (.seq e2 e3), ⟨m3 ▸ hS2.inv, m3 ▸ hS2.rep, m3 ▸ hS2.bnd,
    r151⟩, r195, m3 ▸ hmf2, fr3, ?_, ?_, by omega⟩
  · rw [r193, hfr2.2.1 193 (by omega) (by omega)]; config_simp; exact hv
  · rw [r194, hfr2.2.1 194 (by omega) (by omega)]; config_simp

end

end DynTree

end PlanarFlow
