module

public import PlanarFlow.NegSSSP.NdFullB

/-!
# The full branch: the vertex numbering of the piece map in the node's numbering

The positions of the sources that the side arrays leave are indexed by the numbering
`vn ∘ ψ` of the vertices of the piece map of `K`; the node reads them indexed by its own
numbering `ν`. The re-indexing array `J[ν x] = vn (ψ x)` (`x` a vertex of `K`) is a scatter
over the tails and heads of the darts of `K`:

* `blV_cons`: the scatter's value at `j` is `v` when some flagged entry has index `j` and every
  flagged entry with index `j` has value `v`;
* **`fbJ_val`**: with the indices `X'[i] = ν (tail (en i))`, `X'[m + i] = ν (head (en i))`, the
  flags of `K` twice, and the values `vn (ψ (tail (en i)))`, `vn (ψ (head (en i)))` (read from the
  plain encoding of the piece map: `vn ∘ vert` at the index array, `vn ∘ vert ∘ α` through
  the `α` column), the scatter is `vn (ψ x)` at `ν x` for every vertex `x` of `K`;
* `gaS a b c d = cpRegs … ; gaProg` (a gather from four registers), `gaS_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  PlanarSeparator.MillerProg

universe u v w

variable {P : Input} {W : ℕ}

/-- **A consistent scatter.** -/
theorem blV_cons {mem : ℕ → ℕ} {Fb Xb Rb j v : ℕ} :
    ∀ n, (∀ h < n, mem (Fb + h) ≠ 0 → mem (Xb + h) = j → mem (Rb + h) = v) →
      (∃ h < n, mem (Fb + h) ≠ 0 ∧ mem (Xb + h) = j) → blV mem Fb Xb Rb n j = v
  | 0, _, ⟨h, hh, _⟩ => absurd hh (by omega)
  | n + 1, hc, ⟨h, hh, hf, hx⟩ => by
    simp only [blV]
    by_cases hn : mem (Fb + n) ≠ 0 ∧ mem (Xb + n) = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
      exact hc n (by omega) hn.1 hn.2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
      have hlt : h < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hh with h' | rfl
        · exact h'
        · exact absurd ⟨hf, hx⟩ hn
      exact blV_cons n (fun h' hh' => hc h' (by omega)) ⟨h, hlt, hf, hx⟩

/-- The registers of a gather. -/
def gaL (a b c d : ℕ) : List (ℕ × ℕ) := [(2105, a), (2106, b), (2107, c), (2108, d)]

/-- **A gather from four registers.** -/
def gaS (a b c d : ℕ) : Stmt := .seq (cpRegs (gaL a b c d)) gaProg

theorem gaS_natOnly (a b c d : ℕ) : Klein.natOnly (gaS a b c d) = true := by
  have h1 := cpRegs_natOnly (gaL a b c d)
  simp [gaS, Klein.natOnly, h1, gaProg_natOnly]

theorem gaL_ok {a b c d : ℕ} (ha : a < 2105 ∨ 2108 < a) (hb : b < 2105 ∨ 2108 < b)
    (hc : c < 2105 ∨ 2108 < c) (hd : d < 2105 ∨ 2108 < d) :
    cpOK (gaL a b c d) = true ∧ cpSrc (gaL a b c d) = true := by
  constructor
  · simp [gaL, cpOK]
  · simp [gaL, cpSrc]; omega

theorem gaL_frame {a b c d r : ℕ} (h : r < 2105 ∨ 2108 < r) : r ∉ (gaL a b c d).map (·.1) := by
  simp only [gaL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **A gather from four registers** `OUT[i] := IN[J[i]]`. -/
theorem gaS_exec {a b c d n INb Jb Ob : ℕ} (ha : a < 2105 ∨ 2108 < a) (hb : b < 2105 ∨ 2108 < b)
    (hc : c < 2105 ∨ 2108 < c) (hd : d < 2105 ∨ 2108 < d) (c₀ : Config)
    (hw : WordsBounded W c₀) (ra : c₀.nreg a = n) (rb : c₀.nreg b = INb) (rc : c₀.nreg c = Jb)
    (rd : c₀.nreg d = Ob) (h1 : 1 ≤ W) (wO : Ob + n ≤ W) (wJ : Jb + n ≤ W)
    (dJ : Ob + n ≤ Jb ∨ Jb + n ≤ Ob)
    (hI : ∀ i < n, INb + c₀.nmem (Jb + i) ≤ W ∧
      (INb + c₀.nmem (Jb + i) < Ob ∨ Ob + n ≤ INb + c₀.nmem (Jb + i))) :
    ∃ c' t, Exec P W (gaS a b c d) c₀ c' t ∧ t ≤ 9 * n + 8 ∧
      (∀ i < n, c'.nmem (Ob + i) = c₀.nmem (INb + c₀.nmem (Jb + i))) ∧
      (∀ x, (x < Ob ∨ Ob + n ≤ x) → c'.nmem x = c₀.nmem x) ∧
      (∀ r, (r < 2105 ∨ 2113 < r) → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  obtain ⟨ok, sr⟩ := gaL_ok ha hb hc hd
  obtain ⟨c₁, e₁, g₁, f₁, m₁, rr₁, rm₁, o₁⟩ := cpRegs_exec (P := P) (W := W) _ ok sr c₀ hw
  simp only [gaL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₁
  obtain ⟨u5, u6, u7, u8⟩ := g₁
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, m₂, f₂, rr₂, rm₂, o₂⟩ := gaProg_exec (P := P) (n := n) (INb := INb)
    (Jb := Jb) (Ob := Ob) c₁ e₁.wb_right (by rw [u5, ra]) (by rw [u6, rb]) (by rw [u7, rc])
    (by rw [u8, rd]) h1 wO wJ dJ (fun i hi => by rw [m₁]; exact hI i hi)
  refine ⟨c₂, (gaL a b c d).length + t₂, .seq e₁ e₂, by simp [gaL]; omega,
    fun i hi => by rw [v₂ i hi, m₁], fun x hx => by rw [m₂ x hx, m₁],
    fun r hr => by rw [f₂ r (by omega), f₁ r (gaL_frame (by omega))], by rw [rr₂, rr₁],
    by rw [rm₂, rm₁], by rw [o₂, o₁]⟩

theorem blV_le {mem : ℕ → ℕ} {Fb Xb Rb B : ℕ} :
    ∀ n, (∀ h < n, mem (Rb + h) ≤ B) → ∀ j, blV mem Fb Xb Rb n j ≤ B
  | 0, _, _ => Nat.zero_le _
  | n + 1, hR, j => by
    simp only [blV]
    split_ifs
    · exact hR n (by omega)
    · exact blV_le n (fun h hh => hR h (by omega)) j

/-- The bases of the re-indexing (scratch `2296`, `2297`). -/
def fbJL : List PcStep :=
  [(2260, [(1, .v 3003), (130, .v 2475)], 0),
    (2261, [(1, .v 3003), (130, .v 2475), (1, .v 2474)], 0),
    (2262, [(1, .v 3003), (132, .v 2475)], 0),
    (2263, [(1, .v 3003), (132, .v 2475), (1, .v 2474)], 0),
    (2264, [(1, .v 3003), (134, .v 2475)], 0),
    (2265, [(1, .v 3003), (134, .v 2475), (1, .v 2474)], 0),
    (2266, [(1, .v 3003), (136, .v 2475)], 0), (2267, [(1, .v 3003), (138, .v 2475)], 0),
    (2268, [(1, .v 2217), (3, .v 960)], 0), (2269, [(2, .v 2474)], 0)]

set_option maxRecDepth 100000 in
theorem fbJL_wf : pcWF 2296 9600 fbJL = true := by kernel_rfl

theorem fbJL_cost : pcCost fbJL = 118 := by kernel_rfl

set_option maxHeartbeats 1000000 in
theorem fbJL_eqs {g : ℕ → ℕ} (h : PcSol fbJL g) :
    g 2260 = g 3003 + 130 * g 2475 ∧ g 2261 = g 3003 + 130 * g 2475 + g 2474 ∧
    g 2262 = g 3003 + 132 * g 2475 ∧ g 2263 = g 3003 + 132 * g 2475 + g 2474 ∧
    g 2264 = g 3003 + 134 * g 2475 ∧ g 2265 = g 3003 + 134 * g 2475 + g 2474 ∧
    g 2266 = g 3003 + 136 * g 2475 ∧ g 2267 = g 3003 + 138 * g 2475 ∧
    g 2268 = g 2217 + 3 * g 960 ∧ g 2269 = 2 * g 2474 := by
  simp only [PcSol, fbJL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero] at h
  omega

theorem fbJL_bound {g : ℕ → ℕ} (h : PcSol fbJL g) {W : ℕ}
    (h1 : g 3003 + 140 * g 2475 ≤ W) (h2 : g 2474 ≤ g 2475) (h3 : g 2217 + 3 * g 960 ≤ W) :
    ∀ s ∈ fbJL, hpSum g s.2.1 ≤ W := by
  intro s hs
  simp only [fbJL, List.mem_cons, List.not_mem_nil, or_false] at hs
  have E := fbJL_eqs h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, add_zero]
    omega

theorem fbJL_notDst {r : ℕ} (h : r < 2260 ∨ (2269 < r ∧ r ≠ 2296 ∧ r ≠ 2297)) :
    r ∉ pcDsts fbJL := by
  simp only [pcDsts, fbJL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

/-- The registers of the scatter of the re-indexing. -/
def fbJB : List (ℕ × ℕ) :=
  [(2776, 2464), (2777, 2267), (2778, 2269), (2779, 2262), (2780, 2260), (2781, 2264)]

theorem fbJB_ok : cpOK fbJB = true ∧ cpSrc fbJB = true := by
  constructor <;> decide

theorem fbJB_frame {r : ℕ} (h : r < 2776 ∨ 2781 < r) : r ∉ fbJB.map (·.1) := by
  simp only [fbJB, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **The re-indexing array** `J[ν x] = vn (ψ x)` at `h + 138k`. -/
def fbJ : Stmt :=
  .seq (pcProg 2296 fbJL) <| .seq (gaS 2474 3003 2203 2260) <| .seq (gaS 2474 2214 2203 2261) <|
  .seq (gaS 2474 2215 2203 2262) <| .seq (gaS 2474 2215 2203 2263) <|
  .seq (gaS 2474 2268 2216 2264) <| .seq (gaS 2474 2217 2216 2266) <|
  .seq (gaS 2474 2268 2266 2265) <| .seq (cpRegs fbJB) blProg

/-- The cost of `fbJ`. -/
def fbJCost (k : ℕ) : ℕ := 118 + 7 * (9 * k + 8) + 6 + (5 * (2 * k) + 14 * (2 * k) + 10)

section Sem

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The re-indexing array**: the scatter of the vertex numbers of the piece map over the
tails and heads of the darts of `K` (see the module docstring). -/
theorem fbJ_val {K Pc : Finset D} {m : ℕ} {en : ℕ → D} (hen : IsEnum m en Pc) (hKP : K ⊆ Pc)
    {ν : V → ℕ} {ι : ℕ → V} (hι : ∀ x ∈ verts N Pc, ι (ν x) = x) {nV : ℕ}
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (ψ : V → SVert (kσ N K) (rcl N K))
    {mem : ℕ → ℕ} {Fb Xb Rb : ℕ}
    (hX : ∀ i < m, mem (Xb + i) = ν (N.tail (en i)) ∧ mem (Xb + (m + i)) = ν (N.head (en i)))
    (hF : ∀ i < m, (mem (Fb + i) ≠ 0 ↔ en i ∈ K) ∧ (mem (Fb + (m + i)) ≠ 0 ↔ en i ∈ K))
    (hR : ∀ i < m, en i ∈ K → mem (Rb + i) = vn (ψ (N.tail (en i))) ∧
      mem (Rb + (m + i)) = vn (ψ (N.head (en i))))
    {x : V} (hx : x ∈ verts N K) : blV mem Fb Xb Rb (2 * m) (ν x) = vn (ψ x) := by
  have hxP : x ∈ verts N Pc := verts_mono hKP hx
  apply blV_cons
  · intro h hh hf hxh
    by_cases hm : h < m
    · have hK := (hF h hm).1.1 hf
      rw [(hX h hm).1] at hxh
      have ht : N.tail (en h) ∈ verts N Pc := tail_mem_verts (hen.mem h hm)
      have e : N.tail (en h) = x := by rw [← hι _ ht, hxh, hι _ hxP]
      rw [(hR h hm hK).1, e]
    · obtain ⟨i, rfl⟩ : ∃ i, h = m + i := ⟨h - m, by omega⟩
      have hi : i < m := by omega
      have hK := (hF i hi).2.1 hf
      rw [(hX i hi).2] at hxh
      have ht : N.head (en i) ∈ verts N Pc := head_mem_verts (hen.mem i hi)
      have e : N.head (en i) = x := by rw [← hι _ ht, hxh, hι _ hxP]
      rw [(hR i hi hK).2, e]
  · obtain ⟨d, hd, hdx⟩ := mem_verts_iff'.1 hx
    obtain ⟨i, hi, rfl⟩ := hen.surj d (hKP hd)
    rcases hdx with h | h
    · exact ⟨i, by omega, (hF i hi).1.2 hd, by rw [(hX i hi).1, h]⟩
    · exact ⟨m + i, by omega, (hF i hi).2.2 hd, by rw [(hX i hi).2, h]⟩

set_option maxHeartbeats 4000000 in
/-- The end of `fbJ`: the scatter of the re-indexing. -/
theorem fbJ_tail {K Pc : Finset D} {m k w nV h Ws : ℕ} {en : ℕ → D} (hen : IsEnum m en Pc)
    (hKP : K ⊆ Pc) {ν : V → ℕ} {ι : ℕ → V} (hι : ∀ x ∈ verts N Pc, ι (ν x) = x)
    (hνw : ∀ x ∈ verts N Pc, ν x < w) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (ψ : V → SVert (kσ N K) (rcl N K)) (c : Config) (hc : WordsBounded W c)
    (r64 : c.nreg 2464 = w) (r67 : c.nreg 2267 = h + 138 * k) (r69 : c.nreg 2269 = 2 * m)
    (r62 : c.nreg 2262 = h + 132 * k) (r60 : c.nreg 2260 = h + 130 * k)
    (r64' : c.nreg 2264 = h + 134 * k)
    (hX : ∀ i < m, c.nmem (h + 130 * k + i) = ν (N.tail (en i)) ∧
      c.nmem (h + 130 * k + (m + i)) = ν (N.head (en i)))
    (hF : ∀ i < m, (c.nmem (h + 132 * k + i) ≠ 0 ↔ en i ∈ K) ∧
      (c.nmem (h + 132 * k + (m + i)) ≠ 0 ↔ en i ∈ K))
    (hR : ∀ i < m, en i ∈ K → c.nmem (h + 134 * k + i) = vn (ψ (N.tail (en i))) ∧
      c.nmem (h + 134 * k + (m + i)) = vn (ψ (N.head (en i))))
    (hRb : ∀ i < 2 * m, c.nmem (h + 134 * k + i) ≤ Ws)
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hW : h + 140 * k ≤ W) (h1 : 1 ≤ W) :
    ∃ c' t, Exec P W (.seq (cpRegs fbJB) blProg) c c' t ∧ t ≤ 6 + (5 * (2 * k) + 14 * (2 * k) + 10) ∧
      (∀ x ∈ verts N K, c'.nmem (h + 138 * k + ν x) = vn (ψ x)) ∧
      (∀ j < w, c'.nmem (h + 138 * k + j) ≤ Ws) ∧
      (∀ a, (a < h + 138 * k ∨ h + 138 * k + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2776 ∨ 2788 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ok, sr⟩ := fbJB_ok
  obtain ⟨c₁, e₁, g₁, f₁, m₁, rr₁, rm₁, o₁⟩ := cpRegs_exec (P := P) (W := W) _ ok sr c hc
  simp only [fbJB, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₁
  obtain ⟨u76, u77, u78, u79, u80, u81⟩ := g₁
  have hX2 : ∀ i < 2 * m, c₁.nmem (h + 132 * k + i) ≠ 0 → c₁.nmem (h + 130 * k + i) < w :=
    fun i hi hf => by
      rw [m₁] at hf ⊢
      by_cases him : i < m
      · rw [(hX i him).1]; exact hνw _ (tail_mem_verts (hen.mem i him))
      · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
        rw [(hX j (by omega)).2]; exact hνw _ (head_mem_verts (hen.mem j (by omega)))
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, m₂, f₂, rr₂, rm₂, o₂⟩ := blProg_exec (P := P) (W := W) (m' := w)
    (m := 2 * m) (Kb := h + 138 * k) (Fb := h + 132 * k) (Xb := h + 130 * k)
    (Rb := h + 134 * k) c₁ e₁.wb_right (by rw [u76, r64]) (by rw [u77, r67])
    (by rw [u78, r69]) (by rw [u79, r62]) (by rw [u80, r60]) (by rw [u81, r64']) h1
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) hX2
  refine ⟨c₂, fbJB.length + t₂, .seq e₁ e₂, ?_, fun x hx => ?_, fun j hj => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · simp only [fbJB, List.length_cons, List.length_nil]; omega
  · have hxP : x ∈ verts N Pc := verts_mono hKP hx
    rw [v₂ _ (hνw x hxP), m₁]
    exact fbJ_val hen hKP hι vn ψ hX hF hR hx
  · rw [v₂ j hj, m₁]
    exact blV_le _ hRb j
  · rw [m₂ a ha, m₁]
  · rw [f₂ r hr, f₁ r (fbJB_frame (by omega))]

set_option maxHeartbeats 8000000 in
/-- **The re-indexing array on the machine** (see the module docstring). -/
theorem fbJ_exec {K Pc : Finset D} {m k m' w nV nF h d B₀ L : ℕ} {en : ℕ → D} {α σ : ℕ → ℕ}
    (he : PEnc N Pc m k en α σ) (hKP : K ⊆ Pc) {ν : V → ℕ} {ι : ℕ → V}
    (hι : ∀ x ∈ verts N Pc, ι (ν x) = x) (hνw : ∀ x ∈ verts N Pc, ν x < w)
    (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (ψ : V → SVert (kσ N K) (rcl N K))
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r75 : c.nreg 2475 = k) (r74 : c.nreg 2474 = m)
    (r64 : c.nreg 2464 = w) (r960 : c.nreg 960 = m') (R : FbRegs c h d k B₀ m' L)
    (hid : ∀ i < 2 * k, c.nmem (h + 10 * k + i) = i)
    (hT : ∀ i < m, c.nmem (h + i) = ν (N.tail (en i)))
    (hH : ∀ i < m, c.nmem (h + k + i) = ν (N.head (en i)))
    (hE : Enc (kmap N K) cn vn fn c.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m'))
    (hXm : ∀ i < k, ∀ hm : en i ∈ rcl N K, c.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hm⟩)
    (hFm : ∀ x < m, (c.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ en x ∈ K))
    (hlow : ∀ a < 2 * (B₀ + 66 * k + 35) + 2, c.nmem a ≤ B₀ + 66 * k + 35)
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k)
    (hBh : 2 * (B₀ + 66 * k + 35) + 2 ≤ h) (hW : h + 140 * k ≤ W) (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W fbJ c c' t ∧ t ≤ fbJCost k ∧
      (∀ x ∈ verts N K, c'.nmem (h + 138 * k + ν x) = vn (ψ x)) ∧
      (∀ j < w, c'.nmem (h + 138 * k + j) ≤ B₀ + 66 * k + 35) ∧
      (∀ a, (a < h + 130 * k ∨ h + 140 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2105 ∨ (2113 < r ∧ r < 2260) ∨ (2269 < r ∧ r < 2296) ∨
        (2297 < r ∧ r < 2776) ∨ 2788 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set Ws := B₀ + 66 * k + 35 with hWs
  -- the bases
  obtain ⟨c₁, e₁, s₁, f₁, m₁, rr₁, rm₁, o₁⟩ := pcProg_exec (I := P) (W := W) fbJL fbJL_wf h9600
    c hc (fun g hg hs => by
      have k : ∀ r, r ∉ pcDsts fbJL → r ≠ 2296 → r ≠ 2297 → g r = c.nreg r := hg
      have a1 := k 3003 (fbJL_notDst (by omega)) (by omega) (by omega)
      have a2 := k 2475 (fbJL_notDst (by omega)) (by omega) (by omega)
      have a3 := k 2474 (fbJL_notDst (by omega)) (by omega) (by omega)
      have a4 := k 2217 (fbJL_notDst (by omega)) (by omega) (by omega)
      have a5 := k 960 (fbJL_notDst (by omega)) (by omega) (by omega)
      rw [r03] at a1; rw [r75] at a2; rw [r74] at a3; rw [R.rY] at a4; rw [r960] at a5
      exact fbJL_bound hs (by rw [a1, a2]; omega) (by rw [a3, a2]; omega)
        (by rw [a4, a5]; omega))
  have F₁ : ∀ r, r ∉ pcDsts fbJL → r ≠ 2296 → r ≠ 2297 → c₁.nreg r = c.nreg r := f₁
  have q03 : c₁.nreg 3003 = h := (F₁ 3003 (fbJL_notDst (by omega)) (by omega) (by omega)).trans r03
  have q75 : c₁.nreg 2475 = k := (F₁ 2475 (fbJL_notDst (by omega)) (by omega) (by omega)).trans r75
  have q74 : c₁.nreg 2474 = m := (F₁ 2474 (fbJL_notDst (by omega)) (by omega) (by omega)).trans r74
  have q960 : c₁.nreg 960 = m' := (F₁ 960 (fbJL_notDst (by omega)) (by omega) (by omega)).trans r960
  have q17 : c₁.nreg 2217 = B₀ + 28 * k + 3 :=
    (F₁ 2217 (fbJL_notDst (by omega)) (by omega) (by omega)).trans R.rY
  obtain ⟨E60, E61, E62, E63, E64, E65, E66, E67, E68, E69⟩ := fbJL_eqs s₁
  rw [q03, q75] at E60 E62 E64 E66 E67
  rw [q03, q75, q74] at E61 E63 E65
  rw [q17, q960] at E68
  rw [q74] at E69
  have R₁ : FbRegs c₁ h d k B₀ m' L :=
    R.of fun r h1 h2 => F₁ r (fbJL_notDst (by omega)) (by omega) (by omega)
  have L₁ : ∀ a, c₁.nmem a = c.nmem a := fun a => by rw [m₁]
  have hX' : ∀ i < m, c.nmem (B₀ + 25 * k + 3 + i) ≤ Ws := fun i hi => hlow _ (by omega)
  -- tails, heads
  obtain ⟨c₂, t₂, e₂, ht₂, v₂, m₂, f₂, rr₂, rm₂, o₂⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 3003) (c := 2203) (d := 2260) (n := m) (INb := h) (Jb := h + 10 * k)
    (Ob := h + 130 * k) (by omega) (by omega) (by omega) (by omega) c₁ e₁.wb_right q74 q03
    R₁.rra E60 (by omega) (by omega) (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₁, hid i (by omega)]; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₂ : ∀ r, (r < 2105 ∨ 2113 < r) → c₂.nreg r = c₁.nreg r := f₂
  have L₂ : ∀ a, a < h + 130 * k → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m₂ a (Or.inl ha), L₁]
  obtain ⟨c₃, t₃, e₃, ht₃, v₃, m₃, f₃, rr₃, rm₃, o₃⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2214) (c := 2203) (d := 2261) (n := m) (INb := h + k) (Jb := h + 10 * k)
    (Ob := h + 130 * k + m) (by omega) (by omega) (by omega) (by omega) c₂ e₂.wb_right
    (by rw [N₂ _ (by omega), q74]) (by rw [N₂ _ (by omega), R₁.rHh])
    (by rw [N₂ _ (by omega), R₁.rra]) (by rw [N₂ _ (by omega), E61]) (by omega) (by omega)
    (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₂ _ (by omega), hid i (by omega)]; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₃ : ∀ r, (r < 2105 ∨ 2113 < r) → c₃.nreg r = c₁.nreg r := fun r hr => by
    rw [f₃ r hr, N₂ r hr]
  have L₃ : ∀ a, a < h + 130 * k → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃ a (Or.inl (by omega)), L₂ a ha]
  -- the flags, twice
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, m₄, f₄, rr₄, rm₄, o₄⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2215) (c := 2203) (d := 2262) (n := m) (INb := B₀ + 33 * k + 3)
    (Jb := h + 10 * k) (Ob := h + 132 * k) (by omega) (by omega) (by omega) (by omega) c₃
    e₃.wb_right (by rw [N₃ _ (by omega), q74]) (by rw [N₃ _ (by omega), R₁.rFb])
    (by rw [N₃ _ (by omega), R₁.rra]) (by rw [N₃ _ (by omega), E62]) (by omega) (by omega)
    (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₃ _ (by omega), hid i (by omega)]; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₄ : ∀ r, (r < 2105 ∨ 2113 < r) → c₄.nreg r = c₁.nreg r := fun r hr => by
    rw [f₄ r hr, N₃ r hr]
  have L₄ : ∀ a, a < h + 130 * k → c₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄ a (Or.inl (by omega)), L₃ a ha]
  obtain ⟨c₅, t₅, e₅, ht₅, v₅, m₅, f₅, rr₅, rm₅, o₅⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2215) (c := 2203) (d := 2263) (n := m) (INb := B₀ + 33 * k + 3)
    (Jb := h + 10 * k) (Ob := h + 132 * k + m) (by omega) (by omega) (by omega) (by omega) c₄
    e₄.wb_right (by rw [N₄ _ (by omega), q74]) (by rw [N₄ _ (by omega), R₁.rFb])
    (by rw [N₄ _ (by omega), R₁.rra]) (by rw [N₄ _ (by omega), E63]) (by omega) (by omega)
    (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₄ _ (by omega), hid i (by omega)]; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₅ : ∀ r, (r < 2105 ∨ 2113 < r) → c₅.nreg r = c₁.nreg r := fun r hr => by
    rw [f₅ r hr, N₄ r hr]
  have L₅ : ∀ a, a < h + 130 * k → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅ a (Or.inl (by omega)), L₄ a ha]
  -- the values: tails
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, m₆, f₆, rr₆, rm₆, o₆⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2268) (c := 2216) (d := 2264) (n := m)
    (INb := B₀ + 28 * k + 3 + 3 * m') (Jb := B₀ + 25 * k + 3) (Ob := h + 134 * k) (by omega)
    (by omega) (by omega) (by omega) c₅ e₅.wb_right (by rw [N₅ _ (by omega), q74])
    (by rw [N₅ _ (by omega), E68]) (by rw [N₅ _ (by omega), R₁.rXb])
    (by rw [N₅ _ (by omega), E64]) (by omega) (by omega) (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₅ _ (by omega)]; have := hX' i hi; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₆ : ∀ r, (r < 2105 ∨ 2113 < r) → c₆.nreg r = c₁.nreg r := fun r hr => by
    rw [f₆ r hr, N₅ r hr]
  have L₆ : ∀ a, a < h + 130 * k → c₆.nmem a = c.nmem a := fun a ha => by
    rw [m₆ a (Or.inl (by omega)), L₅ a ha]
  -- the reversal column
  obtain ⟨c₇, t₇, e₇, ht₇, v₇, m₇, f₇, rr₇, rm₇, o₇⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2217) (c := 2216) (d := 2266) (n := m)
    (INb := B₀ + 28 * k + 3) (Jb := B₀ + 25 * k + 3) (Ob := h + 136 * k) (by omega)
    (by omega) (by omega) (by omega) c₆ e₆.wb_right (by rw [N₆ _ (by omega), q74])
    (by rw [N₆ _ (by omega), R₁.rY]) (by rw [N₆ _ (by omega), R₁.rXb])
    (by rw [N₆ _ (by omega), E66]) (by omega) (by omega) (by omega) (Or.inr (by omega))
    (fun i hi => by rw [L₆ _ (by omega)]; have := hX' i hi; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₇ : ∀ r, (r < 2105 ∨ 2113 < r) → c₇.nreg r = c₁.nreg r := fun r hr => by
    rw [f₇ r hr, N₆ r hr]
  have L₇ : ∀ a, a < h + 130 * k → c₇.nmem a = c.nmem a := fun a ha => by
    rw [m₇ a (Or.inl (by omega)), L₆ a ha]
  have T₇ : ∀ i < m, c₇.nmem (h + 136 * k + i) ≤ Ws := fun i hi => by
    rw [v₇ i hi, L₆ (B₀ + 25 * k + 3 + i) (by omega), L₆ _ (by have := hX' i hi; omega)]
    exact hlow _ (by have := hX' i hi; omega)
  -- the values: heads
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, m₈, f₈, rr₈, rm₈, o₈⟩ := gaS_exec (P := P) (W := W)
    (a := 2474) (b := 2268) (c := 2266) (d := 2265) (n := m)
    (INb := B₀ + 28 * k + 3 + 3 * m') (Jb := h + 136 * k) (Ob := h + 134 * k + m) (by omega)
    (by omega) (by omega) (by omega) c₇ e₇.wb_right (by rw [N₇ _ (by omega), q74])
    (by rw [N₇ _ (by omega), E68]) (by rw [N₇ _ (by omega), E66])
    (by rw [N₇ _ (by omega), E65]) (by omega) (by omega) (by omega) (Or.inl (by omega))
    (fun i hi => by have := T₇ i hi; exact ⟨by omega, Or.inl (by omega)⟩)
  have N₈ : ∀ r, (r < 2105 ∨ 2113 < r) → c₈.nreg r = c₁.nreg r := fun r hr => by
    rw [f₈ r hr, N₇ r hr]
  -- the arrays at `c₈`
  have A3 : ∀ a, (a < h + 134 * k + m ∨ h + 134 * k + m + m ≤ a) → c₈.nmem a = c₇.nmem a :=
    fun a ha => m₈ a ha
  have hX8 : ∀ i < m, c₈.nmem (h + 130 * k + i) = ν (N.tail (en i)) ∧
      c₈.nmem (h + 130 * k + (m + i)) = ν (N.head (en i)) := fun i hi => by
    have e : h + 130 * k + (m + i) = h + 130 * k + m + i := by ring
    rw [e, A3 _ (Or.inl (by omega)), A3 _ (Or.inl (by omega)), m₇ _ (Or.inl (by omega)),
      m₇ _ (Or.inl (by omega)), m₆ _ (Or.inl (by omega)), m₆ _ (Or.inl (by omega)),
      m₅ _ (Or.inl (by omega)), m₅ _ (Or.inl (by omega)), m₄ _ (Or.inl (by omega)),
      m₄ _ (Or.inl (by omega)), m₃ _ (Or.inl (by omega)), v₃ i hi, v₂ i hi,
      L₁ (h + 10 * k + i), hid i (by omega), L₁, L₂ (h + 10 * k + i) (by omega),
      hid i (by omega), L₂ _ (by omega)]
    exact ⟨hT i hi, hH i hi⟩
  have hF8 : ∀ i < m, (c₈.nmem (h + 132 * k + i) ≠ 0 ↔ en i ∈ K) ∧
      (c₈.nmem (h + 132 * k + (m + i)) ≠ 0 ↔ en i ∈ K) := fun i hi => by
    have e : h + 132 * k + (m + i) = h + 132 * k + m + i := by ring
    rw [e, A3 _ (Or.inl (by omega)), A3 _ (Or.inl (by omega)), m₇ _ (Or.inl (by omega)),
      m₇ _ (Or.inl (by omega)), m₆ _ (Or.inl (by omega)), m₆ _ (Or.inl (by omega)),
      m₅ _ (Or.inl (by omega)), v₅ i hi, v₄ i hi, L₃ (h + 10 * k + i) (by omega),
      hid i (by omega), L₃ _ (by omega), L₄ (h + 10 * k + i) (by omega), hid i (by omega),
      L₄ _ (by omega)]
    exact ⟨hFm i hi, hFm i hi⟩
  have hR8 : ∀ i < m, en i ∈ K → c₈.nmem (h + 134 * k + i) = vn (ψ (N.tail (en i))) ∧
      c₈.nmem (h + 134 * k + (m + i)) = vn (ψ (N.head (en i))) := fun i hi hK => by
    have hr : en i ∈ rcl N K := subset_rcl K hK
    have hk : i < k := by omega
    have e : h + 134 * k + (m + i) = h + 134 * k + m + i := by ring
    have x1 : c.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hr⟩ := hXm i hk hr
    have x2 : c.nmem (B₀ + 28 * k + 3 + cn ⟨en i, hr⟩) =
        cn ((kmap N K).α ⟨en i, hr⟩) := hE.α _
    have x3 : ∀ y, c.nmem (B₀ + 28 * k + 3 + 3 * m' + cn y) = vn ((kmap N K).vert y) :=
      fun y => hE.vn y
    have hy : ∀ y : SDart (rcl N K), (cn y : ℕ) < m' := fun y => (cn y).2
    refine ⟨?_, ?_⟩
    · rw [A3 _ (Or.inl (by omega)), m₇ _ (Or.inl (by omega)), v₆ i hi,
        L₅ (B₀ + 25 * k + 3 + i) (by omega), x1, L₅ _ (by have := hy ⟨en i, hr⟩; omega), x3,
        ← hψ]
    · rw [e, v₈ i hi, v₇ i hi, L₆ (B₀ + 25 * k + 3 + i) (by omega), x1,
        L₆ _ (by have := hy ⟨en i, hr⟩; omega), x2,
        L₇ _ (by have := hy ((kmap N K).α ⟨en i, hr⟩); omega), x3, ← hψ, pieceSep_α]
      rfl
  have hRb8 : ∀ i < 2 * m, c₈.nmem (h + 134 * k + i) ≤ Ws := fun i hi => by
    by_cases him : i < m
    · rw [A3 _ (Or.inl (by omega)), m₇ _ (Or.inl (by omega)), v₆ i him,
        L₅ (B₀ + 25 * k + 3 + i) (by omega)]
      have := hX' i him
      rw [L₅ _ (by omega)]
      exact hlow _ (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
      have hj : j < m := by omega
      have e : h + 134 * k + (m + j) = h + 134 * k + m + j := by ring
      rw [e, v₈ j hj]
      have := T₇ j hj
      rw [L₇ _ (by omega)]
      exact hlow _ (by omega)
  obtain ⟨c₉, t₉, e₉, ht₉, J₉, Jb₉, m₉, f₉, rr₉, rm₉, o₉⟩ := fbJ_tail (P := P) (W := W)
    he.enumP hKP hι hνw vn ψ c₈ e₈.wb_right
    (by rw [N₈ _ (by omega), F₁ _ (fbJL_notDst (by omega)) (by omega) (by omega), r64])
    (by rw [N₈ _ (by omega), E67]) (by rw [N₈ _ (by omega), E69])
    (by rw [N₈ _ (by omega), E62]) (by rw [N₈ _ (by omega), E60])
    (by rw [N₈ _ (by omega), E64]) hX8 hF8 hR8 hRb8 hmk hw hW (by omega)
  refine ⟨c₉, pcCost fbJL + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))), ?_,
    J₉, Jb₉, fun a ha => ?_, fun r hr => ?_, by rw [rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [fbJL_cost]; unfold fbJCost
    clear * - ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ hmk; omega
  · rcases ha with ha | ha
    · rw [m₉ a (Or.inl (by omega)), A3 a (Or.inl (by omega)), L₇ a ha]
    · rw [m₉ a (Or.inr (by omega)), A3 a (Or.inr (by omega)), m₇ a (Or.inr (by omega)),
        m₆ a (Or.inr (by omega)), m₅ a (Or.inr (by omega)), m₄ a (Or.inr (by omega)),
        m₃ a (Or.inr (by omega)), m₂ a (Or.inr (by omega)), L₁]
  · rw [f₉ r (by omega), N₈ r (by omega), F₁ r (fbJL_notDst (by omega)) (by omega) (by omega)]

end Sem

end NegSSSP

end PlanarFlow
