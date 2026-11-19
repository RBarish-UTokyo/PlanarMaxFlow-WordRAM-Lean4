module

public import PlanarFlow.NegSSSP.NdFullA
public import PlanarFlow.NegSSSP.Enc.ResLoad

/-!
# The full branch: the inputs of the side arrays

`fbPre = fbL ; pcProg 2196 fbCL ; idProg ; (cpRegs ; ldProg) ×3 ; cpRegs ; bkProg`: the offset
`L` loaded from the frame, the layout of the heap room computed (`fbCL`: the room starts at
`ra = h + 10 k`), the identity array at `ra` (`2k` words), the residues modulo `Ms = 3L + 1` of
the lengths (`ra + 2k`), of the two children's potentials (`ra + 3k`, `ra + 5k`, read from the
gathered arrays `G₀`, `G₁` of `ndB` with offset `L + 1`), the flags of the large component in
the numbering of the piece map (`ra + 7k`, `bkProg`).

**`fbPre_exec`**: within `fbPreCost k` steps; memory below `ra` and from `ra + 8k` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW

variable {P : Input} {W : ℕ}

/-- The load of the offset `L = mem (d + 3)` into `r2204`. -/
def fbL : Stmt := block [.constN 2190 3, .addN 2191 3004 2190, .loadN 2204 2191]

/-- The layout of the room (scratch `2196`, `2197`). -/
def fbCL : List PcStep :=
  [(2203, [(1, .v 3003), (10, .v 2475)], 0), (2205, [(1, .v 2204), (1, .one)], 0),
    (2206, [(3, .v 2204), (1, .one)], 0), (2100, [(2, .v 2475)], 0),
    (2101, [(1, .v 2203)], 0), (2207, [(1, .v 3004), (5, .v 2475), (4, .one)], 0),
    (2208, [(1, .v 2203), (2, .v 2475)], 0), (2209, [(1, .v 2203), (3, .v 2475)], 0),
    (2210, [(1, .v 2203), (5, .v 2475)], 0), (2211, [(1, .v 2203), (7, .v 2475)], 0),
    (2212, [(1, .v 3003), (4, .v 2475)], 0), (2213, [(1, .v 3003), (6, .v 2475)], 0),
    (2214, [(1, .v 3003), (1, .v 2475)], 0),
    (2215, [(1, .v 2972), (33, .v 2475), (3, .one)], 0),
    (2216, [(1, .v 2972), (25, .v 2475), (3, .one)], 0),
    (2217, [(1, .v 2972), (28, .v 2475), (3, .one)], 0),
    (2218, [(1, .v 2972), (22, .v 960)], 0), (2219, [(1, .one)], 0), (2224, [(1, .one)], 1),
    (2220, [(1, .v 2203), (8, .v 2475)], 0), (2221, [(1, .v 2203), (9, .v 2475)], 0),
    (2222, [(1, .v 2203), (10, .v 2475)], 0), (2223, [(1, .v 2203), (40, .v 2475)], 0),
    (2230, [(1, .v 2203), (68, .v 2475)], 0), (2231, [(1, .v 2203), (69, .v 2475)], 0),
    (2232, [(1, .v 2203), (70, .v 2475)], 0), (2233, [(1, .v 2203), (100, .v 2475)], 0)]

set_option maxRecDepth 100000 in
theorem fbCL_wf : pcWF 2196 9600 fbCL = true := by kernel_rfl

theorem fbCL_cost : pcCost fbCL = 297 := by kernel_rfl

set_option maxHeartbeats 1000000 in
/-- The equations of the layout chain. -/
theorem fbCL_eqs {g : ℕ → ℕ} (h : PcSol fbCL g) :
    g 2203 = g 3003 + 10 * g 2475 ∧ g 2205 = g 2204 + 1 ∧ g 2206 = 3 * g 2204 + 1 ∧
    g 2100 = 2 * g 2475 ∧ g 2101 = g 2203 ∧ g 2207 = g 3004 + 5 * g 2475 + 4 ∧
    g 2208 = g 2203 + 2 * g 2475 ∧ g 2209 = g 2203 + 3 * g 2475 ∧
    g 2210 = g 2203 + 5 * g 2475 ∧ g 2211 = g 2203 + 7 * g 2475 ∧
    g 2212 = g 3003 + 4 * g 2475 ∧ g 2213 = g 3003 + 6 * g 2475 ∧ g 2214 = g 3003 + g 2475 ∧
    g 2215 = g 2972 + 33 * g 2475 + 3 ∧ g 2216 = g 2972 + 25 * g 2475 + 3 ∧
    g 2217 = g 2972 + 28 * g 2475 + 3 ∧ g 2218 = g 2972 + 22 * g 960 ∧ g 2219 = 1 ∧
    g 2224 = 0 ∧ g 2220 = g 2203 + 8 * g 2475 ∧ g 2221 = g 2203 + 9 * g 2475 ∧
    g 2222 = g 2203 + 10 * g 2475 ∧ g 2223 = g 2203 + 40 * g 2475 ∧
    g 2230 = g 2203 + 68 * g 2475 ∧ g 2231 = g 2203 + 69 * g 2475 ∧
    g 2232 = g 2203 + 70 * g 2475 ∧ g 2233 = g 2203 + 100 * g 2475 := by
  simp only [PcSol, fbCL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero] at h
  omega

/-- The word bounds of the layout chain. -/
theorem fbCL_bound {g : ℕ → ℕ} (h : PcSol fbCL g) {W : ℕ}
    (h1 : g 3003 + 120 * g 2475 ≤ W) (h2 : g 3004 + 5 * g 2475 + 4 ≤ W)
    (h3 : g 2972 + 33 * g 2475 + 3 ≤ W) (h4 : g 2972 + 22 * g 960 ≤ W)
    (h5 : 3 * g 2204 + 1 ≤ W) (h6 : 1 ≤ W) :
    ∀ s ∈ fbCL, hpSum g s.2.1 ≤ W := by
  intro s hs
  simp only [fbCL, List.mem_cons, List.not_mem_nil, or_false] at hs
  have E := fbCL_eqs h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, add_zero]
    omega

/-- The registers of the residue load of the lengths. -/
def fbR1 : List (ℕ × ℕ) :=
  [(2840, 2474), (2841, 2207), (2842, 2203), (2843, 2208), (2844, 2206), (2845, 2204)]
/-- … of the potential of the first child. -/
def fbR2 : List (ℕ × ℕ) :=
  [(2840, 2464), (2841, 2212), (2842, 2203), (2843, 2209), (2844, 2206), (2845, 2205)]
/-- … of the potential of the second child. -/
def fbR3 : List (ℕ × ℕ) :=
  [(2840, 2464), (2841, 2213), (2842, 2203), (2843, 2210), (2844, 2206), (2845, 2205)]
/-- … of the flags. -/
def fbR4 : List (ℕ × ℕ) := [(2764, 960), (2765, 2211), (2770, 2474), (2771, 2215), (2772, 2216)]

/-- **The inputs of the side arrays.** -/
def fbPre : Stmt :=
  .seq fbL <| .seq (pcProg 2196 fbCL) <| .seq idProg <|
  .seq (cpRegs fbR1) <| .seq ldProg <| .seq (cpRegs fbR2) <| .seq ldProg <|
  .seq (cpRegs fbR3) <| .seq ldProg <| .seq (cpRegs fbR4) bkProg

/-- The cost of `fbPre`. -/
def fbPreCost (k : ℕ) : ℕ := 3 + 297 + (10 * k + 4) + 3 * (6 + (22 * k + 6)) + 5 + (18 * k + 10)

theorem fbL_exec (c : Config) (hc : WordsBounded W c) {d : ℕ} (r04 : c.nreg 3004 = d)
    (hW : d + 3 ≤ W) (h3 : 3 ≤ W) :
    ∃ c' t, Exec P W fbL c c' t ∧ t = 3 ∧ c'.nreg 2204 = c.nmem (d + 3) ∧
      (∀ r, r ≠ 2190 → r ≠ 2191 → r ≠ 2204 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fbL
  exec_block
  all_goals try ((try config_simp); (try simp only [r04]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r04]
  · simp (disch := omega) only [upd_other]

theorem fbR_ok : cpOK fbR1 = true ∧ cpSrc fbR1 = true ∧ cpOK fbR2 = true ∧ cpSrc fbR2 = true ∧
    cpOK fbR3 = true ∧ cpSrc fbR3 = true ∧ cpOK fbR4 = true ∧ cpSrc fbR4 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem fbR_frame {r : ℕ} (h : r < 2764 ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) :
    r ∉ fbR1.map (·.1) ∧ r ∉ fbR2.map (·.1) ∧ r ∉ fbR3.map (·.1) ∧ r ∉ fbR4.map (·.1) := by
  simp only [fbR1, fbR2, fbR3, fbR4, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  omega

section Pre

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

/-- The registers of `fbPre`'s result that the side arrays read. -/
structure FbRegs (c : Config) (h d k B₀ m' L : ℕ) : Prop where
  rra : c.nreg 2203 = h + 10 * k
  rL : c.nreg 2204 = L
  rL1 : c.nreg 2205 = L + 1
  rMs : c.nreg 2206 = 3 * L + 1
  rRL : c.nreg 2208 = h + 12 * k
  rD0 : c.nreg 2209 = h + 13 * k
  rD1 : c.nreg 2210 = h + 15 * k
  rbK : c.nreg 2211 = h + 17 * k
  rHh : c.nreg 2214 = h + k
  rFb : c.nreg 2215 = B₀ + 33 * k + 3
  rXb : c.nreg 2216 = B₀ + 25 * k + 3
  rY : c.nreg 2217 = B₀ + 28 * k + 3
  rbz : c.nreg 2218 = B₀ + 22 * m'
  rone : c.nreg 2219 = 1
  rzero : c.nreg 2224 = 0
  rS0 : c.nreg 2220 = h + 18 * k
  rbL0 : c.nreg 2221 = h + 19 * k
  rT00 : c.nreg 2222 = h + 20 * k
  rI00 : c.nreg 2223 = h + 50 * k
  rS1 : c.nreg 2230 = h + 78 * k
  rbL1 : c.nreg 2231 = h + 79 * k
  rT01 : c.nreg 2232 = h + 80 * k
  rI01 : c.nreg 2233 = h + 110 * k

theorem FbRegs.of {c c' : Config} {h d k B₀ m' L : ℕ} (H : FbRegs c h d k B₀ m' L)
    (hr : ∀ r, 2200 ≤ r → r < 2240 → c'.nreg r = c.nreg r) : FbRegs c' h d k B₀ m' L := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23⟩ := H
  exact ⟨(hr _ (by omega) (by omega)).trans a1, (hr _ (by omega) (by omega)).trans a2,
    (hr _ (by omega) (by omega)).trans a3, (hr _ (by omega) (by omega)).trans a4,
    (hr _ (by omega) (by omega)).trans a5, (hr _ (by omega) (by omega)).trans a6,
    (hr _ (by omega) (by omega)).trans a7, (hr _ (by omega) (by omega)).trans a8,
    (hr _ (by omega) (by omega)).trans a9, (hr _ (by omega) (by omega)).trans a10,
    (hr _ (by omega) (by omega)).trans a11, (hr _ (by omega) (by omega)).trans a12,
    (hr _ (by omega) (by omega)).trans a13, (hr _ (by omega) (by omega)).trans a14,
    (hr _ (by omega) (by omega)).trans a15, (hr _ (by omega) (by omega)).trans a16,
    (hr _ (by omega) (by omega)).trans a17, (hr _ (by omega) (by omega)).trans a18,
    (hr _ (by omega) (by omega)).trans a19, (hr _ (by omega) (by omega)).trans a20,
    (hr _ (by omega) (by omega)).trans a21, (hr _ (by omega) (by omega)).trans a22,
    (hr _ (by omega) (by omega)).trans a23⟩

/-- The layout facts of `fbPre_exec`. -/
theorem fbPre_lay {h d k m w L B₀ m' W : ℕ} (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k)
    (hdh : d + 4 + 5 * k + m ≤ h) (hB : B₀ + 66 * k + 35 < d) (hW : h + 130 * k ≤ W)
    (hL : 3 * (3 * L + 1) + 2 * L + 2 ≤ W) :
    h + 10 * k + 2 * k ≤ W ∧ h + 12 * k + m ≤ W ∧ (h + 12 * k + m ≤ h + 10 * k ∨
      h + 10 * k + m ≤ h + 12 * k) ∧ h + 13 * k + w ≤ W ∧ (h + 13 * k + w ≤ h + 10 * k ∨
      h + 10 * k + w ≤ h + 13 * k) ∧ h + 15 * k + w ≤ W ∧ (h + 15 * k + w ≤ h + 10 * k ∨
      h + 10 * k + w ≤ h + 15 * k) ∧ h + 17 * k + m' ≤ W ∧
      B₀ + 33 * k + 3 + m ≤ W ∧ B₀ + 25 * k + 3 + m ≤ W ∧
      (h + 17 * k + m' ≤ B₀ + 33 * k + 3 ∨ B₀ + 33 * k + 3 + m ≤ h + 17 * k) ∧
      (h + 17 * k + m' ≤ B₀ + 25 * k + 3 ∨ B₀ + 25 * k + 3 + m ≤ h + 17 * k) ∧
      1 ≤ W ∧ 3 ≤ W ∧ d + 3 ≤ W := by
  refine ⟨by omega, by omega, Or.inr (by omega), by omega, Or.inr (by omega), by omega,
    Or.inr (by omega), by omega, by omega, by omega, Or.inr (by omega), Or.inr (by omega),
    by omega, by omega, by omega⟩

end Pre

end NegSSSP

end PlanarFlow

namespace PlanarFlow

namespace NegSSSP

open Finset Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW

variable {P : Input} {W : ℕ}

section Pre

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

/-- A residue loaded from an offset word. -/
theorem fb_res {M L u : ℕ} {z : ℤ} (hM : 0 < M) (hu : (u : ℤ) = z + L) :
    (((u + (M - L % M)) % M : ℕ) : ℤ) = z % M := ld_val hM hu

/-- A residue loaded through the identity array. -/
theorem fb_ldv {mem : ℕ → ℕ} {INb Jb M L i : ℕ} {z : ℤ} (hM : 0 < M) (hJ : mem (Jb + i) = i)
    (hu : (mem (INb + i) : ℤ) = z + L) : (ldV mem INb Jb M L i : ℤ) = z % M := by
  unfold ldV; rw [hJ]; exact ld_val hM hu

theorem fb_off {z : ℤ} {L : ℕ} (h : |z| ≤ L) : (((z + L).toNat : ℕ) : ℤ) = z + L := by
  have := abs_le.1 h
  exact Int.toNat_of_nonneg (by omega)

theorem fbCL_notDst {r : ℕ} (h : r < 2100 ∨ 2240 ≤ r) : r ∉ pcDsts fbCL := by
  simp only [pcDsts, fbCL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

set_option maxHeartbeats 8000000 in
/-- **The inputs of the side arrays** (see the module docstring). -/
theorem fbPre_exec {Pc K : Finset D} {m k m' w L h d B₀ : ℕ} {en : ℕ → D} {α σ : ℕ → ℕ}
    (he : PEnc N Pc m k en α σ) (hKP : K ⊆ Pc) (cn : SDart (rcl N K) ≃ Fin m')
    (ℓ : D → ℤ) (δ₀ δ₁ : V → ℤ) (ι : ℕ → V) (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d) (r75 : c.nreg 2475 = k)
    (r74 : c.nreg 2474 = m) (r64 : c.nreg 2464 = w) (r72 : c.nreg 2972 = B₀)
    (r960 : c.nreg 960 = m') (hL : c.nmem (d + 3) = L)
    (hln : ∀ i < m, c.nmem (d + 4 + 5 * k + i) = (ℓ (en i) + L).toNat)
    (hℓ : ∀ i < m, |ℓ (en i)| ≤ L)
    (hG₀ : ∀ v < w, (c.nmem (h + 4 * k + v) : ℤ) = δ₀ (ι v) + (L + 1) ∧ |δ₀ (ι v)| ≤ L + 1)
    (hG₁ : ∀ v < w, (c.nmem (h + 6 * k + v) : ℤ) = δ₁ (ι v) + (L + 1) ∧ |δ₁ (ι v)| ≤ L + 1)
    (hXm : ∀ i < k, ∀ hm : en i ∈ rcl N K, c.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hm⟩)
    (hFm : ∀ x < m, (c.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ en x ∈ K))
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k) (hdh : d + 4 + 5 * k + m ≤ h)
    (hB : B₀ + 66 * k + 35 < d) (hW : h + 130 * k ≤ W) (hLW : 3 * (3 * L + 1) + 2 * L + 2 ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W fbPre c c' t ∧ t ≤ fbPreCost k ∧ FbRegs c' h d k B₀ m' L ∧
      (∀ i < 2 * k, c'.nmem (h + 10 * k + i) = i) ∧
      (∀ i < m, (c'.nmem (h + 12 * k + i) : ℤ) = ℓ (en i) % ((3 * L + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (h + 13 * k + v) : ℤ) = δ₀ (ι v) % ((3 * L + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (h + 15 * k + v) : ℤ) = δ₁ (ι v) % ((3 * L + 1 : ℕ) : ℤ)) ∧
      (∀ x, c'.nmem (h + 17 * k + cn x) = if x.1 ∈ K then 1 else 0) ∧
      (∀ a, (a < h + 10 * k ∨ h + 18 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2100 ∨ (2240 ≤ r ∧ r < 2764) ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ :=
    fbPre_lay (L := L) hmk hw hm' hdh hB hW hLW
  obtain ⟨ok1, sr1, ok2, sr2, ok3, sr3, ok4, sr4⟩ := fbR_ok
  -- the offset
  obtain ⟨c₁, t₁, e₁, ht₁, q04, f₁, m₁, rr₁, rm₁, o₁⟩ := fbL_exec (P := P) c hc r04 y15 y14
  rw [hL] at q04
  have F₁ : ∀ r, 2190 ≠ r → 2191 ≠ r → 2204 ≠ r → c₁.nreg r = c.nreg r := fun r a b c' =>
    f₁ r (Ne.symm a) (Ne.symm b) (Ne.symm c')
  -- the layout of the room
  have hgs : ∀ g : ℕ → ℕ, (∀ r, r ∉ pcDsts fbCL → r ≠ 2196 → r ≠ 2196 + 1 → g r = c₁.nreg r) →
      g 3003 = h ∧ g 3004 = d ∧ g 2475 = k ∧ g 2972 = B₀ ∧ g 960 = m' ∧ g 2204 = L := by
    intro g hg
    have k : ∀ r, r ∉ pcDsts fbCL → r ≠ 2196 → r ≠ 2197 → g r = c₁.nreg r := hg
    refine ⟨(k 3003 (by decide) (by omega) (by omega)).trans
        ((F₁ 3003 (by omega) (by omega) (by omega)).trans r03),
      (k 3004 (by decide) (by omega) (by omega)).trans
        ((F₁ 3004 (by omega) (by omega) (by omega)).trans r04),
      (k 2475 (by decide) (by omega) (by omega)).trans
        ((F₁ 2475 (by omega) (by omega) (by omega)).trans r75),
      (k 2972 (by decide) (by omega) (by omega)).trans
        ((F₁ 2972 (by omega) (by omega) (by omega)).trans r72),
      (k 960 (by decide) (by omega) (by omega)).trans
        ((F₁ 960 (by omega) (by omega) (by omega)).trans r960),
      (k 2204 (by decide) (by omega) (by omega)).trans q04⟩
  obtain ⟨c₂, e₂, s₂, f₂, m₂, rr₂, rm₂, o₂⟩ := pcProg_exec (I := P) (W := W) fbCL fbCL_wf h9600 c₁
    e₁.wb_right (fun g hg hs => by
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgs g hg
      exact fbCL_bound hs (by rw [g1, g3]; omega) (by rw [g2, g3]; omega)
        (by rw [g4, g3]; omega) (by rw [g4, g5]; omega) (by rw [g6]; omega) (by omega))
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgs c₂.nreg f₂
  obtain ⟨E03, E05, E06, E100, E101, E07, E08, E09, E10, E11, E12, E13, E14, E15, E16, E17, E18,
    E19, E24, E20, E21, E22, E23, E30, E31, E32, E33⟩ := fbCL_eqs s₂
  rw [g1, g3] at E03
  rw [g6] at E05 E06
  rw [g3] at E100
  have F₂ : ∀ r, r ∉ pcDsts fbCL → r ≠ 2196 → r ≠ 2197 → c₂.nreg r = c₁.nreg r := f₂
  have hR₂ : FbRegs c₂ h d k B₀ m' L := by
    refine ⟨E03, g6, E05, E06, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, E19, E24, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ <;> omega
  -- the identity array
  obtain ⟨c₃, t₃, e₃, ht₃, i₃, m₃, f₃, rr₃, rm₃, o₃⟩ := idProg_exec (P := P) (n := 2 * k)
    (Ob := h + 10 * k) c₂ e₂.wb_right E100 (by rw [E101, E03]) y1 y13
  have K₃ : ∀ r, (r < 2100 ∨ 2240 ≤ r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [f₃ r (by omega), F₂ r (fbCL_notDst hr) (by omega) (by omega),
      F₁ r (by omega) (by omega) (by omega)]
  have M₃ : ∀ a, a < h + 10 * k → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃ a (Or.inl ha), m₂, m₁]
  have hR₃ : FbRegs c₃ h d k B₀ m' L := hR₂.of fun r h1 h2 => f₃ r (by omega)
  -- the residues of the lengths
  obtain ⟨c₄, e₄, g₄, f₄, m₄, rr₄, rm₄, o₄⟩ := cpRegs_exec (P := P) (W := W) _ ok1 sr1 c₃
    e₃.wb_right
  simp only [fbR1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₄
  obtain ⟨u40, u41, u42, u43, u44, u45⟩ := g₄
  have I₄ : ∀ i < 2 * k, c₄.nmem (h + 10 * k + i) = i := fun i hi => by rw [m₄]; exact i₃ i hi
  have M₄ : ∀ a, a < h + 10 * k → c₄.nmem a = c.nmem a := fun a ha => by rw [m₄]; exact M₃ a ha
  obtain ⟨c₅, t₅, e₅, ht₅, v₅, m₅, f₅, rr₅, rm₅, o₅⟩ := ldProg_exec (P := P) (n := m)
    (INb := d + 4 + 5 * k) (Jb := h + 10 * k) (Ob := h + 12 * k) (M := 3 * L + 1) (L := L)
    c₄ e₄.wb_right (by rw [u40, K₃ _ (by omega), r74])
    (by rw [u41, f₃ _ (by omega), E07, g2, g3]; omega)
    (by rw [u42, hR₃.rra]) (by rw [u43, hR₃.rRL]) (by rw [u44, hR₃.rMs])
    (by rw [u45, hR₃.rL]) (by omega) y13 (by omega) y2 y3
    (fun i hi => by
      rw [I₄ i (by omega), M₄ _ (by omega), hln i hi]
      have := abs_le.1 (hℓ i hi)
      refine ⟨by omega, Or.inl (by omega), by omega⟩)
  have RL₅ : ∀ i < m, (c₅.nmem (h + 12 * k + i) : ℤ) = ℓ (en i) % ((3 * L + 1 : ℕ) : ℤ) :=
    fun i hi => by
      rw [v₅ i hi]
      exact fb_ldv (by omega) (I₄ i (by omega))
        (by rw [M₄ _ (by omega), hln i hi]; exact fb_off (hℓ i hi))
  have fr1 := fbR_frame (r := 2212) (by omega)
  have Q₅ : ∀ r, (r < 2764 ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) → c₅.nreg r = c₃.nreg r :=
    fun r hr => by rw [f₅ r (by omega), f₄ r (fbR_frame hr).1]
  -- the residues of the first child's potential
  obtain ⟨c₆, e₆, g₆, f₆, m₆, rr₆, rm₆, o₆⟩ := cpRegs_exec (P := P) (W := W) _ ok2 sr2 c₅
    e₅.wb_right
  simp only [fbR2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₆
  obtain ⟨u60, u61, u62, u63, u64, u65⟩ := g₆
  have M₆ : ∀ a, (a < h + 12 * k ∨ h + 12 * k + m ≤ a) → c₆.nmem a = c₄.nmem a := fun a ha => by
    rw [m₆, m₅ a ha]
  obtain ⟨c₇, t₇, e₇, ht₇, v₇, m₇, f₇, rr₇, rm₇, o₇⟩ := ldProg_exec (P := P) (n := w)
    (INb := h + 4 * k) (Jb := h + 10 * k) (Ob := h + 13 * k) (M := 3 * L + 1) (L := L + 1)
    c₆ e₆.wb_right (by rw [u60, Q₅ _ (by omega), K₃ _ (by omega), r64])
    (by rw [u61, Q₅ _ (by omega), f₃ _ (by omega), E12, g1, g3])
    (by rw [u62, Q₅ _ (by omega), hR₃.rra]) (by rw [u63, Q₅ _ (by omega), hR₃.rD0])
    (by rw [u64, Q₅ _ (by omega), hR₃.rMs]) (by rw [u65, Q₅ _ (by omega), hR₃.rL1])
    (by omega) y13 (by omega) y4 y5
    (fun v hv => by
      rw [M₆ _ (Or.inl (by omega)), I₄ v (by omega), M₆ _ (Or.inl (by omega)),
        M₄ _ (by omega)]
      obtain ⟨h1, h2⟩ := hG₀ v hv
      have := abs_le.1 h2
      refine ⟨by omega, Or.inl (by omega), by omega⟩)
  have D₇ : ∀ v < w, (c₇.nmem (h + 13 * k + v) : ℤ) = δ₀ (ι v) % ((3 * L + 1 : ℕ) : ℤ) :=
    fun v hv => by
      rw [v₇ v hv]
      exact fb_ldv (by omega) (by rw [M₆ _ (Or.inl (by omega))]; exact I₄ v (by omega))
        (by rw [M₆ _ (Or.inl (by omega)), M₄ _ (by omega), (hG₀ v hv).1]; push_cast; ring)
  have Q₇ : ∀ r, (r < 2764 ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) → c₇.nreg r = c₃.nreg r :=
    fun r hr => by rw [f₇ r (by omega), f₆ r (fbR_frame hr).2.1, Q₅ r hr]
  -- the residues of the second child's potential
  obtain ⟨c₈, e₈, g₈, f₈, m₈, rr₈, rm₈, o₈⟩ := cpRegs_exec (P := P) (W := W) _ ok3 sr3 c₇
    e₇.wb_right
  simp only [fbR3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₈
  obtain ⟨u80, u81, u82, u83, u84, u85⟩ := g₈
  have M₈ : ∀ a, (a < h + 12 * k ∨ h + 13 * k + w ≤ a) → c₈.nmem a = c₄.nmem a := fun a ha => by
    rw [m₈, m₇ a (by omega), M₆ a (by omega)]
  obtain ⟨c₉, t₉, e₉, ht₉, v₉, m₉, f₉, rr₉, rm₉, o₉⟩ := ldProg_exec (P := P) (n := w)
    (INb := h + 6 * k) (Jb := h + 10 * k) (Ob := h + 15 * k) (M := 3 * L + 1) (L := L + 1)
    c₈ e₈.wb_right (by rw [u80, Q₇ _ (by omega), K₃ _ (by omega), r64])
    (by rw [u81, Q₇ _ (by omega), f₃ _ (by omega), E13, g1, g3])
    (by rw [u82, Q₇ _ (by omega), hR₃.rra]) (by rw [u83, Q₇ _ (by omega), hR₃.rD1])
    (by rw [u84, Q₇ _ (by omega), hR₃.rMs]) (by rw [u85, Q₇ _ (by omega), hR₃.rL1])
    (by omega) y13 (by omega) y6 y7
    (fun v hv => by
      rw [M₈ _ (Or.inl (by omega)), I₄ v (by omega), M₈ _ (Or.inl (by omega)),
        M₄ _ (by omega)]
      obtain ⟨h1, h2⟩ := hG₁ v hv
      have := abs_le.1 h2
      refine ⟨by omega, Or.inl (by omega), by omega⟩)
  have D₉ : ∀ v < w, (c₉.nmem (h + 15 * k + v) : ℤ) = δ₁ (ι v) % ((3 * L + 1 : ℕ) : ℤ) :=
    fun v hv => by
      rw [v₉ v hv]
      exact fb_ldv (by omega) (by rw [M₈ _ (Or.inl (by omega))]; exact I₄ v (by omega))
        (by rw [M₈ _ (Or.inl (by omega)), M₄ _ (by omega), (hG₁ v hv).1]; push_cast; ring)
  have Q₉ : ∀ r, (r < 2764 ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) → c₉.nreg r = c₃.nreg r :=
    fun r hr => by rw [f₉ r (by omega), f₈ r (fbR_frame hr).2.2.1, Q₇ r hr]
  -- the flags
  obtain ⟨c₁₀, e₁₀, g₁₀, f₁₀, m₁₀, rr₁₀, rm₁₀, o₁₀⟩ := cpRegs_exec (P := P) (W := W) _ ok4 sr4
    c₉ e₉.wb_right
  simp only [fbR4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₁₀
  obtain ⟨u64', u65', u70, u71, u72⟩ := g₁₀
  have M₁₀ : ∀ a, a < h + 10 * k → c₁₀.nmem a = c.nmem a := fun a ha => by
    rw [m₁₀, m₉ a (Or.inl (by omega)), M₈ a (Or.inl (by omega)), M₄ a ha]
  have hXm' : ∀ i < k, ∀ hm : en i ∈ rcl N K, c₁₀.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hm⟩ :=
    fun i hi hm => by rw [M₁₀ _ (by omega)]; exact hXm i hi hm
  have hFm' : ∀ x < m, (c₁₀.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ en x ∈ K) := fun x hx => by
    rw [M₁₀ _ (by omega)]; exact hFm x hx
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, v₁₁, m₁₁, f₁₁, rr₁₁, rm₁₁, o₁₁⟩ := bkProg_exec (P := P)
    (m' := m') (m := m) (Kb := h + 17 * k) (Fb := B₀ + 33 * k + 3) (Xb := B₀ + 25 * k + 3) c₁₀
    e₁₀.wb_right (by rw [u64', Q₉ _ (by omega), K₃ _ (by omega), r960])
    (by rw [u65', Q₉ _ (by omega), hR₃.rbK]) (by rw [u70, Q₉ _ (by omega), K₃ _ (by omega), r74])
    (by rw [u71, Q₉ _ (by omega), hR₃.rFb]) (by rw [u72, Q₉ _ (by omega), hR₃.rXb])
    y13 y8 y9 y10 y11 y12 (bk_idx he cn hXm' hFm')
  have Q₁₁ : ∀ r, (r < 2764 ∨ (2775 < r ∧ r < 2840) ∨ 2850 < r) → c₁₁.nreg r = c₃.nreg r :=
    fun r hr => by
      rw [f₁₁ r (by omega), f₁₀ r (fbR_frame hr).2.2.2, Q₉ r hr]
  refine ⟨c₁₁, t₁ + (pcCost fbCL + (t₃ + (fbR1.length + (t₅ + (fbR2.length + (t₇ +
    (fbR3.length + (t₉ + (fbR4.length + t₁₁))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ e₁₁))))))))), ?_, hR₃.of fun r h1 h2 => Q₁₁ r (by omega),
    fun i hi => ?_, fun i hi => ?_, fun v hv => ?_, fun v hv => ?_, fun x => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₁₁, rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂,
      rr₁], by rw [rm₁₁, rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₁₁, o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [fbCL_cost]; simp only [fbR1, fbR2, fbR3, fbR4, List.length_cons, List.length_nil]
    unfold fbPreCost; clear * - ht₁ ht₃ ht₅ ht₇ ht₉ ht₁₁ hmk hw hm'; omega
  · rw [m₁₁ _ (Or.inl (by omega)), m₁₀, m₉ _ (Or.inl (by omega)), M₈ _ (Or.inl (by omega))]
    exact I₄ i hi
  · rw [m₁₁ _ (Or.inl (by omega)), m₁₀, m₉ _ (Or.inl (by omega)), m₈, m₇ _ (Or.inl (by omega)),
      m₆]
    exact RL₅ i hi
  · rw [m₁₁ _ (Or.inl (by omega)), m₁₀, m₉ _ (Or.inl (by omega)), m₈]
    exact D₇ v hv
  · rw [m₁₁ _ (Or.inl (by omega)), m₁₀]
    exact D₉ v hv
  · rw [v₁₁ _ (cn x).2]
    exact bk_flK he hKP cn hXm' hFm' x
  · rcases ha with ha | ha
    · rw [m₁₁ _ (Or.inl (by omega)), M₁₀ a ha]
    · rw [m₁₁ _ (Or.inr (by omega)), m₁₀, m₉ _ (Or.inr (by omega)), M₈ _ (Or.inr (by omega)),
        m₄, m₃ _ (Or.inr (by omega)), m₂, m₁]
  · rw [Q₁₁ r (by omega), K₃ r (by omega)]

end Pre

end NegSSSP

end PlanarFlow
