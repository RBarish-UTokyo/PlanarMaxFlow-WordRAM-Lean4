module

public import PlanarFlow.NegSSSP.NdRun2

/-!
# The full branch: after the node — the clearing and the outcome

* **`fbClr`** `= lgClr ; cpRegs fbZL1 ; zrProg ; cpRegs fbZL2 ; zrProg`: the cells logged by
  the node zeroed, then the node's low arrays `[Z, END₁)` and the residues
  `[W' + 1 + Z + 3M₀, W' + 1 + Z + 6M₀)` (all below the heap): **`fbClr_exec`**.
* **`fbNo`** `= fbClr ; cpRegs fbNL ; ndNone` (no feasible potential: the flag).
* **`fbW WN`** `= cpRegs fbWL ; WN → r2865 ; wbProg` (the node's outcome residues at
  `W' + 1 + Z + 20M₀ + v` to offset values `f + WN` at `h + 8k + v`), **`fbYes WN`** `= fbW WN ;
  fbClr ; cpRegs fbYL ; ndC ; resProg` (the renormalized outcome, `resProg_res` with `Lf = WN`).
* **`fbOut WN`** `= if 0 < r990 then fbNo else fbYes WN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The registers of the first zero loop: `n = END₁ − Z`, `OUTb = Z`. -/
def fbZL1 : List (ℕ × ℕ) := [(2114, 2954), (2115, 2931)]
/-- The registers of the second zero loop: `n = 3M₀`, `OUTb = W' + 1 + Z + 3M₀`. -/
def fbZL2 : List (ℕ × ℕ) := [(2114, 2953), (2115, 2952)]

/-- **The clearing after the node.** -/
def fbClr : Stmt :=
  .seq lgClr <| .seq (cpRegs fbZL1) <| .seq zrProg <| .seq (cpRegs fbZL2) zrProg

theorem fbZL_ok : cpOK fbZL1 = true ∧ cpSrc fbZL1 = true ∧ cpOK fbZL2 = true ∧
    cpSrc fbZL2 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem fbClr_natOnly : Klein.natOnly fbClr = true := by
  simp [fbClr, Klein.natOnly, lgClr_natOnly, cpRegs_natOnly, zrProg_natOnly]

/-- The cost of `fbClr`. -/
def fbClrCost (j n₁ n₂ : ℕ) : ℕ := 6 * j + 5 + 2 + (5 * n₁ + 5) + 2 + (5 * n₂ + 5)

set_option maxHeartbeats 4000000 in
/-- **The clearing after the node** (see the module docstring). -/
theorem fbClr_exec (c : Config) (hc : WordsBounded W c) {p j Ws Z E R n : ℕ}
    (r24 : c.nreg 2924 = p) (r25 : c.nreg 2925 = p + j) (r26 : c.nreg 2926 = 1)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p)
    (r54 : c.nreg 2954 = E - Z) (r31 : c.nreg 2931 = Z) (r53 : c.nreg 2953 = n)
    (r52 : c.nreg 2952 = R) (hZE : Z ≤ E) (hEW : E ≤ W) (hRW : R + n ≤ W) (h1 : 1 ≤ W) :
    ∃ c' t, Exec P W fbClr c c' t ∧ t ≤ fbClrCost j (E - Z) n ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) → c'.nmem a = 0) ∧
      (∀ a, Z ≤ a → a < E → c'.nmem a = 0) ∧ (∀ a, R ≤ a → a < R + n → c'.nmem a = 0) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → (a < Z ∨ E ≤ a) → (a < R ∨ R + n ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2923 → (r < 2927 ∨ 2929 < r) → (r < 2114 ∨ 2119 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ok1, sr1, ok2, sr2⟩ := fbZL_ok
  obtain ⟨c₁, t₁, e₁, ht₁, z₁, k₁, n₁, rr₁, rm₁, o₁⟩ := lgClr_exec (P := P) c hc r24 r25 r26
    hlog hp
  have N₁ : ∀ r, 2930 ≤ r → c₁.nreg r = c.nreg r := fun r hr => n₁ r (by omega) (by omega)
  obtain ⟨c₂, e₂, g₂, f₂, m₂, rr₂, rm₂, o₂⟩ := cpRegs_exec (P := P) (W := W) _ ok1 sr1 c₁
    e₁.wb_right
  simp only [fbZL1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₂
  obtain ⟨u14, u15⟩ := g₂
  obtain ⟨c₃, t₃, e₃, ht₃, z₃, k₃, n₃, rr₃, rm₃, o₃⟩ := zrProg_exec (P := P) (n := E - Z)
    (Ob := Z) c₂ e₂.wb_right (by rw [u14, N₁ _ (by omega), r54])
    (by rw [u15, N₁ _ (by omega), r31]) (by omega) h1
  obtain ⟨c₄, e₄, g₄, f₄, m₄, rr₄, rm₄, o₄⟩ := cpRegs_exec (P := P) (W := W) _ ok2 sr2 c₃
    e₃.wb_right
  simp only [fbZL2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₄
  obtain ⟨v14, v15⟩ := g₄
  have F₃ : ∀ r, 2930 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [n₃ r (by omega), f₂ r (by simp [fbZL1]; omega), N₁ r hr]
  obtain ⟨c₅, t₅, e₅, ht₅, z₅, k₅, n₅, rr₅, rm₅, o₅⟩ := zrProg_exec (P := P) (n := n)
    (Ob := R) c₄ e₄.wb_right (by rw [v14, F₃ _ (by omega), r53])
    (by rw [v15, F₃ _ (by omega), r52]) hRW h1
  have M₃ : ∀ a, (a < Z ∨ E ≤ a) → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [k₃ a (by omega), m₂]
  refine ⟨c₅, t₁ + (2 + (t₃ + (2 + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_,
    fun a ha => ?_, fun a h1 h2 => ?_, fun a h1 h2 => ?_, fun a h1 h2 h3 => ?_,
    fun r h1 h2 h3 => ?_, by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · unfold fbClrCost; omega
  · by_cases hR : R ≤ a ∧ a < R + n
    · have := z₅ (a - R) (by omega); rwa [show R + (a - R) = a by omega] at this
    · rw [k₅ a (by omega), m₄]
      by_cases hZ : Z ≤ a ∧ a < E
      · have := z₃ (a - Z) (by omega); rwa [show Z + (a - Z) = a by omega] at this
      · rw [M₃ a (by omega)]; exact z₁ a ha
  · by_cases hR : R ≤ a ∧ a < R + n
    · have := z₅ (a - R) (by omega); rwa [show R + (a - R) = a by omega] at this
    · rw [k₅ a (by omega), m₄]
      have := z₃ (a - Z) (by omega); rwa [show Z + (a - Z) = a by omega] at this
  · have := z₅ (a - R) (by omega); rwa [show R + (a - R) = a by omega] at this
  · rw [k₅ a h3, m₄, M₃ a h2]; exact k₁ a h1
  · rw [n₅ r (by omega), f₄ r (by simp [fbZL2]; omega), n₃ r (by omega),
      f₂ r (by simp [fbZL1]; omega), n₁ r h1 h2]

/-- The registers of the flag: `m`, `k`, `1`. -/
def fbNL : List (ℕ × ℕ) := [(2474, 2937), (2475, 2938), (2472, 2926)]

/-- **No feasible potential**: the clearing, then the flag. -/
def fbNo : Stmt := .seq fbClr (.seq (cpRegs fbNL) Frame.ndNone)

/-- The registers of the write-back: `n = w`, `INb`, `OUTb = h + 8k`, `M`, `H`. -/
def fbWL : List (ℕ × ℕ) := [(2860, 2936), (2861, 2951), (2862, 2957), (2863, 2934), (2864, 2933)]

/-- **The write-back of the node's outcome** (offset `WN`). -/
def fbW (WN : ℕ) : Stmt := .seq (cpRegs fbWL) (.seq (.instr (.constN 2865 WN)) wbProg)

/-- The registers of `ndC`: `w`, `k`. -/
def fbYL : List (ℕ × ℕ) := [(2464, 2936), (2475, 2938)]

/-- **A feasible potential**: the write-back, the clearing, the renormalized outcome. -/
def fbYes (WN : ℕ) : Stmt :=
  .seq (fbW WN) (.seq fbClr (.seq (cpRegs fbYL) (.seq Frame.ndC Frame.resProg)))

/-- **After the node.** -/
def fbOut (WN : ℕ) : Stmt := .ifLtN 2956 990 fbNo (fbYes WN)

theorem fbOL_ok : cpOK fbNL = true ∧ cpSrc fbNL = true ∧ cpOK fbWL = true ∧
    cpSrc fbWL = true ∧ cpOK fbYL = true ∧ cpSrc fbYL = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 4000000 in
/-- **No feasible potential**: `fbClr_exec`, then the flag `1` at `d + 5k + m + 4`. -/
theorem fbNo_exec (c : Config) (hc : WordsBounded W c) {p j Ws Z E R n d m k : ℕ}
    (r24 : c.nreg 2924 = p) (r25 : c.nreg 2925 = p + j) (r26 : c.nreg 2926 = 1)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p)
    (r54 : c.nreg 2954 = E - Z) (r31 : c.nreg 2931 = Z) (r53 : c.nreg 2953 = n)
    (r52 : c.nreg 2952 = R) (hZE : Z ≤ E) (hEW : E ≤ W) (hRW : R + n ≤ W) (h1 : 5 ≤ W)
    (r37 : c.nreg 2937 = m) (r38 : c.nreg 2938 = k) (r04 : c.nreg 3004 = d)
    (hW : d + 5 * k + m + 4 ≤ W) :
    ∃ c' t, Exec P W fbNo c c' t ∧ t ≤ fbClrCost j (E - Z) n + 3 + 7 ∧
      c'.nmem (d + 5 * k + m + 4) = 1 ∧
      (∀ a, a ≠ d + 5 * k + m + 4 → (∃ i < j, c.nmem (p + i) = a) → c'.nmem a = 0) ∧
      (∀ a, a ≠ d + 5 * k + m + 4 → Z ≤ a → a < E → c'.nmem a = 0) ∧
      (∀ a, a ≠ d + 5 * k + m + 4 → R ≤ a → a < R + n → c'.nmem a = 0) ∧
      (∀ a, a ≠ d + 5 * k + m + 4 → (∀ i < j, c.nmem (p + i) ≠ a) → (a < Z ∨ E ≤ a) →
        (a < R ∨ R + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 2930 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ok1, sr1, -, -, -, -⟩ := fbOL_ok
  obtain ⟨c₁, t₁, e₁, ht₁, z₁, y₁, x₁, k₁, n₁, rr₁, rm₁, o₁⟩ := fbClr_exec (P := P) c hc r24 r25
    r26 hlog hp r54 r31 r53 r52 hZE hEW hRW (by omega)
  have N₁ : ∀ r, 2930 ≤ r → c₁.nreg r = c.nreg r := fun r hr =>
    n₁ r (by omega) (by omega) (by omega)
  obtain ⟨c₂, e₂, g₂, f₂, m₂, rr₂, rm₂, o₂⟩ := cpRegs_exec (P := P) (W := W) _ ok1 sr1 c₁
    e₁.wb_right
  simp only [fbNL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₂
  obtain ⟨u74, u75, u72⟩ := g₂
  have F₂ : ∀ r, 2930 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [f₂ r (by simp [fbNL]; omega), N₁ r hr]
  obtain ⟨c₃, t₃, e₃, ht₃, m₃, n₃, rr₃, rm₃, o₃⟩ := Frame.ndNone_exec (I := P) c₂ e₂.wb_right
    (by rw [F₂ _ (by omega), r04]) (by rw [u74, N₁ _ (by omega), r37])
    (by rw [u75, N₁ _ (by omega), r38]) (by rw [u72, n₁ _ (by omega) (by omega) (by omega), r26])
    hW (by omega)
  have M₃ : ∀ a, a ≠ d + 5 * k + m + 4 → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [m₃, upd_other _ _ _ ha, m₂]
  refine ⟨c₃, t₁ + (3 + t₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [m₃, upd_same],
    fun a ha h => by rw [M₃ a ha]; exact z₁ a h, fun a ha h1 h2 => by rw [M₃ a ha]; exact y₁ a h1 h2,
    fun a ha h1 h2 => by rw [M₃ a ha]; exact x₁ a h1 h2,
    fun a ha h1 h2 h3 => by rw [M₃ a ha]; exact k₁ a h1 h2 h3,
    fun r hr => by rw [n₃ r (by omega), F₂ r hr], by rw [rr₃, rr₂, rr₁],
    by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩

/-- **The outcome read back**: a value `v ≤ WN` read back by `sgnD H M` (`M = 2H + 1`,
`H ≤ WN`) is within `WN` of `0`. -/
theorem sgnD_le_WN {H M WN v : ℕ} {f : ℤ} (hf : (f : ℝ) = sgnD H M v) (hM : M = 2 * H + 1)
    (hv : v ≤ WN) : |f| ≤ WN := by
  unfold sgnD at hf
  split_ifs at hf with h
  · have e : f = v := by exact_mod_cast hf
    rw [abs_le]; omega
  · have e : f = (v : ℤ) - M := by
      exact_mod_cast (show (f : ℝ) = (((v : ℤ) - M : ℤ) : ℝ) by push_cast; linarith)
    rw [abs_le]; omega

section Yes

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : Frame.GIds D V} {N : CombMap D V F}

/-- The cost of `fbYes`. -/
def fbYesCost (j n₁ n₂ m w : ℕ) : ℕ :=
  5 + 1 + (10 * w + 5) + fbClrCost j n₁ n₂ + 2 + 12 + (22 + rnCost m w + 6 + (7 * w + 2))

set_option maxHeartbeats 8000000 in
/-- **A feasible potential**: the node's outcome `f` (residues at `Rb + v`, `v < w`, read back
by `sgnD H M`, at most `WN`) written back with the offset `WN` to `h + 8k`, the clearing, the
renormalized outcome (`resProg_res`, `Lf = WN`). -/
theorem fbYes_exec {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} {d e : ℕ} {f : V → ℤ} {ν : V → ℕ}
    {ι : ℕ → V} (c : Config) (hc : WordsBounded W c) {p j Ws Z E R n₂ w h k H M WN Rb : ℕ}
    (hin : Frame.InP g N ℓ L n Q d e c) (hf : (pg N Q ℓ).IsPot f)
    (r24 : c.nreg 2924 = p) (r25 : c.nreg 2925 = p + j) (r26 : c.nreg 2926 = 1)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p)
    (r54 : c.nreg 2954 = E - Z) (r31 : c.nreg 2931 = Z) (r53 : c.nreg 2953 = n₂)
    (r52 : c.nreg 2952 = R) (hZE : Z ≤ E)
    (r36 : c.nreg 2936 = w) (r51 : c.nreg 2951 = Rb) (r57 : c.nreg 2957 = h + 8 * k)
    (r34 : c.nreg 2934 = M) (r33 : c.nreg 2933 = H) (r38 : c.nreg 2938 = k)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d)
    (hν : ∀ x ∈ verts N Q, ν x < w ∧ ι (ν x) = x)
    (hι : ∀ v < w, ι v ∈ verts N Q ∧ ν (ι v) = v) (hw : w ≤ 2 * Q.card)
    (hT : ∀ a < Q.card, c.nmem (h + a) = ν (N.tail (Frame.cδ g N Q a)))
    (hH : ∀ a < Q.card, c.nmem (h + k + a) = ν (N.head (Frame.cδ g N Q a)))
    (hI : ∀ v < w, c.nmem (h + 2 * k + v) = g.gv (ι v))
    (hval : ∀ v < w, (f (ι v) : ℝ) = sgnD H M (c.nmem (Rb + v)) ∧ c.nmem (Rb + v) ≤ WN)
    (hM : M = 2 * H + 1) (hHW : H ≤ WN)
    (hℓL : ∀ x ∈ Q, |ℓ x| ≤ L) (hL : ∑ x ∈ Q, |ℓ x| ≤ L)
    (hmk : Q.card ≤ k) (hk2 : w ≤ 2 * k)
    (hph : h + 8 * k + w ≤ p) (hWd : Ws < d) (hEd : E ≤ d) (hRd : R + n₂ ≤ d) (hRb : Rb + w ≤ d) (heh : e ≤ h)
    (hroom : h + 10 * k + 5 * (Q.card + w) + 8 * (w + 1) + 1 ≤ W)
    (hWN : 4 * WN + 3 * L + 2 ≤ W) (h10 : 10 ≤ W) :
    ∃ c' t g', Exec P W (fbYes WN) c c' t ∧ t ≤ fbYesCost j (E - Z) n₂ Q.card w ∧
      PotOut (pg N Q ℓ) (some g') ∧ Frame.Res g N L Q (some g') d e c' ∧
      (∀ a < d, (∃ i < j, c.nmem (p + i) = a) → c'.nmem a = 0) ∧
      (∀ a < d, Z ≤ a → a < E → c'.nmem a = 0) ∧ (∀ a < d, R ≤ a → a < R + n₂ → c'.nmem a = 0) ∧
      (∀ a < d, (∀ i < j, c.nmem (p + i) ≠ a) → (a < Z ∨ E ≤ a) → (a < R ∨ R + n₂ ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, e ≤ a → a < h → c'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨-, -, ok2, sr2, ok3, sr3⟩ := fbOL_ok
  have he := hin.en
  unfold Frame.fsz at he
  -- the write-back
  obtain ⟨c₁, e₁, g₁, f₁, m₁, rr₁, rm₁, o₁⟩ := cpRegs_exec (P := P) (W := W) _ ok2 sr2 c hc
  simp only [fbWL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₁
  obtain ⟨u60, u61, u62, u63, u64⟩ := g₁
  have F₁ : ∀ r, (r < 2860 ∨ 2864 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁ r (by simp [fbWL]; omega)
  have e₂ := Exec.constN (P := P) e₁.wb_right 2865 WN (by omega)
  set c₂ := ({ c₁ with nreg := upd c₁.nreg 2865 WN } : Config) with hc₂
  have q : ∀ r, r ≠ 2865 → c₂.nreg r = c₁.nreg r := fun r hr => by
    simp only [hc₂, upd_other _ _ _ hr]
  have hv' : ∀ v < w, c.nmem (Rb + v) ≤ WN := fun v hv => (hval v hv).2
  obtain ⟨c₃, t₃, e₃, ht₃, w₃, k₃, n₃, rr₃, rm₃, o₃⟩ := wbProg_exec (P := P) (n := w) (INb := Rb)
    (Ob := h + 8 * k) (M := M) (H := H) (L := WN) c₂ e₂.wb_right
    (by rw [q _ (by omega), u60, r36]) (by rw [q _ (by omega), u61, r51])
    (by rw [q _ (by omega), u62, r57]) (by rw [q _ (by omega), u63, r34])
    (by rw [q _ (by omega), u64, r33]) (by simp [hc₂]) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun i hi => by
      show c₁.nmem (Rb + i) + WN ≤ W
      rw [m₁]; have := hv' i hi; omega)
  have M₃ : ∀ a, (a < h + 8 * k ∨ h + 8 * k + w ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [k₃ a ha]; show c₁.nmem a = _; rw [m₁]
  have R₃ : ∀ r, 2871 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [n₃ r (by omega), q r (by omega), F₁ r (by omega)]
  have hF₃ : ∀ v < w, (c₃.nmem (h + 8 * k + v) : ℤ) = f (ι v) + WN := fun v hv => by
    rw [w₃ v hv]
    have h1 := (hval v hv).1
    rw [show c₂.nmem (Rb + v) = c.nmem (Rb + v) by show c₁.nmem _ = _; rw [m₁]] 
    have hb := abs_le.1 (sgnD_le_WN h1 hM (hv' v hv))
    rw [wb_val h1 (by omega)]
    exact Int.toNat_of_nonneg (by omega)
  -- the clearing
  have hlog₃ : ∀ i < j, c₃.nmem (p + i) = c.nmem (p + i) := fun i hi => by
    have := hlog i hi
    exact M₃ _ (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, z₄, y₄, x₄, k₄, n₄, rr₄, rm₄, o₄⟩ := fbClr_exec (P := P) c₃
    e₃.wb_right (by rw [R₃ _ (by omega), r24]) (by rw [R₃ _ (by omega), r25])
    (by rw [R₃ _ (by omega), r26]) (fun i hi => by rw [hlog₃ i hi]; exact hlog i hi) hp
    (by rw [R₃ _ (by omega), r54]) (by rw [R₃ _ (by omega), r31]) (by rw [R₃ _ (by omega), r53])
    (by rw [R₃ _ (by omega), r52]) hZE (by omega) (by omega) (by omega)
  have M₄ : ∀ a, d ≤ a → c₄.nmem a = c₃.nmem a := fun a ha =>
    k₄ a (fun i hi => by rw [hlog₃ i hi]; have := hlog i hi; omega) (by omega) (by omega)
  have R₄ : ∀ r, 2930 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [n₄ r (by omega) (by omega) (by omega), R₃ r (by omega)]
  -- `ndC`
  obtain ⟨c₅, e₅, g₅, f₅, m₅, rr₅, rm₅, o₅⟩ := cpRegs_exec (P := P) (W := W) _ ok3 sr3 c₄
    e₄.wb_right
  simp only [fbYL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at g₅
  obtain ⟨u64', u75⟩ := g₅
  have F₅ : ∀ r, 2930 ≤ r → c₅.nreg r = c.nreg r := fun r hr => by
    rw [f₅ r (by simp [fbYL]; omega), R₄ r hr]
  obtain ⟨c₆, t₆, e₆, ht₆, s50, s51, s52, s53, s54, s55, sn₆, sm₆, sr₆, srm₆, so₆⟩ :=
    Frame.ndC_exec (I := P) c₅ e₅.wb_right (by rw [u64', R₄ _ (by omega), r36])
      (by rw [F₅ _ (by omega), r03]) (by rw [u75, R₄ _ (by omega), r38]) (by omega) h10
  have M₆ : ∀ a, d ≤ a → c₆.nmem a = c₃.nmem a := fun a ha => by rw [sm₆, m₅, M₄ a ha]
  have hin₆ : Frame.InP g N ℓ L n Q d e c₆ := Frame.inP_stab hin fun a h1 h2 => by
    refine ⟨?_, ?_⟩
    · rw [M₆ a h1, M₃ a (by omega)]
    · rw [srm₆, rm₅, rm₄, rm₃]; show c₁.rmem a = _; rw [rm₁]
  -- the renormalization
  obtain ⟨c₇, t₇, g', e₇, ht₇, hpo, hres, hm₇, hn₇, hr₇, hrm₇, ho₇⟩ :=
    Frame.resProg_res (I := P) (g := g) (N := N) (f := f) (ν := ν) (ι := ι) (w := w) (Tb := h)
      (HHb := h + k) (Fb := h + 8 * k) (Ab := h + 10 * k) (Ib := h + 2 * k) (Lf := WN)
      c₆ e₆.wb_right hin₆ hf (by rw [sn₆ _ (by omega), F₅ _ (by omega), r04]) s50 s51 s52 s53
      s54 s55 hν hι hw
      (fun a ha => by rw [M₆ _ (by omega), M₃ _ (by omega)]; exact hT a ha)
      (fun a ha => by rw [M₆ _ (by omega), M₃ _ (by omega)]; exact hH a ha)
      (fun v hv => by rw [M₆ _ (by omega)]; exact hF₃ v hv)
      (fun v hv => by rw [M₆ _ (by omega), M₃ _ (by omega)]; exact hI v hv)
      (fun v hv => sgnD_le_WN (hval v hv).1 hM (hv' v hv)) hℓL hL
      (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by omega) (by omega)
  have M₇ : ∀ a, a < d → c₇.nmem a = c₄.nmem a := fun a ha => by
    rw [hm₇ a (Or.inl (by unfold Frame.fin; omega)) (Or.inl (by omega)), sm₆, m₅]
  refine ⟨c₇, (5 + (1 + t₃)) + (t₄ + (2 + (t₆ + t₇))), g',
    .seq (.seq e₁ (.seq e₂ e₃)) (.seq e₄ (.seq e₅ (.seq e₆ e₇))), ?_, hpo, hres,
    fun a ha h => ?_, fun a ha h1 h2 => ?_, fun a ha h1 h2 => ?_, fun a ha h1 h2 h3 => ?_,
    fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have : (fbWL).length = 5 := rfl
    have : (fbYL).length = 2 := rfl
    unfold fbYesCost; omega
  · rw [M₇ a ha]; obtain ⟨i, hi, rfl⟩ := h; exact z₄ _ ⟨i, hi, by rw [hlog₃ i hi]⟩
  · rw [M₇ a ha]; exact y₄ a h1 h2
  · rw [M₇ a ha]; exact x₄ a h1 h2
  · rw [M₇ a ha, k₄ a (fun i hi => by rw [hlog₃ i hi]; exact h1 i hi) h2 h3, M₃ a (by omega)]
  · rw [hm₇ a (Or.inr h1) (Or.inl (by omega)), sm₆, m₅, M₄ a (by omega), M₃ a (by omega)]
  · rw [hn₇ r (by omega), sn₆ r (by omega), F₅ r (by omega)]
  · rw [hr₇, sr₆, rr₅, rr₄, rr₃]; show c₁.rreg = _; rw [rr₁]
  · rw [hrm₇, srm₆, rm₅, rm₄, rm₃]; show c₁.rmem = _; rw [rm₁]
  · rw [ho₇, so₆, o₅, o₄, o₃]; show c₁.output = _; rw [o₁]

end Yes

end NegSSSP

end PlanarFlow
