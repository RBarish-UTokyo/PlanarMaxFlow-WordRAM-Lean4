module

public import PlanarSeparator.Machine.SepProg10

/-!
# Miller's program on one stellar subdivision of a plain encoding

`PlanarSeparator.MillerProg.prog10_spec10` runs Miller's whole program on the *twice* subdivided
map of a plain encoding (the recursion for negative lengths). The split chain of `BKMNW` needs
Miller's separator of the *once* subdivided piece map `(psep M hσ hB).stellar` with arbitrary
natural vertex weights. Here:

* `msIn1`/`msIn2`/**`msIn`**: from the plain encoding (`Enc`) of a map `M` with `m` darts at `B₀`
  and a weight array (indexed by `stVi vn fn`, `nV + nF` words) at `B₀ + 5 m`, one stellar
  subdivision (`stA ; stV`: the reversals at `0`, the vertex numbers at `11 m`, darts numbered by
  `stCode c`, faces the triples `phi3`), the weights copied to `bw`, and the registers of
  `millerA` (`aSetup`).
* **`msep := msIn ; setup10 ; millerFull`**, **`msep_spec`**: for a plane map without loops with
  `m ≥ 2` darts and weights of positive total, `msep` ends within
  `msT m (nV + nF) = (231 m + 60 n + 156) log₂ n + 1844 m + 817 n + 1654` steps
  (`n = nV + nF`) with a separator `R` of `M.stellar` in the output registers (`r641` its length,
  the dart numbers `stCode c` at `r640`, the face marks at `r642` read with `r643`, `r644`, the
  faces numbered by `stFn c`) meeting `SepOK (wR w) (6 √n + 4)`; the memory from `B₀` on is
  kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

open Finset PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg
  PlanarSeparator.CycleSearch WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The bases of the subdivision (the input at `r393 = B₀`, `r390 = m`, `r391 = nV`): the
reversals at `0`, the vertex numbers at `11 m`, the weights at `r325 = B₀ + 5 m`. -/
def msIn1 : Stmt := block [.constN 306 3, .constN 307 1, .constN 308 2, .copyN 301 390,
  .copyN 302 393, .addN 303 302 390, .addN 304 303 390, .addN 315 304 390, .addN 316 315 390,
  .addN 325 316 390, .constN 305 0, .constN 327 11, .mulN 317 390 327, .copyN 318 391]

/-- The registers of the weight copy and of `aSetup` (`r326 = k = m`, `r330 = n = nV + nF`,
`bw = 17 k + 6 n`). -/
def msIn2 : Stmt := block [.copyN 326 390, .addN 330 391 392, .constN 334 17,
  .mulN 335 326 334, .constN 334 6, .mulN 336 330 334, .addN 340 335 336, .copyN 338 330,
  .copyN 339 325]

/-- **The input of Miller's program on one subdivision.** -/
def msIn : Stmt := .seq msIn1 <| .seq (.seq stA stV) <| .seq msIn2 <| .seq cpyN aSetup

/-- **Miller's separator of the stellar subdivision of a plain encoding.** -/
def msep : Stmt := .seq msIn (.seq setup10 millerFull)

/-- The time bound of `msep` (`m` darts, `n = nV + nF` vertices of the subdivision). -/
def msT (m n : ℕ) : ℕ := (231 * m + 60 * n + 156) * Nat.log 2 n + 1844 * m + 817 * n + 1654

variable {W : ℕ} {P : Input}

section Spec

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

set_option maxHeartbeats 8000000 in
/-- **The input of Miller's program on one subdivision, on the machine.** -/
theorem msIn_exec (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (w : Q ⊕ M.Face → ℕ) {B₀ : ℕ} {c₀ : Config}
    (hE : Enc M c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hw : ∀ x, c₀.nmem (B₀ + 5 * m + M.stVi vn fn x) = w x) (hn : 1 ≤ nV + nF)
    (hB : aEnd m (nV + nF) ≤ B₀) (hW : B₀ + 5 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t L, Exec P W msIn c₀ c' t ∧
      t ≤ 40 * m + 7 * (nV + nF) + 4 * Nat.log 2 (nV + nF) + 82 ∧
      Nat.log 2 (nV + nF) ≤ L ∧ L ≤ Nat.log 2 (nV + nF) + 1 ∧
      ARegs (aBase m (nV + nF) L) m (nV + nF) c' ∧
      (∀ y, c'.nmem (M.stCode c y) = M.stCode c (M.stellar.α y)) ∧
      (∀ y, (M.stCode c (M.stellar.φ y) : ℕ) = CycleSearch.phi3 (M.stCode c y)) ∧
      (∀ y, c'.nmem (11 * m + M.stCode c y) = M.stVi vn fn (M.stellar.vert y)) ∧
      (∀ x, c'.nmem ((aBase m (nV + nF) L).bw + M.stVi vn fn x) = w x) ∧
      (∀ a, B₀ ≤ a → c'.nmem a = c₀.nmem a) ∧
      c'.output = c₀.output := by
  have hB' := hB
  unfold aEnd at hB'
  -- 1. the bases
  obtain ⟨c₁, t₁, e₁, ht₁, hR₁, k325, hm₁, ho₁⟩ : ∃ c₁ t₁, Exec P W msIn1 c₀ c₁ t₁ ∧
      t₁ ≤ 14 ∧
      StR m B₀ (B₀ + m) (B₀ + 2 * m) 0 (B₀ + 3 * m) (B₀ + 4 * m) (11 * m) nV c₁ ∧
        c₁.nreg 325 = B₀ + 5 * m ∧ c₁.nmem = c₀.nmem ∧ c₁.output = c₀.output := by
    unfold msIn1
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [h390, h391, h393]); omega)
    refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [h390, h391, h393]) <;> omega)
  have j390 : c₁.nreg 390 = m := (e₁.nreg_of_wr (by decide)).trans h390
  have j391 : c₁.nreg 391 = nV := (e₁.nreg_of_wr (by decide)).trans h391
  have j392 : c₁.nreg 392 = nF := (e₁.nreg_of_wr (by decide)).trans h392
  -- 2. the subdivision
  obtain ⟨c₂, t₂, e₂, ht₂, hA₁, hφ₁, hV₁, hr₂, hm₂, ho₂⟩ := stPhase (P := P) (W := W) M c vn fn
    (c₀ := c₁) (by rw [hm₁]; exact hE) (by unfold StDisj; omega) (by omega) e₁.wb_right hR₁
  have g : ∀ r, 314 < r → c₂.nreg r = c₁.nreg r := fun r h => hr₂ r (by omega) (Or.inr h)
  set n := nV + nF with hn
  set bw := 17 * m + 6 * n with hbw
  -- 3. the registers of the copy
  obtain ⟨c₃, t₃, e₃, ht₃, q326, q330, q338, q339, q340, q307, hm₃, ho₃⟩ :
      ∃ c₃ t₃, Exec P W msIn2 c₂ c₃ t₃ ∧ t₃ ≤ 9 ∧ c₃.nreg 326 = m ∧ c₃.nreg 330 = n ∧
      c₃.nreg 338 = n ∧ c₃.nreg 339 = B₀ + 5 * m ∧ c₃.nreg 340 = bw ∧ c₃.nreg 307 = 1 ∧
      c₃.nmem = c₂.nmem ∧ c₃.output = c₂.output := by
    have hc := e₂.wb_right
    have a390 := (g 390 (by omega)).trans j390
    have a391 := (g 391 (by omega)).trans j391
    have a392 := (g 392 (by omega)).trans j392
    have a325 := (g 325 (by omega)).trans k325
    have a307 : c₂.nreg 307 = 1 := (hr₂ 307 (by omega) (Or.inl (by omega))).trans hR₁.r307
    unfold msIn2
    exec_block
    all_goals try (show _ ≤ W; config_simp; (try simp only [a390, a391, a392, a325]); omega)
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals (config_simp <;> (try simp only [a390, a391, a392, a325, a307, hbw, hn]) <;>
      omega)
  -- 4. the weights
  obtain ⟨c₄, t₄, e₄, ht₄, hd₄, hr₄, hm₄, ho₄⟩ := cpyN_exec (P := P) (W := W) (N := n)
    (bs := B₀ + 5 * m) (bd := bw) (by omega) (by omega) c₃ e₃.wb_right q307 q338 q339 q340
  -- 5. the registers of `millerA`
  obtain ⟨c', t₅, L, e₅, ht₅, hL1, hL2, hAR, -, hm₅, ho₅⟩ := aSetup_exec (P := P) (W := W)
    (k := m) (n := n) (by omega) (by omega) c₄ e₄.wb_right
    ((hr₄ 326 (by omega) (by omega) (by omega)).trans q326)
    ((hr₄ 330 (by omega) (by omega) (by omega)).trans q330)
  have M₅ : ∀ a, (a < bw ∨ bw + n ≤ a) → c'.nmem a = c₂.nmem a := fun a h => by
    rw [hm₅, hm₄ a h, hm₃]
  have eAll : Exec P W msIn c₀ c' _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have hk : ∀ y : StDart D, (M.stCode c y : ℕ) < 3 * m := fun y => (M.stCode c y).2
  have hlogeq : Nat.log 2 n = Nat.log 2 (nV + nF) := rfl
  refine ⟨c', _, L, eAll, by omega, hL1, hL2, hAR, fun y => ?_, hφ₁, fun y => ?_,
    fun x => ?_, fun a ha => ?_, ?_⟩
  · have := hk y
    rw [M₅ _ (by omega), ← zero_add (M.stCode c y : ℕ), hA₁ y]
  · have := hk y
    rw [M₅ _ (by omega), hV₁ y]
  · have h1 := (M.stVi vn fn x).2
    rw [show (aBase m n L).bw = bw from rfl, hm₅, hd₄ _ h1, hm₃,
      hm₂ _ (by omega) (by omega), hm₁]
    exact hw x
  · rw [M₅ _ (by omega), hm₂ _ (by omega) (by omega), hm₁]
  · rw [ho₅, ho₄, ho₃, ho₂, ho₁]

set_option maxHeartbeats 8000000 in
open Classical in
/-- **Miller's separator of the stellar subdivision of a plain encoding, on the machine.** For a
plane map `M` without loops with `m ≥ 2` darts, plainly encoded at `B₀ ≥ aEnd10 m n`
(`n = nV + nF`), with natural vertex weights `w` of positive total at `B₀ + 5 m` (indexed by
`stVi vn fn`), `msep` ends within `msT m n` steps with a separator `R` of `M.stellar` meeting
`SepOK (wR w) (6 √n + 4)` in the output registers: `r641 = R.1.k`, the numbers `stCode c` of its
darts at `r640`, and `G ∈ R.2 ↔ (mark of G ≠ r643 ↔ r644 = 1)` for the marks at `r642` (faces
numbered by `stFn c`). The memory from `B₀` on is kept. -/
theorem msep_spec (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (w : Q ⊕ M.Face → ℕ) {B₀ : ℕ} {c₀ : Config}
    (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (hpos : 0 < ∑ v, w v)
    (hE : Enc M c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hw : ∀ x, c₀.nmem (B₀ + 5 * m + M.stVi vn fn x) = w x)
    (hB : aEnd10 m (nV + nF) ≤ B₀) (hW : B₀ + 5 * m + nV + nF + 2 ≤ W)
    (hWt : 11 * m + 3 * ∑ v, w v + 4 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t, Exec P W msep c₀ c' t ∧ t ≤ msT m (nV + nF) ∧
      ∃ R : M.stellar.SCycle × Finset M.stellar.Face,
        c'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, c'.nmem (c'.nreg 640 + i) = M.stCode c (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ (c'.nmem (c'.nreg 642 + M.stFn c G) ≠ c'.nreg 643 ↔
          c'.nreg 644 = 1)) ∧
        SepOK (wR w) (6 * Nat.sqrt (nV + nF) + 4) R ∧
        ∀ a, B₀ ≤ a → c'.nmem a = c₀.nmem a := by
  set n := nV + nF with hn
  have hn1 : 1 ≤ n := by
    have := (vn (M.vert (c.symm ⟨0, by omega⟩))).2
    omega
  have hB0 : aEnd m n ≤ B₀ := by have h := hB; unfold aEnd10 at h; omega
  obtain ⟨c₁, t₁, L, e₁, ht₁, hL1, hL2, hAR, hA, hφ, hV, hw₁, hm₁, -⟩ :=
    msIn_exec (P := P) (W := W) M c vn fn w hE hw hn1 hB0 hW hc h390 h391 h392 h393
  have hc₁ := e₁.wb_right
  have hlogeq : Nat.log 2 n = Nat.log 2 (nV + nF) := rfl
  set b := aBase m n L with hb
  set S := b.bS₂ with hSdef
  have hSv : S = 22 * m + 14 * n + 3 + (L + 1) * n := rfl
  have hLn : (L + 1) * n ≤ (Nat.log 2 n + 2) * n := Nat.mul_le_mul_right _ (by omega)
  have hE' : S + 10 * m + 21 * n + 4 ≤ B₀ := by
    have h := hB; unfold aEnd10 aEnd at h; omega
  have hEW : S + 10 * m + 21 * n + 4 ≤ W := by omega
  have hS22 : 22 * m + 14 * n + 3 ≤ S := by omega
  have hlay : ALay b m n W := aLay_of hL1 hL2 (by omega)
  have hbV : b.bV = 11 * m := rfl
  have hbLv : b.bLv = 14 * m := rfl
  have hbw : b.bw = 17 * m + 6 * n := rfl
  have hlay9 : b.bS₂ + n ≤ S + n ∧ S + n + m ≤ S + m + n ∧ S + m + n + n ≤ S + m + 2 * n ∧
      S + m + 2 * n + n ≤ S + m + 3 * n ∧ S + m + 3 * n + 2 * n + 1 ≤ W := by omega
  have hlay10 : S + m + 3 * n + 2 * n + 1 ≤ S + m + 5 * n + 1 ∧
      S + m + 5 * n + 1 + n ≤ S + m + 6 * n + 1 ∧
      S + m + 6 * n + 1 + m ≤ S + 2 * m + 6 * n + 1 ∧
      S + 2 * m + 6 * n + 1 + m ≤ S + 3 * m + 6 * n + 1 ∧
      S + 3 * m + 6 * n + 1 + m ≤ S + 4 * m + 6 * n + 1 ∧
      S + 4 * m + 6 * n + 1 + m + 1 ≤ S + 5 * m + 6 * n + 2 ∧
      S + 5 * m + 6 * n + 2 + 3 * m ≤ S + 8 * m + 6 * n + 2 ∧
      S + 8 * m + 6 * n + 2 + n ≤ W ∧ S + 4 * m + 6 * n + 1 + 3 * m + 4 * n + 1 ≤ W := by
    omega
  have hlay11 : S + 8 * m + 6 * n + 2 + n ≤ S + 8 * m + 10 * n + 2 ∧
      S + 4 * m + 6 * n + 1 + 3 * m + 4 * n + 1 ≤ S + 8 * m + 10 * n + 2 ∧
      S + 8 * m + 10 * n + 2 + n ≤ S + 8 * m + 11 * n + 2 ∧
      S9Lay m n b.bV (S + 8 * m + 11 * n + 2) b.bLv (S + 8 * m + 12 * n + 2)
        (S + 9 * m + 12 * n + 2) (S + 9 * m + 13 * n + 2) (S + 9 * m + 14 * n + 2) W ∧
      S + 9 * m + 14 * n + 2 + 2 * n + 1 ≤ S + 9 * m + 16 * n + 3 ∧
      S9Lay m n b.bV (S + 9 * m + 16 * n + 3) b.bLv (S + 9 * m + 17 * n + 3)
        (S + 10 * m + 17 * n + 3) (S + 10 * m + 18 * n + 3) (S + 10 * m + 19 * n + 3) W := by
    refine ⟨by omega, by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> omega
  -- 1. the setup
  obtain ⟨c₂, t₂, e₂, ht₂, hfr₂, hR9, hR10, hR11, -, -, -, hz₂, hm₂, -⟩ :=
    setup10_exec (P := P) c₁ hc₁ hAR (by omega) hEW
  have hAR₂ : ARegs b m n c₂ := hAR.of_nreg hfr₂
  have Zr : ∀ a, S + n ≤ a → a < S + 10 * m + 21 * n + 4 → c₂.nmem a = 0 := fun a h1 h2 => by
    have := hz₂ (a - (S + n)) (by omega)
    rwa [show S + n + (a - (S + n)) = a by omega] at this
  have Lo : ∀ a, a < S + n → c₂.nmem a = c₁.nmem a := fun a h => hm₂ a (Or.inl h)
  -- 2. Miller's program
  obtain ⟨c₃, t₃, e₃, ht₃, T, T₁, l₀, l₂, K₀, cn, δ, x₀, xg, hl02, hl2s, h3, hK, -, -, h641,
      h640, hmk, hsep, -, hm₃⟩ :=
    millerFull_spec (M := M.stellar) (cd := M.stCode c)
      (vi := M.stVi vn fn) (A := fun x => c₁.nmem x)
      (V := fun x => c₁.nmem (11 * m + x)) w (P := P) (W := W) (c := c₂) (b := b)
      (bIm := S + n) (bMk := S + m + n) (bTmp := S + m + 2 * n) (bFc := S + m + 3 * n)
      (bA' := S + m + 6 * n + 1) (bL' := S + 2 * m + 6 * n + 1) (bS' := S + 3 * m + 6 * n + 1)
      (bSum' := S + 4 * m + 6 * n + 1) (bNx := S + m + 5 * n + 1)
      (bCy := S + 5 * m + 6 * n + 2) (bPos := S + 8 * m + 6 * n + 2)
      (bCv := S + 8 * m + 10 * n + 2) (bP1 := S + 8 * m + 11 * n + 2)
      (bI1 := S + 8 * m + 12 * n + 2) (bT1 := S + 9 * m + 13 * n + 2)
      (bF1 := S + 9 * m + 14 * n + 2) (bM1 := S + 9 * m + 12 * n + 2)
      (bP2 := S + 9 * m + 16 * n + 3) (bI2 := S + 9 * m + 17 * n + 3)
      (bT2 := S + 10 * m + 18 * n + 3) (bF2 := S + 10 * m + 19 * n + 3)
      (bM2 := S + 10 * m + 17 * n + 3)
      (isPlane_stellar hM) (M.isTriangle_stellar hl)
      hm2 hA hφ hV hpos hlay hWt hlay9
      hlay10 hlay11 e₂.wb_right hAR₂ hR9 hR10 hR11
      (fun x hx => Lo x (by omega))
      (fun x hx => by rw [hbV]; exact Lo _ (by omega))
      (fun v => by
        have := (M.stVi vn fn v).2
        rw [Lo _ (by omega)]; exact hw₁ v)
      (fun v hv => Zr _ (by omega) (by omega)) (fun x hx => Zr _ (by omega) (by omega))
      (fun v hv => Zr _ (by omega) (by omega)) (fun v hv => Zr _ (by omega) (by omega))
      (fun v hv => Zr _ (by omega) (by omega)) (fun v hv => Zr _ (by omega) (by omega))
  set R := bandSep T T₁ l₂ cn (wR w) δ x₀ (M.stellar.face xg)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), ?_, R, h641, h640, fun G => ?_,
    ⟨?_, hsep.2⟩, fun a ha => ?_⟩
  · -- the time
    have ht₁' : t₁ ≤ 40 * m + 7 * (nV + nF) + 4 * Nat.log 2 (nV + nF) + 82 := ht₁
    have ht₂' : t₂ ≤ 50 * m + 100 * (nV + nF) + 101 := ht₂
    have ht₃' : t₃ ≤ (231 * Nat.log 2 (nV + nF) + 1134) * m +
        (60 * (nV + nF) + 152) * Nat.log 2 (nV + nF) + 278 * (nV + nF) + 637 +
        (113 * m + 90 * (nV + nF) + 145) + (281 * m + 51 * (nV + nF) + 69) +
        (226 * m + 291 * (nV + nF) + 620) := ht₃
    have hX : (231 * Nat.log 2 (nV + nF) + 1134) * m +
        (60 * (nV + nF) + 152) * Nat.log 2 (nV + nF) + 278 * (nV + nF) + 637 +
        (113 * m + 90 * (nV + nF) + 145) + (281 * m + 51 * (nV + nF) + 69) +
        (226 * m + 291 * (nV + nF) + 620) =
        (231 * m + 60 * (nV + nF) + 152) * Nat.log 2 (nV + nF) + 1754 * m +
          710 * (nV + nF) + 1471 := by ring
    show t₁ + (t₂ + t₃) ≤ msT m (nV + nF)
    unfold msT
    clear * - ht₁' ht₂' ht₃' hX
    have : (231 * m + 60 * (nV + nF) + 156) * Nat.log 2 (nV + nF) =
        (231 * m + 60 * (nV + nF) + 152) * Nat.log 2 (nV + nF) + 4 * Nat.log 2 (nV + nF) := by
      ring
    omega
  · -- the marks
    have hfi : fi (M.stCode c) G = M.stFn c G := by
      unfold fi
      rw [← Map.stFn_face, (M.stellar.face_surjective G).choose_spec]
    rw [← hfi]
    exact hmk G
  · -- the number of darts
    have hk' : R.1.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) := hsep.1
    have h3n : (Nat.sqrt (nV + nF) + 1) * #(T.lvl l₂) ≤ nV + nF := h3
    have hl2n : l₂ ≤ l₀ + 2 * Nat.sqrt (nV + nF) + 1 := hl2s
    show R.1.k ≤ 6 * Nat.sqrt (nV + nF) + 4
    have h3' := Map.le_sqrt_of_mul_le' h3n
    rcases hK with ⟨rfl, rfl⟩ | ⟨-, hK, hK'⟩
    · rw [card_singleton] at hk'; clear * - hk' h3' hl2n; omega
    · have hK'' : (Nat.sqrt (nV + nF) + 1) * #(T.lvl l₀) ≤ nV + nF := hK'
      have := (card_le_card hK).trans (Map.le_sqrt_of_mul_le' hK'')
      clear * - hk' h3' hl2n this; omega
  · rw [hm₃ a (by omega), hm₂ a (Or.inr (by omega)), hm₁ a ha]

end Spec

end BKMNW

end PlanarFlow
