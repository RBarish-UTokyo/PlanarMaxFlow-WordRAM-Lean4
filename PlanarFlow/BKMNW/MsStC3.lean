module

public import PlanarFlow.BKMNW.MsStC2

/-!
# The MSSP encoder, stage C2: Klein's initial trees (`kiProg`) and the out-lists (`osProg`)

* `svSet` (saves `r7950`, `r7957`, `r7959` into `r8297 … r8299`, which every later stage keeps),
  `kiL`, **`kiSet = hpProg 7980 8262 kiL`** (the registers of `StEnc.kiProg`: `nD`, `NT`, `NF`,
  `RV`, `IV = IM + iIV nD n k`, `n = 4 nD + 1`, `ofF = 2 nD + 1`, `cV`, `cF`,
  `PR = A0 + 9 n + nD + 1`, `Z = aZk`, `Gb = p + 16 m`), `ggCp` (the two words at `aGG` copied to
  `Gb`, below the image of the trees), `osL`, **`osSet = hpProg 1500 8262 osL`** (the registers of
  `osProg`: `Ob = aOs`, the arrays `OB`, `OE`, `OL` of Klein's input);
* **`msC2 = kiSet ; ggCp ; StEnc.kiProg ; osSet ; osProg`**, **`msC2_exec`**: the words of
  `KInit` at `IM + iIV nD n k` (`StEnc.kiProg_exec`) and of `KOut` at `IM + iOB` (`osProg_kout`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

/-- Saves `nD`, `cV`, `cF`. -/
def svSet : Stmt := block [.copyN 8297 7950, .copyN 8298 7957, .copyN 8299 7959]

theorem svSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W svSet c c' t ∧ t = 3 ∧ c'.nreg 8297 = c.nreg 7950 ∧
      c'.nreg 8298 = c.nreg 7957 ∧ c'.nreg 8299 = c.nreg 7959 ∧
      (∀ r, r < 8297 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold svSet
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- Restores `nD`, `cV`, `cF`. -/
def rsSet : Stmt := block [.copyN 7950 8297, .copyN 7957 8298, .copyN 7959 8299]

theorem rsSet_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W rsSet c c' t ∧ t = 3 ∧ c'.nreg 7950 = c.nreg 8297 ∧
      c'.nreg 7957 = c.nreg 8298 ∧ c'.nreg 7959 = c.nreg 8299 ∧
      (∀ r, r ≠ 7950 → r ≠ 7957 → r ≠ 7959 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rsSet
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The registers of `kiProg` as linear forms. -/
def kiL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8297)], 0),
    ([(1, hpM.v 8282), (4, hpM.v 8297)], 0),
    ([(1, hpM.v 8282), (1, hpM.v 8297)], 0),
    ([(1, hpM.v 8282)], 0),
    ([(1, hpM.v 8282), (21, hpM.v 8297), (1, hpM.v 8156), (3, hpM.one)], 0),
    ([(4, hpM.v 8297), (1, hpM.one)], 0),
    ([(2, hpM.v 8297), (1, hpM.one)], 0),
    ([(1, hpM.v 8298)], 0),
    ([(1, hpM.v 8299)], 0),
    ([(1, hpM.v 8290), (37, hpM.v 8297), (10, hpM.one)], 0),
    ([(1, hpM.v 8292)], 0),
    ([(1, hpM.v 8280), (16, hpM.v 8000)], 0)]

theorem kiL_shape : hpShape 8000 8300 37 0 kiL = true := by decide

def kiSet : Stmt := hpProg 7980 7370 kiL

theorem kiSet_exec (c : Config) (hc : WordsBounded W c) {nD cV cF IM k A0 Z p m : ℕ}
    (r97 : c.nreg 8297 = nD) (r98 : c.nreg 8298 = cV) (r99 : c.nreg 8299 = cF)
    (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k) (r90 : c.nreg 8290 = A0)
    (r92 : c.nreg 8292 = Z) (r80 : c.nreg 8280 = p) (r00 : c.nreg 8000 = m)
    (hW : IM + 21 * nD + k + 3 + A0 + 37 * nD + 10 + p + 16 * m + 37 ≤ W) :
    ∃ c', Exec P W kiSet c c' (hpCost kiL) ∧
      c'.nreg 7980 = nD ∧ c'.nreg 7981 = IM + 4 * nD ∧ c'.nreg 7982 = IM + nD ∧
      c'.nreg 7983 = IM ∧ c'.nreg 7984 = IM + 21 * nD + k + 3 ∧ c'.nreg 7985 = 4 * nD + 1 ∧
      c'.nreg 7986 = 2 * nD + 1 ∧ c'.nreg 7987 = cV ∧ c'.nreg 7988 = cF ∧
      c'.nreg 7989 = A0 + 37 * nD + 10 ∧ c'.nreg 7990 = Z ∧ c'.nreg 7991 = p + 16 * m ∧
      (∀ r, (r < 7980 ∨ 7992 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7980 7370 kiL :=
    hpShape_ok kiL_shape (by omega) (by omega) (by simp [kiL]) (by omega) (by simp [kiL])
  have h98 := hc.1 8298
  have h99 := hc.1 8299
  have h92 := hc.1 8292
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) kiL 7980 hok c hc (fun e he => by
    simp only [kiL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r97,
        r98, r99, r82, r56, r90, r92, r80, r00] <;> omega)
  have g : ∀ j < 12, c'.nreg (7980 + j) =
      hpSum c.nreg (kiL.getD j ([], 0)).1 - (kiL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [kiL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [kiL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 1 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 2 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 3 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 4 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 5 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 6 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 7 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 8 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 9 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 10 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 11 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring

/-- The two words at `aGG` copied to `Gb = r7991`. -/
def ggCp : Stmt :=
  block [.loadN 7366 8284, .storeN 7991 7366, .constN 7360 1, .addN 7367 8284 7360,
    .loadN 7366 7367, .addN 7368 7991 7360, .storeN 7368 7366]

theorem ggCp_exec (c : Config) (hc : WordsBounded W c) {GG Gb : ℕ} (r84 : c.nreg 8284 = GG)
    (r91 : c.nreg 7991 = Gb) (hGb : Gb + 1 ≤ W) (hGG : GG + 1 ≤ W)
    (hd : GG + 2 ≤ Gb ∨ Gb + 2 ≤ GG) :
    ∃ c' t, Exec P W ggCp c c' t ∧ t = 7 ∧ c'.nmem Gb = c.nmem GG ∧
      c'.nmem (Gb + 1) = c.nmem (GG + 1) ∧
      (∀ a, a ≠ Gb → a ≠ Gb + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7360 ∨ 7368 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 := hc.2 GG
  have h2 := hc.2 (GG + 1)
  unfold ggCp
  exec_block
  all_goals try ((try config_simp); (try simp only [r84, r91]); omega)
  refine ⟨rfl, ?_, ?_, fun a a1 a2 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r84, r91])
  all_goals (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The registers of `osProg` as linear forms (`r1503` unused, set to `0`). -/
def osL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8297)], 0),
    ([(4, hpM.v 8297), (1, hpM.one)], 0),
    ([(1, hpM.v 8282), (4, hpM.v 8297)], 0),
    ([], 0),
    ([(1, hpM.v 8282), (6, hpM.v 8297)], 0),
    ([(1, hpM.v 8293)], 0),
    ([(1, hpM.v 8293), (4, hpM.v 8297), (2, hpM.one)], 0),
    ([(1, hpM.v 8282), (12, hpM.v 8297), (1, hpM.v 8156), (1, hpM.one)], 0),
    ([(1, hpM.v 8282), (16, hpM.v 8297), (1, hpM.v 8156), (2, hpM.one)], 0),
    ([(1, hpM.v 8282), (20, hpM.v 8297), (1, hpM.v 8156), (3, hpM.one)], 0)]

theorem osL_shape : hpShape 8000 8300 20 0 osL = true := by decide

def osSet : Stmt := hpProg 1500 7370 osL

theorem osSet_exec (c : Config) (hc : WordsBounded W c) {nD IM k Ob : ℕ}
    (r97 : c.nreg 8297 = nD) (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k)
    (r93 : c.nreg 8293 = Ob) (hW : IM + 20 * nD + k + 3 + Ob + 4 * nD + 2 + 20 ≤ W) :
    ∃ c', Exec P W osSet c c' (hpCost osL) ∧
      c'.nreg 1500 = nD ∧ c'.nreg 1501 = 4 * nD + 1 ∧ c'.nreg 1502 = IM + 4 * nD ∧
      c'.nreg 1504 = IM + 6 * nD ∧ c'.nreg 1505 = Ob ∧ c'.nreg 1506 = Ob + 4 * nD + 2 ∧
      c'.nreg 1507 = IM + 12 * nD + 1 + k ∧ c'.nreg 1508 = IM + 16 * nD + 2 + k ∧
      c'.nreg 1509 = IM + 20 * nD + 3 + k ∧
      (∀ r, (r < 1500 ∨ 1510 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 1500 7370 osL :=
    hpShape_ok osL_shape (by omega) (by omega) (by simp [osL]) (by omega) (by simp [osL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) osL 1500 hok c hc (fun e he => by
    simp only [osL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r97,
        r82, r56, r93] <;> omega)
  have g : ∀ j < 10, c'.nreg (1500 + j) =
      hpSum c.nreg (osL.getD j ([], 0)).1 - (osL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [osL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [osL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 1 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 2 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 4 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 5 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 6 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 7 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 8 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 9 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring

/-- **Stage C2**, part a: the trees. -/
def msC2a : Stmt := .seq kiSet (.seq ggCp StEnc.kiProg)

/-- **Stage C2**, part b: the out-lists. -/
def msC2b : Stmt := .seq osSet osProg

/-- **Stage C2.** -/
def msC2 : Stmt := .seq msC2a msC2b

section C2

open STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

/-- The cost of stage C2. -/
def costC2 (nD nF nV : ℕ) : ℕ :=
  hpCost kiL + 7 + StEnc.kiCost nD nF nV + hpCost osL + osCost nD (4 * nD + 1)

lemma kiOff (nD k : ℕ) : Klein.iIV nD (4 * nD + 1) k = 21 * nD + k + 3 ∧
    Klein.iOL nD (4 * nD + 1) k = 20 * nD + 3 + k ∧ Klein.iOB nD (4 * nD + 1) k = 12 * nD + 1 + k ∧
    Klein.iOE nD (4 * nD + 1) k = 16 * nD + 2 + k ∧ Klein.iXT nD (4 * nD + 1) k = 37 * nD + k + 11 ∧
    Klein.iHD nD (4 * nD + 1) k = 37 * nD + k + 7 := by
  simp only [Klein.iIV, Klein.iOL, Klein.iOB, Klein.iOE, Klein.iXT, Klein.iHD]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

set_option maxHeartbeats 4000000 in
/-- **Stage C2a: the trees** (the words of `KInit`, for any memory agreeing on their region). -/
theorem msC2a_exec [Nonempty D] {M : CombMap D V F} (hM : M.IsPlane) {nD nF nV : ℕ}
    (σ : D ≃ Fin nD) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV) {T₀ : DTree M} (d₀ : D)
    (hroot : T₀.root = M.face d₀) {IM A0 Z p m k GG : ℕ} (c : Config) (hc : WordsBounded W c)
    (r97 : c.nreg 8297 = nD) (r98 : c.nreg 8298 = nF) (r99 : c.nreg 8299 = nV)
    (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k) (r90 : c.nreg 8290 = A0)
    (r92 : c.nreg 8292 = Z) (r80 : c.nreg 8280 = p) (r00 : c.nreg 8000 = m)
    (r84 : c.nreg 8284 = GG)
    (hNT : ∀ d, c.nmem (IM + 4 * nD + σ d) = 1 + τv (M.face d))
    (hNF : ∀ d, c.nmem (IM + nD + σ d) = 2 * nD + 1 + τf (M.tail d))
    (hRV : ∀ d, c.nmem (IM + σ d) = σ (M.rev d))
    (hPAR : ∀ x, x ≠ T₀.root → c.nmem (A0 + 37 * nD + 10 + 1 + τv x) = σ (T₀.par x))
    (hG0 : c.nmem GG = σ d₀) (hG1 : c.nmem (GG + 1) = σ d₀)
    (hnF : nF ≤ 4 * nD + 1) (hnV : nV ≤ 4 * nD + 1)
    (l1 : p + 16 * m + 2 ≤ IM) (l2 : IM + 37 * nD + k + 9 ≤ GG) (l3 : GG + 2 ≤ A0)
    (l4 : A0 + 37 * nD + 11 + nF ≤ Z)
    (hW : Z + 8 * nF + 4 * nD + 15 * nV + 3 + IM + 21 * nD + k + 3 + A0 + 37 * nD + 10 + p +
      16 * m + 37 ≤ W) :
    ∃ e t, Exec P W msC2a c e t ∧ t ≤ hpCost kiL + 7 + StEnc.kiCost nD nF nV ∧
      ∃ (ts : List F) (C₀ : DTree M.dual) (cs : List V), C₀.root = M.tail d₀ ∧
        (∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) ∧
        (∀ mem : ℕ → ℕ, (∀ a, IM + 21 * nD + k + 3 ≤ a → a < IM + 37 * nD + k + 11 →
            mem a = e.nmem a) → ∀ Pk : Input, (∀ j, j < Klein.iHD nD (4 * nD + 1) k + 4 →
            Pk.data.getD j 0 = mem (IM + j)) →
          Klein.KInit M.dual σ (fun x => 1 + (τv x : ℕ)) (fun v => 2 * nD + 1 + (τf v : ℕ))
            (4 * nD + 1) k (toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts
            ((List.finRange nV).map τf.symm) cs Pk) ∧
        (∀ a, (a < IM + 21 * nD + k + 3 ∨ IM + 37 * nD + k + 13 ≤ a) → a ≠ p + 16 * m →
          a ≠ p + 16 * m + 1 → (a < A0 + 37 * nD + 11 ∨ A0 + 37 * nD + 11 + nF ≤ a) →
          (a < Z ∨ Z + 8 * nF + 4 * nD + 15 * nV + 3 ≤ a) → e.nmem a = c.nmem a) ∧
        (∀ r, (r < 1400 ∨ 1720 ≤ r) → (r < 7360 ∨ 7372 ≤ r) → (r < 7980 ∨ 8000 ≤ r) →
          e.nreg r = c.nreg r) ∧
        e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := kiOff nD k
  have hσ : ∀ d, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨c₁, e₁, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, aR, am, ar, arm,
    ao⟩ := kiSet_exec (P := P) c hc r97 r98 r99 r82 r56 r90 r92 r80 r00 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g0, g1, gm, gR, gr, grm, go⟩ :=
    ggCp_exec (P := P) c₁ e₁.wb_right (GG := GG) (Gb := p + 16 * m)
      (by rw [aR _ (by omega) (by omega) (by omega)]; exact r84) a91 (by omega) (by omega)
      (Or.inr (by omega))
  rw [am] at g0 g1
  have m2 : ∀ a, a ≠ p + 16 * m → a ≠ p + 16 * m + 1 → c₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [gm a h1 h2, am]
  have q2 : ∀ r, (r < 7360 ∨ 7368 < r) → c₂.nreg r = c₁.nreg r := gR
  obtain ⟨c₃, t₃, e₃, ht₃, ts, C₀, cs, hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC, hH0, hH1, hH2, hH3,
    m3, R3, rr3, rm3, o3⟩ :=
    StEnc.kiProg_exec (P := P) hM σ τv τf d₀ d₀ hroot (NTb := IM + 4 * nD) (NFb := IM + nD)
      (RVb := IM) (IVb := IM + 21 * nD + k + 3) (ofF := 2 * nD + 1) (PRb := A0 + 37 * nD + 10)
      (Z := Z) (Gb := p + 16 * m) (n := 4 * nD + 1) c₂ e₂.wb_right
      (by rw [q2 _ (by omega)]; exact a80) (by rw [q2 _ (by omega)]; exact a81)
      (by rw [q2 _ (by omega)]; exact a82) (by rw [q2 _ (by omega)]; exact a83)
      (by rw [q2 _ (by omega)]; exact a84) (by rw [q2 _ (by omega)]; exact a85)
      (by rw [q2 _ (by omega)]; exact a86) (by rw [q2 _ (by omega)]; exact a87)
      (by rw [q2 _ (by omega)]; exact a88) (by rw [q2 _ (by omega)]; exact a89)
      (by rw [q2 _ (by omega)]; exact a90) (by rw [q2 _ (by omega)]; exact a91)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hNT d)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hNF d)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hRV d)
      (fun x hx => by
        have := (τv x).2
        rw [m2 _ (by omega) (by omega)]; exact hPAR x hx)
      (g0.trans hG0) (g1.trans hG1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hnF hnV
      (by omega) (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ts, C₀, cs, hC₀, hoff,
    fun mem hmem Pk hPk => ?_, fun a h1 h2 h3 h4 h5 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr3, gr, ar], by rw [rm3, grm, arm], by rw [o3, go, ao]⟩
  · refine MsEnc.kInit_ofK σ τv τf hOT hOC (ib := IM) (mem := mem) (fun i h => ?_)
      (fun i h => ?_) (fun i h => ?_) (fun i h => ?_) ?_ ?_ ?_ ?_ Pk hPk hnF hnV
    · have : i < nF := by simpa using h
      rw [hn1, show IM + (21 * nD + k + 3) + i = IM + 21 * nD + k + 3 + i by ring,
        hmem _ (by omega) (by omega)]; exact hIV i h
    · have : ts.length ≤ nF := by
        have h1 := hOT.ylen; have h2 := Fintype.card_fin nF ▸ Fintype.card_congr τv; omega
      rw [hn1, show IM + (21 * nD + k + 3) + (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIT i h
    · have : i < nV := by simpa using h
      rw [hn1, show IM + (21 * nD + k + 3) + 2 * (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + 2 * (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIF i h
    · have : cs.length ≤ nV := by
        have h1 := hOC.ylen; have h2 := Fintype.card_fin nV ▸ Fintype.card_congr τf; omega
      rw [hn1, show IM + (21 * nD + k + 3) + 3 * (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + 3 * (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIC i h
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) by ring, hmem _ (by omega) (by omega)]
      exact hH0
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 1 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 1 by ring, hmem _ (by omega) (by omega)]
      exact hH1
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 2 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 2 by ring, hmem _ (by omega) (by omega)]
      exact hH2
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 3 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 3 by ring, hmem _ (by omega) (by omega)]
      exact hH3
  · rw [m3 a (by omega) h4 h5, m2 a h2 h3]
  · rw [R3 r (by omega), q2 r (by omega), aR r (by omega) (by omega) (by omega)]

set_option maxHeartbeats 2000000 in
/-- **Stage C2b: the out-lists** (`KOut` for any input agreeing with the image). -/
theorem msC2b_exec {N : CombMap D' X Y} {S : Finset D'} {nD : ℕ} (σ' : D' ≃ Fin nD)
    {ιv : X → ℕ} (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < 4 * nD + 1)
    {IM k Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r97 : c.nreg 8297 = nD) (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k)
    (r93 : c.nreg 8293 = Ob)
    (hNT' : ∀ d, c.nmem (IM + Klein.iNT nD + σ' d) = ιv (N.tail d))
    (hIS : ∀ d, c.nmem (IM + Klein.iIS nD + σ' d) = if d ∈ S then 1 else 0)
    (l1 : IM + 21 * nD + k + 3 ≤ Ob) (hW : Ob + 2 * (4 * nD + 1) + 1 + IM + 20 * nD + k + 3 +
      4 * nD + 22 ≤ W) :
    ∃ e t, Exec P W msC2b c e t ∧ t ≤ hpCost osL + osCost nD (4 * nD + 1) ∧
      (∀ Pk : Input, (∀ i < Klein.iOL nD (4 * nD + 1) k + nD,
          Pk.data.getD i 0 = e.nmem (IM + i)) →
        Klein.KOut N S σ' ιv (4 * nD + 1) k Pk) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * (4 * nD + 1) + 1 ≤ a) →
        (a < IM + 12 * nD + 1 + k ∨ IM + 21 * nD + k + 3 ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 1521 ≤ r) → r ≠ 7370 → r ≠ 7371 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := kiOff nD k
  have hσ' : ∀ d, (σ' d : ℕ) < nD := fun d => (σ' d).2
  obtain ⟨c₄, e₄, b00, b01, b02, b04, b05, b06, b07, b08, b09, bR, bm, br, brm, bo⟩ :=
    osSet_exec (P := P) c hc (nD := nD) (IM := IM) (k := k) (Ob := Ob) r97 r82 r56 r93 (by omega)
  obtain ⟨c₅, t₅, e₅, ht₅, hKO, m5, R5, rr5, rm5, o5⟩ :=
    osProg_kout (P := P) (M := N) (S := S) σ' (n := 4 * nD + 1) (k := k) (β := IM) (Ob := Ob)
      hinj hιv (Or.inr (by rw [hn2]; omega)) ⟨by omega, by rw [hn2]; omega, by omega, by omega⟩
      c₄ e₄.wb_right (fun d => by rw [bm]; exact hNT' d) (fun d => by rw [bm]; exact hIS d)
      b00 b01 (by rw [b02]; rfl) (by rw [b04]; rfl) b05 (by rw [b06]; ring)
      (by rw [b07, hn3]; ring) (by rw [b08, hn4]; ring) (by rw [b09, hn2]; ring)
  refine ⟨c₅, _, .seq e₄ e₅, by omega, hKO, fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr5, br], by rw [rm5, brm], by rw [o5, bo]⟩
  · rw [m5 a h1 (by rw [hn3, hn2]; omega), bm]
  · rw [R5 r (by omega), bR r (by omega) h2 h3]

end C2

end MsEnc

end BKMNW

end PlanarFlow
