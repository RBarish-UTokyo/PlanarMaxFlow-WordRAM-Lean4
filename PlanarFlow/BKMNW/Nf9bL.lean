module

public import PlanarFlow.BKMNW.NcFzN
public import PlanarFlow.BKMNW.Nf7eWI
public import PlanarFlow.BKMNW.Nf7dI

/-!
# The envelopes of the frozen fix (room, zero area) and its step bound

Monotonicity facts (copies of `Nf7fA`/`Nf7fB` lemmas, suffix `9`, so that this file does not
depend on the `Nf7f*` files), and in the style of the envelopes of `fixP7`, in the size `m'` and the
offset `Z'` of the pendant frame (the base map has `m ≤ m'` darts, a part `k ≤ m` darts and
`b ≤ 2k` faces, `AS ≤ m' Z'`):

* `fpM9 m Z = fpB (m Z) m m`, `KM9 = 16 fpM9`, `LM9 = 8 fpM9` (bounds of `K`, `L`), `shw9` (the
  resident image `SH + WN`);
* **`wzF9 wzm m Z = Σ_{n ≤ m} (wzm n (2Z) + 9n + 1 + tsz n + rtW n (n·KM9 m Z) n) + shw9 m Z`**
  (the zero area);
* **`rOF9 C C₀ Rm m Z = 100 + 100m + lyP 0 (2m) m + lgT9 (2m) m + Σ_{n ≤ m} (RmS9 Rm n + negT C C₀ n)
  + valM9 m Z`** (the room above the heap top);
* **`fxT9 C C₀ m xf k`** (the steps) and **`fxT9_le_fixRun`**: the cost hypothesis of
  `fzHypF_of_frame`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset NegSSSP NegSSSP.Frame MsCall MfDrv NsStep NcFz

/-! ### Monotonicity -/

theorem pe_eval_mono9 {ρ ρ' : ℕ → ℕ} (h : ∀ i, ρ i ≤ ρ' i) : ∀ e : PE, PE.eval ρ e ≤ PE.eval ρ' e
  | .cst _ => le_rfl
  | .var i => h i
  | .add a b => Nat.add_le_add (pe_eval_mono9 h a) (pe_eval_mono9 h b)
  | .mul a b => Nat.mul_le_mul (pe_eval_mono9 h a) (pe_eval_mono9 h b)

theorem pe_evalU_mono9 {ρ ρ' : ℕ → ℕ} (h : ∀ i, ρ i ≤ ρ' i) :
    ∀ e : PE, PE.evalU ρ e ≤ PE.evalU ρ' e
  | .cst _ => le_rfl
  | .var i => Nat.add_le_add_right (h i) 1
  | .add a b => Nat.add_le_add (pe_evalU_mono9 h a) (pe_evalU_mono9 h b)
  | .mul a b => Nat.mul_le_mul (pe_evalU_mono9 h a) (pe_evalU_mono9 h b)

lemma fxρ_mono9 {n L L' : ℕ} (h : L ≤ L') : ∀ i, fxρ n L i ≤ fxρ n L' i
  | 0 => le_rfl
  | 1 => h
  | 2 => le_rfl
  | _ + 3 => le_rfl

lemma fxWB_mono9 {n L L' : ℕ} (h : L ≤ L') : fxWB n L ≤ fxWB n L' :=
  pe_evalU_mono9 (fxρ_mono9 h) _

lemma WNb_mono9 {n L L' : ℕ} (h : L ≤ L') : WNb n L ≤ WNb n L' := by
  have e1 := PE.eval_WNbE (fxρ n L) rfl
  have e2 := PE.eval_WNbE (fxρ n L') rfl
  have h3 := pe_eval_mono9 (fxρ_mono9 (n := n) h) PE.WNbE
  have a1 : fxρ n L 0 = n := rfl
  have a2 : fxρ n L 1 = L := rfl
  have a3 : fxρ n L' 0 = n := rfl
  have a4 : fxρ n L' 1 = L' := rfl
  rw [a1, a2] at e1; rw [a3, a4] at e2
  omega

lemma rtW_mono9 {n L L' G : ℕ} (h : L ≤ L') : rtW n L G ≤ rtW n L' G := by
  have h1 := WNb_mono9 (n := n) h
  have h2 := fxWB_mono9 (n := n) h
  have h3 : 8 * n * n * (L + 1) ≤ 8 * n * n * (L' + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold rtW rtH rtHb
  omega

lemma fLv_mono9 {b b' : ℕ} (h : b ≤ b') : fLv b ≤ fLv b' := by
  unfold fLv; have := Nat.log_mono_right (b := 2) h; omega

lemma fP2_mono9 {b b' : ℕ} (h : b ≤ b') : fP2 b ≤ fP2 b' := by
  unfold fP2
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul h (fLv_mono9 h))) 1)

lemma fW_mono9 {b b' w w' : ℕ} (hb : b ≤ b') (hw : w ≤ w') : fW b w ≤ fW b' w' := by
  have h1 := fLv_mono9 hb
  have h2 := fP2_mono9 hb
  unfold fW
  gcongr

lemma lySb_mono9 {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lySb b k ≤ lySb b' k' := by
  unfold lySb; gcongr

lemma wfOf_mono9 {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : wfOf b k ≤ wfOf b' k' := by
  unfold wfOf
  exact fW_mono9 hb (by have := lySb_mono9 hb hk; omega)

lemma moOf_mono9 {b b' L L' : ℕ} (hb : b ≤ b') (hL : L ≤ L') : moOf b L ≤ moOf b' L' := by
  unfold moOf; gcongr

lemma shOf_mono9 {b b' k k' L L' : ℕ} (hb : b ≤ b') (hk : k ≤ k') (hL : L ≤ L') :
    shOf b k L ≤ shOf b' k' L' := by
  have h1 := wfOf_mono9 hb hk
  have h2 := moOf_mono9 hb hL
  unfold shOf
  gcongr

lemma lyP_eq9 (S1 b k : ℕ) : lyP S1 b k = S1 + lyP 0 b k := by
  unfold lyP lyOb lyS lyA lyOm; omega

lemma lyP0_mono9 {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lyP 0 b k ≤ lyP 0 b' k' := by
  have h1 := lySb_mono9 hb hk
  unfold lyP lyOb lyS lyA lyOm lyT
  have : b * b ≤ b' * b' := Nat.mul_le_mul hb hb
  omega

/-- The room of the log of a run (`SLx.LG`). -/
def lgT9 (b k : ℕ) : ℕ := 4 * (6300 * (b * lg b ^ 2 + 2 * k * lg b)) + 3

lemma lgT9_mono {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lgT9 b k ≤ lgT9 b' k' := by
  have := lg_mono hb
  unfold lgT9; gcongr

lemma fpB_mono9 {A A' m m' k k' : ℕ} (hA : A ≤ A') (hm : m ≤ m') (hk : k ≤ k') :
    fpB A m k ≤ fpB A' m' k' := by
  unfold fpB; gcongr

theorem rtL_le_mul9 {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
    [Fintype F'] [DecidableEq F'] (N : CombMap D' V' F') (ℓ : D' → ℤ) {B : ℕ}
    (hB : ∀ y, |ℓ y| ≤ B) : rtL N ℓ ≤ Fintype.card D' * B := by
  have h : ∑ y, |minLen N.dual ℓ y| ≤ ∑ _y : D', (B : ℤ) := sum_le_sum fun y _ => by
    obtain ⟨z, -, -, e⟩ := exists_minLen (N := N.dual) ℓ y
    rw [e]; exact hB z
  rw [sum_const, card_univ, nsmul_eq_mul] at h
  unfold rtL
  exact Int.toNat_le.2 (by push_cast; exact h)

lemma k_le_card9 {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
    [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} (P : SPath N) : P.k ≤ Fintype.card D' := by
  have := card_le_card_of_injOn P.d (s := range P.k) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))
    (fun i hi j hj e => P.d_inj (mem_range.1 hi) (mem_range.1 hj) e)
  simpa using this

lemma one_le_faces9 {D' V' F' : Type} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {N : CombMap D' V' F'} (P : SPath N)
    (hk : 0 < P.k) : 1 ≤ P.faces.card :=
  Finset.card_pos.2 ⟨_, P.face_mem (P.d_mem 0 hk)⟩

lemma sum_ge9 {f : ℕ → ℕ} {i N : ℕ} (h : i ≤ N) : f i ≤ ∑ j ∈ range (N + 1), f j :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))

/-! ### The envelopes -/

/-- `fpB` at `AS ≤ m Z`, `k ≤ m`. -/
def fpM9 (m Z : ℕ) : ℕ := fpB (m * Z) m m
/-- The bound of `K = 16 fpB`. -/
def KM9 (m Z : ℕ) : ℕ := 16 * fpM9 m Z
/-- The bound of `L = 8 fpB`. -/
def LM9 (m Z : ℕ) : ℕ := 8 * fpM9 m Z

/-- The bound of the resident image `SH + WN` of the stages. -/
def shw9 (m Z : ℕ) : ℕ :=
  shOf (2 * m) m (LM9 m Z) + (2 * wfOf (2 * m) m + 1 + moOf (2 * m) (LM9 m Z) * moOf (2 * m) (LM9 m Z) +
    moOf (2 * m) (LM9 m Z))

/-- **The zero area of the frozen fix** (pendant frame of `m` darts, offset `Z`). -/
def wzF9 (wzm : ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  ∑ n ∈ range (m + 1), (wzm n (2 * Z) + (9 * n + 1 + tsz n) + rtW n (n * KM9 m Z) n) + shw9 m Z

/-- `Rm` summed over `k ≤ n`, `b ≤ 2n`. -/
def RmS9 (Rm : ℕ → ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ∑ b ∈ range (2 * n + 1), Rm n k b

/-- The address-free values bounded by the word size. -/
def valM9 (m Z : ℕ) : ℕ :=
  4 * (m * Z) + 20 * KM9 m Z + 2 * LM9 m Z + 2 * moOf (2 * m) (LM9 m Z) + 3 * (m * KM9 m Z) +
    3 * Z + m + 300 + ∑ n ∈ range (m + 1), (spWs n + fxWB n (n * KM9 m Z))

/-- **The room of the frozen fix above the heap top** (pendant frame of `m` darts, offset `Z`). -/
def rOF9 (C C₀ : ℕ) (Rm : ℕ → ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  100 + 100 * m + lyP 0 (2 * m) m + lgT9 (2 * m) m +
    ∑ n ∈ range (m + 1), (RmS9 Rm n + negT C C₀ n) + valM9 m Z

lemma Rm_le_RmS9 (Rm : ℕ → ℕ → ℕ → ℕ) {n k b : ℕ} (hk : k ≤ n) (hb : b ≤ 2 * n) :
    Rm n k b ≤ RmS9 Rm n := by
  unfold RmS9
  have h1 : Rm n k b ≤ ∑ b ∈ range (2 * n + 1), Rm n k b :=
    single_le_sum (f := fun b => Rm n k b) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
  exact h1.trans (single_le_sum (f := fun k => ∑ b ∈ range (2 * n + 1), Rm n k b)
    (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))

/-! ### The steps -/

/-- The steps of the branch `0 < k`. -/
def posT9 (C C₀ : ℕ) (cost : ℕ → ℕ → ℕ → ℕ) (m m' k b : ℕ) : ℕ :=
  (162 * m' + 103 * k + 180) + (6 + (16 * k + 3) + (cost m k b + st2T b k + 4)) +
    (loopT b k + (20 * (b * b + b + b + 1 + 2 * k + 2 * k) + 32 + finT C C₀ m k))

/-- The steps of the branch `k = 0`. -/
def zT9 (C C₀ m m' : ℕ) : ℕ := 63 + (120 * m' + 60) + (12 * m' + 22) + 1 + (5 + finT C C₀ m 0)


/-- **The steps of the frozen fix** (`m` darts of the base map, `xf` faces and `k` darts on the
part; the pendant frame has at most `3m` darts). -/
noncomputable def fxT9 (C C₀ m xf k : ℕ) : ℕ :=
  if 0 < k ∧ 1 ≤ xf ∧ xf ≤ 2 * k ∧ k ≤ m then
    posT9 C C₀ (MsEnc.msCostS C C₀) m (3 * m) k xf + 9
  else zT9 C C₀ m (3 * m) + 9

lemma posT9_mono {C C₀ : ℕ} {cost : ℕ → ℕ → ℕ → ℕ} {m m₁ m₂ k b : ℕ} (h : m₁ ≤ m₂) :
    posT9 C C₀ cost m m₁ k b ≤ posT9 C C₀ cost m m₂ k b := by
  unfold posT9; omega

lemma zT9_mono {C C₀ m m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : zT9 C C₀ m m₁ ≤ zT9 C C₀ m m₂ := by
  unfold zT9; omega

/-- **The steps of the frozen fix fit the budget** (with `2L` bookkeeping, for
`fzCost_le`). -/
theorem fxT9_le {C C₀ : ℕ} (hC : 1 ≤ C) {m xf k L : ℕ} (hm : 1 ≤ m) (hL : m ≤ L) :
    fxT9 C C₀ m xf k ≤ (cMachS C C₀).mssp m k +
      k * ((cMachS C C₀).fr xf (2 * k) + (cMachS C C₀).lin xf) + (cMachS C C₀).negsssp m +
      (cMachS C C₀).lin (2 * L) := by
  have hlin : (cMachS C C₀).lin (2 * L) = csK * (C * (2 * L)) := rfl
  have hCL : 2 * L ≤ C * (2 * L) := Nat.le_mul_of_pos_left _ hC
  have hbig : 1000 * (2 * L) ≤ csK * (C * (2 * L)) :=
    Nat.mul_le_mul (by unfold csK; norm_num) hCL
  unfold fxT9
  split_ifs with h
  · obtain ⟨hk, hb, hbk, hkm⟩ := h
    have hcost : MsEnc.msCostS C C₀ m k xf ≤ (cMachS C C₀).mssp m k := by
      unfold MsEnc.msCostS; rw [if_pos ⟨hm, hbk⟩]
    have h1 := posT_le_fixRun (L := 0) hC hm hb hbk hkm hcost
    have e : posT9 C C₀ (MsEnc.msCostS C C₀) m (3 * m) k xf =
        posT C C₀ (MsEnc.msCostS C C₀) m k xf + (324 * m + 16 * k + 9) := by
      unfold posT9 posT; ring
    rw [e]
    unfold SubCosts.fixRun at h1
    have : (cMachS C C₀).lin 0 = 0 := by show csK * (C * 0) = 0; simp
    rw [this] at h1
    rw [hlin]
    omega
  · have h1 := zT_le_fixRun (C := C) (C₀ := C₀) (b := xf) (k := k) (L := 0) hm
    have e : zT9 C C₀ m (3 * m) = zT C C₀ m + (264 * m + 5) := by
      unfold zT9 zT; ring
    rw [e]
    unfold SubCosts.fixRun at h1
    have : (cMachS C C₀).lin 0 = 0 := by show csK * (C * 0) = 0; simp
    rw [this] at h1
    rw [hlin]
    omega

/-- **The cost hypothesis of `fzHypF_of_frame`** for the frozen fix. -/
theorem fxT9_le_fixRun {C C₀ : ℕ} (hC : 1 ≤ C) :
    ∀ m xf k L, 1 ≤ m → m ≤ L →
      pfT m + 3 + fxT9 C C₀ m xf k + (24 * m + 40) ≤ (cMachS C C₀).fixRun m xf k (3 * L) :=
  fzCost_le hC fun m xf k L hm hL => fxT9_le hC hm hL

end F9b

end BKMNW

end PlanarFlow
