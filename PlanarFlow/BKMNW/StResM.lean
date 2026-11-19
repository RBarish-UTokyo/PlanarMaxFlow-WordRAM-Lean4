module

public import PlanarFlow.BKMNW.StRes

/-!
# The real start of the s-t flow on natural words, on a map

`StEnc.srProg_exec` (`StRes.lean`) on index arrays; here on the arrays of a map `M` numbered by
`σ : D ≃ Fin nD` (capacities `c ≥ 0`, flags of `X` and `Y` by the tails, reverses, the shifted
isolating weight `B₀ + w`, `|w| ≤ B₀`):

* `sum_range_σ`; `SrD.OfMap` (the arrays of the map), and the values: `ins_iff` (`Inside`),
  `S_eq`, `cr_eq` (`capR`), `rs_eq` (`rsIn`), `ep_eq` (`isoEpsG`), `E_eq`, `SC_eq`, `lex_eq`,
  `N_eq` (`stN`), `kZ_eq`, `kTh_eq`, `kH0_eq`, `H_eq` (`pcoreH`), `wl_eq` (`wlen`);
* `sr_bounds`: the bound hypotheses of `srProg_exec` from `Mo ≤ W`, `S + 1 ≤ W`,
  `L₀ + WW ≤ W`; `srProg_exec'`;
* **`srProg_map`**: `srProg` writes at `Ob` the words `zres Mo` of `wlen (stN w) (capR c X Y)
  (isoEpsG w)` (`WT`, `PH`), `capR c X Y` (`CP`), `rsIn` (`RS`), `kTh`, `kH0` — exactly the residue
  hypotheses of `STFlow.st_sNFM` for `Ob = W₀ + 1` — and `H = pcoreH …`, `Mo = pstM H` in
  `r7833`, `r7834`, within `61 nD + 72` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP STFlow CombMap

variable {P : Input} {W : ℕ}

/-! ### Index-level bounds -/

theorem sr_bounds {p : SrD} (hMo : p.Mo ≤ W) (hS : p.S + 1 ≤ W)
    (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (hn : 1 ≤ p.n) (hFV : p.nF + p.nV ≤ p.n)
    (hV : 1 ≤ p.nV) :
    4 * p.nF + 5 ≤ p.L0 ∧ p.E ≤ W ∧ p.N ≤ W ∧ p.nF + 1 ≤ W ∧ p.SC ≤ W ∧ p.kH0 ≤ W ∧
      (∀ i < p.nD, p.wl i ≤ W) := by
  have eMo : p.Mo = 2 * p.H + 1 := rfl
  have eH : p.H = 2 * STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 := rfl
  have eV : STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 = p.n * (4 * (p.nF + p.nV) * p.kH0) +
      (p.nD + 2) * (2 * p.n * p.kH0 + p.n + 4 * p.kH0) + p.n * (8 * p.nF * p.kH0) + p.n +
      p.kH0 + 1 := rfl
  have eZ : p.kZ = p.N * p.SC + 2 * p.lex := rfl
  have eK : p.kH0 = p.kZ + 1 + (p.nD + 2) * p.kZ := rfl
  have eN : p.N = 2 * p.lex + 1 := rfl
  have hEl : p.E ≤ p.lex := Nat.le_mul_of_pos_left _ (by omega)
  have hSC : p.SC ≤ p.N * p.SC := Nat.le_mul_of_pos_left _ (by omega)
  have hK1 : 1 ≤ p.kH0 := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, b13, -, -, -, -, -, b19⟩ :=
    vb_bounds (cD := p.nD) hn hK1 hFV
  have hL0 : 4 * p.nF + 5 ≤ p.L0 := Nat.le_mul_of_pos_right _ hV
  have hKV : p.kH0 ≤ STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 := by omega
  have hMV : 4 * STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 + 1 = p.Mo := by omega
  have hZK : p.kZ ≤ p.kH0 := by omega
  refine ⟨hL0, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  have h1 : p.cr i ≤ p.SC := Finset.single_le_sum (f := p.cr) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hi)
  have h2 : p.ep i ≤ p.E := Finset.single_le_sum (f := p.ep) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hi)
  have h3 : p.N * p.cr i ≤ p.N * p.SC := Nat.mul_le_mul_left _ h1
  have : p.wl i = p.N * p.cr i + p.ep i := rfl
  omega

/-- `srProg_exec` with the bounds derived by `sr_bounds`. -/
theorem srProg_exec' {p : SrD} {Cb Xb Yb RVb Wb Ob : ℕ} (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W)
    (hRV : ∀ i < p.nD, p.RV i < p.nD) (hMo : p.Mo ≤ W) (hS : p.S + 1 ≤ W)
    (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (hn : 1 ≤ p.n) (hFV : p.nF + p.nV ≤ p.n)
    (hV : 1 ≤ p.nV) (hL0 : p.L0 ≤ W) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) :
    ∃ c' t, Exec P W srProg c c' t ∧ t ≤ 61 * p.nD + 72 ∧
      ((∀ j < p.nD, c'.nmem (Ob + j) = p.wl j ∧ c'.nmem (Ob + p.nD + j) = p.wl j ∧
          c'.nmem (Ob + 3 * p.nD + 3 + j) = p.cr j ∧ c'.nmem (Ob + 4 * p.nD + 3 + j) = p.rs j) ∧
        c'.nmem (Ob + 3 * p.nD + 1) = p.kTh ∧ c'.nmem (Ob + 3 * p.nD + 2) = p.kH0 ∧
        c'.nreg 7833 = p.H ∧ c'.nreg 7834 = p.Mo ∧
        (∀ a, a < Ob ∨ Ob + 5 * p.nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≤ 7810 ∨ 7844 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := sr_bounds hMo hS hLW hn hFV hV
  exact srProg_exec hL hRV (by omega) hL0 hS b2 hLW b3 b4 b5 b6 hMo hn hFV b7 c hc hI

/-! ### On a map -/

lemma sum_range_σ {D : Type*} [Fintype D] {nD : ℕ} (σ : D ≃ Fin nD) (f : ℕ → ℕ) :
    ∑ i ∈ range nD, f i = ∑ d, f (σ d) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Equiv.sum_comp σ (fun i : Fin nD => f i)).symm

lemma sum_range_σZ {D : Type*} [Fintype D] {nD : ℕ} (σ : D ≃ Fin nD) (f : ℕ → ℕ) :
    ((∑ i ∈ range nD, f i : ℕ) : ℤ) = ∑ d, (f (σ d) : ℤ) := by
  rw [sum_range_σ σ f]; push_cast; rfl

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The arrays of a map**: `p` describes `M` numbered by `σ`, the capacities `c`, the terminals
`X`, `Y` and the isolating weight `w` shifted by `B₀`. -/
structure SrD.OfMap (p : SrD) (M : CombMap D V F) (σ : D ≃ Fin p.nD) (c : D → ℤ)
    (X Y : Finset V) (w : D → ℤ) : Prop where
  nF : p.nF = Fintype.card F
  nV : p.nV = Fintype.card V
  C : ∀ d, p.C (σ d) = (c d).toNat
  XT : ∀ d, p.XT (σ d) = if M.tail d ∈ X then 1 else 0
  YT : ∀ d, p.YT (σ d) = if M.tail d ∈ Y then 1 else 0
  RV : ∀ d, p.RV (σ d) = σ (M.rev d)
  WW : ∀ d, p.WW (σ d) = (p.B0 + w d).toNat
  wB : ∀ d, |w d| ≤ p.B0
  wV : ∀ d, |w d| ≤ Fintype.card V
  nn : ∀ d, 0 ≤ c d

namespace SrD.OfMap

variable {p : SrD} {σ : D ≃ Fin p.nD} {c : D → ℤ} {X Y : Finset V} {w : D → ℤ}
  (h : p.OfMap M σ c X Y w)
include h

theorem ins_iff (d : D) : p.ins (σ d) ↔ Inside M X Y d := by
  have k : ∀ (Q : Prop) [Decidable Q], (0 < (if Q then 1 else 0 : ℕ)) ↔ Q := by
    intro Q _; split_ifs <;> simp_all
  unfold SrD.ins Inside
  rw [h.XT, h.YT, h.RV, h.XT, h.YT]
  simp only [CombMap.tail_rev]
  by_cases h1 : M.tail d ∈ X <;> by_cases h2 : M.head d ∈ X <;> by_cases h3 : M.tail d ∈ Y <;>
    by_cases h4 : M.head d ∈ Y <;> simp [h1, h2, h3, h4]

theorem S_eq : (p.S : ℤ) = ∑ d, c d := by
  unfold SrD.S
  rw [sum_range_σZ σ]
  exact Finset.sum_congr rfl fun d _ => by rw [h.C, Int.toNat_of_nonneg (h.nn d)]

theorem cr_eq (d : D) : (p.cr (σ d) : ℤ) = capR M c X Y d := by
  unfold SrD.cr capR
  by_cases hi : Inside M X Y d
  · rw [if_pos ((h.ins_iff d).2 hi), if_pos hi]; push_cast; rw [h.S_eq]
  · rw [if_neg (fun e => hi ((h.ins_iff d).1 e)), if_neg hi, h.YT]
    by_cases hy : M.tail d ∈ Y
    · simp [hy]
    · simp only [hy, ↓reduceIte, lt_self_iff_false]
      rw [h.C, Int.toNat_of_nonneg (h.nn d)]

theorem rs_eq (d : D) : (p.rs (σ d) : ℤ) = rsIn M X Y d := by
  unfold SrD.rs rsIn
  by_cases hi : Inside M X Y d
  · rw [if_pos ((h.ins_iff d).2 hi), if_pos hi]; rfl
  · rw [if_neg (fun e => hi ((h.ins_iff d).1 e)), if_neg hi]; rfl

theorem ep_eq (d : D) : (p.ep (σ d) : ℤ) = isoEpsG V F w d + (p.L0 - isoL V F) := by
  have hb := abs_le.1 (h.wB d)
  have hv := abs_le.1 (h.wV d)
  have hLV : (Fintype.card V : ℤ) ≤ p.L0 := by
    have : p.nV ≤ p.L0 := Nat.le_mul_of_pos_left _ (by omega)
    rw [← h.nV]; exact_mod_cast this
  have e := Int.toNat_of_nonneg (show 0 ≤ (p.B0 : ℤ) + w d by omega)
  have hle : p.B0 ≤ p.L0 + (p.B0 + w d).toNat := by omega
  unfold SrD.ep isoEpsG
  rw [h.WW, Nat.cast_sub hle]
  push_cast
  rw [e]
  ring

/-- `L₀ = isoL`. -/
theorem L0_eq : (p.L0 : ℤ) = isoL V F := by
  unfold SrD.L0 isoL; rw [h.nF, h.nV]; push_cast; ring

theorem ep_eq' (d : D) : (p.ep (σ d) : ℤ) = isoEpsG V F w d := by
  rw [h.ep_eq, h.L0_eq, sub_self, add_zero]

theorem E_eq : (p.E : ℤ) = ∑ d, isoEpsG V F w d := by
  unfold SrD.E
  rw [sum_range_σZ σ]
  exact Finset.sum_congr rfl fun d _ => h.ep_eq' d

theorem SC_eq : (p.SC : ℤ) = ∑ d, capR M c X Y d := by
  unfold SrD.SC
  rw [sum_range_σZ σ]
  exact Finset.sum_congr rfl fun d _ => h.cr_eq d

theorem lex_eq : (p.lex : ℤ) = lexR F (isoEpsG V F w) := by
  unfold SrD.lex lexR; push_cast; rw [h.E_eq, h.nF]

theorem N_eq : (p.N : ℤ) = stN (V := V) (F := F) w := by
  unfold SrD.N stN; push_cast; rw [h.lex_eq]

theorem kZ_eq : (p.kZ : ℤ) = STFlow.kZ D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) := by
  unfold SrD.kZ STFlow.kZ; push_cast; rw [h.N_eq, h.SC_eq, h.lex_eq]

theorem kTh_eq :
    (p.kTh : ℤ) = STFlow.kTh D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) := by
  unfold SrD.kTh STFlow.kTh; push_cast; rw [h.kZ_eq]

theorem nD_eq : p.nD = Fintype.card D := by
  rw [Fintype.card_congr σ, Fintype.card_fin]

theorem kH0_eq :
    (p.kH0 : ℤ) = STFlow.kH0 D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) := by
  unfold SrD.kH0 STFlow.kH0; push_cast; rw [h.kTh_eq, h.kZ_eq, h.nD_eq]

theorem H_eq :
    p.H = pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) := by
  unfold SrD.H pcoreH pstH
  rw [← h.nF, ← h.nV, ← h.nD_eq]
  congr
  have := h.kH0_eq
  omega

theorem wl_eq (d : D) :
    (p.wl (σ d) : ℤ) = STFlow.wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) d := by
  unfold SrD.wl STFlow.wlen; push_cast; rw [h.N_eq, h.cr_eq, h.ep_eq']

end SrD.OfMap

/-- The residue of a natural number below the modulus. -/
lemma zres_nat {Mo : ℕ} {z : ℤ} {v : ℕ} (hv : (v : ℤ) = z) (hlt : v < Mo) : zres Mo z = v := by
  unfold zres; rw [← hv, Int.emod_eq_of_lt (by omega) (by omega)]; simp


/-- The values written are below the modulus. -/
theorem sr_lt (p : SrD) (hn : 1 ≤ p.n) (hFV : p.nF + p.nV ≤ p.n) :
    (∀ i < p.nD, p.wl i < p.Mo ∧ p.cr i < p.Mo ∧ p.rs i < p.Mo) ∧ p.kTh < p.Mo ∧
      p.kH0 < p.Mo := by
  have eMo : p.Mo = 2 * p.H + 1 := rfl
  have eH : p.H = 2 * STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 := rfl
  have eV : STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 = p.n * (4 * (p.nF + p.nV) * p.kH0) +
      (p.nD + 2) * (2 * p.n * p.kH0 + p.n + 4 * p.kH0) + p.n * (8 * p.nF * p.kH0) + p.n +
      p.kH0 + 1 := rfl
  have eZ : p.kZ = p.N * p.SC + 2 * p.lex := rfl
  have eK : p.kH0 = p.kZ + 1 + (p.nD + 2) * p.kZ := rfl
  have eT : p.kTh = p.kZ + 1 := rfl
  have hEl : p.E ≤ p.lex := Nat.le_mul_of_pos_left _ (by omega)
  have hSC : p.SC ≤ p.N * p.SC := Nat.le_mul_of_pos_left _ (by unfold SrD.N; omega)
  refine ⟨fun i hi => ⟨?_, ?_, ?_⟩, by omega, by omega⟩
  · have h1 : p.cr i ≤ p.SC := Finset.single_le_sum (f := p.cr) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hi)
    have h2 : p.ep i ≤ p.E := Finset.single_le_sum (f := p.ep) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hi)
    have h3 : p.N * p.cr i ≤ p.N * p.SC := Nat.mul_le_mul_left _ h1
    have : p.wl i = p.N * p.cr i + p.ep i := rfl
    omega
  · have h1 : p.cr i ≤ p.SC := Finset.single_le_sum (f := p.cr) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hi)
    omega
  · have : p.rs i ≤ 1 := by unfold SrD.rs; split_ifs <;> omega
    omega

set_option maxHeartbeats 1000000 in
/-- **The real start of the s-t flow on natural words, on a map.** For the arrays of a map
(`SrD.OfMap`), `srProg` writes at `Ob + a` the words `zres Mo z` of the real start of
`STFlow.st_sNFM` (`a = aWT + σ e`, `aPH + σ e`: `wlen (stN w) (capR c X Y) (isoEpsG w) e`;
`aCP + σ e`: `capR c X Y e`; `aRS + σ e`: `rsIn e`; `aTH`: `kTh`; `aH0`: `kH0`), with
`Mo = pstM (pcoreH …)`, and leaves `pcoreH …`, `Mo` in `r7833`, `r7834`, within `61 nD + 72`
steps. -/
theorem srProg_map {p : SrD} {σ : D ≃ Fin p.nD} {c : D → ℤ} {X Y : Finset V} {w : D → ℤ}
    (h : p.OfMap M σ c X Y w) {Cb Xb Yb RVb Wb Ob : ℕ} (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W)
    (hMo : p.Mo ≤ W) (hS : p.S + 1 ≤ W) (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (hL0 : p.L0 ≤ W)
    (hn : 1 ≤ p.n) (hFV : Fintype.card F + Fintype.card V ≤ p.n) (hV : 1 ≤ Fintype.card V)
    (c₀ : Config) (hc : WordsBounded W c₀) (hI : SrIn p Cb Xb Yb RVb Wb Ob c₀) :
    ∃ c' t, Exec P W srProg c₀ c' t ∧ t ≤ 61 * p.nD + 72 ∧
      (∀ e, c'.nmem (Ob + (Klein.aWT + σ e)) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (STFlow.wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) e)) ∧
      (∀ e, c'.nmem (Ob + (Klein.aPH p.nD + σ e)) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (STFlow.wlen (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) e)) ∧
      (∀ e, c'.nmem (Ob + (aCP p.nD + σ e)) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (capR M c X Y e)) ∧
      (∀ e, c'.nmem (Ob + (aRS p.nD + σ e)) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (rsIn M X Y e)) ∧
      c'.nmem (Ob + Klein.aTH p.nD) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (STFlow.kTh D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) ∧
      c'.nmem (Ob + Klein.aH0 p.nD) =
        zres (pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)))
          (STFlow.kH0 D F (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) ∧
      c'.nreg 7833 = pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w) ∧
      c'.nreg 7834 =
        pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) ∧
      (∀ a, a < Ob ∨ Ob + 5 * p.nD + 3 ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≤ 7810 ∨ 7844 ≤ r → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  have hRV : ∀ i < p.nD, p.RV i < p.nD := fun i hi => by
    have e : σ (σ.symm ⟨i, hi⟩) = (⟨i, hi⟩ : Fin p.nD) := σ.apply_symm_apply _
    have : p.RV i = σ (M.rev (σ.symm ⟨i, hi⟩)) := by
      rw [← h.RV]; rw [e]
    rw [this]; exact (σ _).2
  have hFV' : p.nF + p.nV ≤ p.n := by rw [h.nF, h.nV]; exact hFV
  have hV' : 1 ≤ p.nV := by rw [h.nV]; exact hV
  obtain ⟨c', t, ex, ht, ⟨hj, hTh, hH0, h33, h34, hm, hr, hrr, hrm, ho⟩⟩ :=
    srProg_exec' (P := P) hL hRV hMo hS hLW hn hFV' hV' hL0 c₀ hc hI
  obtain ⟨lt1, lt2, lt3⟩ := sr_lt p hn hFV'
  have eH := h.H_eq
  have eMo : pstM (pcoreH D V F p.n (stN (V := V) (F := F) w) (capR M c X Y) (isoEpsG V F w)) =
      p.Mo := by rw [← eH]; rfl
  rw [eMo]
  have hσ : ∀ e : D, (σ e : ℕ) < p.nD := fun e => (σ e).2
  refine ⟨c', t, ex, ht, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, ?_, ?_,
    by rw [h33, eH], by rw [h34], hm, hr, hrr, hrm, ho⟩
  · rw [show Ob + (Klein.aWT + σ e) = Ob + (σ e : ℕ) by unfold Klein.aWT; omega,
      (hj _ (hσ e)).1]
    exact (zres_nat (h.wl_eq e) (lt1 _ (hσ e)).1).symm
  · rw [show Ob + (Klein.aPH p.nD + σ e) = Ob + p.nD + (σ e : ℕ) by unfold Klein.aPH; omega,
      (hj _ (hσ e)).2.1]
    exact (zres_nat (h.wl_eq e) (lt1 _ (hσ e)).1).symm
  · rw [show Ob + (aCP p.nD + σ e) = Ob + 3 * p.nD + 3 + (σ e : ℕ) by unfold aCP; omega,
      (hj _ (hσ e)).2.2.1]
    exact (zres_nat (h.cr_eq e) (lt1 _ (hσ e)).2.1).symm
  · rw [show Ob + (aRS p.nD + σ e) = Ob + 4 * p.nD + 3 + (σ e : ℕ) by unfold aRS; omega,
      (hj _ (hσ e)).2.2.2]
    exact (zres_nat (h.rs_eq e) (lt1 _ (hσ e)).2.2).symm
  · rw [show Ob + Klein.aTH p.nD = Ob + 3 * p.nD + 1 by unfold Klein.aTH; omega, hTh]
    exact (zres_nat h.kTh_eq lt2).symm
  · rw [show Ob + Klein.aH0 p.nD = Ob + 3 * p.nD + 2 by unfold Klein.aH0; omega, hH0]
    exact (zres_nat h.kH0_eq lt3).symm

end StEnc

end BKMNW

end PlanarFlow
