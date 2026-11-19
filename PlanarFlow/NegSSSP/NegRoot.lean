module

public import PlanarFlow.NegSSSP.DrvFix

/-!
# The root frame of the recursion, and the field `negsssp` of `cMach` realized by `negFix`

* `blk b l f r`: the memory `f (a - b)` on the block `[b, b + l)`, `r a` elsewhere (`blk_in`,
  `blk_out`, `blk_le`);
* **`rootMem`**, **`rootCfg`**: the root configuration of the recursion for the dual of a plane
  map `M` with lengths `ℓ₀`, global identifiers `g`, the length bound `rtL = Σ |minLen|`: the
  registers `r3001 = 1`, `r3002 = Hb`, `r3003 = h` (others `0`), the cell `Hb + 2 ↦ e`, the frame
  of `reps M.dual` at `Hb + 5` (`n, m, k, L`, then `gd ∘ cδ`, `cα`, `cσ`, `gv ∘ tail ∘ cδ`,
  `gv ∘ head ∘ cδ`, `(minLen ∘ cδ + L).toNat`), zero elsewhere, the reals zero;
  `rtHb n L G = 3 spWs n + G + WNb n L + 4`, `e = h = Hb + 5 + fsz m k`;
* `rtW`: the explicit (polynomial) word bound: the sum of the hypotheses of
  `drive_negsssp_fixed`;
* **`rootCfg_props`**: every hypothesis of `drive_negsssp_fixed` on `rootCfg`;
* **`BKMNW.cMach_negsssp_exec`**: **the field `negsssp` of `cMach` realized** (as
  `cMach_leaf_exec` for the leaf): the fixed program `negFix` runs from `rootCfg` within
  `(10¹² + 1 + fsKC + 80) · (cMach C C₀).negsssp (#D) + fsKC + 22 + 12 #D + 4610` steps under the
  word bound `rtW`, and its outcome `o` is a feasible potential of the dual with lengths `ℓ₀`, or
  `none` exactly when there is none (`PotOut`), written in the outcome region of the root frame
  (`Res`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine PlanarFlow.NegSSSP.Driver PlanarFlow.NegSSSP.Frame

/-! ### Blocks of memory -/

/-- The memory `f (a - b)` on `[b, b + l)`, `r a` elsewhere. -/
def blk (b l : ℕ) (f : ℕ → ℕ) (r : ℕ → ℕ) : ℕ → ℕ :=
  fun a => if b ≤ a ∧ a < b + l then f (a - b) else r a

theorem blk_in {b l : ℕ} {f r : ℕ → ℕ} {a : ℕ} (h1 : b ≤ a) (h2 : a < b + l) :
    blk b l f r a = f (a - b) := by
  simp only [blk, h1, h2, and_self, ite_true]

theorem blk_out {b l : ℕ} {f r : ℕ → ℕ} {a : ℕ} (h : a < b ∨ b + l ≤ a) :
    blk b l f r a = r a := by
  have : ¬ (b ≤ a ∧ a < b + l) := by omega
  simp only [blk, this, ite_false]

theorem blk_le {b l W : ℕ} {f r : ℕ → ℕ} (hf : ∀ i < l, f i ≤ W) (hr : ∀ a, r a ≤ W) (a : ℕ) :
    blk b l f r a ≤ W := by
  unfold blk; split_ifs with h
  · exact hf _ (by omega)
  · exact hr a

/-! ### The root configuration -/

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- The length bound of the root: `Σ |minLen|`. -/
noncomputable def rtL (M : CombMap D V F) (ℓ₀ : D → ℤ) : ℕ :=
  (∑ x, |minLen M.dual ℓ₀ x|).toNat

/-- The heap base of the root. -/
def rtHb (n L G : ℕ) : ℕ := 3 * spWs n + G + WNb n L + 4

/-- The memory of the root configuration: `Hb + 2 ↦ e`, the frame at `d = Hb + 5`. -/
noncomputable def rootMem (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) : ℕ → ℕ :=
  let n := Fintype.card D
  let L := rtL M ℓ₀
  let P := reps M.dual
  let m := P.card
  let k := ck M.dual P
  let Hb := rtHb n L g.G
  let d := Hb + 5
  blk (Hb + 2) 1 (fun _ => d + fsz m k) <|
  blk d 1 (fun _ => n) <| blk (d + 1) 1 (fun _ => m) <| blk (d + 2) 1 (fun _ => k) <|
  blk (d + 3) 1 (fun _ => L) <|
  blk (d + 4) k (fun h => g.gd (cδ g M.dual P h)) <|
  blk (d + 4 + k) k (fun h => cα g M.dual P h) <|
  blk (d + 4 + 2 * k) k (fun h => cσ g M.dual P h) <|
  blk (d + 4 + 3 * k) k (fun h => g.gv (M.dual.tail (cδ g M.dual P h))) <|
  blk (d + 4 + 4 * k) k (fun h => g.gv (M.dual.head (cδ g M.dual P h))) <|
  blk (d + 4 + 5 * k) m (fun h => (minLen M.dual ℓ₀ (cδ g M.dual P h) + L).toNat) <|
  fun _ => 0

/-- The heap top of the root (the end of its frame). -/
def rtH (n L G m k : ℕ) : ℕ := rtHb n L G + 5 + fsz m k

/-- **The root configuration of the recursion.** -/
noncomputable def rootCfg (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) : Config where
  pc := 0
  nreg := upd (upd (upd (fun _ => 0) 3001 1) 3002 (rtHb (Fintype.card D) (rtL M ℓ₀) g.G)) 3003
    (rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)))
  rreg := fun _ => 0
  nmem := rootMem g M ℓ₀
  rmem := fun _ => 0
  output := []

/-- **The word bound of the root run** (polynomial in `n = #D`, `L`, `G`): the sum of the
hypotheses of `drive_negsssp_fixed`. -/
def rtW (n L G : ℕ) : ℕ :=
  rtH n L G n n + (n + 1) * roomB n (66 * n + 31 + fsRF n) + 8 * n * n * (L + 1) + 7 * L +
    4 * WNb n L + spWs n + fxWB n L + G + 1000210

theorem uL_length (g : GIds D F) : g.uL.length = Fintype.card D := by
  have h1 : g.uL.toFinset = Finset.univ := Finset.eq_univ_of_forall fun d => List.mem_toFinset.2 (g.comp d)
  rw [← List.toFinset_card_of_nodup g.nodup, h1, Finset.card_univ]

theorem rtL_spec (M : CombMap D V F) (ℓ₀ : D → ℤ) :
    (∀ x, |minLen M.dual ℓ₀ x| ≤ (rtL M ℓ₀ : ℤ)) ∧ ∑ x, |minLen M.dual ℓ₀ x| ≤ (rtL M ℓ₀ : ℤ) := by
  have h0 : 0 ≤ ∑ x, |minLen M.dual ℓ₀ x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  have he : (rtL M ℓ₀ : ℤ) = ∑ x, |minLen M.dual ℓ₀ x| := Int.toNat_of_nonneg h0
  refine ⟨fun x => ?_, he.ge⟩
  rw [he]
  exact Finset.single_le_sum (f := fun x => |minLen M.dual ℓ₀ x|) (fun x _ => abs_nonneg _)
    (Finset.mem_univ x)

set_option maxHeartbeats 4000000 in
/-- **The root frame**: `rootCfg` holds the frame of `reps M.dual` at `Hb + 5` (`InPR`), the
heap base `Hb + 2 ↦ e`, zero below the heap, its words bounded by `rtW`. -/
theorem rootCfg_props (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) {n L Hb e : ℕ}
    (hn : n = Fintype.card D) (hL : L = rtL M ℓ₀) (hHb : Hb = rtHb n L g.G)
    (he : e = rtH n L g.G (reps M.dual).card (ck M.dual (reps M.dual))) :
    WordsBounded (rtW n L g.G) (rootCfg g M ℓ₀) ∧ GZ0 Hb (rootCfg g M ℓ₀) ∧
      (rootCfg g M ℓ₀).nreg 3000 = 0 ∧ (rootCfg g M ℓ₀).nreg 3001 = 1 ∧
      (rootCfg g M ℓ₀).nreg 3002 = Hb ∧ (rootCfg g M ℓ₀).nreg 3003 = e ∧
      (rootCfg g M ℓ₀).nmem Hb = 0 ∧ (rootCfg g M ℓ₀).nmem (Hb + 1) = 0 ∧
      (rootCfg g M ℓ₀).nmem (Hb + 2) = e ∧
      InPR g M.dual (minLen M.dual ℓ₀) L n (reps M.dual) (Hb + 5) e (rootCfg g M ℓ₀) := by
  subst hn hL hHb he
  have hm : (reps M.dual).card ≤ Fintype.card D := card_le_univ _
  have hk : ck M.dual (reps M.dual) ≤ Fintype.card D := ck_le_card _
  have hmk : (reps M.dual).card ≤ ck M.dual (reps M.dual) := ck_ge _
  have hen : rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)) ≤
      rtH (Fintype.card D) (rtL M ℓ₀) g.G (Fintype.card D) (Fintype.card D) := by
    simp only [rtH, fsz]; omega
  have hW : rtH (Fintype.card D) (rtL M ℓ₀) g.G (Fintype.card D) (Fintype.card D) ≤
      rtW (Fintype.card D) (rtL M ℓ₀) g.G := by unfold rtW; omega
  have hG : g.G ≤ rtW (Fintype.card D) (rtL M ℓ₀) g.G := by unfold rtW; omega
  have hL7 : 7 * rtL M ℓ₀ ≤ rtW (Fintype.card D) (rtL M ℓ₀) g.G := by unfold rtW; omega
  have hnW : Fintype.card D ≤ rtW (Fintype.card D) (rtL M ℓ₀) g.G := by
    have : Fintype.card D ≤ rtH (Fintype.card D) (rtL M ℓ₀) g.G (Fintype.card D)
      (Fintype.card D) := by unfold rtH fsz; omega
    omega
  have hHe : rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5 ≤
      rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)) := by
    unfold rtH; omega
  have hHe' : rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5 + fsz (reps M.dual).card
      (ck M.dual (reps M.dual)) =
      rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)) := rfl
  obtain ⟨hl1, -⟩ := rtL_spec M ℓ₀
  have pc := penc_canon (g := g) (N := M.dual) (reps M.dual)
  refine ⟨⟨fun r => ?_, fun a => ?_⟩, ⟨fun r => rfl, fun a _ => rfl, fun a ha => ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, subset_refl _, ?_⟩
  · -- the registers
    simp only [rootCfg, upd_apply]
    split_ifs <;> omega
  · -- the memory
    simp only [rootCfg, rootMem]
    refine blk_le (fun _ _ => by omega) (blk_le (fun _ _ => by omega) (blk_le
      (fun _ _ => by omega) (blk_le (fun _ _ => by omega) (blk_le (fun _ _ => by omega)
      (blk_le (fun i _ => ?_) (blk_le (fun i hi => ?_) (blk_le (fun i hi => ?_) (blk_le
      (fun i _ => ?_) (blk_le (fun i _ => ?_) (blk_le (fun i hi => ?_)
      (fun _ => Nat.zero_le _))))))))))) a
    · have := g.gd_lt (cδ g M.dual (reps M.dual) i); rw [uL_length] at this; omega
    · have := pc.α_lt i hi; unfold ck at hk; omega
    · have := pc.σ_lt i hi; unfold ck at hk; omega
    · have := g.gv_lt (M.dual.tail (cδ g M.dual (reps M.dual) i)); omega
    · have := g.gv_lt (M.dual.head (cδ g M.dual (reps M.dual) i)); omega
    · have h1 := hl1 (cδ g M.dual (reps M.dual) i)
      have h2 : (minLen M.dual ℓ₀ (cδ g M.dual (reps M.dual) i) + rtL M ℓ₀).toNat ≤ 2 * rtL M ℓ₀ := by
        rw [Int.toNat_le]; push_cast; have := (abs_le.1 h1).2; omega
      omega
  · simp only [rootCfg, rootMem]
    simp (disch := omega) only [blk_out]
  · simp [rootCfg]
  · simp [rootCfg]
  · simp [rootCfg]
  · simp [rootCfg]
  · simp only [rootCfg, rootMem]
    simp (disch := omega) only [blk_out]
  · simp only [rootCfg, rootMem]
    simp (disch := omega) only [blk_out]
  · simp only [rootCfg, rootMem]
    rw [blk_in (by omega) (by omega)]
    rfl
  · refine ⟨rfl, ?_, ?_, ?_, ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_,
      fun h hh => ?_, fun h hh => ?_⟩
    all_goals simp only [rootCfg, rootMem]
    all_goals simp (disch := omega) only [blk_out, blk_in, Nat.add_sub_cancel_left]

end NegSSSP

namespace BKMNW

open Finset WordRAM WordRAM.Machine NegSSSP NegSSSP.Driver NegSSSP.Frame

universe w

set_option maxHeartbeats 4000000 in
/-- **The field `negsssp` of `cMach` realized by one fixed program** (as `cMach_leaf_exec` for
the leaf): for a plane map whose dual has transitive rotations and faces, lengths `ℓ₀` with
nonnegative loops and any global identifiers `g`, the fixed program `NegSSSP.negFix` runs from
the root configuration `rootCfg g M ℓ₀` (the frame of `reps M.dual` built from the map) within
`(10¹² + 1 + fsKC + 80) · (cMach C C₀).negsssp (#D) + fsKC + 22 + (12 #D + 4610)` steps
(`O(n log² n)`) under the polynomial word bound `rtW (#D) L G` (`L = Σ |minLen|`, `G = g.G`),
and writes into the outcome region of the root frame (`Res`) an outcome `o` that is a feasible
potential of the dual with lengths `ℓ₀`, or `none` when there is none (`PotOut`). -/
theorem cMach_negsssp_exec (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d) (I : Input) :
    ∃ (c' : Config) (t : ℕ) (o : Option (F → ℤ)),
      Exec I (rtW (Fintype.card D) (rtL M ℓ₀) g.G) negFix (rootCfg g M ℓ₀) c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 +
        (12 * Fintype.card D + 4610) ∧
      PotOut (M.dual.graph ℓ₀) o ∧
      Res g M.dual (rtL M ℓ₀) (reps M.dual) o (rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5)
        (rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual))) c' ∧
      c'.output = [] := by
  classical
  obtain ⟨hc, hg, r0, r1, r2, r3, m0, m1, m2, hin⟩ :=
    rootCfg_props g M ℓ₀ rfl rfl rfl rfl
  obtain ⟨hl1, hl2⟩ := rtL_spec M ℓ₀
  have hm : (reps M.dual).card ≤ Fintype.card D := card_le_univ _
  have hk : ck M.dual (reps M.dual) ≤ Fintype.card D := ck_le_card _
  have hen : rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)) ≤
      rtH (Fintype.card D) (rtL M ℓ₀) g.G (Fintype.card D) (Fintype.card D) := by
    simp only [rtH, fsz]; omega
  have hHe : rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5 ≤
      rtH (Fintype.card D) (rtL M ℓ₀) g.G (reps M.dual).card (ck M.dual (reps M.dual)) := by
    unfold rtH; omega
  obtain ⟨c', t, o, ex, ht, hpot, hres, -, hout⟩ :=
    drive_negsssp_fixed (I := I) (W := rtW (Fintype.card D) (rtL M ℓ₀) g.G) C C₀ hC g hM hrot
      hface hneg (L := rtL M ℓ₀) (Hb := rtHb (Fintype.card D) (rtL M ℓ₀) g.G)
      (by unfold rtHb; omega) (by unfold rtHb; omega) (by unfold rtHb; omega) hl1 hl2
      (by unfold rtW; omega) (by unfold rtW; omega) (by unfold rtW; omega)
      (by unfold rtW; omega) (by unfold rtW; omega) (by unfold rtW; omega)
      (rootCfg g M ℓ₀) hc hg r0 r1 r2 r3 m0 m1 m2 hHe le_rfl (by unfold rtW; omega) hin
  exact ⟨c', t, o, ex, ht, hpot, hres, hout⟩

end BKMNW

end PlanarFlow
