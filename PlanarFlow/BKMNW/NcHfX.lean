module

public import PlanarFlow.BKMNW.NcHfM

/-!
# `hfP` also exports the number of holes of the piece map

The scan of `hfP` counts the distinct positive labels in `r9780` (`cnt`). Here:

* `dscan_cnt` (after the sort the final `cnt` is `#posVals`), **`hfScan_exec'`** (`hfScan_exec`
  with `r9780 = (dscan i …).2.1`), **`hfP_exec'`** (`hfP_exec` with `r9780 = hfN mem HLb m`,
  `hfN = #posVals (segL mem HLb m)`);
* **`pholes_length_hfN`**: at a frame (holes pairwise disjoint) the number of holes of the piece
  map is `hfN mem (d + 4 + 5 m) m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

/-- **The final count of the scan of a sorted list** is the number of its positive values. -/
lemma dscan_sorted_cnt {i : ℕ} {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) :
    (dscan i L).2.1 = (posVals L).card := by
  have := dinv_foldl L [] (0, 0, 0) (dinv_nil i) (by simpa using hL)
  simp only [List.nil_append] at this
  exact this.2.2.1

/-- **The final count after the sort.** -/
theorem dscan_cnt {i m : ℕ} {L : List ℕ} (hl : L.length = m) :
    (dscan i (msortW m 1 L)).2.1 = (posVals L).card := by
  rw [← posVals_perm (perm_msortW m 1 L)]
  exact dscan_sorted_cnt (msortW_sorted m 1 L one_pos hl (bsorted_one L))

/-- The number of distinct positive labels. -/
def hfN (mem : ℕ → ℕ) (HLb m : ℕ) : ℕ := (posVals (segL mem HLb m)).card

variable {P : Input} {W : ℕ}

/-- **The scan**, with the count. -/
theorem hfScan_exec' (c : Config) (hc : WordsBounded W c) {m Sb i : ℕ}
    (r57 : c.nreg 9757 = m) (r60 : c.nreg 9760 = Sb) (r64 : c.nreg 9764 = 1)
    (r59 : c.nreg 9759 = i) (w1 : Sb + m ≤ W) (w2 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfScan c c' k ∧ k ≤ 14 * m + 6 ∧
      c'.nreg 9763 = (dscan i (segL c.nmem Sb m)).2.2 ∧
      c'.nreg 9780 = (dscan i (segL c.nmem Sb m)).2.1 ∧
      (∀ r, r ≠ 9763 → r ≠ 9775 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → r ≠ 9781 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a78, a79, a80, a63, g₀, m₀, rr₀, rm₀, o₀⟩ := hfScI_exec (P := P) c hc
  have q : ∀ r, r ≠ 9763 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → c₀.nreg r = c.nreg r := g₀
  let J : ℕ → Config → Prop := fun t c' =>
    (c'.nreg 9779, c'.nreg 9780, c'.nreg 9763) = (segL c.nmem Sb t).foldl (dstep i) (0, 0, 0) ∧
    (∀ r, r ≠ 9763 → r ≠ 9775 → r ≠ 9778 → r ≠ 9779 → r ≠ 9780 → r ≠ 9781 →
      c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hk₁, -, a₁, ⟨j1, j2, j3, j4, j5, j6⟩⟩ := lnRange (P := P) (a := 9778)
    (b := 9757) (body := hfScB) J (lo := 0) (hi := m) (B := 12) c₀ e₀.wb_right a78
    (by rw [q _ (by omega) (by omega) (by omega) (by omega), r57]) (Nat.zero_le m)
    ⟨by rw [a79, a80, a63, segL_zero]; rfl,
      fun r h1 h2 h3 h4 h5 h6 => q r h1 h3 h4 h5, m₀, rr₀, rm₀, o₀⟩
    (fun t c' _ ht hw e78 e57 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hcnt : c'.nreg 9780 ≤ t := by
        have h := congrArg (fun s => s.2.1) j1
        simp only at h
        have := foldl_dstep_cnt_le i (segL c.nmem Sb t) (0, 0, 0)
        rw [segL_length] at this; simp only at this; omega
      obtain ⟨c'', k, ex, hk, d, b78, g, mm, rr, rm, oo⟩ := hfScB_exec (P := P) c' hw
        (Sb := Sb) (t := t) (i := i) (prev := c'.nreg 9779) (cnt := c'.nreg 9780)
        (v := c'.nreg 9763)
        (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r60])
        (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r64])
        e78 (by rw [j2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r59])
        rfl rfl rfl (by omega) (by omega) (by omega)
      refine ⟨c'', k, ex, hk, b78, by
        rw [g _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact e57,
        ⟨?_, fun r h1 h2 h3 h4 h5 h6 => by rw [g r h1 h2 h3 h4 h5 h6, j2 r h1 h2 h3 h4 h5 h6],
          by rw [mm, j3], by rw [rr, j4], by rw [rm, j5], by rw [oo, j6]⟩⟩
      rw [d, segL_succ_right, List.foldl_append, ← j1, j3]
      rfl)
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, ?_, ?_, j2, j3, j4, j5, j6⟩
  · have := congrArg (fun s => s.2.2) j1
    simp only at this
    rw [this]; rfl
  · have := congrArg (fun s => s.2.1) j1
    simp only at this
    rw [this]; rfl

/-- **The hole-flag program, with the count**: `hfP_exec` and `r9780 = hfN`. -/
theorem hfP_exec' (c : Config) (hc : WordsBounded W c) {m HLb i A B Fb : ℕ}
    (r57 : c.nreg 9757 = m) (r58 : c.nreg 9758 = HLb) (r59 : c.nreg 9759 = i)
    (r60 : c.nreg 9760 = A) (r61 : c.nreg 9761 = B) (r62 : c.nreg 9762 = Fb)
    (h1 : HLb + m ≤ A) (h2 : A + m ≤ B) (h3 : B + m ≤ Fb) (w1 : Fb + m ≤ W)
    (w2 : 3 * m + 1 ≤ W) :
    ∃ c' k, Exec P W hfP c c' k ∧ k ≤ hfCost m ∧ c'.nreg 9763 = hfV c.nmem HLb m i ∧
      c'.nreg 9780 = hfN c.nmem HLb m ∧
      (∀ t < m, c'.nmem (Fb + t) = if c.nmem (HLb + t) = hfV c.nmem HLb m i then 1 else 0) ∧
      (∀ a, (a < A ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ HfScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a64, v₁, f₁, g₁, rr₁, rm₁, o₁⟩ :=
    hfCopy_exec (P := P) c hc r57 r58 r60 h1 (by omega) (by omega)
  have hseg₁ : segL c₁.nmem A m = segL c.nmem HLb m := by
    unfold segL; apply List.map_congr_left; intro t ht; exact v₁ t (List.mem_range.1 ht)
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, b₂, f₂, g₂, rr₂, rm₂, o₂⟩ := hfSort_exec (P := P) c₁ e₁.wb_right
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r57])
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r60])
    (by rw [g₁ _ (by omega) (by omega) (by omega) (by omega), r61]) a64 h2 (by omega) w2
  obtain ⟨c₃, k₃, e₃, hk₃, a63, a80, g₃, m₃, rr₃, rm₃, o₃⟩ := hfScan_exec' (P := P) c₂ e₂.wb_right
    (m := m) (Sb := c₂.nreg 9760) (i := i)
    (by rw [g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r57]) rfl
    (by rw [g₂ _ (by omega), a64])
    (by rw [g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r59])
    (by omega) (by omega)
  have hv : c₃.nreg 9763 = hfV c.nmem HLb m i := by
    rw [a63, s₂, hseg₁]; rfl
  have hn : c₃.nreg 9780 = hfN c.nmem HLb m := by
    rw [a80, s₂, hseg₁, dscan_cnt (segL_length _ _ _)]; rfl
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄, g₄, rr₄, rm₄, o₄⟩ := hfFlag_exec (P := P) c₃ e₃.wb_right
    (m := m) (HLb := HLb) (Fb := Fb) (v := hfV c.nmem HLb m i)
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r57])
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r58])
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), g₁ _ (by omega) (by omega) (by omega) (by omega), r62]) hv
    (by rw [g₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ _ (by omega), a64]) (by omega) w1 (by omega)
  have hHL : ∀ t < m, c₃.nmem (HLb + t) = c.nmem (HLb + t) := fun t ht => by
    rw [m₃, f₂ _ (Or.inl (by omega)), f₁ _ (Or.inl (by omega))]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), e₁.seq (e₂.seq (e₃.seq e₄)), ?_, ?_, ?_, fun t ht => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩
  · unfold hfCost; omega
  · rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv
  · rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hn
  · rw [v₄ t ht, hHL t ht]
  · rw [f₄ a (by omega), m₃, f₂ a (by omega), f₁ a (by omega)]
  · unfold HfScr at hr
    rw [g₄ r (by omega) (by omega) (by omega) (by omega) (by omega),
      g₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ r (by omega), g₁ r (by omega) (by omega) (by omega) (by omega)]

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The number of holes of the piece map is the count of `hfP`.** -/
theorem pholes_length_hfN {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hd : x.2.1.Pairwise Disjoint) :
    (pholes M x.2.2 (pdarts M x.1.piece x.2.1) x.2.1).length = hfN mem (d + 4 + 5 * m) m := by
  classical
  have e1 := filter_take_length (M := M) x (le_refl x.2.1.length)
  rw [List.take_of_length_le (by simp)] at e1
  unfold pholes hfN
  rw [e1]
  have e2 : posVals (segL mem (d + 4 + 5 * m) m) =
      ((range x.2.1.length).filter (holeQ x)).image (· + 1) := by
    ext v
    simp only [posVals_hl hL hd, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨hpos, hlt, hq⟩; exact ⟨v - 1, ⟨hlt, hq⟩, by omega⟩
    · rintro ⟨J', ⟨hJ', hq⟩, rfl⟩; exact ⟨by omega, by simpa using hJ', by simpa using hq⟩
  rw [e2, card_image_of_injective _ (fun a b h => by simpa using h)]

end NcStep

end BKMNW

end PlanarFlow
