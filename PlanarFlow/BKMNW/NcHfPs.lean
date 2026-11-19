module

public import PlanarFlow.BKMNW.NcHfMg

/-!
# The passes of the merge sort of `hfP`

**`hfBlk_exec`** (one block), **`hfPass_exec`** (one pass: `mpass w`, `30 m + 4` steps),
**`hfSort_exec`** (the sort: `msortW m 1`, `(30 m + 10) lg m + 3` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- **One block of a pass.** -/
theorem hfBlk_exec (c : Config) (hc : WordsBounded W c) {m S T lo w : ℕ}
    (r57 : c.nreg 9757 = m) (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T)
    (r64 : c.nreg 9764 = 1) (r66 : c.nreg 9766 = w) (r67 : c.nreg 9767 = lo)
    (r77 : c.nreg 9777 = 2 * w) (hlo : lo < m)
    (hdj : S + m ≤ T ∨ T + m ≤ S) (w1 : S + m ≤ W) (w2 : T + m ≤ W) (w3 : lo + 2 * w ≤ W)
    (w4 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfBlk c c' k ∧ k ≤ 16 * (min (lo + 2 * w) m - lo) + 12 ∧
      segL c'.nmem (T + lo) (min (lo + 2 * w) m - lo) =
        List.merge (segL c.nmem (S + lo) (min (lo + w) m - lo))
          (segL c.nmem (S + min (lo + w) m) (min (lo + 2 * w) m - min (lo + w) m)) ∧
      (∀ a, (a < T + lo ∨ T + min (lo + 2 * w) m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 9767 = lo + 2 * w ∧
      (∀ r, ¬ (9767 ≤ r ∧ r ≤ 9776) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a68, a69, a70, a71, a72, g₁, m₁, rr₁, rm₁, o₁⟩ :=
    hfBlkA_exec (P := P) c hc r57 r66 r67 r77 w3
  have hw₁ := e₁.wb_right
  have q : ∀ r, r ≠ 9768 → r ≠ 9769 → r ≠ 9770 → r ≠ 9771 → r ≠ 9772 → r ≠ 9776 →
      c₁.nreg r = c.nreg r := g₁
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, f₂, g₂, rr₂, rm₂, o₂⟩ := mergeLoop_exec (P := P) c₁ hw₁
    (S := S) (T := T) (lo := lo) (mid := min (lo + w) m) (hi := min (lo + 2 * w) m)
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r60])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r61])
    (by rw [q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r64])
    a68 a69 a70 a71 a72 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, a67, g₃, m₃, rr₃, rm₃, o₃⟩ := hfBlkB_exec (P := P) c₂ hw₂
    (lo := lo) (w := w)
    (by rw [g₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r67])
    (by rw [g₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r77]) w3
  refine ⟨c₃, k₁ + (k₂ + k₃), e₁.seq (e₂.seq e₃), by omega, ?_, fun a ha => ?_, a67,
    fun r hr => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · rw [m₃, s₂, m₁]
  · rw [m₃, f₂ a ha, m₁]
  · rw [g₃ r (by omega), g₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The invariant of a pass. -/
def HfPInv (c₀ : Config) (m S T w : ℕ) (c : Config) : Prop :=
  ∃ lo, c.nreg 9767 = lo ∧
    segL c.nmem T (min lo m) ++ mpass w ((segL c₀.nmem S m).drop lo) =
      mpass w (segL c₀.nmem S m) ∧
    (∀ a, (a < T ∨ T + m ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ r, ¬ (9767 ≤ r ∧ r ≤ 9776) → c.nreg r = c₀.nreg r) ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧ WordsBounded W c

/-- The block of `mpass` at a position `lo < m`, written with the bounds of the machine. -/
lemma mpass_drop_blk {w m lo : ℕ} (hw : 0 < w) (hlo : lo < m) (mem : ℕ → ℕ) (S : ℕ) :
    mpass w ((segL mem S m).drop lo) =
      List.merge (segL mem (S + lo) (min (lo + w) m - lo))
        (segL mem (S + min (lo + w) m) (min (lo + 2 * w) m - min (lo + w) m)) ++
      mpass w ((segL mem S m).drop (lo + 2 * w)) := by
  have hX : (segL mem S m).drop lo ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop, segL_length] at this
    simp at this; omega
  rw [mpass_blk hw hX]
  congr 1
  · congr 1
    · rw [segL_drop, segL_take]; congr 1; omega
    · rw [segL_drop, segL_drop, segL_take]
      rcases le_or_gt (lo + w) m with h | h
      · rw [show min (lo + w) m = lo + w by omega]
        congr 1 <;> omega
      · rw [show min (lo + 2 * w) m - min (lo + w) m = 0 by omega,
          show min w (m - lo - w) = 0 by omega, segL_zero, segL_zero]
  · rw [List.drop_drop]

/-- **One pass of the merge sort**: `T := mpass w S`. -/
theorem hfPass_exec (c : Config) (hc : WordsBounded W c) {m S T w : ℕ}
    (r57 : c.nreg 9757 = m) (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T)
    (r64 : c.nreg 9764 = 1) (r66 : c.nreg 9766 = w) (hw : 0 < w)
    (hdj : S + m ≤ T ∨ T + m ≤ S) (w1 : S + m ≤ W) (w2 : T + m ≤ W) (w3 : m + 2 * w ≤ W)
    (w4 : m + 1 ≤ W) :
    ∃ c' k, Exec P W hfPass c c' k ∧ k ≤ 30 * m + 4 ∧
      segL c'.nmem T m = mpass w (segL c.nmem S m) ∧
      (∀ a, (a < T ∨ T + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (9767 ≤ r ∧ r ≤ 9777) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a67, a77, g₀, m₀, rr₀, rm₀, o₀⟩ :=
    hfPassI_exec (P := P) c hc r66 (by omega)
  have hw₀ := e₀.wb_right
  have q0 : ∀ r, r ≠ 9767 → r ≠ 9777 → c₀.nreg r = c.nreg r := g₀
  have hI0 : HfPInv (W := W) c₀ m S T w c₀ :=
    ⟨0, a67, by simp [segL_zero], fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, hw₀⟩
  obtain ⟨c', k, ex, hI, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 9767)
    (b := 9757) (body := hfBlk) (HfPInv (W := W) c₀ m S T w)
    (fun c => 30 * (m - c.nreg 9767)) (fun c h => by
      obtain ⟨_, _, _, _, _, _, _, _, hw⟩ := h; exact hw)
    (fun c ⟨lo, e67, hseg, hmem, hreg, er, erm, eo, hwc⟩ hlt => by
      have q : ∀ r, ¬ (9767 ≤ r ∧ r ≤ 9776) → c.nreg r = c.nreg r := fun _ _ => rfl
      have p57 : c.nreg 9757 = m := by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r57]
      rw [e67, p57] at hlt
      obtain ⟨c₁, k₁, e₁, hk₁, s₁, f₁, b₁, g₁, rr₁, rm₁, o₁⟩ := hfBlk_exec (P := P) c hwc
        (lo := lo) (w := w) p57
        (by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r60])
        (by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r61])
        (by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r64])
        (by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r66]) e67
        (by rw [hreg _ (by omega), a77]) hlt hdj w1 w2 (by omega) w4
      have hS : ∀ t < m, c.nmem (S + t) = c₀.nmem (S + t) := fun t ht => hmem _ (by omega)
      refine ⟨c₁, k₁, e₁, ⟨lo + 2 * w, b₁, ?_, fun a ha => ?_,
        fun r hr => by rw [g₁ r hr, hreg r hr], by rw [rr₁, er], by rw [rm₁, erm],
        by rw [o₁, eo], e₁.wb_right⟩, ?_⟩
      · rw [← hseg, mpass_drop_blk hw hlt, ← List.append_assoc]
        congr 1
        have hsplit : segL c₁.nmem T (min (lo + 2 * w) m) =
            segL c₁.nmem T lo ++ segL c₁.nmem (T + lo) (min (lo + 2 * w) m - lo) := by
          rw [← segL_add]; congr 1; omega
        have hT : segL c₁.nmem T lo = segL c.nmem T lo :=
          segL_congr fun t ht => f₁ _ (Or.inl (by omega))
        rw [hsplit, s₁, show min lo m = lo by omega, hT]
        congr 1
        congr 1
        · exact segL_congr fun t ht => by rw [Nat.add_assoc]; exact hS _ (by omega)
        · exact segL_congr fun t ht => by rw [Nat.add_assoc]; exact hS _ (by omega)
      · rw [f₁ a (by omega)]; exact hmem a ha
      · rw [b₁]; omega)
    hI0
  obtain ⟨lo, e67, hseg, hmem, hreg, er, erm, eo, hwc⟩ := hI
  have p57 : c'.nreg 9757 = m := by rw [hreg _ (by omega), q0 _ (by omega) (by omega), r57]
  rw [e67, p57] at hn
  rw [show min lo m = m by omega, List.drop_eq_nil_of_le (by rw [segL_length]; omega),
    mpass_nil, List.append_nil] at hseg
  refine ⟨c', k₀ + k, e₀.seq ex, by rw [a67] at hk; omega, ?_, fun a ha => by
    rw [hmem a ha, m₀], fun r hr => by rw [hreg r (by omega), q0 r (by omega) (by omega)],
    by rw [er, rr₀], by rw [erm, rm₀], by rw [eo, o₀]⟩
  rw [hseg, m₀]

/-- The invariant of the sort. -/
def HfSInv (c₀ : Config) (m A B : ℕ) (L₀ : List ℕ) (c : Config) : Prop :=
  ∃ w S T, c.nreg 9766 = w ∧ 0 < w ∧ c.nreg 9760 = S ∧ c.nreg 9761 = T ∧
    ((S = A ∧ T = B) ∨ (S = B ∧ T = A)) ∧
    msortW m w (segL c.nmem S m) = msortW m 1 L₀ ∧
    (∀ a, (a < A ∨ B + m ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ r, ¬ (r = 9760 ∨ r = 9761 ∨ (9766 ≤ r ∧ r ≤ 9777)) → c.nreg r = c₀.nreg r) ∧
    c.rreg = c₀.rreg ∧ c.rmem = c₀.rmem ∧ c.output = c₀.output ∧ WordsBounded W c

theorem hfSortI_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.constN 9766 1]) c c' k ∧ k = 1 ∧ c'.nreg 9766 = 1 ∧
      (∀ r, r ≠ 9766 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

/-- **The merge sort**: the buffer `r9760` holds `msortW m 1` of the first buffer. -/
theorem hfSort_exec (c : Config) (hc : WordsBounded W c) {m A B : ℕ}
    (r57 : c.nreg 9757 = m) (r60 : c.nreg 9760 = A) (r61 : c.nreg 9761 = B)
    (r64 : c.nreg 9764 = 1) (hAB : A + m ≤ B) (w1 : B + m ≤ W) (w2 : 3 * m + 1 ≤ W) :
    ∃ c' k, Exec P W hfSort c c' k ∧ k ≤ (30 * m + 10) * lg m + 3 ∧
      segL c'.nmem (c'.nreg 9760) m = msortW m 1 (segL c.nmem A m) ∧
      (c'.nreg 9760 = A ∨ c'.nreg 9760 = B) ∧
      (∀ a, (a < A ∨ B + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (r = 9760 ∨ r = 9761 ∨ (9766 ≤ r ∧ r ≤ 9777)) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a66, g₀, m₀, rr₀, rm₀, o₀⟩ :=
    hfSortI_exec (P := P) c hc (by omega)
  have hw₀ := e₀.wb_right
  have hI0 : HfSInv (W := W) c₀ m A B (segL c.nmem A m) c₀ :=
    ⟨1, A, B, a66, one_pos, by rw [g₀ _ (by omega), r60], by rw [g₀ _ (by omega), r61],
      Or.inl ⟨rfl, rfl⟩, by rw [m₀], fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, hw₀⟩
  obtain ⟨c', k, ex, hI, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 9766)
    (b := 9757) (body := .seq hfPass hfSwap) (HfSInv (W := W) c₀ m A B (segL c.nmem A m))
    (fun c => (30 * m + 10) * npass m (c.nreg 9766)) (fun c h => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hw⟩ := h; exact hw)
    (fun c ⟨w, S, T, e66, hw, e60, e61, hST, hsrt, hmem, hreg, er, erm, eo, hwc⟩ hlt => by
      have p57 : c.nreg 9757 = m := by rw [hreg _ (by omega), g₀ _ (by omega), r57]
      have p64 : c.nreg 9764 = 1 := by rw [hreg _ (by omega), g₀ _ (by omega), r64]
      rw [e66, p57] at hlt
      have hdj : S + m ≤ T ∨ T + m ≤ S := by omega
      obtain ⟨c₁, k₁, e₁, hk₁, s₁, f₁, g₁, rr₁, rm₁, o₁⟩ := hfPass_exec (P := P) c hwc p57 e60
        e61 p64 e66 hw hdj (by omega) (by omega) (by omega) (by omega)
      obtain ⟨c₂, k₂, e₂, hk₂, b60, b61, b66, g₂, m₂, rr₂, rm₂, o₂⟩ := hfSwap_exec (P := P) c₁
        e₁.wb_right (S := S) (T := T) (w := w) (by rw [g₁ _ (by omega), e60])
        (by rw [g₁ _ (by omega), e61]) (by rw [g₁ _ (by omega), e66]) (by omega)
      have hstep : ¬ (m ≤ w ∨ w = 0) := by omega
      refine ⟨c₂, k₁ + k₂, e₁.seq e₂, ⟨2 * w, T, S, b66, by omega, b60, b61, by omega, ?_,
        fun a ha => ?_, fun r hr => ?_, by rw [rr₂, rr₁, er], by rw [rm₂, rm₁, erm],
        by rw [o₂, o₁, eo], e₂.wb_right⟩, ?_⟩
      · rw [m₂, s₁, ← msortW_step hstep]; exact hsrt
      · rw [m₂, f₁ a (by omega)]; exact hmem a ha
      · rw [g₂ r (by omega) (by omega) (by omega) (by omega), g₁ r (by omega), hreg r hr]
      · rw [b66, e66, npass_step hstep]; nlinarith)
    hI0
  obtain ⟨w, S, T, e66, hw, e60, e61, hST, hsrt, hmem, hreg, er, erm, eo, hwc⟩ := hI
  have p57 : c'.nreg 9757 = m := by rw [hreg _ (by omega), g₀ _ (by omega), r57]
  rw [e66, p57] at hn
  rw [msortW_stop (by omega)] at hsrt
  have hnp := npass_one_le m
  have hk' : k ≤ (30 * m + 10) * lg m + 2 := by
    rw [a66] at hk
    exact hk.trans (by have := Nat.mul_le_mul_left (30 * m + 10) hnp; omega)
  refine ⟨c', k₀ + k, e₀.seq ex, by omega, by rw [e60]; exact hsrt, by omega,
    fun a ha => by rw [hmem a ha, m₀], fun r hr => by rw [hreg r hr, g₀ r (by omega)],
    by rw [er, rr₀], by rw [erm, rm₀], by rw [eo, o₀]⟩

end NcStep

end BKMNW

end PlanarFlow
