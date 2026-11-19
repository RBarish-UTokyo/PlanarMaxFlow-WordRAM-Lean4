module

public import PlanarFlow.BKMNW.TfProg
public import PlanarFlow.BKMNW.ScertBase

/-!
# `scertD` as one program in `O(L² n + |Hs|)` steps: the pre-filter, then `scProg mbBase`

`scProg_exec_sepC` costs `(L + 1) (|Hs| (160 n + 36) + …)`: a term `|Hs| · n`, which neither the
node charge nor `C n lg n + C k` absorbs. Here the hole labels are first relabelled by
the holes touching the enumerated darts `B` (`tfProg`, `O(n + |Hs|)`), and `scProg mbBase` runs on
the list `tHs B Hs` of those holes (`scertD_tHs`: the same certificate). With
`|tHs B Hs| ≤ L` (e.g. `L = nTouch ≤ 6` for `B ⊆ P`, `length_tHs_le_nTouch`):

* `PMap.tHs` (a piece map with the holes `Hs` is one with the touching holes), `LvIn.tHs`,
  `LvRegs.tf`;
* **`scProgT_exec`**: `tfProg ; scProg mbBase` within
  `32 n + 17 |Hs| + 62 + (L + 1) (L (160 n + 36) + 244 n + 110) + mbT n Bz T₀ + L (7 n + 40) +
  22 n + 40` steps, with the outcome of `scProg_exec_sepC` **for the holes `Hs`** (the certificate
  `scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex`, the flags of `newHole Hs`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv

section Pure

open Equiv Orbit CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **A piece map with the holes `Hs` is one with the holes touching `B ⊇ N`.** -/
theorem PMap.tHs {N B : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hNB : N ⊆ B)
    (h : PMap M N Hs τ) : PMap M N (tHs M B Hs) τ where
  rev := h.rev
  stable := h.stable
  gap := h.gap
  vert x hx y hy := (h.vert x hx y hy).trans (hRel_tHs (hNB hx) _)
  conn := conn_tHs hNB h.conn
  inner x hx := fun ⟨H, hH, h1, h2⟩ => h.inner x hx ⟨H, (mem_tHs.1 hH).1, h1, h2⟩
  fok x hx := by
    rcases h.fok x hx with h1 | ⟨H, hH, h2⟩
    · exact Or.inl h1
    · refine Or.inr ⟨H, mem_tHs.2 ⟨hH, ?_⟩, h2⟩
      rcases h2 x (self_mem_pface hx) with h3 | h3
      · exact ⟨x, hNB hx, h3⟩
      · have hr : M.rev x ∈ N := by have := h.rev x hx; rwa [revPerm_apply] at this
        exact ⟨M.rev x, hNB hr, by rw [tail_rev]; exact h3⟩

/-- **The input of a level with the touching holes**: the same arrays, the labels `TH` replaced by
those of `tHs B Hs`. -/
theorem LvIn.tHs {m m' : ℕ → ℕ} {n b : ℕ} {e : ℕ → D} {B N : Finset D} {Hs : List (Finset V)}
    {ex : D → ℕ} (h : LvIn M m n b e B N Hs ex)
    (he : ∀ a, ¬ (b + n ≤ a ∧ a < b + 2 * n) → b ≤ a → a < b + 7 * n → m' a = m a)
    (hth : ∀ i < n, ∀ j, (m' (b + n + i) = j + 1 ↔ M.tail (e i) ∈ (tHs M B Hs).getD j ∅)) :
    LvIn M m' n b e B N (tHs M B Hs) ex where
  mem := h.mem
  surj := h.surj
  inj := h.inj
  sub := h.sub
  rv0 i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.rv0 i hi
  nf i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.nf i hi
  th i hi j _ := hth i hi j
  tk i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.tk i hi
  key i hi j hj := by
    rw [he _ (by omega) (by omega) (by omega), he (b + 6 * n + j) (by omega) (by omega)
      (by omega), h.key i hi j hj]
    exact hRel_tHs (h.mem i hi) _
  ex i hi := by rw [he _ (by omega) (by omega) (by omega)]; exact h.ex i hi

end Pure

/-- **The fixed registers of a level after the pre-filter**: the hole count is the new one. -/
theorem LvRegs.tf {c c' : Config} {n b nH nH' A W₀ : ℕ} (h : LvRegs c n b nH A W₀)
    (hf : ∀ x, ¬ tfW x → c'.nreg x = c.nreg x) (h74 : c'.nreg 4874 = nH') :
    LvRegs c' n b nH' A W₀ := by
  obtain ⟨p0, p1, p2, p3, p6, p7, p8, p9, p10, r0, r1, r2, r3, r4, r5, r6, s0, s1, s2, s3, s4, u0, u1, u2, v4, l0, l1, l2, l3, l5, l6, l7, l8, a0, a1, a2, a3, a4, h0, h1, h2, h3, h4, h5, c0, k0, k1, k2, k4, y0, y1, y2⟩ := h
  exact ⟨by rw [hf _ (by unfold tfW; omega)]; exact p0,
    by rw [hf _ (by unfold tfW; omega)]; exact p1,
    by rw [hf _ (by unfold tfW; omega)]; exact p2,
    by rw [hf _ (by unfold tfW; omega)]; exact p3,
    by rw [hf _ (by unfold tfW; omega)]; exact p6,
    by rw [hf _ (by unfold tfW; omega)]; exact p7,
    by rw [hf _ (by unfold tfW; omega)]; exact p8,
    by rw [hf _ (by unfold tfW; omega)]; exact p9,
    by rw [hf _ (by unfold tfW; omega)]; exact p10,
    by rw [hf _ (by unfold tfW; omega)]; exact r0,
    by rw [hf _ (by unfold tfW; omega)]; exact r1,
    by rw [hf _ (by unfold tfW; omega)]; exact r2,
    by rw [hf _ (by unfold tfW; omega)]; exact r3,
    by rw [hf _ (by unfold tfW; omega)]; exact r4,
    by rw [hf _ (by unfold tfW; omega)]; exact r5,
    by rw [hf _ (by unfold tfW; omega)]; exact r6,
    by rw [hf _ (by unfold tfW; omega)]; exact s0,
    by rw [hf _ (by unfold tfW; omega)]; exact s1,
    by rw [hf _ (by unfold tfW; omega)]; exact s2,
    by rw [hf _ (by unfold tfW; omega)]; exact s3,
    by rw [hf _ (by unfold tfW; omega)]; exact s4,
    by rw [hf _ (by unfold tfW; omega)]; exact u0,
    by rw [hf _ (by unfold tfW; omega)]; exact u1,
    by rw [hf _ (by unfold tfW; omega)]; exact u2,
    h74,
    by rw [hf _ (by unfold tfW; omega)]; exact l0,
    by rw [hf _ (by unfold tfW; omega)]; exact l1,
    by rw [hf _ (by unfold tfW; omega)]; exact l2,
    by rw [hf _ (by unfold tfW; omega)]; exact l3,
    by rw [hf _ (by unfold tfW; omega)]; exact l5,
    by rw [hf _ (by unfold tfW; omega)]; exact l6,
    by rw [hf _ (by unfold tfW; omega)]; exact l7,
    by rw [hf _ (by unfold tfW; omega)]; exact l8,
    by rw [hf _ (by unfold tfW; omega)]; exact a0,
    by rw [hf _ (by unfold tfW; omega)]; exact a1,
    by rw [hf _ (by unfold tfW; omega)]; exact a2,
    by rw [hf _ (by unfold tfW; omega)]; exact a3,
    by rw [hf _ (by unfold tfW; omega)]; exact a4,
    by rw [hf _ (by unfold tfW; omega)]; exact h0,
    by rw [hf _ (by unfold tfW; omega)]; exact h1,
    by rw [hf _ (by unfold tfW; omega)]; exact h2,
    by rw [hf _ (by unfold tfW; omega)]; exact h3,
    by rw [hf _ (by unfold tfW; omega)]; exact h4,
    by rw [hf _ (by unfold tfW; omega)]; exact h5,
    by rw [hf _ (by unfold tfW; omega)]; exact c0,
    by rw [hf _ (by unfold tfW; omega)]; exact k0,
    by rw [hf _ (by unfold tfW; omega)]; exact k1,
    by rw [hf _ (by unfold tfW; omega)]; exact k2,
    by rw [hf _ (by unfold tfW; omega)]; exact k4,
    by rw [hf _ (by unfold tfW; omega)]; exact y0,
    by rw [hf _ (by unfold tfW; omega)]; exact y1,
    by rw [hf _ (by unfold tfW; omega)]; exact y2⟩


section Full

open Equiv Orbit

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

set_option maxHeartbeats 2000000 in
open Classical in
/-- **`scertD` as one program in `O(L² n + |Hs|)` steps** (plus Miller's base): the pre-filter
`tfProg` (scratch `[Zb, Zb + 3 |Hs| + n + 2)`, `Zb = r5830`), then `scProg mbBase` on the holes
touching `B` (at most `L` of them); the outcome is that of `scProg_exec_sepC` for the holes `Hs`. -/
theorem scProgT_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {e : ℕ → D} {B N : Finset D}
    {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {τ : Perm D} {ex : D → ℕ}
    {n b A W₀ RECb IX0 L ITEMb NHb T₀ SGb Hb Bz SVb Zb : ℕ} (c : Config)
    (hPN : PMap M N Hs τ) (hNne : N.Nonempty) (hT₀ : ∑ d ∈ N, (1 + ex d) ≤ T₀)
    (hc : WordsBounded W c) (hR : LvRegs c n b Hs.length A W₀)
    (hI : LvIn M c.nmem n b e B N Hs ex) (hTHle : ∀ i < n, c.nmem (b + n + i) ≤ Hs.length)
    (r36 : c.nreg 4936 = RECb) (r37 : c.nreg 4937 = IX0)
    (r55 : c.nreg 4955 = ITEMb) (r56 : c.nreg 4956 = NHb)
    (s0 : c.nreg 5200 = SGb) (s1 : c.nreg 5201 = Hb) (s2 : c.nreg 5202 = Bz)
    (s3 : c.nreg 5203 = SVb) (r30 : c.nreg 5830 = Zb)
    (hSG : ∀ i < n, c.nmem (SGb + i) < n ∧ e (c.nmem (SGb + i)) = τ (e i)) (hτB : Stable τ B)
    (hBz : encB' n ≤ Bz) (hHW : Hs.length + 1 ≤ W) (hL : (tHs M B Hs).length ≤ L)
    (lay : b + 20 * n + 3 ≤ RECb ∧ RECb + 3 * L ≤ IX0 ∧ IX0 + L * n + n + 1 ≤ ITEMb ∧
      ITEMb + n ≤ NHb ∧ n + 2 + L ≤ W ∧ SGb + n ≤ b ∧ NHb + n ≤ Hb ∧
      Bz + 25 * n + 3 * T₀ + 15 ≤ Hb ∧ Hb + 13 * n ≤ SVb ∧ SVb + Bz + 25 * n + 3 * T₀ + 16 ≤ W)
    (lZ : b + 7 * n ≤ Zb) (wZ : Zb + 3 * Hs.length + n + 2 ≤ W) (wk : n + Hs.length + 2 ≤ W)
    (hS : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c.nmem (b + 3 * n + j))) ≤ W) :
    ∃ c' t, Exec P W (.seq tfProg (scProg mbBase)) c c' t ∧
      t ≤ 32 * n + 17 * Hs.length + 62 + ((L + 1) * (L * (160 * n + 36) + 244 * n + 110) +
        mbT n Bz T₀ + L * (7 * n + 40) + 22 * n + 40) ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I,
         scertD (scChoiceE M (sepC M e n Bz) e n Hs A W₀) Hs N τ ex = some (ρ, I) ∧
         ItemRep e n I (fun i => c'.nmem (ITEMb + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNH M e n NHb Hs c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lay
  -- the pre-filter
  obtain ⟨c₁, t₁, e₁, ht₁, Fl, hFl, k1, TH1, M1, q1, rr1, rm1, o1⟩ := tfProg_exec (P := P) c hc
    hR.p0 hR.p2 hR.v4 r30 hTHle (by omega) wZ wk
  obtain ⟨hlen, hth⟩ := tf_th (M := M) (B := B) (Hs := Hs) hI.mem hI.surj hTHle
    (fun i hi j hj => hI.th i hi j hj) (fun j hj => hFl j)
  have hk1 : c₁.nreg 4874 = (tHs M B Hs).length := by rw [k1, hlen]
  have hR₁ : LvRegs c₁ n b (tHs M B Hs).length A W₀ := hR.tf q1 hk1
  have he : ∀ a, ¬ (b + n ≤ a ∧ a < b + 2 * n) → b ≤ a → a < b + 7 * n →
      c₁.nmem a = c.nmem a := fun a h1 h2 h3 => M1 a (by omega) (by omega)
  have hI₁ : LvIn M c₁.nmem n b e B N (tHs M B Hs) ex := hI.tHs he fun i hi j => by
    rw [TH1 i hi]; exact hth i hi j
  have hSG₁ : ∀ i < n, c₁.nmem (SGb + i) < n ∧ e (c₁.nmem (SGb + i)) = τ (e i) := fun i hi => by
    rw [M1 _ (by omega) (by omega)]; exact hSG i hi
  have hS₁ : A + 2 * ((L + 1) * ∑ j ∈ range n, (1 + c₁.nmem (b + 3 * n + j))) ≤ W := by
    rw [sum_congr rfl fun j hj => by rw [M1 _ (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega)]]
    exact hS
  have hd' := tHs_pairwise (M := M) (B := B) hd
  have hPN' : PMap M N (tHs M B Hs) τ := hPN.tHs hI.sub
  have hdep := scDepth_tHs_le (sepC M e n Bz) e n A W₀ hI.sub hd ex hPN.rev hPN.conn (τ := τ)
  obtain ⟨c₂, t₂, e₂, ht₂, hout⟩ := scProg_exec_sepC (P := P) (W := W) hloopM hd' c₁ hPN' hNne
    hT₀ e₁.wb_right hR₁ hI₁ (by rw [q1 _ (by unfold tfW; omega)]; exact r36)
    (by rw [q1 _ (by unfold tfW; omega)]; exact r37) (by rw [q1 _ (by unfold tfW; omega)]; exact r55)
    (by rw [q1 _ (by unfold tfW; omega)]; exact r56) (by rw [q1 _ (by unfold tfW; omega)]; exact s0)
    (by rw [q1 _ (by unfold tfW; omega)]; exact s1) (by rw [q1 _ (by unfold tfW; omega)]; exact s2)
    (by rw [q1 _ (by unfold tfW; omega)]; exact s3) hSG₁ hτB hBz
    (by have := length_tHs_le (M := M) B Hs; omega) (hdep.trans hL)
    ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ hS₁
  have heq := scertD_tHs (M := M) (sepC M e n Bz) e n A W₀ (B := B) hd _ N τ ex rfl hI.sub
    hPN.conn
  have hc2 : (tHs M B Hs).length * (160 * n + 36) ≤ L * (160 * n + 36) :=
    Nat.mul_le_mul_right _ hL
  have hc3 : (L + 1) * ((tHs M B Hs).length * (160 * n + 36) + 244 * n + 110) ≤
      (L + 1) * (L * (160 * n + 36) + 244 * n + 110) := Nat.mul_le_mul_left _ (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, ?_⟩
  rw [heq]
  rcases hout with ⟨h0, h1⟩ | ⟨h0, ρ, I, h1, h2, h3⟩
  · exact Or.inl ⟨h0, h1⟩
  · refine Or.inr ⟨h0, ρ, I, h1, h2, ?_⟩
    rcases h3 with ⟨h4, h5⟩ | h4
    · refine Or.inl ⟨h4, fun i hi => ?_⟩
      rw [h5 i hi]
      exact (newHole_tHs (hI.mem i hi) ρ.mverts).symm
    · exact Or.inr h4

end Full

end BKMNW

end PlanarFlow
