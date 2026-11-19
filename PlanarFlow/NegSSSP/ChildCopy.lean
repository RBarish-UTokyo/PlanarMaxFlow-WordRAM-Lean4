module

public import PlanarFlow.NegSSSP.ChildProg

/-!
# The child encodings on the machine, part 2: the arrays of the child

After `ciProg` (the list `L` of the child as `OLD`, `NI`), `ccProg` writes the data of the
child's frame at `Cb = r2937`: the header (`n - 1`, `mₛ = r2950`, `kₛ = r2951 = #L`, the offset
`L` of the parent), then for `j < kₛ`, with `h = L[j]`: the global identifier `GD[h]`, the
reversal `NI[AL[h]] - 1`, the first return `NI[SG^[t] h] - 1` (`t` the first iterate of the
parent's first return `SG` landing in the list: the inner walk), the tail and head identifiers
`GT[h]`, `GH[h]`; for `j < mₛ` the length `LN[h]`.

* `forLoopV_exec`: a counted loop whose `i`-th iteration costs at most `K + f i`.
* `ccW_exec`: the walk (`6 t` steps).
* **`ccProg_exec`** (generic): within `33 kₛ + 6 Σ_j t_j + 9 mₛ + 30` steps, the arrays above
  (the reversal and the first return as indices in `L`, `L.idxOf`); memory written only in the
  child's data `[Cb, Cb + 4 + 5 kₛ + mₛ)`; registers outside `2940 … 2965` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-- **A counted loop with costs varying with the iteration.** -/
theorem forLoopV_exec {a bR : ℕ} {body : Stmt} (J : ℕ → Config → Prop) {n K : ℕ}
    (f : ℕ → ℕ) (c : Config) (hc : WordsBounded W c) (ha : c.nreg a = 0)
    (hb : c.nreg bR = n) (hJ : J 0 c)
    (hbody : ∀ i c, i < n → WordsBounded W c → c.nreg a = i → c.nreg bR = n → J i c →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ K + f i ∧ c'.nreg a = i + 1 ∧ c'.nreg bR = n ∧
        J (i + 1) c') :
    ∃ c' k, Exec P W (.whileLtN a bR body) c c' k ∧
      k ≤ (K + 2) * n + ∑ i ∈ Finset.range n, f i + 2 ∧ WordsBounded W c' ∧ J n c' := by
  obtain ⟨c', k, e, ⟨hw, hle, hb', hJ'⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := a) (b := bR) (body := body)
    (fun c => WordsBounded W c ∧ c.nreg a ≤ n ∧ c.nreg bR = n ∧ J (c.nreg a) c)
    (fun c => (K + 2) * (n - c.nreg a) + ∑ i ∈ Finset.Ico (c.nreg a) n, f i)
    (fun c h => h.1) (fun c₁ ⟨hw₁, hle, hb₁, hJ₁⟩ hlt => by
      rw [hb₁] at hlt
      obtain ⟨c₂, k, hex, hk, ha₂, hb₂, hJ₂⟩ := hbody _ c₁ hlt hw₁ rfl hb₁ hJ₁
      refine ⟨c₂, k, hex, ⟨hex.wb_right, by omega, hb₂, by rw [ha₂]; exact hJ₂⟩, ?_⟩
      rw [ha₂, Finset.sum_eq_sum_Ico_succ_bot hlt]
      have := mul_pred_add (a := K + 2) (x := n - c₁.nreg a) (by omega)
      rw [show n - c₁.nreg a - 1 = n - (c₁.nreg a + 1) by omega] at this
      omega) (c := c) ⟨hc, by omega, hb, by rw [ha]; exact hJ⟩
  rw [hb'] at hn
  have e' : c'.nreg a = n := by omega
  rw [e'] at hJ'
  refine ⟨c', k, e, ?_, hw, hJ'⟩
  rw [ha, Nat.sub_zero, ← Finset.range_eq_Ico] at hk
  omega

/-! ### The program -/

/-- The bases of the child's arrays, its header, the loop counter. -/
def ccSet : Stmt := block [.constN 2942 4, .addN 2958 2937 2942, .addN 2959 2958 2951,
  .addN 2960 2959 2951, .addN 2961 2960 2951, .addN 2962 2961 2951, .addN 2963 2962 2951,
  .loadN 2943 2931, .subN 2943 2943 2939, .constN 2944 3, .addN 2944 2931 2944,
  .loadN 2945 2944, .storeN 2937 2943, .addN 2942 2937 2939, .storeN 2942 2950,
  .addN 2942 2942 2939, .storeN 2942 2951, .addN 2942 2942 2939, .storeN 2942 2945,
  .constN 2940 0]

/-- The copies at `j = r2940` (`h = OLD[j]`), the reversal, the start of the walk. -/
def ccD1 : Stmt := block [.addN 2942 2936 2940, .loadN 2943 2942,
  .addN 2942 2952 2943, .loadN 2944 2942, .addN 2942 2955 2943, .loadN 2945 2942,
  .addN 2942 2956 2943, .loadN 2946 2942,
  .addN 2942 2953 2943, .loadN 2947 2942, .addN 2942 2935 2947, .loadN 2947 2942,
  .subN 2947 2947 2939,
  .addN 2942 2954 2943, .loadN 2964 2942, .addN 2942 2935 2964, .loadN 2965 2942,
  .addN 2942 2958 2940, .storeN 2942 2944, .addN 2942 2961 2940, .storeN 2942 2945,
  .addN 2942 2962 2940, .storeN 2942 2946, .addN 2942 2959 2940, .storeN 2942 2947]

/-- One step of the walk: `y := SG[y]`, `t := NI[y]`. -/
def ccW1 : Stmt := block [.addN 2942 2954 2964, .loadN 2964 2942, .addN 2942 2935 2964,
  .loadN 2965 2942]

/-- The first return and the counter. -/
def ccD3 : Stmt := block [.subN 2944 2965 2939, .addN 2942 2960 2940, .storeN 2942 2944,
  .addN 2940 2940 2939]

/-- One step of the copy of the closure. -/
def ccD : Stmt := .seq ccD1 (.seq (.whileLtN 2965 2939 ccW1) ccD3)

/-- One step of the copy of the lengths. -/
def ccE : Stmt := block [.addN 2942 2936 2940, .loadN 2943 2942, .addN 2942 2957 2943,
  .loadN 2944 2942, .addN 2942 2963 2940, .storeN 2942 2944, .addN 2940 2940 2939]

/-- **The arrays of the child** (see the module docstring). -/
def ccProg : Stmt :=
  .seq ccSet <| .seq (.whileLtN 2940 2951 ccD) <| .seq (block [.constN 2940 0]) <|
  .whileLtN 2940 2950 ccE

theorem ccProg_natOnly : Klein.natOnly ccProg = true := by kernel_rfl

set_option maxHeartbeats 2000000 in
theorem ccSet_exec (c : Config) (hc : WordsBounded W c) {d Cb ms ks : ℕ}
    (r31 : c.nreg 2931 = d) (r37 : c.nreg 2937 = Cb) (r39 : c.nreg 2939 = 1)
    (r50 : c.nreg 2950 = ms) (r51 : c.nreg 2951 = ks) (w : Cb + 4 + 5 * ks ≤ W)
    (wd : d + 3 ≤ W) :
    ∃ c' t, Exec P W ccSet c c' t ∧ t = 20 ∧ c'.nreg 2940 = 0 ∧
      c'.nreg 2958 = Cb + 4 ∧ c'.nreg 2959 = Cb + 4 + ks ∧ c'.nreg 2960 = Cb + 4 + 2 * ks ∧
      c'.nreg 2961 = Cb + 4 + 3 * ks ∧ c'.nreg 2962 = Cb + 4 + 4 * ks ∧
      c'.nreg 2963 = Cb + 4 + 5 * ks ∧
      c'.nmem = upd (upd (upd (upd c.nmem Cb (c.nmem d - 1)) (Cb + 1) ms) (Cb + 2) ks) (Cb + 3)
        (c.nmem (d + 3)) ∧
      (∀ r, (r < 2940 ∨ (2945 < r ∧ r < 2958) ∨ 2963 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r31, r37, r39, r50, r51]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r31, r37, r39, r50, r51] <;> omega)
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

set_option maxHeartbeats 4000000 in
theorem ccD1_exec (c : Config) (hc : WordsBounded W c) {Xb Yb Gb Ab Sb Tb Hb B0 ks j h a y : ℕ}
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1)
    (r40 : c.nreg 2940 = j) (r52 : c.nreg 2952 = Gb) (r53 : c.nreg 2953 = Ab)
    (r54 : c.nreg 2954 = Sb) (r55 : c.nreg 2955 = Tb) (r56 : c.nreg 2956 = Hb)
    (r58 : c.nreg 2958 = B0) (r59 : c.nreg 2959 = B0 + ks) (r61 : c.nreg 2961 = B0 + 3 * ks)
    (r62 : c.nreg 2962 = B0 + 4 * ks)
    (eh : c.nmem (Yb + j) = h) (ea : c.nmem (Ab + h) = a) (ey : c.nmem (Sb + h) = y)
    (w1 : Yb + j ≤ W) (w2 : Gb + h ≤ W) (w3 : Tb + h ≤ W) (w4 : Hb + h ≤ W) (w5 : Ab + h ≤ W)
    (w6 : Xb + a ≤ W) (w7 : Sb + h ≤ W) (w8 : Xb + y ≤ W) (w9 : B0 + 4 * ks + j ≤ W) :
    ∃ c' t, Exec P W ccD1 c c' t ∧ t = 25 ∧ c'.nreg 2964 = y ∧
      c'.nreg 2965 = c.nmem (Xb + y) ∧
      c'.nmem = upd (upd (upd (upd c.nmem (B0 + j) (c.nmem (Gb + h))) (B0 + 3 * ks + j)
        (c.nmem (Tb + h))) (B0 + 4 * ks + j) (c.nmem (Hb + h))) (B0 + ks + j)
        (c.nmem (Xb + a) - 1) ∧
      (∀ r, (r < 2942 ∨ (2947 < r ∧ r < 2964) ∨ 2965 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccD1
  exec_block
  all_goals try ((try config_simp); (try simp only [r35, r36, r39, r40, r52, r53, r54, r55,
    r56, r58, r59, r61, r62, eh, ea, ey]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r35, r36, r39, r40, r52, r53, r54, r55, r56, r58, r59, r61, r62,
    eh, ea, ey])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem ccW1_exec (c : Config) (hc : WordsBounded W c) {Xb Sb y z : ℕ}
    (r35 : c.nreg 2935 = Xb) (r54 : c.nreg 2954 = Sb) (r64 : c.nreg 2964 = y)
    (ez : c.nmem (Sb + y) = z) (w1 : Sb + y ≤ W) (w2 : Xb + z ≤ W) :
    ∃ c' t, Exec P W ccW1 c c' t ∧ t = 4 ∧ c'.nreg 2964 = z ∧ c'.nreg 2965 = c.nmem (Xb + z) ∧
      (∀ r, r ≠ 2942 → r ≠ 2964 → r ≠ 2965 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccW1
  exec_block
  all_goals try ((try config_simp); (try simp only [r35, r54, r64, ez]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r35, r54, r64, ez])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- **The walk**: from `y = sg h`, `t = ni y`, while `t < 1` step `y := sg y`; it stops at the
first iterate `sg^[T] h` with `ni ≥ 1`, within `6 T` steps. -/
theorem ccW_exec {Xb Sb k : ℕ} {sg ni : ℕ → ℕ} {h T : ℕ} (hT : 1 ≤ T)
    (hsg : ∀ x < k, sg x < k) (hh : h < k) (hstop : 1 ≤ ni (sg^[T] h))
    (hgo : ∀ i, 1 ≤ i → i < T → ni (sg^[i] h) = 0) (wS : Sb + k ≤ W) (wX : Xb + k ≤ W) :
    ∀ r i (c : Config), i + r = T → 1 ≤ i → WordsBounded W c → c.nreg 2935 = Xb →
      c.nreg 2954 = Sb → c.nreg 2939 = 1 → c.nreg 2964 = sg^[i] h →
      c.nreg 2965 = ni (sg^[i] h) →
      (∀ x < k, c.nmem (Sb + x) = sg x) → (∀ x < k, c.nmem (Xb + x) = ni x) →
      ∃ c' t, Exec P W (.whileLtN 2965 2939 ccW1) c c' t ∧ t ≤ 6 * r + 2 ∧
        c'.nreg 2964 = sg^[T] h ∧ c'.nreg 2965 = ni (sg^[T] h) ∧
        (∀ r, r ≠ 2942 → r ≠ 2964 → r ≠ 2965 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlt : ∀ i, (sg^[i]) h < k := fun i => by
    induction i with
    | zero => exact hh
    | succ i ih => rw [Function.iterate_succ_apply']; exact hsg _ ih
  intro r
  induction r with
  | zero =>
    intro i c hi h1 hw r35 r54 r39 r64 r65 hS hX
    have : i = T := by omega
    subst this
    exact ⟨c, 2, .whileLtN_false (by rw [r65, r39]; omega) hw, by omega, r64, r65,
      fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ r ih =>
    intro i c hi h1 hw r35 r54 r39 r64 r65 hS hX
    have h0 := hgo i h1 (by omega)
    have ez : c.nmem (Sb + (sg^[i]) h) = (sg^[i + 1]) h := by
      rw [hS _ (hlt i), Function.iterate_succ_apply']
    obtain ⟨c₁, t₁, e₁, ht₁, s64, s65, sn, sm, sr, srm, so⟩ := ccW1_exec (P := P) c hw r35 r54
      r64 ez (by have := hlt i; omega) (by have := hlt (i + 1); omega)
    rw [hX _ (hlt (i + 1))] at s65
    obtain ⟨c₂, t₂, e₂, ht₂, q64, q65, qn, qm, qr, qrm, qo⟩ := ih (i + 1) c₁ (by omega)
      (by omega) e₁.wb_right (by rw [sn _ (by omega) (by omega) (by omega)]; exact r35)
      (by rw [sn _ (by omega) (by omega) (by omega)]; exact r54)
      (by rw [sn _ (by omega) (by omega) (by omega)]; exact r39) s64 s65
      (fun x hx => by rw [sm]; exact hS x hx) (fun x hx => by rw [sm]; exact hX x hx)
    refine ⟨c₂, t₁ + 2 + t₂, .whileLtN_true (by rw [r65, r39, h0]; omega) e₁ e₂, by omega,
      q64, q65, fun r a b d => by rw [qn r a b d, sn r a b d], by rw [qm, sm], by rw [qr, sr],
      by rw [qrm, srm], by rw [qo, so]⟩

theorem ccD3_exec (c : Config) (hc : WordsBounded W c) {B2 j v : ℕ}
    (r39 : c.nreg 2939 = 1) (r40 : c.nreg 2940 = j) (r60 : c.nreg 2960 = B2)
    (r65 : c.nreg 2965 = v) (w1 : B2 + j ≤ W) (w2 : j + 1 ≤ W) :
    ∃ c' t, Exec P W ccD3 c c' t ∧ t = 4 ∧ c'.nreg 2940 = j + 1 ∧
      c'.nmem = upd c.nmem (B2 + j) (v - 1) ∧
      (∀ r, r ≠ 2940 → r ≠ 2942 → r ≠ 2944 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccD3
  exec_block
  all_goals try ((try config_simp); (try simp only [r39, r40, r60, r65]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r39, r40, r60, r65])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem ccE_exec (c : Config) (hc : WordsBounded W c) {Yb Lb B5 j h : ℕ}
    (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1) (r40 : c.nreg 2940 = j)
    (r57 : c.nreg 2957 = Lb) (r63 : c.nreg 2963 = B5) (eh : c.nmem (Yb + j) = h)
    (w1 : Yb + j ≤ W) (w2 : Lb + h ≤ W) (w3 : B5 + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' t, Exec P W ccE c c' t ∧ t = 7 ∧ c'.nreg 2940 = j + 1 ∧
      c'.nmem = upd c.nmem (B5 + j) (c.nmem (Lb + h)) ∧
      (∀ r, r ≠ 2940 → r ≠ 2942 → r ≠ 2943 → r ≠ 2944 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccE
  exec_block
  all_goals try ((try config_simp); (try simp only [r36, r39, r40, r57, r63, eh]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r36, r39, r40, r57, r63, eh])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem NIv_sub_one {L : List ℕ} {x : ℕ} (hx : x ∈ L) : NIv L x - 1 = L.idxOf x := by
  simp [NIv, hx]

/-- The cells of the closure of the child written for `j' < j`. -/
def CCells (Cb ks : ℕ) (L : List ℕ) (GD AL SG GT GH : ℕ → ℕ) (T : ℕ → ℕ) (mem : ℕ → ℕ)
    (j : ℕ) : Prop :=
  ∀ j' < j, ∀ hj : j' < L.length,
    mem (Cb + 4 + j') = GD L[j'] ∧ mem (Cb + 4 + ks + j') = L.idxOf (AL L[j']) ∧
    mem (Cb + 4 + 2 * ks + j') = L.idxOf (SG^[T j'] L[j']) ∧
    mem (Cb + 4 + 3 * ks + j') = GT L[j'] ∧ mem (Cb + 4 + 4 * ks + j') = GH L[j']

/-- One step of the copy of the closure. -/
theorem ccD_exec (c : Config) (hc : WordsBounded W c)
    {Xb Yb Cb ks k Gb Ab Sb Tb Hb j h T : ℕ} {SG ni : ℕ → ℕ}
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb) (r39 : c.nreg 2939 = 1)
    (r40 : c.nreg 2940 = j) (r52 : c.nreg 2952 = Gb) (r53 : c.nreg 2953 = Ab)
    (r54 : c.nreg 2954 = Sb) (r55 : c.nreg 2955 = Tb) (r56 : c.nreg 2956 = Hb)
    (r58 : c.nreg 2958 = Cb + 4) (r59 : c.nreg 2959 = Cb + 4 + ks)
    (r60 : c.nreg 2960 = Cb + 4 + 2 * ks) (r61 : c.nreg 2961 = Cb + 4 + 3 * ks)
    (r62 : c.nreg 2962 = Cb + 4 + 4 * ks)
    (eh : c.nmem (Yb + j) = h) (hh : h < k) (hS : ∀ x < k, c.nmem (Sb + x) = SG x)
    (hsg : ∀ x < k, SG x < k) (hX : ∀ x < k, c.nmem (Xb + x) = ni x)
    (ha : c.nmem (Ab + h) < k) (hT : 1 ≤ T) (hstop : 1 ≤ ni (SG^[T] h))
    (hgo : ∀ i, 1 ≤ i → i < T → ni (SG^[i] h) = 0)
    (lG : Gb + k ≤ Cb) (lA : Ab + k ≤ Cb) (lS : Sb + k ≤ Cb) (lT : Tb + k ≤ Cb)
    (lH : Hb + k ≤ Cb) (lX : Xb + k ≤ Cb) (lY : Yb + ks ≤ Cb) (hj : j < ks)
    (wC : Cb + 4 + 5 * ks ≤ W) :
    ∃ c' t, Exec P W ccD c c' t ∧ t ≤ 31 + 6 * T ∧ c'.nreg 2940 = j + 1 ∧
      c'.nmem = upd (upd (upd (upd (upd c.nmem (Cb + 4 + j) (c.nmem (Gb + h)))
          (Cb + 4 + 3 * ks + j) (c.nmem (Tb + h))) (Cb + 4 + 4 * ks + j) (c.nmem (Hb + h)))
          (Cb + 4 + ks + j) (ni (c.nmem (Ab + h)) - 1)) (Cb + 4 + 2 * ks + j)
          (ni (SG^[T] h) - 1) ∧
      (∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2964) ∨ 2965 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccD
  have hsg' := hsg h hh
  rw [← hS h hh] at hsg'
  obtain ⟨c₂, t₂, e₂, ht₂, g64, g65, gm₂, gn₂, gr₂, grm₂, go₂⟩ := ccD1_exec (P := P)
    (Xb := Xb) (Yb := Yb) (Gb := Gb) (Ab := Ab) (Sb := Sb) (Tb := Tb) (Hb := Hb)
    (B0 := Cb + 4) (ks := ks) (j := j) (h := h) (a := c.nmem (Ab + h)) (y := c.nmem (Sb + h))
    c hc r35 r36 r39 r40 r52 r53 r54 r55 r56 r58 r59 r61 r62 eh rfl rfl (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have G2 : ∀ a, a < Cb → c₂.nmem a = c.nmem a := fun a ha' => by
    rw [gm₂, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  rw [hS h hh] at g64 g65
  rw [hX _ (hsg h hh)] at g65
  obtain ⟨c₃, t₃, e₃, ht₃, w64, w65, wn₃, wm₃, wr₃, wrm₃, wo₃⟩ :=
    ccW_exec (P := P) (Xb := Xb) (Sb := Sb) (k := k) (sg := SG) (ni := ni) (h := h)
      (T := T) hT hsg hh hstop hgo (by omega) (by omega) (T - 1) 1 c₂ (by omega) le_rfl
      e₂.wb_right (by rw [gn₂ _ (by omega)]; exact r35) (by rw [gn₂ _ (by omega)]; exact r54)
      (by rw [gn₂ _ (by omega)]; exact r39) g64 g65
      (fun x hx => by rw [G2 _ (by omega)]; exact hS x hx)
      (fun x hx => by rw [G2 _ (by omega)]; exact hX x hx)
  obtain ⟨c₄, t₄, e₄, ht₄, h40, gm₄, gn₄, gr₄, grm₄, go₄⟩ := ccD3_exec (P := P)
    (B2 := Cb + 4 + 2 * ks) (j := j) (v := ni (SG^[T] h)) c₃ e₃.wb_right
    (by rw [wn₃ _ (by omega) (by omega) (by omega), gn₂ _ (by omega)]; exact r39)
    (by rw [wn₃ _ (by omega) (by omega) (by omega), gn₂ _ (by omega)]; exact r40)
    (by rw [wn₃ _ (by omega) (by omega) (by omega), gn₂ _ (by omega)]; exact r60) w65
    (by omega) (by omega)
  refine ⟨c₄, t₂ + (t₃ + t₄), .seq e₂ (.seq e₃ e₄), by omega, h40, ?_, fun r hr => ?_,
    by rw [gr₄, wr₃, gr₂], by rw [grm₄, wrm₃, grm₂], by rw [go₄, wo₃, go₂]⟩
  · rw [gm₄, wm₃, gm₂, hX _ ha]
  · rw [gn₄ r (by omega) (by omega) (by omega), wn₃ r (by omega) (by omega) (by omega),
      gn₂ r (by omega)]

/-- The cells of the closure after one more step. -/
theorem CCells.step {Cb ks j : ℕ} {L : List ℕ} {GD AL SG GT GH T : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hj : j < L.length) (hks : L.length = ks)
    (h : CCells Cb ks L GD AL SG GT GH T mem j)
    (hm : mem' = upd (upd (upd (upd (upd mem (Cb + 4 + j) (GD L[j]))
      (Cb + 4 + 3 * ks + j) (GT L[j])) (Cb + 4 + 4 * ks + j) (GH L[j]))
      (Cb + 4 + ks + j) (L.idxOf (AL L[j]))) (Cb + 4 + 2 * ks + j)
      (L.idxOf (SG^[T j] L[j]))) :
    CCells Cb ks L GD AL SG GT GH T mem' (j + 1) := by
  intro j' hj' hj'L
  subst hm
  rcases Nat.lt_or_ge j' j with hlt | hge
  · obtain ⟨a1, a2, a3, a4, a5⟩ := h j' hlt hj'L
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;> first | omega | assumption
  · have e : j' = j := by omega
    subst e
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;> first | omega | rfl

theorem upd5_out {mem : ℕ → ℕ} {a1 a2 a3 a4 a5 v1 v2 v3 v4 v5 a : ℕ} (h1 : a ≠ a1)
    (h2 : a ≠ a2) (h3 : a ≠ a3) (h4 : a ≠ a4) (h5 : a ≠ a5) :
    upd (upd (upd (upd (upd mem a1 v1) a2 v2) a3 v3) a4 v4) a5 v5 a = mem a := by
  simp [upd_apply, h1, h2, h3, h4, h5]

set_option maxHeartbeats 4000000 in
/-- **The arrays of the child on the machine** (see the module docstring). -/
theorem ccProg_exec (c : Config) (hc : WordsBounded W c)
    {d Xb Yb Cb ms ks k Gb Ab Sb Tb Hb Lb : ℕ} {L : List ℕ} {T : ℕ → ℕ}
    (r31 : c.nreg 2931 = d) (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb)
    (r37 : c.nreg 2937 = Cb) (r39 : c.nreg 2939 = 1) (r50 : c.nreg 2950 = ms)
    (r51 : c.nreg 2951 = ks) (r52 : c.nreg 2952 = Gb) (r53 : c.nreg 2953 = Ab)
    (r54 : c.nreg 2954 = Sb) (r55 : c.nreg 2955 = Tb) (r56 : c.nreg 2956 = Hb)
    (r57 : c.nreg 2957 = Lb) (hlen : L.length = ks) (hms : ms ≤ ks)
    (hLk : ∀ x ∈ L, x < k) (hA : LArr Xb Yb k L c)
    (hsg : ∀ x < k, c.nmem (Sb + x) < k) (hal : ∀ x < k, c.nmem (Ab + x) < k)
    (hAm : ∀ j (hj : j < L.length), c.nmem (Ab + L[j]) ∈ L)
    (hT : ∀ j (hj : j < L.length), 1 ≤ T j ∧
      (fun x => c.nmem (Sb + x))^[T j] L[j] ∈ L ∧
      ∀ i, 1 ≤ i → i < T j → (fun x => c.nmem (Sb + x))^[i] L[j] ∉ L)
    (lG : Gb + k ≤ Cb) (lA : Ab + k ≤ Cb) (lS : Sb + k ≤ Cb) (lT : Tb + k ≤ Cb)
    (lH : Hb + k ≤ Cb) (lL : Lb + k ≤ Cb) (lX : Xb + k ≤ Cb) (lY : Yb + k ≤ Cb)
    (ld : d + 4 ≤ Cb) (hkk : ks ≤ k) (wC : Cb + 4 + 5 * ks + ms ≤ W) :
    ∃ c' t, Exec P W ccProg c c' t ∧
      t ≤ 33 * ks + 6 * ∑ j ∈ Finset.range ks, T j + 9 * ms + 30 ∧
      c'.nmem Cb = c.nmem d - 1 ∧ c'.nmem (Cb + 1) = ms ∧ c'.nmem (Cb + 2) = ks ∧
      c'.nmem (Cb + 3) = c.nmem (d + 3) ∧
      CCells Cb ks L (fun x => c.nmem (Gb + x)) (fun x => c.nmem (Ab + x))
        (fun x => c.nmem (Sb + x)) (fun x => c.nmem (Tb + x)) (fun x => c.nmem (Hb + x)) T
        c'.nmem ks ∧
      (∀ j (hj : j < ms), c'.nmem (Cb + 4 + 5 * ks + j) = c.nmem (Lb + L[j]'(by omega))) ∧
      (∀ a, (a < Cb ∨ Cb + 4 + 5 * ks + ms ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2958) ∨ 2965 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ccProg
  obtain ⟨c₁, t₁, e₁, ht₁, s40, s58, s59, s60, s61, s62, s63, sm₁, sr₁, srr₁, srm₁, so₁⟩ :=
    ccSet_exec (P := P) c hc r31 r37 r39 r50 r51 (by omega) (by omega)
  have M1 : ∀ a, (a < Cb ∨ Cb + 4 ≤ a) → c₁.nmem a = c.nmem a := fun a ha => by
    rw [sm₁, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
      upd_other _ _ _ (by omega)]
  have hLlt : ∀ j (hj : j < L.length), L[j] < k := fun j hj => hLk _ (List.getElem_mem hj)
  set SG : ℕ → ℕ := fun x => c.nmem (Sb + x) with hSG
  -- the closure
  let JD : ℕ → Config → Prop := fun j c' =>
    CCells Cb ks L (fun x => c.nmem (Gb + x)) (fun x => c.nmem (Ab + x)) SG
        (fun x => c.nmem (Tb + x)) (fun x => c.nmem (Hb + x)) T c'.nmem j ∧
      (∀ a, (a < Cb + 4 ∨ Cb + 4 + 5 * ks ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2964) ∨ 2965 < r) → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, d1, d2, d3, dr, drm, do'⟩ := forLoopV_exec (P := P)
    (a := 2940) (bR := 2951) (body := ccD) JD (K := 31) (n := ks) (fun j => 6 * T j) c₁
    e₁.wb_right s40 (by rw [sr₁ _ (by omega)]; exact r51)
    ⟨fun j' hj' => absurd hj' (by omega), fun _ _ => rfl, fun _ _ => rfl, srr₁, srm₁, so₁⟩
    (fun j c' hj hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jr, jrm, jo⟩ := hJ
      have hjL : j < L.length := by omega
      have hh := hLlt j hjL
      have R : ∀ a, a < Cb → c'.nmem a = c.nmem a := fun a ha' => by
        rw [j2 a (by omega), M1 a (by omega)]
      have eh : c'.nmem (Yb + j) = L[j] := by
        rw [R _ (by omega), hA.old j hjL, List.getD_eq_getElem _ _ hjL]
      have q : ∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2958)) → c'.nreg r = c.nreg r := fun r hr => by
        rw [j3 r (by omega), sr₁ r (by omega)]
      obtain ⟨hT1, hTm, hTn⟩ := hT j hjL
      have hal' := hal _ hh
      obtain ⟨c₄, t₄, e₄, ht₄, h40, gm₄, gn₄, gr₄, grm₄, go₄⟩ := ccD_exec (P := P)
        (Xb := Xb) (Yb := Yb) (Cb := Cb) (ks := ks) (k := k) (Gb := Gb) (Ab := Ab) (Sb := Sb)
        (Tb := Tb) (Hb := Hb) (j := j) (h := L[j]) (T := T j) (SG := SG) (ni := NIv L) c' hw
        (by rw [q _ (by omega)]; exact r35) (by rw [q _ (by omega)]; exact r36)
        (by rw [q _ (by omega)]; exact r39) ha (by rw [q _ (by omega)]; exact r52)
        (by rw [q _ (by omega)]; exact r53) (by rw [q _ (by omega)]; exact r54)
        (by rw [q _ (by omega)]; exact r55) (by rw [q _ (by omega)]; exact r56)
        (by rw [j3 _ (by omega)]; exact s58) (by rw [j3 _ (by omega)]; exact s59)
        (by rw [j3 _ (by omega)]; exact s60) (by rw [j3 _ (by omega)]; exact s61)
        (by rw [j3 _ (by omega)]; exact s62) eh hh (fun x hx => R _ (by omega)) hsg
        (fun x hx => by rw [R _ (by omega)]; exact hA.ni x hx)
        (by rw [R _ (by omega)]; exact hal') hT1 (NIv_pos_iff.2 hTm)
        (fun i h1 h2 => ite_eq_right_of_eq_false _ _ (eq_false (hTn i h1 h2)))
        lG lA lS lT lH lX (by omega) hj (by omega)
      have hm : c₄.nmem = upd (upd (upd (upd (upd c'.nmem (Cb + 4 + j) (c.nmem (Gb + L[j])))
          (Cb + 4 + 3 * ks + j) (c.nmem (Tb + L[j]))) (Cb + 4 + 4 * ks + j)
          (c.nmem (Hb + L[j]))) (Cb + 4 + ks + j) (L.idxOf (c.nmem (Ab + L[j]))))
          (Cb + 4 + 2 * ks + j) (L.idxOf (SG^[T j] L[j])) := by
        rw [gm₄, R _ (by omega), R _ (by omega), R _ (by omega), R _ (by omega),
          NIv_sub_one (hAm j hjL), NIv_sub_one hTm]
      refine ⟨c₄, t₄, e₄, ht₄, h40, by rw [gn₄ _ (by omega)]; exact hb,
        CCells.step hjL hlen j1 hm, fun a ha' => ?_, fun r hr => ?_,
        by rw [gr₄, jr], by rw [grm₄, jrm], by rw [go₄, jo]⟩
      · rw [hm, upd5_out (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact j2 a ha'
      · rw [gn₄ r (by omega)]; exact j3 r hr)
  obtain ⟨c₃, t₃, e₃, ht₃, h40₃, hn₃, hm₃, hr₃, hrm₃, ho₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.constN 2940 0]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 2940 = 0 ∧
      (∀ r, r ≠ 2940 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- the lengths
  let JE : ℕ → Config → Prop := fun j c' =>
    (∀ j' (hj' : j' < j) (hj : j' < L.length),
        c'.nmem (Cb + 4 + 5 * ks + j') = c.nmem (Lb + L[j'])) ∧
      (∀ a, (a < Cb + 4 + 5 * ks ∨ Cb + 4 + 5 * ks + ms ≤ a) → c'.nmem a = c₂.nmem a) ∧
      (∀ r, (r < 2940 ∨ 2944 < r) → c'.nreg r = c₃.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₄, t₄, e₄, ht₄, hw₄, f1, f2, f3, fr, frm, fo⟩ := forLoop_exec (P := P) (a := 2940)
    (bR := 2950) (body := ccE) JE (K := 7) (n := ms) c₃ e₃.wb_right h40₃
    (by rw [hn₃ _ (by omega), d3 _ (by omega), sr₁ _ (by omega)]; exact r50)
    ⟨fun j' hj' => absurd hj' (by omega), fun a _ => by rw [hm₃], fun _ _ => rfl,
      by rw [hr₃, dr], by rw [hrm₃, drm], by rw [ho₃, do']⟩
    (fun j c' hj hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jr, jrm, jo⟩ := hJ
      have hjL : j < L.length := by omega
      have hh := hLlt j hjL
      have R : ∀ a, a < Cb → c'.nmem a = c.nmem a := fun a ha' => by
        rw [j2 a (by omega), d2 a (by omega), M1 a (by omega)]
      have q : ∀ r, (r < 2940 ∨ (2947 < r ∧ r < 2958)) → c'.nreg r = c.nreg r := fun r hr => by
        rw [j3 r (by omega), hn₃ r (by omega), d3 r (by omega), sr₁ r (by omega)]
      obtain ⟨c'', t, ex, ht, h40, hm, hn, hr, hrm, ho⟩ := ccE_exec (P := P) (Yb := Yb)
        (Lb := Lb) (B5 := Cb + 4 + 5 * ks) (j := j) (h := L[j]) c' hw
        (by rw [q _ (by omega)]; exact r36) (by rw [q _ (by omega)]; exact r39) ha
        (by rw [q _ (by omega)]; exact r57)
        (by rw [j3 _ (by omega), hn₃ _ (by omega), d3 _ (by omega)]; exact s63)
        (by rw [R _ (by omega), hA.old j hjL, List.getD_eq_getElem _ _ hjL]) (by omega)
        (by omega) (by omega) (by omega)
      have hb' : c''.nreg 2950 = ms := by
        rw [hn _ (by omega) (by omega) (by omega) (by omega)]; exact hb
      refine ⟨c'', t, ex, by omega, h40, hb', fun j' hj' hj'L => ?_, fun a ha' => ?_,
        fun r hr' => by rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact j3 r hr',
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        split_ifs with e
        · have : j' = j := by omega
          subst this; exact R _ (by omega)
        · exact j1 j' (by omega) hj'L
      · rw [hm, upd_other _ _ _ (by omega)]; exact j2 a ha')
  have M2 : ∀ a, (a < Cb + 4 ∨ Cb + 4 + 5 * ks + ms ≤ a) → c₄.nmem a = c₁.nmem a :=
    fun a ha => by rw [f2 a (by omega), d2 a (by omega)]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_, ?_, ?_, ?_,
    fun j' hj' hj'L => ?_, fun j hj => ?_, fun a ha => ?_, fun r hr => ?_,
    by rw [fr], by rw [frm], by rw [fo]⟩
  · have := Finset.sum_range_succ (fun j => 6 * T j) 0
    rw [← Finset.mul_sum] at ht₂
    omega
  · rw [M2 _ (by omega), sm₁]; simp [upd_apply]
  · rw [M2 _ (by omega), sm₁]; simp [upd_apply]
  · rw [M2 _ (by omega), sm₁]; simp [upd_apply]
  · rw [M2 _ (by omega), sm₁]; simp [upd_apply]
  · obtain ⟨a1, a2, a3, a4, a5⟩ := d1 j' hj' hj'L
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [f2 _ (by omega)]; exact a1
    · rw [f2 _ (by omega)]; exact a2
    · rw [f2 _ (by omega)]; exact a3
    · rw [f2 _ (by omega)]; exact a4
    · rw [f2 _ (by omega)]; exact a5
  · exact f1 j hj (by omega)
  · rw [f2 a (by omega), d2 a (by omega), M1 a (by omega)]
  · rw [f3 r (by omega), hn₃ r (by omega), d3 r (by omega), sr₁ r (by omega)]

end Frame

end NegSSSP

end PlanarFlow
