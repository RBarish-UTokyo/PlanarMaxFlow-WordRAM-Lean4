module

public import PlanarFlow.NegSSSP.Enc.RnProg
public import PlanarFlow.NegSSSP.Enc.DkDist

/-!
# Renormalized potentials on the machine: the whole run

**`rnProg_exec`**: from `m` darts (tails `T[a] < w` at `Tb`, heads `H[a] < w` at `Hb`, lengths
`LL[a] ≤ Lm` at `LLb`) and `w` potentials `F[v] ≤ Fm` at `Fb`, all below the scratch base `Ab`,
`rnProg` writes `OUT[v] = D v + F v + L − K` (`K = rnK … = max F`) where `D` are the distances
from the source of the arcs `rnArcs` (`RnReach`: some walk has length `D y`, none is shorter),
within **`rnCost m w = O((m + w) log w)`** steps (Dijkstra in memory), natural words only, with
words `≤ W` for `W ≥ Ab + 5 (m + w) + 8 (w + 1) + 1` and `W ≥ 2 Fm + Lm + L + 2`. Memory written
only in the scratch `[Ab, Ab + 5 (m + w) + 8 (w + 1) + 1)` and the output `[OUTb, OUTb + w)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap Monge.FR

variable {P : Input} {W : ℕ}

/-- The words of the out-lists are arcs. -/
lemma osFl_getD_lt {T K : ℕ → ℕ} {M u j : ℕ} (hj : j < (osFl T K M u).length) :
    (osFl T K M u).getD j 0 < M := by
  have h := List.getElem_mem hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [osFl, List.mem_filter, List.mem_range] at h
  exact h.1

/-- **The parameters of Dijkstra on the out-lists of the arcs are well formed.** -/
theorem rn_dkG {mem : ℕ → ℕ} {A : RnArcs} {N M Dd Xb OBb OEb Ol NHb LNb K Lmax : ℕ}
    (hN : N = A.w + 1)
    (hl : ∀ u < N, mem (OEb + u) = mem (OBb + u) + (osFl A.tk (fun _ => 1) M u).length ∧
      mem (OEb + u) ≤ M ∧ ∀ j < (osFl A.tk (fun _ => 1) M u).length,
        mem (Ol + (mem (OBb + u) + j)) = (osFl A.tk (fun _ => 1) M u).getD j 0)
    (hnh : ∀ a < M, mem (NHb + a) < N) (hln : ∀ a < M, mem (LNb + a) ≤ Lmax)
    (l1 : OBb + N ≤ OEb) (l2 : OEb + N ≤ Dd) (l3 : Ol + M ≤ Dd) (l4 : NHb + M ≤ Dd)
    (l5 : LNb + M ≤ Dd) (l6 : Xb = Dd + N) (l7 : Xb + 3 * N ≤ W) (l8 : K + 1 + Lmax ≤ W) :
    DkG (dkPOf N Dd Xb OBb OEb Ol NHb LNb (K + 1) A.w mem) W := by
  have hol : ∀ y < N, ∀ i, mem (OBb + y) ≤ i → i < mem (OEb + y) → mem (Ol + i) < M := by
    intro y hy i h1 h2
    obtain ⟨he, -, hj⟩ := hl y hy
    have hlt : i - mem (OBb + y) < (osFl A.tk (fun _ => 1) M y).length := by omega
    have e := hj _ hlt
    rw [show mem (OBb + y) + (i - mem (OBb + y)) = i by omega] at e
    rw [e]; exact osFl_getD_lt hlt
  refine ⟨by simp only [dkPOf]; omega, by simp only [dkPOf]; omega, by simp [dkPOf]; omega, by simp [dkPOf]; omega,
    by simp [dkPOf]; omega, by simp [dkPOf]; omega, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy i h1 h2 => ?_, fun y hy i h1 h2 => ?_, fun y hy i h1 h2 => ?_,
    fun y hy i h1 h2 => ?_, fun y hy i h1 h2 => ?_⟩
  all_goals simp only [dkPOf, DkOut] at *
  · have := (hl y hy).1; omega
  · omega
  · omega
  · have := (hl y hy).2.1; omega
  · have := hol y hy i h1 h2; omega
  · have := hol y hy i h1 h2; omega
  · exact hnh _ (hol y hy i h1 h2)
  · have := hln _ (hol y hy i h1 h2); omega

lemma rnArcs_tk_lt {mem : ℕ → ℕ} {m w Tb Hb LLb Fb L a : ℕ}
    (hT : ∀ a < m, mem (Tb + a) < w) : (rnArcs mem m w Tb Hb LLb Fb L).tk a < w + 1 := by
  by_cases h : a < m
  · have := hT a h; simp only [RnArcs.tk, rnArcs, h, ite_true]; omega
  · simp only [RnArcs.tk, rnArcs, h, ite_false]; omega

lemma rnArcs_nh_lt {mem : ℕ → ℕ} {m w Tb Hb LLb Fb L a : ℕ}
    (hH : ∀ a < m, mem (Hb + a) < w) (ha : a < m + w) :
    (rnArcs mem m w Tb Hb LLb Fb L).nh a < w + 1 := by
  by_cases h : a < m
  · have := hH a h; simp only [RnArcs.nh, rnArcs, h, ite_true]; omega
  · simp only [RnArcs.nh, rnArcs, h, ite_false]; omega

lemma rnArcs_ln_le {mem : ℕ → ℕ} {m w Tb Hb LLb Fb L Fm Lm a : ℕ}
    (hT : ∀ a < m, mem (Tb + a) < w) (hF : ∀ v < w, mem (Fb + v) ≤ Fm)
    (hLL : ∀ a < m, mem (LLb + a) ≤ Lm) :
    (rnArcs mem m w Tb Hb LLb Fb L).ln a ≤ Lm + Fm := by
  by_cases h : a < m
  · have := hLL a h; have := hF _ (hT a h)
    simp only [RnArcs.ln, rnArcs, h, ite_true]; omega
  · have := rnK_le (mem := mem) (Fb := Fb) (i := w) hF
    simp only [RnArcs.ln, rnArcs, h, ite_false]; omega

/-- The cost bound of `dkProg` (`n` nodes, `mm` arcs). -/
def dkC (n mm : ℕ) : ℕ :=
  17 * n + 13 * lg (2 * n) + 22 + n * (23 * lg (2 * n) + 21) + (13 * lg (2 * n) + 20) * mm

/-- The cost of `rnProg`: `O((m + w) log w)`. -/
def rnCost (m w : ℕ) : ℕ :=
  7 * w + 25 * (m + w) + 16 + 10 + osCost (m + w) (w + 1) + 11 + dkC (w + 1) (m + w) + 1 +
    (12 * w + 2)

/-- **The out-lists of the arcs** (`rnOsSet ; osProg`): keys `tk` at `Ab`, flags `1` at
`Ab + M`, the out-lists at `OBb = B3 + M + N + 1 + N`, `OEb = OBb + N`, `Ol = OEb + N`. -/
theorem rnMid_exec (c : Config) (hc : WordsBounded W c) {M N Ab B3 : ℕ} {tk : ℕ → ℕ}
    (r75 : c.nreg 2975 = M) (r76 : c.nreg 2976 = N) (r79 : c.nreg 2979 = 1)
    (r80 : c.nreg 2980 = Ab) (r81 : c.nreg 2981 = Ab + M) (r83 : c.nreg 2983 = B3)
    (hB : Ab + M + M ≤ B3) (htk : ∀ i < M, c.nmem (Ab + i) = tk i)
    (hkp : ∀ i < M, c.nmem (Ab + M + i) = 1) (htkN : ∀ i < M, tk i < N)
    (hW : B3 + M + 4 * N + 1 + M ≤ W) :
    ∃ c' k, Exec P W rnMid c c' k ∧ k ≤ 10 + osCost M N ∧
      (∀ u < N, c'.nmem (B3 + M + N + 1 + N + N + u) =
          c'.nmem (B3 + M + N + 1 + N + u) + (osFl tk (fun _ => 1) M u).length ∧
        c'.nmem (B3 + M + N + 1 + N + N + u) ≤ M ∧
        ∀ j < (osFl tk (fun _ => 1) M u).length,
          c'.nmem (B3 + M + N + 1 + N + N + N + (c'.nmem (B3 + M + N + 1 + N + u) + j)) =
            (osFl tk (fun _ => 1) M u).getD j 0) ∧
      (∑ u ∈ range N, (c'.nmem (B3 + M + N + 1 + N + N + u) -
        c'.nmem (B3 + M + N + 1 + N + u)) ≤ M) ∧
      c'.nreg 1507 = B3 + M + N + 1 + N ∧ c'.nreg 1508 = B3 + M + N + 1 + N + N ∧
      c'.nreg 1509 = B3 + M + N + 1 + N + N + N ∧
      (∀ a, a < B3 + M ∨ B3 + M + N + 1 + N + N + N + M ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1500 ∨ 1520 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₅, k₅, e₅, hk₅, o00, o01, o02, o04, o05, o06, o07, o08, o09, on₅, om₅, or₅, orm₅,
    oo₅⟩ := rnOsSet_exec (P := P) c hc r75 r76 r79 r80 r81 r83 (by omega)
  have hw₅ := e₅.wb_right
  have hLay : OsLay M N Ab (Ab + M) (B3 + M) (B3 + M + N + 1) (B3 + M + N + 1 + N)
      (B3 + M + N + 1 + N + N) (B3 + M + N + 1 + N + N + N) W tk (fun _ => 1) :=
    ⟨fun i hi _ => htkN i hi, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hIn : OsIn M N Ab (Ab + M) (B3 + M) (B3 + M + N + 1) (B3 + M + N + 1 + N)
      (B3 + M + N + 1 + N + N) (B3 + M + N + 1 + N + N + N) tk (fun _ => 1) c₅ :=
    ⟨o00, o01, o02, o04, o05, o06, o07, o08, o09, fun i hi => by rw [om₅]; exact htk i hi,
      fun i hi => by rw [om₅]; exact hkp i hi⟩
  obtain ⟨c₆, k₆, e₆, hk₆, hl₆, hs₆, hm₆, hn₆, hr₆, hrm₆, ho₆⟩ :=
    osProg_lists (P := P) hLay c₅ hw₅ hIn
  refine ⟨c₆, k₅ + k₆, .seq e₅ e₆, by omega, hl₆, hs₆, by rw [hn₆ _ (by omega)]; exact o07,
    by rw [hn₆ _ (by omega)]; exact o08, by rw [hn₆ _ (by omega)]; exact o09,
    fun a ha => ?_, fun r hr => ?_, by rw [hr₆, or₅], by rw [hrm₆, orm₅], by rw [ho₆, oo₅]⟩
  · rw [hm₆ a (by omega) (by omega), om₅]
  · rcases hr with hr | hr
    · rw [hn₆ r (by omega), on₅ r (by omega)]
    · rw [hn₆ r (by omega), on₅ r (by omega)]

set_option maxHeartbeats 1600000 in
/-- **Dijkstra from the source and the output** (`rnBack`): from the out-lists of the arcs `A`
(`osFl`), their heads and lengths in memory, `OUT[v] = D v + F v + L − K` with `D` the
distances of the walks from the source. -/
theorem rnBack_exec (c : Config) (hc : WordsBounded W c) {A : RnArcs}
    {K OBb OEb Ol NHb LNb Fb L OUTb Fm Lmax : ℕ}
    (r75 : c.nreg 2975 = A.m + A.w) (r76 : c.nreg 2976 = A.w + 1) (r67 : c.nreg 2967 = A.w)
    (r77 : c.nreg 2977 = K) (r79 : c.nreg 2979 = 1) (r82 : c.nreg 2982 = NHb)
    (r83 : c.nreg 2983 = LNb) (r07 : c.nreg 1507 = OBb) (r08 : c.nreg 1508 = OEb)
    (r09 : c.nreg 1509 = Ol) (r71 : c.nreg 2971 = Fb) (r72 : c.nreg 2972 = L)
    (r73 : c.nreg 2973 = OUTb)
    (hl : ∀ u < A.w + 1, c.nmem (OEb + u) =
        c.nmem (OBb + u) + (osFl A.tk (fun _ => 1) (A.m + A.w) u).length ∧
      c.nmem (OEb + u) ≤ A.m + A.w ∧ ∀ j < (osFl A.tk (fun _ => 1) (A.m + A.w) u).length,
        c.nmem (Ol + (c.nmem (OBb + u) + j)) = (osFl A.tk (fun _ => 1) (A.m + A.w) u).getD j 0)
    (hdeg : ∑ u ∈ range (A.w + 1), (c.nmem (OEb + u) - c.nmem (OBb + u)) ≤ A.m + A.w)
    (hnh : ∀ a < A.m + A.w, c.nmem (NHb + a) = A.nh a)
    (hln : ∀ a < A.m + A.w, c.nmem (LNb + a) = A.ln a)
    (hnhN : ∀ a < A.m + A.w, A.nh a < A.w + 1) (hlnL : ∀ a < A.m + A.w, A.ln a ≤ Lmax)
    (htkN : ∀ a < A.m + A.w, A.tk a < A.w + 1)
    (hsrc : ∀ y < A.w, ∃ Lr ≤ K, RnReach A y Lr)
    (hF : ∀ v < A.w, c.nmem (Fb + v) ≤ Fm)
    (l1 : OBb + (A.w + 1) ≤ OEb) (l2 : OEb + (A.w + 1) ≤ Ol) (l4 : NHb + (A.m + A.w) ≤ Ol)
    (l5 : LNb + (A.m + A.w) ≤ Ol) (lF : Fb + A.w ≤ Ol + (A.m + A.w))
    (lO : OUTb + A.w ≤ Ol + (A.m + A.w)) (dOF : OUTb + A.w ≤ Fb ∨ Fb + A.w ≤ OUTb)
    (wE : Ol + (A.m + A.w) + 4 * (A.w + 1) ≤ W) (wV1 : K + 1 + Lmax ≤ W)
    (wV2 : Fm + K + 1 + L ≤ W) :
    ∃ c' k, Exec P W rnBack c c' k ∧
      k ≤ 11 + dkC (A.w + 1) (A.m + A.w) + 1 + (12 * A.w + 2) ∧
      (∃ Dd : ℕ → ℕ, (∀ y < A.w, RnReach A y (Dd y)) ∧
        (∀ y < A.w, ∀ Lr, RnReach A y Lr → Dd y ≤ Lr) ∧
        ∀ v < A.w, c'.nmem (OUTb + v) = Dd v + c.nmem (Fb + v) + L - K) ∧
      (∀ a, (a < Ol + (A.m + A.w) ∨ Ol + (A.m + A.w) + 4 * (A.w + 1) ≤ a) →
        (a < OUTb ∨ OUTb + A.w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2500 ∨ (2547 < r ∧ r ≠ 2978 ∧ r ≠ 2984 ∧ r ≠ 2985 ∧ r ≠ 2986 ∧ r ≠ 2990) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₇, k₇, e₇, hk₇, d00, d01, d02, d04, d05, d06, d07, d08, d09, d10, d90, dn₇, dm₇,
    dr₇, drm₇, do₇⟩ := rnDkSet_exec (P := P) c hc r75 r76 r67 r77 r79 r82 r83 r07 r08 r09
      (by omega) (by omega)
  have hw₇ := e₇.wb_right
  have hl₇ := hl
  rw [← dm₇] at hl₇
  have hG : DkG (dkPOf (A.w + 1) (Ol + (A.m + A.w)) (Ol + (A.m + A.w) + (A.w + 1)) OBb OEb Ol
      NHb LNb (K + 1) A.w c₇.nmem) W :=
    rn_dkG (A := A) (Lmax := Lmax) rfl hl₇
      (fun a ha => by rw [dm₇, hnh a ha]; exact hnhN a ha)
      (fun a ha => by rw [dm₇, hln a ha]; exact hlnL a ha)
      l1 (by omega) (by omega) (by omega) (by omega) rfl (by omega) wV1
  obtain ⟨c₈, k₈, e₈, hk₈, hD₈, hm₈, hn₈, hr₈, hrm₈, ho₈⟩ :=
    dkProg_exec (P := P) hG c₇ hw₇ ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩ d00 d01 d02 d04 d05 d06 d07 d08 d09 d10
      (mm := A.m + A.w) (by simp only [dkPOf]; rw [dm₇]; exact hdeg)
  have hw₈ := e₈.wb_right
  obtain ⟨hDR, hRD⟩ := dk_rn (A := A) (p := dkPOf (A.w + 1) (Ol + (A.m + A.w))
      (Ol + (A.m + A.w) + (A.w + 1)) OBb OEb Ol NHb LNb (K + 1) A.w c₇.nmem) rfl
    (fun u hu => ⟨(hl₇ u hu).1, (hl₇ u hu).2.2⟩)
    (fun a ha => by simp only [dkPOf]; rw [dm₇, hnh a ha])
    (fun a ha => by simp only [dkPOf]; rw [dm₇, hln a ha]) htkN
  have hD2 : ∀ y < A.w, ∀ Lr, RnReach A y Lr → c₈.nmem (Ol + (A.m + A.w) + y) ≤ Lr :=
    fun y hy Lr h => (hD₈ y (by simp only [dkPOf]; omega)).2.2 Lr (hRD y Lr h)
  have hDle : ∀ y < A.w, c₈.nmem (Ol + (A.m + A.w) + y) ≤ K := fun y hy => by
    obtain ⟨Lr, hLr, h⟩ := hsrc y hy
    exact (hD2 y hy Lr h).trans hLr
  have hD1 : ∀ y < A.w, RnReach A y (c₈.nmem (Ol + (A.m + A.w) + y)) := fun y hy =>
    hDR y _ ((hD₈ y (by simp only [dkPOf]; omega)).2.1
      (by have := hDle y hy; simp only [dkPOf]; omega))
  have e₉ := Exec.constN (P := P) hw₈ 2978 0 (by omega)
  have hw₉ := e₉.wb_right
  have n₉ : ∀ r, r ≠ 2978 → 2547 < r → r ≠ 2990 → (r < 2500 ∨ 2510 < r) →
      (upd c₈.nreg 2978 0) r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [upd_other _ _ _ h1, hn₈ r (by omega), dn₇ r h4 h3]
  have mF : ∀ v < A.w, c₈.nmem (Fb + v) = c.nmem (Fb + v) := fun v hv => by
    rw [hm₈ _ (by simp only [dkPOf, DkOut]; omega), dm₇]
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, u₁₀, um₁₀, un₁₀, ur₁₀, urm₁₀, uo₁₀⟩ := rnOut_exec (P := P)
    (w := A.w) (Fb := Fb) (L := L) (OUTb := OUTb) (K := K) (Db := Ol + (A.m + A.w)) _ hw₉
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r67)
    (by simp only []; rw [upd_other _ _ _ (by omega), hn₈ _ (by omega)]; exact d90)
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r71)
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r72)
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r73)
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r77)
    (by simp only [upd_apply, ite_true])
    (by simp only []; rw [n₉ _ (by omega) (by omega) (by omega) (by omega)]; exact r79)
    (by omega) (by omega) (by omega) (by omega) dOF
    (fun v hv => by
      simp only []; rw [mF v hv]; have := hDle v hv; have := hF v hv; omega)
  refine ⟨c₁₀, k₇ + (k₈ + (1 + k₁₀)), .seq e₇ (.seq e₈ (.seq e₉ e₁₀)), ?_,
    ⟨fun y => c₈.nmem (Ol + (A.m + A.w) + y), hD1, hD2, fun v hv => ?_⟩, fun a h1 h2 => ?_,
    fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [dkPOf] at hk₈; unfold dkC; omega
  · rw [u₁₀ v hv]; simp only []; rw [mF v hv]
  · rw [um₁₀ a h2]; simp only []
    rw [hm₈ _ (by simp only [dkPOf, DkOut]; omega), dm₇]
  · rw [un₁₀ r (by omega) (by omega) (by omega) (by omega)]
    simp only []
    rcases hr with hr | ⟨hr, h1, h2, h3, h4, h5⟩
    · rw [upd_other _ _ _ (by omega), hn₈ r (Or.inl hr), dn₇ r (Or.inl hr) (by omega)]
    · rw [upd_other _ _ _ h1, hn₈ r (by omega), dn₇ r (by omega) h5]
  · rw [ur₁₀]; simp only []; rw [hr₈, dr₇]
  · rw [urm₁₀]; simp only []; rw [hrm₈, drm₇]
  · rw [uo₁₀]; simp only []; rw [ho₈, do₇]

set_option maxHeartbeats 1600000 in
/-- **The renormalization on the machine** (see the module docstring). -/
theorem rnProg_exec {m w Tb Hb LLb Fb L OUTb Ab Fm Lm : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r68 : c.nreg 2968 = Tb)
    (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r73 : c.nreg 2973 = OUTb) (r74 : c.nreg 2974 = Ab)
    (hT : ∀ a < m, c.nmem (Tb + a) < w) (hH : ∀ a < m, c.nmem (Hb + a) < w)
    (hF : ∀ v < w, c.nmem (Fb + v) ≤ Fm) (hLL : ∀ a < m, c.nmem (LLb + a) ≤ Lm)
    (lT : Tb + m ≤ Ab) (lH : Hb + m ≤ Ab) (lL : LLb + m ≤ Ab) (lF : Fb + w ≤ Ab)
    (lO : OUTb + w ≤ Ab) (dOF : OUTb + w ≤ Fb ∨ Fb + w ≤ OUTb)
    (wE : Ab + 5 * (m + w) + 8 * (w + 1) + 1 ≤ W) (wV : 2 * Fm + Lm + L + 2 ≤ W) :
    ∃ c' k, Exec P W rnProg c c' k ∧ k ≤ rnCost m w ∧
      (∃ Dd : ℕ → ℕ, (∀ y < w, RnReach (rnArcs c.nmem m w Tb Hb LLb Fb L) y (Dd y)) ∧
        (∀ y < w, ∀ Lr, RnReach (rnArcs c.nmem m w Tb Hb LLb Fb L) y Lr → Dd y ≤ Lr) ∧
        ∀ v < w, c'.nmem (OUTb + v) = Dd v + c.nmem (Fb + v) + L - rnK c.nmem Fb w) ∧
      (∀ a, (a < Ab ∨ Ab + 5 * (m + w) + 8 * (w + 1) + 1 ≤ a) → (a < OUTb ∨ OUTb + w ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1500 ∨ (1520 < r ∧ r < 2500) ∨ (2547 < r ∧ r < 2975) ∨ 2990 < r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hKF : rnK c.nmem Fb w ≤ Fm := rnK_le hF
  obtain ⟨c₄, k₄, e₄, hk₄, a₄, f₄, g75, g76, g77, g79, g80, g81, g82, g83, gn₄, gr₄, grm₄,
    go₄⟩ := rnFront_exec (P := P) (Fm := Fm) (Lm := Lm) c hc r66 r67 r68 r69 r70 r71 r72 r74
      hT hH hF hLL lT lH lL lF (by omega) (by omega)
  have hw₄ := e₄.wb_right
  obtain ⟨c₆, k₆, e₆, hk₆, hl₆, hs₆, h07, h08, h09, hm₆, hn₆, hr₆, hrm₆, ho₆⟩ :=
    rnMid_exec (P := P) (M := m + w) (N := w + 1) (Ab := Ab)
      (B3 := Ab + (m + w) + (m + w) + (m + w)) (tk := (rnArcs c.nmem m w Tb Hb LLb Fb L).tk)
      c₄ hw₄ g75 g76 g79 g80 g81 g83 (by omega) (fun i hi => (a₄ i hi).1)
      (fun i hi => (a₄ i hi).2.1) (fun i _ => rnArcs_tk_lt hT) (by omega)
  have hw₆ := e₆.wb_right
  have q₆ : ∀ r, 2547 < r → r < 2975 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hn₆ r (by omega), gn₄ r (by omega)]
  have q₆' : ∀ r, 2974 < r → c₆.nreg r = c₄.nreg r := fun r h1 => hn₆ r (by omega)
  have mF : ∀ v < w, c₆.nmem (Fb + v) = c.nmem (Fb + v) := fun v hv => by
    rw [hm₆ _ (by omega), f₄ _ (by omega)]
  have hsrc : ∀ y < w, ∃ Lr ≤ rnK c.nmem Fb w,
      RnReach (rnArcs c.nmem m w Tb Hb LLb Fb L) y Lr := fun y hy => by
    have r := RnReach.step (A := rnArcs c.nmem m w Tb Hb LLb Fb L) .src (a := m + y)
      (by simp only [rnArcs]; omega) (by simp [RnArcs.tk, rnArcs])
    have e1 : (rnArcs c.nmem m w Tb Hb LLb Fb L).nh (m + y) = y := by
      simp [RnArcs.nh, rnArcs]
    rw [e1, Nat.zero_add] at r
    refine ⟨_, ?_, r⟩
    simp only [RnArcs.ln, rnArcs]; simp
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, ⟨Dd, hD1, hD2, hOut⟩, um₁₀, un₁₀, ur₁₀, urm₁₀, uo₁₀⟩ :=
    rnBack_exec (P := P) (A := rnArcs c.nmem m w Tb Hb LLb Fb L) (K := rnK c.nmem Fb w)
      (OBb := Ab + (m + w) + (m + w) + (m + w) + (m + w) + (w + 1) + 1 + (w + 1))
      (OEb := Ab + (m + w) + (m + w) + (m + w) + (m + w) + (w + 1) + 1 + (w + 1) + (w + 1))
      (Ol := Ab + (m + w) + (m + w) + (m + w) + (m + w) + (w + 1) + 1 + (w + 1) + (w + 1) +
        (w + 1))
      (NHb := Ab + (m + w) + (m + w)) (LNb := Ab + (m + w) + (m + w) + (m + w)) (Fb := Fb)
      (L := L) (OUTb := OUTb) (Fm := Fm) (Lmax := Lm + Fm) c₆ hw₆
      (by rw [q₆' _ (by omega)]; exact g75) (by rw [q₆' _ (by omega)]; exact g76)
      (by rw [q₆ _ (by omega) (by omega)]; exact r67) (by rw [q₆' _ (by omega)]; exact g77)
      (by rw [q₆' _ (by omega)]; exact g79) (by rw [q₆' _ (by omega)]; exact g82)
      (by rw [q₆' _ (by omega)]; exact g83) h07 h08 h09
      (by rw [q₆ _ (by omega) (by omega)]; exact r71)
      (by rw [q₆ _ (by omega) (by omega)]; exact r72)
      (by rw [q₆ _ (by omega) (by omega)]; exact r73) hl₆ hs₆
      (fun a ha => by rw [hm₆ _ (by simp only [rnArcs] at ha; omega)]; exact (a₄ a ha).2.2.1)
      (fun a ha => by rw [hm₆ _ (by simp only [rnArcs] at ha; omega)]; exact (a₄ a ha).2.2.2)
      (fun a ha => rnArcs_nh_lt hH ha) (fun a _ => rnArcs_ln_le hT hF hLL)
      (fun a _ => rnArcs_tk_lt hT) hsrc (fun v hv => by rw [mF v hv]; exact hF v hv)
      (by simp only [rnArcs]; omega) (by simp only [rnArcs]; omega)
      (by simp only [rnArcs]; omega) (by simp only [rnArcs]; omega)
      (by simp only [rnArcs]; omega) (by simp only [rnArcs]; omega) dOF
      (by simp only [rnArcs]; omega) (by omega) (by omega)
  have hk' : k₁₀ ≤ 11 + dkC (w + 1) (m + w) + 1 + (12 * w + 2) := hk₁₀
  refine ⟨c₁₀, k₄ + (k₆ + k₁₀), .seq e₄ (.seq e₆ e₁₀), ?_,
    ⟨Dd, hD1, hD2, fun v hv => ?_⟩, fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · unfold rnCost; omega
  · rw [hOut v hv, mF v hv]
  · rw [um₁₀ a (by simp only [rnArcs]; omega) h2, hm₆ _ (by omega), f₄ _ (by omega)]
  · rw [un₁₀ r (by omega), hn₆ r (by omega), gn₄ r (by omega)]
  · rw [ur₁₀, hr₆, gr₄]
  · rw [urm₁₀, hrm₆, grm₄]
  · rw [uo₁₀, ho₆, go₄]

/-! ### The meaning: a renormalized feasible potential -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

set_option maxHeartbeats 1600000 in
/-- **The renormalized potential on the machine.** The piece `P` (darts `e a`, `a < m`, its
vertices numbered `ν` below `w` with inverse `ι`), a feasible potential `f` of the piece in the
offset encoding `F[v] = f (ι v) + Lf` (any magnitude `|f| ≤ Lf`), the lengths `LL[a] = ℓ (e a) + L`,
the tails and heads `T[a] = ν (tail (e a))`, `H[a] = ν (head (e a))`: `rnProg` writes
`OUT[v] = (g (ι v) + L).toNat` for a **feasible potential `g` of the piece with
`−Σ_{d ∈ P} |ℓ d| ≤ g ≤ 0`** on its vertices, within `rnCost m w = O((m + w) log w)` steps,
words `≤ W` for `W ≥ Ab + 5 (m + w) + 8 (w + 1) + 1` and `W ≥ 4 Lf + 2 L + L + 2`. So the
magnitude of the outcome no longer depends on that of `f`. -/
theorem rnProg_pot {Q : Finset D} {ℓ : D → ℤ} {f : V → ℤ} (hf : (pg N Q ℓ).IsPot f)
    {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} {m w Tb Hb LLb Fb L Lf OUTb Ab : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (r66 : c.nreg 2966 = m) (r67 : c.nreg 2967 = w) (r68 : c.nreg 2968 = Tb)
    (r69 : c.nreg 2969 = Hb) (r70 : c.nreg 2970 = LLb) (r71 : c.nreg 2971 = Fb)
    (r72 : c.nreg 2972 = L) (r73 : c.nreg 2973 = OUTb) (r74 : c.nreg 2974 = Ab)
    (he : ∀ a < m, e a ∈ Q) (he_inj : ∀ a < m, ∀ b < m, e a = e b → a = b)
    (he_surj : ∀ d ∈ Q, ∃ a < m, e a = d)
    (hν : ∀ x ∈ verts N Q, ν x < w ∧ ι (ν x) = x) (hι : ∀ v < w, ι v ∈ verts N Q ∧ ν (ι v) = v)
    (hT : ∀ a < m, c.nmem (Tb + a) = ν (N.tail (e a)))
    (hH : ∀ a < m, c.nmem (Hb + a) = ν (N.head (e a)))
    (hLL : ∀ a < m, (c.nmem (LLb + a) : ℤ) = ℓ (e a) + L)
    (hF : ∀ v < w, (c.nmem (Fb + v) : ℤ) = f (ι v) + Lf)
    (hfL : ∀ v < w, |f (ι v)| ≤ Lf) (hℓL : ∀ d ∈ Q, |ℓ d| ≤ L)
    (hL : ∑ d ∈ Q, |ℓ d| ≤ L)
    (lT : Tb + m ≤ Ab) (lH : Hb + m ≤ Ab) (lL : LLb + m ≤ Ab) (lF : Fb + w ≤ Ab)
    (lO : OUTb + w ≤ Ab) (dOF : OUTb + w ≤ Fb ∨ Fb + w ≤ OUTb)
    (wE : Ab + 5 * (m + w) + 8 * (w + 1) + 1 ≤ W) (wV : 4 * Lf + 2 * L + L + 2 ≤ W) :
    ∃ c' k, Exec P W rnProg c c' k ∧ k ≤ rnCost m w ∧
      (∃ g : V → ℤ, (pg N Q ℓ).IsPot g ∧
        (∀ x ∈ verts N Q, -(∑ d ∈ Q, |ℓ d|) ≤ g x ∧ g x ≤ 0) ∧
        ∀ v < w, c'.nmem (OUTb + v) = (g (ι v) + L).toNat) ∧
      (∀ a, (a < Ab ∨ Ab + 5 * (m + w) + 8 * (w + 1) + 1 ≤ a) → (a < OUTb ∨ OUTb + w ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1500 ∨ (1520 < r ∧ r < 2500) ∨ (2547 < r ∧ r < 2975) ∨ 2990 < r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hTw : ∀ a < m, c.nmem (Tb + a) < w := fun a ha => by
    rw [hT a ha]; exact (hν _ (tail_mem_verts (he a ha))).1
  have hHw : ∀ a < m, c.nmem (Hb + a) < w := fun a ha => by
    rw [hH a ha]; exact (hν _ (head_mem_verts (he a ha))).1
  have hFm : ∀ v < w, c.nmem (Fb + v) ≤ 2 * Lf := fun v hv => by
    have := hF v hv; have := abs_le.1 (hfL v hv); omega
  have hLm : ∀ a < m, c.nmem (LLb + a) ≤ 2 * L := fun a ha => by
    have := hLL a ha; have := abs_le.1 (hℓL _ (he a ha)); omega
  obtain ⟨c', k, ex, hk, ⟨Dd, hD1, hD2, hOut⟩, hm, hn, hr, hrm, ho⟩ :=
    rnProg_exec (P := P) (Fm := 2 * Lf) (Lm := 2 * L) c hc r66 r67 r68 r69 r70 r71 r72 r73 r74
      hTw hHw hFm hLm lT lH lL lF lO dOF wE (by omega)
  set K := rnK c.nmem Fb w with hK
  have hFK : ∀ v < w, c.nmem (Fb + v) ≤ K := fun v hv => le_rnK hv
  -- the value of `F` at the tail and the head of a dart
  have hFx : ∀ x ∈ verts N Q, (c.nmem (Fb + ν x) : ℤ) = f x + Lf := fun x hx => by
    obtain ⟨h1, h2⟩ := hν x hx; rw [hF _ h1, h2]
  obtain ⟨hpot, hbd⟩ := rn_pot (A := rnArcs c.nmem m w Tb Hb LLb Fb L) (N := N) (P := Q)
    (ℓ := ℓ) (f := f) (e := e) (ν := ν) (ι := ι) (Kz := (K : ℤ) - Lf) (Dd := Dd)
    he he_inj he_surj hν (fun a ha => hT a ha) (fun a ha => hH a ha)
    (fun a ha => by
      have ht := hFx _ (tail_mem_verts (he a ha))
      have hh := hFx _ (head_mem_verts (he a ha))
      have hd := hf ⟨e a, he a ha⟩
      simp only [pg, MSSP.pieceGraph] at hd
      have hl := hLL a ha
      show ((c.nmem (LLb + a) + c.nmem (Fb + c.nmem (Tb + a)) -
        (c.nmem (Fb + c.nmem (Hb + a)) + L) : ℕ) : ℤ) = _
      rw [hT a ha, hH a ha]
      rw [Nat.cast_sub (by omega)]
      push_cast; linarith)
    (fun v hv => by
      show ((K - c.nmem (Fb + v) : ℕ) : ℤ) = _
      rw [Nat.cast_sub (hFK v hv), hF v hv]; ring)
    hD1 hD2
  refine ⟨c', k, ex, hk, ⟨fun x => (Dd (ν x) : ℤ) + f x - ((K : ℤ) - Lf), hpot, hbd,
    fun v hv => ?_⟩, hm, hn, hr, hrm, ho⟩
  obtain ⟨hx, hνι⟩ := hι v hv
  obtain ⟨b1, b2⟩ := hbd _ hx
  rw [hOut v hv]
  simp only [hνι] at b1 b2 ⊢
  have := hF v hv
  have := hFK v hv
  omega

end NegSSSP

end PlanarFlow
