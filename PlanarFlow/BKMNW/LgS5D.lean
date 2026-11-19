module

public import PlanarFlow.BKMNW.LgS5C

/-!
# The large-piece separator, stage 5: the certificate and the body

* **`s5Fin_exec`**: `s5E1 ; s5E2 ; s5E3 ; s5E4 ; tfProg ; scProg mbBase` from the arrays of
  stages 2–4 (any enumeration `e` of `B` increasing in `gid`, weights `ex` of total `≤ W₀`): the
  outcome of `scProgT_execK` for `L = 6`, `T₀ = W₀`, with its layout from `U`;
* **`s5Body_exec`**: the whole body `s5Body` (keys, weights, base, certificate) for the
  headline's choices: the certificate `scertD (s5sc M eG N Hs A W₀) Hs B st (s5ex …)` (by
  `scertD_gidLoc`), within `9500 n + 40 k + 5 log₂ (2 W₀) + mbT n' (encB' W₀) W₀ + 3500` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

section Exec

variable {I : Input} {W : ℕ}

/-- **Stage 5, the certificate**: `LvRegs` and the bases, then `tfProg ; scProg mbBase`. -/
theorem s5Fin_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {B : Finset D} {st : Perm D} (hPM : PMap M B Hs st)
    {e : ℕ → D} {ex : D → ℕ} {n n' U A W₀ Bz : ℕ} (c : Config) (hc : WordsBounded W c)
    (hem : ∀ j < n', e j ∈ B) (hes : ∀ y ∈ B, ∃ j < n', e j = y)
    (hmono : ∀ i j, i < j → j < n' → gid (e i) < gid (e j)) (hne : 0 < n') (hn'n : n' ≤ n)
    (hL : (tHs M B Hs).length ≤ 6) (hT₀ : ∑ d ∈ B, (1 + ex d) ≤ W₀) (hBz : encB' n' ≤ Bz)
    (hnf : ∀ j < n', c.nmem (U + 4 * n + j) = 1)
    (hth : ∀ j < n', c.nmem (U + 4 * n + n' + j) = hlab Hs (M.tail (e j)))
    (hrv : ∀ j < n', c.nmem (U + 4 * n + 2 * n' + j) < n' ∧
      e (c.nmem (U + 4 * n + 2 * n' + j)) = M.rev (e j))
    (hsg : ∀ j < n', c.nmem (U + 3 * n + j) < n' ∧ e (c.nmem (U + 3 * n + j)) = st (e j))
    (htk : ∀ i < n', c.nmem (U + 4 * n + 6 * n' + i) < n')
    (hkey : ∀ i < n', ∀ j < n', (c.nmem (U + 4 * n + 6 * n' + i) =
      c.nmem (U + 4 * n + 6 * n' + j) ↔ st.SameCycle (e i) (e j)))
    (hex : ∀ j < n', c.nmem (U + 4 * n + 3 * n' + j) = ex (e j))
    (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = U + 4 * n) (r11 : c.nreg 5811 = n')
    (r14 : c.nreg 5814 = U + 3 * n) (r3102 : c.nreg 3102 = Hs.length) (r58 : c.nreg 5858 = Bz)
    (r911 : c.nreg 5911 = A) (r912 : c.nreg 5912 = W₀)
    (w : U + 600 * n + 10 * Hs.length + 2 * Bz + 20 * W₀ + A + 400 ≤ W) :
    ∃ c' t, Exec I W s5Fin c c' t ∧
      t ≤ 92 + (32 * n' + 17 * Hs.length + 62 + ((6 + 1) * (6 * (160 * n' + 36) + 244 * n' + 110) +
        mbT n' Bz W₀ + 6 * (7 * n' + 40) + 22 * n' + 40)) ∧
      (∀ a < U + 4 * n, c'.nmem a = c.nmem a) ∧ c'.nreg 3109 = Bz ∧
      (∀ y, s5BFr y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      ((c'.nreg 4970 = 0 ∧ scertD (scChoiceE M (sepC M e n' Bz) e n' Hs A W₀) Hs B st ex = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I,
         scertD (scChoiceE M (sepC M e n' Bz) e n' Hs A W₀) Hs B st ex = some (ρ, I) ∧
         ItemRep e n' I (fun i => c'.nmem (U + 42 * n + 5 * Hs.length + 7 * n' + 32 + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNH M e n' (U + 42 * n + 5 * Hs.length + 8 * n' + 32) Hs c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n' ∧
            ρ = (SPath.point (M' := M) (e (c'.nreg 4902)) (M.tail (e (c'.nreg 4902)))).toH)))) := by
  have heinj : ∀ i < n', ∀ j < n', e i = e j → i = j := inj_of_gidMono hmono
  obtain ⟨c₇, t₇, e₇, ht₇, hLv, v5200, v5202, v3109, v4936, v5830, v4937, v4955, v4956, v5201,
    v5203, f₇, m₇, rr₇, rm₇, o₇⟩ := s5E_exec (I := I) c hc r00 r10 r11 r3102 r14 r58 r911 r912
    (by clear * - w hn'n; omega) (by clear * - w hn'n; omega) (by clear * - w; omega)
  have hI : LvIn M c₇.nmem n' (U + 4 * n) e B B Hs ex := by
    rw [m₇]
    exact lvIn_of_stages hd hPM hem hes heinj hnf hth hrv htk hkey hex
  have hsum : ∑ j ∈ range n', (1 + c₇.nmem (U + 4 * n + 3 * n' + j)) ≤ W₀ := by
    rw [m₇, sum_congr rfl fun j hj => by rw [hex j (mem_range.1 hj)]]
    rw [sum_enumG hem hes heinj (fun d => 1 + ex d)]
    exact hT₀
  obtain ⟨c₈, t₈, e₈, ht₈, m₈, hout⟩ := scProgT_execK (P := I) hloopM (e := e) (B := B) (N := B)
    hd (τ := st) (ex := ex) (n := n') (b := U + 4 * n) (A := A) (W₀ := W₀)
    (RECb := U + 42 * n + 5 * Hs.length + 13) (IX0 := U + 42 * n + 5 * Hs.length + 31) (L := 6)
    (ITEMb := U + 42 * n + 5 * Hs.length + 7 * n' + 32)
    (NHb := U + 42 * n + 5 * Hs.length + 8 * n' + 32) (T₀ := W₀) (SGb := U + 3 * n)
    (Hb := U + 42 * n + 5 * Hs.length + 34 * n' + Bz + 3 * W₀ + 47) (Bz := Bz)
    (SVb := U + 42 * n + 5 * Hs.length + 47 * n' + Bz + 3 * W₀ + 47)
    (Zb := U + 42 * n + 5 * Hs.length + 13) c₇ hPM ⟨e 0, hem 0 hne⟩ hT₀ e₇.wb_right
    hLv hI (fun i hi => by rw [m₇, hth i hi]; exact hlab_le _ _)
    (v4936.trans (by clear * -; omega)) (v4937.trans (by clear * -; omega))
    (v4955.trans (by clear * -; omega)) (v4956.trans (by clear * -; omega)) v5200
    (v5201.trans (by clear * -; omega)) v5202 (v5203.trans (by clear * -; omega))
    (v5830.trans (by clear * -; omega)) (fun i hi => by rw [m₇]; exact hsg i hi) hPM.stable hBz
    (by clear * - w; omega) hL
    (by clear * - w hn'n; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by clear * - hn'n; omega) (by clear * - w hn'n; omega) (by clear * - w hn'n; omega)
    (by clear * - w hsum; omega)
  have q₈ := scProgT_frame e₈
  refine ⟨c₈, _, .seq e₇ e₈, ?_, fun a ha => ?_, ?_, fun y hy => ?_, ?_, ?_, ?_, hout⟩
  · clear * - ht₇ ht₈
    omega
  · rw [m₈ a ha, m₇]
  · rw [q₈.1 3109 (by unfold scU; decide), v3109]
  · obtain ⟨g1, -, -, -⟩ := q₈
    unfold s5BFr at hy
    have hy' : scU y = false := by
      unfold scU; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
      omega
    rw [g1 y hy']
    exact f₇ y (by simp only [s5E1w, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by simp only [s5E2w, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by simp only [s5E3w, List.mem_cons, List.not_mem_nil, or_false]; omega)
      (by simp only [s5E4w, List.mem_cons, List.not_mem_nil, or_false]; omega)
  · rw [q₈.2.1, rr₇]
  · rw [q₈.2.2.1, rm₇]
  · rw [q₈.2.2.2, o₇]

/-- **The body of stage 5** for the headline's choices (see the module docstring). -/
theorem s5Body_exec (hloopM : ∀ d, M.head d ≠ M.tail d) {gid : D → ℕ} {ν : V → ℕ}
    {S T Q : Finset V} {x : MCall M} {m n R : ℕ} {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hA : RArr M gid ν S T x m n R g c.nmem) (hTS : TailSorted M gid ν) (hQ : QPar Q ν)
    (hν : Injective ν) (hP : PcOK M S T x.1.piece x.2.1)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {st : Perm D}
    (hCI : CInvS M Q x.1.piece x.2.1 st) (hnt : nTouch M x.1.piece x.2.1 ≤ 6)
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {B : Finset D} (hB : B = pdarts M (core M Q x.1.piece) x.2.1) {n' U : ℕ} {bb : Bool}
    (hn' : n' = B.card) (hne : 0 < n') (hS : S2Arr M gid c.nmem U n n' g B x.2.1 st)
    (r00 : c.nreg 5800 = n) (r01 : c.nreg 5801 = R + 3 + n) (r02 : c.nreg 5802 = R + 3 + 2 * n)
    (r03 : c.nreg 5803 = R + 3 + 4 * n) (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2)
    (r09 : c.nreg 5809 = U + 2 * n) (r10 : c.nreg 5810 = U + 4 * n)
    (r14 : c.nreg 5814 = U + 3 * n) (r70 : c.nreg 5870 = x.2.1.length)
    (r3102 : c.nreg 3102 = x.2.1.length) (r11 : c.nreg 5811 = n')
    (r910 : c.nreg 5910 = s5Kv M x.1.piece x.2.1 bb) (r911 : c.nreg 5911 = s5Av M x.1.piece x.2.1 bb)
    (r912 : c.nreg 5912 = s5Wv M x.1.piece x.2.1 bb) (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + 600 * n + 10 * x.2.1.length + 2 * encB' (s5Wv M x.1.piece x.2.1 bb) +
      20 * s5Wv M x.1.piece x.2.1 bb + s5Kv M x.1.piece x.2.1 bb + s5Av M x.1.piece x.2.1 bb +
      400 ≤ W) :
    ∃ c' t, Exec I W s5Body c c' t ∧
      t ≤ 9500 * n + 40 * x.2.1.length + 5 * Nat.log 2 (2 * s5Wv M x.1.piece x.2.1 bb) +
        mbT n' (encB' (s5Wv M x.1.piece x.2.1 bb)) (s5Wv M x.1.piece x.2.1 bb) + 3500 ∧
      (∀ a < U + 4 * n, c'.nmem a = c.nmem a) ∧
      c'.nreg 3109 = encB' (s5Wv M x.1.piece x.2.1 bb) ∧
      (∀ y, s5BFr y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      ((c'.nreg 4970 = 0 ∧ scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
          (s5Wv M x.1.piece x.2.1 bb)) x.2.1 B st
          (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I, scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb)
          (s5Wv M x.1.piece x.2.1 bb)) x.2.1 B st
          (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) = some (ρ, I) ∧
         ItemRep (fun j => g (c.nmem (U + 2 * n + j))) n' I
           (fun i => c'.nmem (U + 42 * n + 5 * x.2.1.length + 7 * n' + 32 + i)) ∧
         ((c'.nreg 4900 = 0 ∧ PathNH M (fun j => g (c.nmem (U + 2 * n + j))) n'
             (U + 42 * n + 5 * x.2.1.length + 8 * n' + 32) x.2.1 c' ρ) ∨
          (c'.nreg 4900 = 2 ∧ c'.nreg 4902 < n' ∧
            ρ = (SPath.point (M' := M) (g (c.nmem (U + 2 * n + c'.nreg 4902)))
              (M.tail (g (c.nmem (U + 2 * n + c'.nreg 4902))))).toH)))) := by
  have hd : x.2.1.Pairwise Disjoint := hP.disj
  have hPM : PMap M B x.2.1 st := hB ▸ hCI.pmap
  have hBP : B ⊆ x.1.piece := fun y hy => by
    rw [hB] at hy; exact (mem_core.1 (mem_pdarts.1 hy).1).1
  have hcard : x.1.piece.card = n := hA.card.symm
  have hn'n : n' ≤ n := hS.le
  have hT₀ := pcW_total hQdeg hQ5 hP hCI.cinv (hB ▸ card_pos.1 (hn' ▸ hne))
    (s5Kv M x.1.piece x.2.1 bb) (pcChoiceE M Q eG N d₀) (pcChoiceE_ok hesurj d₀ Q x.1.piece x.2.1)
  rw [← hB] at hT₀
  have hT₀' : ∑ d ∈ B, (1 + s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb) d) ≤
      s5Wv M x.1.piece x.2.1 bb := hT₀
  have hnW : n ≤ s5Wv M x.1.piece x.2.1 bb := by
    unfold s5Wv; rw [hcard]; exact Nat.le_add_right _ _
  have hL : (tHs M B x.2.1).length ≤ 6 := (length_tHs_le_nTouch hBP x.2.1).trans hnt
  obtain ⟨c₁, t₁, e₁, ht₁, b58, q₁, mem₁, tk1, tk2, ex1, rr₁, rm₁, o₁⟩ := s5Mid_exec (I := I) c hc
    hA hTS hQ hν hP hCI.1 hQdeg hQ5 he hesurj d₀ hB hn' hne hS r00 r01 r02 r03 r06 r07 r09 r10
    r14 r70 r11 r910 r912 l0 (by clear * - w; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, mem₂, v3109, q₂, rr₂, rm₂, o₂, hout⟩ := s5Fin_exec (I := I) hloopM hd
    hPM (e := fun j => g (c.nmem (U + 2 * n + j)))
    (ex := s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) (n := n) (n' := n')
    (U := U) (A := s5Av M x.1.piece x.2.1 bb) (W₀ := s5Wv M x.1.piece x.2.1 bb)
    (Bz := encB' (s5Wv M x.1.piece x.2.1 bb)) c₁ e₁.wb_right (fun j hj => (hS.ix j hj).2) hS.ixs
    hS.ixm hne hn'n hL hT₀' (encB'_mono (by clear * - hn'n hnW; omega))
    (fun j hj => by rw [mem₁ _ (by clear * - hj; omega)]; exact hS.nf j hj)
    (fun j hj => by rw [mem₁ _ (by clear * - hj; omega)]; exact hS.th j hj)
    (fun j hj => by rw [mem₁ _ (by clear * - hj; omega)]; exact hS.rv j hj)
    (fun j hj => by rw [mem₁ _ (by clear * - hj hn'n; omega)]; exact hS.sg j hj) tk1 tk2 ex1
    ((q₁ 5800 (by decide)).trans r00) ((q₁ 5810 (by decide)).trans r10)
    ((q₁ 5811 (by decide)).trans r11) ((q₁ 5814 (by decide)).trans r14)
    ((q₁ 3102 (by decide)).trans r3102) b58 ((q₁ 5911 (by decide)).trans r911)
    ((q₁ 5912 (by decide)).trans r912) (by clear * - w; omega)
  have hloc : scertD (s5sc M eG N x.2.1 (s5Av M x.1.piece x.2.1 bb) (s5Wv M x.1.piece x.2.1 bb))
      x.2.1 B st (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) =
      scertD (scChoiceE M (sepC M (fun j => g (c.nmem (U + 2 * n + j))) n'
          (encB' (s5Wv M x.1.piece x.2.1 bb))) (fun j => g (c.nmem (U + 2 * n + j))) n' x.2.1
          (s5Av M x.1.piece x.2.1 bb) (s5Wv M x.1.piece x.2.1 bb)) x.2.1 B st
        (s5ex M Q eG N d₀ x.1.piece x.2.1 (s5Kv M x.1.piece x.2.1 bb)) :=
    scertD_gidLoc _ _ _ he hesurj hS.ixm hS.ixs x.2.1 (subset_refl B) st _
  rw [← hloc] at hout
  refine ⟨c₂, _, .seq e₁ e₂, ?_, fun a ha => ?_, v3109, fun y hy => ?_, ?_, ?_, ?_, hout⟩
  · clear * - ht₁ ht₂ hn'n
    omega
  · rw [mem₂ a ha, mem₁ a (by clear * - ha; omega)]
  · rw [q₂ y hy, q₁ y (by unfold s5BFr at hy; clear * - hy; omega)]
  · rw [rr₂, rr₁]
  · rw [rm₂, rm₁]
  · rw [o₂, o₁]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
