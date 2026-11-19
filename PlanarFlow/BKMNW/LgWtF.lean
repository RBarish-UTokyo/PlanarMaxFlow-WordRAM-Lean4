module

public import PlanarFlow.BKMNW.LgWtE

/-!
# The large-piece separator, stage 4: the weights on the machine

* **`lgWt_exec`**: the weights program `lgWt = lgWtA ; lgWtB ; lgWtC` writes, within
  `250 n + 12 kk + 160` steps, `EX[j] = fiO K NF TH j + saF avA 2 n (j + 1)` at `b + 3 n'`
  (`j < n'`), for the record's arrays `RP`, `HP`, `VP` (`n` darts, `kk` holes), the indices `IX`,
  the flags `NF` and the hole labels `TH` of the core's darts (stage 2); memory outside the scratch
  `[Yb, Yb + 11 n + 2 kk + 4)` and `[b + 3n', b + 4n')` kept;
* `TailSorted` (the input convention: darts in increasing `gid` have tails of nondecreasing number
  `ν`), **`lgWt_rec`**: on a record (`RArr`) with the outputs of stage 2, `TailSorted`, `QPar`,
  `ν` injective and the invariant of the piece (`PcOK`, holes off `Q`, pendant `Q`), the weights
  are those of the certificate of the piece:
  `EX[j] = pcExf K (e' j) + lmoved (pcExf K) pcLs (e' j)` for the choices `pcChoiceE M Q eG N d₀`
  of the global enumeration (`gid (eG i) = i`) — the field `ex` of `LvIn`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

attribute [-instance] PlanarFlow.BKMNW.smInnerDec

section Exec

variable {P : Input} {W : ℕ}

/-- **The weights program on the machine** (machine values). -/
theorem lgWt_exec (c : Config) (hc : WordsBounded W c) {n RPb HPb VPb IXb b n' kk K Yb : ℕ}
    (hR : WtR0 c n RPb HPb VPb IXb b n' kk K Yb) (w : Yb + 11 * n + 2 * kk + 4 ≤ W)
    (hn : n + 1 ≤ W) (hn' : n' ≤ n) (hK : K + 2 * n ≤ W) (h2 : 2 ≤ W)
    (l1 : RPb + n ≤ Yb) (l2 : HPb + n ≤ Yb) (l3 : VPb + n ≤ Yb) (l4 : IXb + n' ≤ Yb)
    (l5 : b + 4 * n' ≤ Yb)
    (hrp : ∀ i < n, c.nmem (RPb + i) < n) (hhp : ∀ i < n, c.nmem (HPb + i) ≤ kk)
    (hix : ∀ j < n', c.nmem (IXb + j) < n) (hth : ∀ j < n', c.nmem (b + n' + j) ≤ kk) :
    ∃ c' t, Exec P W lgWt c c' t ∧ t ≤ 250 * n + 12 * kk + 160 ∧
      (∀ j < n', c'.nmem (b + 3 * n' + j) =
        fiO K (fun j => c.nmem (b + j)) (fun j => c.nmem (b + n' + j)) j +
          saF (avA kk (fun j => c.nmem (RPb + j)) (fun j => c.nmem (HPb + j))
            (fun j => c.nmem (VPb + j)) (fun j => c.nmem (IXb + j)) (fun j => c.nmem (b + j))
            (fun i => cfv (c.nmem (VPb + i)) (c.nmem (VPb + c.nmem (RPb + i)))
              (c.nmem (HPb + i)) (c.nmem (HPb + c.nmem (RPb + i)))) n') (fun _ => 2) n (j + 1)) ∧
      (∀ a, ¬ (Yb ≤ a ∧ a < Yb + 11 * n + 2 * kk + 4) → ¬ (b + 3 * n' ≤ a ∧ a < b + 4 * n') →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wtW x → x ≠ 5804 → (x < 5873 ∨ 5889 < x) → x ≠ 5899 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set rp : ℕ → ℕ := fun j => c.nmem (RPb + j) with hrpd
  set hp : ℕ → ℕ := fun j => c.nmem (HPb + j) with hhpd
  set vp : ℕ → ℕ := fun j => c.nmem (VPb + j) with hvpd
  set ix : ℕ → ℕ := fun j => c.nmem (IXb + j) with hixd
  set fl : ℕ → ℕ := fun j => c.nmem (b + j) with hfld
  -- part A
  obtain ⟨c₁, t₁, e₁, ht₁, R1, F1, C1, A1, TW1, M1, N1, rr1, rm1, o1⟩ := lgWtA_exec (P := P) c hc
    hR w (by omega) h2 hn l1 l2 l3 hrp hhp
  have bck : ∀ i < n, ckA kk hp vp i < kk + n + 1 := fun i hi => by
    have := ckv_lt (kk := kk) (hhp i hi) (lt_of_le_of_lt (vkF_le vp i) hi)
    calc ckA kk hp vp i = ckv kk (c.nmem (HPb + i)) (vkF vp i) := rfl
      _ < kk + 1 + n := this
      _ = kk + n + 1 := by omega
  have bak : ∀ i < n, akA kk rp hp vp i < kk + n + 1 := fun i hi => by
    have ha : akI rp vp i < n := by unfold akI; split_ifs; exacts [hrp i hi, hi]
    exact bck _ ha
  have E1 : ∀ a, a < Yb → c₁.nmem a = c.nmem a := fun a ha => M1 a (by omega) (by omega)
  -- part B
  obtain ⟨c₂, t₂, e₂, ht₂, R2, V2, M2, N2, rr2, rm2, o2⟩ := lgWtB_exec (P := P) c₁
    e₁.wb_right R1 (ck := ckA kk hp vp) (ak := akA kk rp hp vp) w hn hn' l1 l2 l4 (by omega)
    (fun i hi => by rw [E1 _ (by omega)]; exact hrp i hi)
    (fun j hj => by rw [E1 _ (by omega)]; exact hix j hj) C1 A1 bck bak
  have E2 : ∀ a, a < Yb → c₂.nmem a = c.nmem a := fun a ha => by rw [M2 a (by omega), E1 a ha]
  have hAV : ∀ i < n, c₂.nmem (Yb + 8 * n + kk + 1 + i) =
      avA kk rp hp vp ix fl (fun i => cfv (vp i) (vp (rp i)) (hp i) (hp (rp i))) n' i := by
    intro i hi
    have er : c₁.nmem (RPb + i) = rp i := E1 _ (by omega)
    have hr : rp i < n := hrp i hi
    have htb : ∀ k, fiF (fun j => c₁.nmem (b + j)) (fun j => ckA kk hp vp (c₁.nmem (IXb + j))) n' k =
        tbA kk hp vp ix fl n' k := fun k =>
      fiF_congrW (fun j hj => E1 _ (by omega)) (fun j hj => by rw [E1 _ (by omega)]) k
    rw [V2 i hi, htb, htb, er, F1 i hi, E1 (HPb + i) (by omega), E1 (HPb + rp i) (by omega)]
    unfold avA selP
    rw [sfM_eq]
    unfold bf
    split_ifs <;> simp
  -- part C
  obtain ⟨c₃, t₃, e₃, ht₃, R3, X3, M3, N3, rr3, rm3, o3⟩ := lgWtC_exec (P := P) c₂
    e₂.wb_right R2 w hn hn' hK l5
    (fun i hi => by
      rw [hAV i hi]
      unfold avA
      split_ifs
      · exact (fiF_leW _ _ _ _)
      · exact Nat.zero_le _)
    (fun j hj => by rw [E2 _ (by omega)]; exact hth j hj)
    (by rw [M2 _ (by omega), TW1])
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, fun j hj => ?_,
    fun a h1 h2 => ?_, fun x hx a1 a2 a3 => ?_, by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1],
    by rw [o3, o2, o1]⟩
  · rw [X3 j hj, fiO_congrW (fl' := fl) (key' := fun j => c.nmem (b + n' + j))
      (fun j' hj' => E2 _ (by omega)) (fun j' hj' => E2 _ (by omega)),
      saF_congr (key' := avA kk rp hp vp ix fl (fun i => cfv (vp i) (vp (rp i)) (hp i) (hp (rp i))) n')
        (val' := fun _ => 2) (fun i hi => hAV i hi) (fun _ _ => rfl)]
  · rw [M3 a (by omega) h2, M2 a (by omega), M1 a (by omega) (by omega)]
  · rw [N3 x hx, N2 x hx, N1 x hx a1 a2 a3]

end Exec

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The input convention for the vertex keys**: darts of increasing `gid` have tails of
nondecreasing number `ν` (the darts are listed vertex by vertex, as in adjacency lists). -/
def TailSorted (gid : D → ℕ) (ν : V → ℕ) : Prop := ∀ a b : D, gid a < gid b → ν (M.tail a) ≤ ν (M.tail b)

section Rec

variable {P : Input} {W : ℕ}

/-- **The weights of the certificate on the machine** (stage 4 of the large-piece separator): on
a record (`RArr`) with the outputs of stage 2 (`IX`, `NF = 1`, `TH`), the weights program writes
`EX[j] = pcExf K (e' j) + lmoved (pcExf K) pcLs (e' j)` at `b + 3 n'`, `e' j = g IX[j]` the
enumeration of the piece map of the core, for the choices `pcChoiceE M Q eG N d₀` of the global
enumeration — within `250 n + 12 kk + 160` steps. -/
theorem lgWt_rec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (c : Config) (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem)
    (hTS : TailSorted M gid ν) (hQ : QPar Q ν) (hν : Injective ν) (hP : PcOK M S T x.1.piece x.2.1)
    (hHQ : Disjoint (hunion x.2.1) Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q))
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {IXb b n' K Yb : ℕ}
    (hR : WtR0 c n (R + 3 + n) (R + 3 + 2 * n) (R + 3 + 4 * n) IXb b n' x.2.1.length K Yb)
    (hn'B : n' = (pdarts M (core M Q x.1.piece) x.2.1).card) (hne : 0 < n')
    (hIX : ∀ j < n', c.nmem (IXb + j) < n ∧
      g (c.nmem (IXb + j)) ∈ pdarts M (core M Q x.1.piece) x.2.1)
    (hIXs : ∀ y ∈ pdarts M (core M Q x.1.piece) x.2.1, ∃ j < n', g (c.nmem (IXb + j)) = y)
    (hIXm : ∀ i j, i < j → j < n' → gid (g (c.nmem (IXb + i))) < gid (g (c.nmem (IXb + j))))
    (hNF : ∀ j < n', c.nmem (b + j) = 1)
    (hTH : ∀ j < n', c.nmem (b + n' + j) = hlab x.2.1 (M.tail (g (c.nmem (IXb + j)))))
    (w : Yb + 11 * n + 2 * x.2.1.length + 4 ≤ W) (hn : n + 1 ≤ W) (hK : K + 2 * n ≤ W)
    (l0 : R + 3 + 6 * n ≤ Yb) (l4 : IXb + n' ≤ Yb) (l5 : b + 4 * n' ≤ Yb) :
    ∃ c' t, Exec P W lgWt c c' t ∧ t ≤ 250 * n + 12 * x.2.1.length + 160 ∧
      (∀ j < n', c'.nmem (b + 3 * n' + j) =
        pcExf M (pcChoiceE M Q eG N d₀) Q x.1.piece x.2.1 K (g (c.nmem (IXb + j))) +
          lmoved (pcExf M (pcChoiceE M Q eG N d₀) Q x.1.piece x.2.1 K)
            (pcLs M (pcChoiceE M Q eG N d₀) Q x.1.piece x.2.1) (g (c.nmem (IXb + j)))) ∧
      (∀ a, ¬ (Yb ≤ a ∧ a < Yb + 11 * n + 2 * x.2.1.length + 4) →
        ¬ (b + 3 * n' ≤ a ∧ a < b + 4 * n') → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wtW x → x ≠ 5804 → (x < 5873 ∨ 5889 < x) → x ≠ 5899 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hd := hP.disj
  have hn' : n' ≤ n := by
    rw [hn'B]
    have h1 : pdarts M (core M Q x.1.piece) x.2.1 ⊆ x.1.piece := fun y hy =>
      (mem_core.1 (mem_pdarts.1 hy).1).1
    rw [hA.card]
    exact card_le_card h1
  obtain ⟨c', t, ex, ht, hEX, hm, hr, rr, rm, oo⟩ := lgWt_exec (P := P) c hc hR w hn hn' hK
    (by omega) (by omega) (by omega) (by omega) l4 l5 (fun i hi => (hA.rp i hi).1)
    (fun i hi => by rw [hA.hp i hi]; exact hlab_le _ _)
    (fun j hj => (hIX j hj).1) (fun j hj => by rw [hTH j hj]; exact hlab_le _ _)
  set e' : ℕ → D := fun j => g (c.nmem (IXb + j)) with he'
  have hW : WtIn M gid ν Q x.1.piece x.2.1 n g (fun j => c.nmem (R + 3 + n + j))
      (fun j => c.nmem (R + 3 + 2 * n + j)) (fun j => c.nmem (R + 3 + 4 * n + j)) n' e'
      (fun j => c.nmem (IXb + j)) :=
    { g_mem := hA.g_mem, g_surj := hA.g_surj, g_mono := hA.g_mono, rpOk := hA.rp,
      hpOk := hA.hp, vpOk := hA.vp
      sorted := fun i j hij hj => by
        show c.nmem (R + 3 + 4 * n + i) ≤ c.nmem (R + 3 + 4 * n + j)
        rw [hA.vp i (by omega), hA.vp j hj]
        exact hTS _ _ (hA.g_mono i j hij hj)
      e_mem := fun j hj => (hIX j hj).2, e_surj := hIXs, e_mono := hIXm
      ixOk := fun j hj => ⟨(hIX j hj).1, rfl⟩ }
  refine ⟨c', t, ex, ht, fun j hj => ?_, hm, hr, rr, rm, oo⟩
  rw [hEX j hj]
  have hcf : ∀ i < n, cfv (c.nmem (R + 3 + 4 * n + i))
      (c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + n + i))) (c.nmem (R + 3 + 2 * n + i))
      (c.nmem (R + 3 + 2 * n + c.nmem (R + 3 + n + i))) =
      bf (g i ∈ pdarts M (core M Q x.1.piece) x.2.1) := by
    intro i hi
    obtain ⟨hj, hgj⟩ := hA.rp i hi
    rw [hA.vp i hi, hA.vp _ hj, hgj, CombMap.tail_rev, hA.hp i hi, hA.hp _ hj, hgj,
      CombMap.tail_rev, cfv_eq]
    unfold bf
    congr 1
    exact propext (mem_pdarts_core_iff hQ hd (hA.g_mem i hi)).symm
  have hcl := wt_closed hW hP hHQ hν hQ hQdeg hQ5 hne he hesurj d₀ K
    (fl := fun j => c.nmem (b + j)) (fun j hj => by rw [hNF j hj]; omega) hcf hj
  rw [← hcl]
  congr 1
  exact fiO_congrW (fun j' hj' => rfl) (fun j' hj' => hTH j' (by omega))

end Rec

end MfDrv

end BKMNW

end PlanarFlow
