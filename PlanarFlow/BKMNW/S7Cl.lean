module

public import PlanarFlow.BKMNW.S7Hf
public import PlanarFlow.BKMNW.ClsProg

/-!
# Stage 7 of `sepL` (II): the classes `clsF` on the record

* `clsIdF_lt` (the class numbers are `< 3 (2 n + nk)`), **`clsProg_clsF'`** (`clsProg_clsF`, proof
  copied, with that bound on the output `ID`);
* `clS` (the bases of `clsProg` from `Cb = r7140`: `YT | YH | NF | R2 | TK | Y2 | LS (nk) | OFF |
  ADJ | LAB | Q | ID`, `RV = RP` of the record), **`s7Cl = clS ; zfill LS ; zfill LAB ; cpArr NF ;
  clsProg`**, **`s7Cl_exec`** (`211 n + 6 nk + 80` steps): `ID[i] = ID[j] ↔ e j ∈ clsF … (e i)`
  and `ID[i] < 3 (2 n + nk)` at `IDb = Cb + 13 n + nk + 2`.

Registers `7100 = n`, `7106 = RPb`, `7140 = Cb`, `7141 = nk`, `7142 = NFsrc`, `7143 = K`,
`6521 = 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

lemma clsIdF_lt {K n nk : ℕ} {rv key yt yh nf lab : ℕ → ℕ} {i : ℕ} (h1 : rv i < n)
    (h2 : lab i ≤ n) (h3 : key i < nk) :
    clsIdF K rv key yt yh nf lab i < 3 * (2 * n + nk) := by
  unfold clsIdF
  have : min i (rv i) ≤ rv i := min_le_right _ _
  split_ifs <;> omega

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **`clsProg_clsF` with a bound on the class numbers** (proof copied). -/
theorem clsProg_clsF' {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)}
    {K : ℕ} {ρ : HPath M} {e : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n nk RVb YTb YHb NFb R2b TKb Y2b LSb OFFb ADJb LABb Qb IDb : ℕ}
    (hL : ClsLay n nk RVb YTb YHb NFb R2b TKb Y2b LSb OFFb ADJb LABb Qb IDb W)
    (hE : ClsEnum M Ps Nf Hs (newHole Hs ρ.mverts) n e (fun i => c.nmem (RVb + i))
      (fun i => c.nmem (TKb + i)) (fun i => c.nmem (YTb + i)) (fun i => c.nmem (YHb + i))
      (fun i => c.nmem (NFb + i)))
    (hNf : Nf ⊆ Ps) (hY : HClosed Hs (newHole Hs ρ.mverts)) (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hTK : ∀ i < n, c.nmem (TKb + i) < nk)
    (hLS : ∀ k < nk, c.nmem (LSb + k) = 0) (hLAB : ∀ u < n, c.nmem (LABb + u) = 0)
    (r0 : c.nreg 4440 = n) (r1 : c.nreg 4441 = RVb) (r2 : c.nreg 4442 = YTb)
    (r3 : c.nreg 4443 = YHb) (r4 : c.nreg 4444 = NFb) (r5 : c.nreg 4445 = R2b)
    (r6 : c.nreg 4446 = Y2b) (r7 : c.nreg 4447 = TKb) (r8 : c.nreg 4448 = LABb)
    (r9 : c.nreg 4449 = IDb) (r10 : c.nreg 4450 = K)
    (t0 : c.nreg 4420 = n) (t1 : c.nreg 4421 = R2b) (t2 : c.nreg 4422 = TKb)
    (t3 : c.nreg 4423 = Y2b) (t4 : c.nreg 4424 = LSb) (t5 : c.nreg 4425 = OFFb)
    (t6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W clsProg c c' k ∧ k ≤ 192 * n + 24 ∧
      (∀ i < n, ∀ j < n, (c'.nmem (IDb + i) = c'.nmem (IDb + j) ↔
        e j ∈ clsF M Ps Nf Hs K ρ (e i))) ∧
      (∀ i < n, c'.nmem (IDb + i) < 3 * (2 * n + nk)) ∧
      (∀ a, (a < R2b ∨ (TKb ≤ a ∧ a < TKb + n) ∨ IDb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4451) ∨ 4467 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a1, a2, a3, a4, hcg, hbf, a5, a6, a7⟩ := hL
  have hcg' := hcg
  have hbf' := hbf
  obtain ⟨l1, l2, l3, l4, l5⟩ := hcg'
  obtain ⟨b1, b2, b3, b4⟩ := hbf'
  set m₀ := c.nmem with hm₀
  have hRV : ∀ j < n, m₀ (RVb + j) < n := fun j hj => hE.rvlt j hj
  unfold clsProg
  -- scan 1
  obtain ⟨c₁, k₁, e₁, hk₁, R1, R2, F1, n₁, gr₁, grm₁, go₁⟩ := csScan1_exec (P := P) c hc a1 a2 a3
    a4 (by omega) (by omega) (by omega) hRV r0 r1 r2 r3 r4 r5 r6
  have hw₁ := e₁.wb_right
  -- the input of the components
  have hsub := (hE.sub hNf).congr (rv' := fun i => c₁.nmem (R2b + i))
    (key' := cgKey c₁.nmem TKb) (yf' := cgYf c₁.nmem Y2b) (fun i hi => R1 i hi)
    (fun i hi => F1 _ (by omega) (by omega)) (fun i hi => by
      have := R2 i hi
      unfold cgYf
      cases h : clsYf (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j)) (fun j => m₀ (NFb + j)) i
      · rw [h] at this; simp only [decide_eq_false_iff_not]; intro h'
        exact Bool.false_ne_true (this.1 h')
      · rw [h] at this; simp only [decide_eq_true_eq]; exact this.2 rfl)
  obtain ⟨c₂, k₂, e₂, hk₂, H1, H2, H3, n₂, gr₂, grm₂, go₂⟩ := ccProg_exec (P := P) c₁ hw₁ hcg hbf
    (fun i hi => by rw [F1 _ (by omega) (by omega)]; exact hTK i hi) hsub.rvOK
    (fun k hk => by rw [F1 _ (by omega) (by omega)]; exact hLS k hk)
    (fun u hu => by rw [F1 _ (by omega) (by omega)]; exact hLAB u hu)
    (by rw [n₁ _ (by omega), t0]) (by rw [n₁ _ (by omega), t1]) (by rw [n₁ _ (by omega), t2])
    (by rw [n₁ _ (by omega), t3]) (by rw [n₁ _ (by omega), t4]) (by rw [n₁ _ (by omega), t5])
    (by rw [n₁ _ (by omega), t6]) (by rw [n₁ _ (by omega), s0]) (by rw [n₁ _ (by omega), s1])
    (by rw [n₁ _ (by omega), s2]) (by rw [n₁ _ (by omega), s3]) (by rw [n₁ _ (by omega), s4])
  have hw₂ := e₂.wb_right
  -- reading the inputs after the components
  have fr2 : ∀ a, (a < R2b ∨ (TKb ≤ a ∧ a < TKb + n)) → c₂.nmem a = m₀ a := by
    intro a ha
    rw [H3 a (by omega) (by omega) (by omega), F1 a (by omega) (by omega)]
  -- the labels
  have hlab : ∀ i < n, ∀ j < n, clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) i → clsN (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) j →
      ((fun j => c₂.nmem (LABb + j)) i = (fun j => c₂.nmem (LABb + j)) j ↔
        e j ∈ comp M (Nf \ clsJs (M := M) Ps (newHole Hs ρ.mverts)) Hs (newHole Hs ρ.mverts)
          (e i)) := by
    intro i hi j hj hci _
    rw [H1 i hi j hj, mem_comp_iff_cgAdj_sub hY hsub hi hj ((hE.memN hi).2 hci)]
  -- scan 2
  obtain ⟨c₃, k₃, e₃, hk₃, I1, I2, n₃, gr₃, grm₃, go₃⟩ := csScan2_exec (P := P) (nk := nk) (RVb := RVb) (YTb := YTb) (YHb := YHb)
    (NFb := NFb) (TKb := TKb) (LABb := LABb) (IDb := IDb) (K := K) c₂ hw₂
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a6 a7
    (fun j hj => by rw [fr2 _ (by omega)]; exact hRV j hj)
    (fun j hj => by rw [fr2 _ (by omega)]; exact hTK j hj) (fun j hj => (H2 j hj).2)
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r0]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r1])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r2]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r3])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r4]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r7])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r8]) (by rw [n₂ _ (by omega), n₁ _ (by omega), r9])
    (by rw [n₂ _ (by omega), n₁ _ (by omega), r10])
  have hv : ∀ j < n, c₃.nmem (IDb + j) = clsIdF K (fun j => m₀ (RVb + j))
      (fun j => m₀ (TKb + j)) (fun j => m₀ (YTb + j)) (fun j => m₀ (YHb + j))
      (fun j => m₀ (NFb + j)) (fun j => c₂.nmem (LABb + j)) j := fun j hj => by
    rw [I1 j hj]
    exact csV3_eq (fun a ha => fr2 a (by omega)) (fun j' hj' => fr2 _ (by omega)) a1 a2 a3 hj
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun i hi j hj => ?_,
    fun i hi => ?_, fun a ha => ?_, fun x hx => ?_, by rw [gr₃, gr₂, gr₁],
    by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
  · rw [hv i hi, hv j hj]
    exact clsIdF_iff hE hlab hC hi hj
  · rw [hv i hi]
    exact clsIdF_lt (hE.rvlt i hi) (H2 i hi).2 (hTK i hi)
  · rw [I2 a (by omega)]
    rcases ha with ha | ha | ha
    · exact fr2 a (Or.inl ha)
    · exact fr2 a (Or.inr ha)
    · rw [H3 a (by omega) (by omega) (by omega), F1 a (by omega) (by omega)]
  · rw [n₃ x (by omega), n₂ x (by omega), n₁ x (by omega)]

end Exec

end BKMNW

end PlanarFlow
