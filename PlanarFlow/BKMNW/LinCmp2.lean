module

public import PlanarFlow.BKMNW.LinCmp

/-!
# The child's rotation with the compaction maps

`chRotProg_exec'`: `chRotProg_exec` (`LinCmp.lean`) with two more outputs, used to write the
child's frame: the count `mc = r6306 = cnt CF m`, and for every index `i` of a child dart the
compaction maps `CI[i] = cnt CF i` (at `A + 8 m`, the child index of the parent index `i`) and
`IX[cnt CF i] = i` (at `A + 9 m`, the parent index of the child index). The proof is that of
`chRotProg_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **`chRotProg_exec` with the compaction maps** `CI` and `IX` and the count. -/
theorem chRotProg_exec' {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (σ : Perm D) (B : Finset D) (L : List D) (Bc : Finset D)
    (c : Config) (hc : WordsBounded W c) {m A : ℕ} (r0 : c.nreg 6200 = m)
    (r1 : c.nreg 6201 = A) (hW : A + 11 * m ≤ W) (hm : m + 2 ≤ W)
    {e : ℕ → D} (he : ∀ i < m, ∀ j < m, e i = e j → i = j) (heB : ∀ i < m, e i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < m, e i = x)
    (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B) (hrL : ∀ x ∈ L, M.rev x ∈ L)
    (hBc : Bc ⊆ B \ L.toFinset)
    (hSG : ∀ i < m, c.nmem (A + i) < m ∧ e (c.nmem (A + i)) = σ (e i))
    (hRV : ∀ i < m, c.nmem (A + m + i) < m ∧ e (c.nmem (A + m + i)) = M.rev (e i))
    (hLF : ∀ i < m, c.nmem (A + 2 * m + i) = if e i ∈ L.toFinset then 1 else 0)
    (hCF : ∀ i < m, c.nmem (A + 3 * m + i) = if e i ∈ Bc then 1 else 0) :
    ∃ c' k, Exec P W chRotProg c c' k ∧ k ≤ 104 * m + 100 ∧ c'.nreg 6306 ≤ m ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 9 * m + k) < m ∧ e (c'.nmem (A + 9 * m + k)) ∈ Bc) ∧
      (∀ x ∈ Bc, ∃ k < c'.nreg 6306, e (c'.nmem (A + 9 * m + k)) = x) ∧
      (∀ k < c'.nreg 6306, ∀ k' < c'.nreg 6306,
        e (c'.nmem (A + 9 * m + k)) = e (c'.nmem (A + 9 * m + k')) → k = k') ∧
      (∀ k < c'.nreg 6306, c'.nmem (A + 10 * m + k) < c'.nreg 6306 ∧
        e (c'.nmem (A + 9 * m + c'.nmem (A + 10 * m + k))) =
          childRot M σ B L Bc (e (c'.nmem (A + 9 * m + k)))) ∧
      (∀ a, ¬ (A + 4 * m ≤ a ∧ a < A + 11 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6200 ∨ 6328 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 6306 = cnt (fun j => c.nmem (A + 3 * m + j)) m ∧
      (∀ i < m, e i ∈ Bc → c'.nmem (A + 8 * m + i) = cnt (fun j => c.nmem (A + 3 * m + j)) i ∧
        c'.nmem (A + 9 * m + cnt (fun j => c.nmem (A + 3 * m + j)) i) = i) := by
  obtain ⟨c1, k1, x1, hk1, cn1, mk1, rk1, rr1, rm1, ro1⟩ := crProg_childRot (P := P) M σ B L Bc c hc
    r0 r1 (by omega) hm he heB hBe hσ hrB hrL hBc hSG hRV hLF hCF
  have s0 : c1.nreg 6200 = m := by rw [rk1 _ (by omega), r0]
  have s1 : c1.nreg 6201 = A := by rw [rk1 _ (by omega), r1]
  have hw1 := x1.wb_right
  obtain ⟨c2, k2, x2, hk2, t0, t1, t2, t3, t20, t21, t22, t27, t28, gn2, gm2, gr2, grm2, go2⟩ :=
    chS1_exec (P := P) c1 hw1 s0 s1 (by omega)
  obtain ⟨F, hFd⟩ : ∃ F : ℕ → ℕ, F = fun j => c.nmem (A + 3 * m + j) := ⟨_, rfl⟩
  have hF1 : ∀ i < m, c1.nmem (A + 3 * m + i) = F i := fun i hi => by
    rw [hFd]; exact mk1 _ (fun h => by omega)
  have hFiff : ∀ i < m, 0 < F i ↔ e i ∈ Bc := fun i hi => by
    rw [hFd]; show 0 < c.nmem (A + 3 * m + i) ↔ _
    rw [hCF i hi]; split_ifs with h <;> simp [h]
  obtain ⟨c3, k3, x3, hk3, u6, ul, uk, urk, urr, urm, uro⟩ := lkProg_exec (P := P) c2 x2.wb_right
    t0 t1 t2 t3 (by omega) (by omega) (by omega) (by omega)
  have cntEq : ∀ i ≤ m, cnt (fun j => c2.nmem (A + 3 * m + j)) i = cnt F i := fun i hi => by
    unfold cnt; congr 1
    apply filter_congr; intro j hj; rw [mem_range] at hj
    show 0 < c2.nmem (A + 3 * m + j) ↔ 0 < F j
    rw [gm2, hF1 j (by omega)]
  rw [cntEq m le_rfl] at u6
  have ul' : ∀ i < m, 0 < F i → c3.nmem (A + 8 * m + i) = cnt F i ∧
      c3.nmem (A + 9 * m + cnt F i) = i := fun i hi hFi => by
    have := ul i hi (by rw [gm2, hF1 i hi]; exact hFi)
    rw [cntEq i hi.le] at this; exact this
  have hw3 := x3.wb_right
  have v : ∀ x, (x < 6300 ∨ 6328 < x) → c3.nreg x = c2.nreg x := fun x hx => urk x (by omega)
  obtain ⟨c4, k4, x4, hk4, w0, w1, w2, w3, w4, gn4, gm4, gr4, grm4, go4⟩ :=
    chS2_exec (P := P) c3 hw3 (by rw [urk 6200 (by omega), gn2 6200 (by omega), s0])
      (by rw [urk 6327 (by omega), t27]) (by rw [urk 6320 (by omega), t20])
      (by rw [urk 6328 (by omega), t28]) (by rw [urk 6322 (by omega), t22])
  -- the memory of `c3` on the arrays read by the remap
  have m3F : ∀ i < m, c3.nmem (A + 3 * m + i) = F i := fun i hi => by
    rw [uk _ (fun h => by omega), gm2, hF1 i hi]
  have m3C : ∀ i < m, c3.nmem (A + 6 * m + i) = c1.nmem (A + 6 * m + i) := fun i hi => by
    rw [uk _ (fun h => by omega), gm2]
  have cnB : ∀ i < m, 0 < F i → c1.nmem (A + 6 * m + i) < m ∧
      e (c1.nmem (A + 6 * m + i)) = childRot M σ B L Bc (e i) := fun i hi hFi =>
    cn1 i hi ((hFiff i hi).1 hFi)
  have cnF : ∀ i < m, 0 < F i → 0 < F (c1.nmem (A + 6 * m + i)) := fun i hi hFi => by
    obtain ⟨a1, a2⟩ := cnB i hi hFi
    rw [hFiff _ a1, a2]
    unfold childRot
    exact ret_mem ((hFiff i hi).1 hFi)
  obtain ⟨c5, k5, x5, hk5, o1, o2, o3, o4, o5, o6⟩ := lrProg_exec (P := P) c4 x4.wb_right w0 w1 w2
    w3 w4 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi hs => by
      rw [gm4, m3F i hi] at hs; rw [gm4, m3C i hi]; exact (cnB i hi hs).1)
    (fun i hi hs => by
      rw [gm4, m3F i hi] at hs; rw [gm4, (ul' i hi hs).1]
      have := cnt_le F i; omega)
    (fun i hi j hj hsi hsj h => by
      rw [gm4, m3F i hi] at hsi; rw [gm4, m3F j hj] at hsj
      rw [gm4, (ul' i hi hsi).1, (ul' j hj hsj).1] at h
      exact cnt_inj F hsi hsj h)
  rw [gm4] at o1 o2
  have m5 : ∀ a, ¬ (A + 10 * m ≤ a ∧ a < A + 10 * m + m) → c5.nmem a = c3.nmem a := o2
  have r6 : c5.nreg 6306 = cnt F m := by
    rw [o3 _ (by omega), gn4 _ (by omega), u6]
  have IXv : ∀ i < m, 0 < F i → c5.nmem (A + 9 * m + cnt F i) = i := fun i hi hFi => by
    rw [m5 _ (fun h => by have := cnt_le F i; omega)]; exact (ul' i hi hFi).2
  have hmc : cnt F m ≤ m := cnt_le F m
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq x1 (.seq x2 (.seq x3 (.seq x4 x5))), by omega,
    by rw [r6]; exact hmc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [r6, hFd],
    fun i hi hx => ?_⟩
  · intro k hk
    rw [r6] at hk
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    rw [IXv i hi hFi]
    exact ⟨hi, (hFiff i hi).1 hFi⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := hBe x (mem_sdiff.1 (hBc hx)).1
    have hFi := (hFiff i hi).2 hx
    exact ⟨cnt F i, by rw [r6]; exact cnt_lt_of F hi hFi, by rw [IXv i hi hFi]⟩
  · intro k hk k' hk' h
    rw [r6] at hk hk'
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    obtain ⟨i', hi', hFi', rfl⟩ := cnt_surj F m k' hk'
    rw [IXv i hi hFi, IXv i' hi' hFi'] at h
    rw [he i hi i' hi' h]
  · intro k hk
    rw [r6] at hk ⊢
    obtain ⟨i, hi, hFi, rfl⟩ := cnt_surj F m k hk
    have h1 := o1 i hi (by rw [m3F i hi]; exact hFi)
    rw [(ul' i hi hFi).1, m3C i hi] at h1
    obtain ⟨a1, a2⟩ := cnB i hi hFi
    have hF' := cnF i hi hFi
    rw [(ul' _ a1 hF').1] at h1
    rw [h1, IXv _ a1 hF', IXv i hi hFi, a2]
    exact ⟨cnt_lt_of F a1 hF', rfl⟩
  · intro a ha
    have g1 : ¬ (A + 10 * m ≤ a ∧ a < A + 10 * m + m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have g2 : ¬ (A + 8 * m ≤ a ∧ a < A + 9 * m + m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have g3 : ¬ (A + 4 * m ≤ a ∧ a < A + 8 * m) := by
      rintro ⟨h1, h2⟩; exact ha ⟨by omega, by omega⟩
    have e1 := m5 a g1
    have e2 := uk a g2
    have e3 := mk1 a g3
    rw [e1, e2, gm2, e3]
  · intro x hx
    rw [o3 x (by omega), gn4 x (by omega), urk x (by omega), gn2 x (by omega), rk1 x (by omega)]
  · rw [o4, gr4, urr, gr2, rr1]
  · rw [o5, grm4, urm, grm2, rm1]
  · rw [o6, go4, uro, go2, ro1]
  · have hFi := (hFiff i hi).2 hx
    rw [← hFd]
    refine ⟨?_, IXv i hi hFi⟩
    rw [m5 _ (fun h => by omega)]; exact (ul' i hi hFi).1

end Exec

end BKMNW

end PlanarFlow
