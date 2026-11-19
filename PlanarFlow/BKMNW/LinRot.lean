module

public import PlanarFlow.BKMNW.LinRet

/-!
# The rotation of a child piece map on the machine (`childRot`, linear time)

`PlanarFlow.BKMNW.childRot M σ B L Bc = ret (con ι σ (B \ L)) Bc` (`ι = revPerm M`): contract the
darts `L` of the separator, then keep the darts `Bc` of the child. On the darts `B` of the parent
piece map, enumerated by `e` (indices `i < m`), with the arrays

* `SG[i]` (the index of `σ (e i)`), `RV[i]` (the index of `rev (e i)`),
* `LF[i] = 1` iff `e i ∈ L`, `CF[i] = 1` iff `e i ∈ Bc`,

the program `crProg` computes in linear time the array `CN` with `e (CN[i]) = childRot … (e i)`
for every `e i ∈ Bc`, by seven linear loops: `NX[i] := SG[RV[i]]` (the permutation `σ ι`),
`PR[NX[i]] := i`, the deletion of `L` (`ldProg`: then `NX` represents `ret (σ ι) (B \ L)`),
`CN[i] := NX[RV[i]]` (the contraction `con ι σ (B \ L)`), `PR[CN[i]] := i` on `B \ L`,
`DF[i] := (1 - LF[i]) - CF[i]` (the darts of `B \ L` outside `Bc`), and their deletion.

Layout: the eight arrays of length `m` from `A` on: `SG | RV | LF | CF | NX | PR | CN | DF`.
Registers: `6200 = m`, `6201 = A`; written `6202 … 6250`.

* `stable_symm`, `retRep_init`, `retRep_congr`, `dset_eq_sdiff`, `dset_eq_child`, `con_apply'`.
* **`crProg`**, **`crProg_childRot`**: within `79 m + 70` steps, `CN[i] < m` and
  `e (CN[i]) = childRot M σ B L Bc (e i)` for every `i < m` with `e i ∈ Bc`; memory outside
  `[A + 4 m, A + 8 m)`, registers below `6200` and above `6250`, reals and output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Math

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The inverse of a permutation keeps every finite set the permutation keeps. -/
lemma stable_symm {π : Perm α} {B : Finset α} (h : Stable π B) {x : α} (hx : x ∈ B) :
    π.symm x ∈ B := by
  have hsub : B.image π ⊆ B := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy; exact h z hz
  have heq : B.image π = B :=
    eq_of_subset_of_card_le hsub (by rw [card_image_of_injective _ π.injective])
  rw [← heq] at hx
  obtain ⟨z, hz, hzx⟩ := mem_image.1 hx
  rw [← hzx, Equiv.symm_apply_apply]; exact hz

/-- **The initial representation**: arrays of the successor `G` on the indices of a stable set
`R`, and of its inverse written by a scatter (`PR[NX[i]] = i`), represent `ret G R`. -/
theorem retRep_init {e : ℕ → α} {m : ℕ} {G : Perm α} {R : Finset α} {mem : ℕ → ℕ}
    {NXb PRb : ℕ} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hR : ∀ x ∈ R, ∃ i < m, e i = x) (hG : Stable G R)
    (hnx : ∀ i < m, e i ∈ R → mem (NXb + i) < m ∧ e (mem (NXb + i)) = G (e i))
    (hpr : ∀ i < m, e i ∈ R → mem (PRb + mem (NXb + i)) = i) :
    RetRep e m G R mem NXb PRb := by
  intro i hi hiR
  obtain ⟨a1, a2⟩ := hnx i hi hiR
  have hy := stable_symm hG hiR
  obtain ⟨j, hj, hej⟩ := hR _ hy
  have hjR : e j ∈ R := hej ▸ hy
  obtain ⟨b1, b2⟩ := hnx j hj hjR
  have hNj : mem (NXb + j) = i := he _ b1 i hi (by rw [b2, hej, Equiv.apply_symm_apply])
  have hPi : mem (PRb + i) = j := by rw [← hNj]; exact hpr j hj hjR
  have hGR : ∀ x ∈ R, ret G R x = G x := fun x hx => ret_eq_self_of hx (hG x hx)
  refine ⟨a1, hPi ▸ hj, by rw [a2, hGR _ hiR], ?_⟩
  rw [hPi, Equiv.eq_symm_apply, hGR _ hjR, hej, Equiv.apply_symm_apply]

/-- `RetRep` depends only on the two arrays. -/
lemma retRep_congr {e : ℕ → α} {m : ℕ} {G : Perm α} {R : Finset α} {mem mem' : ℕ → ℕ}
    {NXb PRb : ℕ} (h : RetRep e m G R mem NXb PRb)
    (h1 : ∀ i < m, mem' (NXb + i) = mem (NXb + i))
    (h2 : ∀ i < m, mem' (PRb + i) = mem (PRb + i)) : RetRep e m G R mem' NXb PRb := by
  intro i hi hiR
  rw [h1 i hi, h2 i hi]; exact h i hi hiR

/-- Deleting the flagged darts of `L` leaves `B \ L`. -/
lemma dset_eq_sdiff {e : ℕ → α} {m : ℕ} {B : Finset α} {L : Finset α} {LF : ℕ → ℕ}
    (hBe : ∀ x ∈ B, ∃ i < m, e i = x) (hLF : ∀ i < m, LF i = if e i ∈ L then 1 else 0) :
    dset e LF B m = B \ L := by
  ext d
  simp only [dset, mem_filter, mem_sdiff]
  constructor
  · rintro ⟨hd, hj⟩
    refine ⟨hd, fun hdL => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hBe d hd
    exact hj i hi (by rw [hLF i hi, iteT hdL]; omega) rfl
  · rintro ⟨hd, hdL⟩
    refine ⟨hd, fun j hj hpos h => ?_⟩
    rw [hLF j hj] at hpos
    split_ifs at hpos with hjL
    · exact hdL (h ▸ hjL)
    · omega

/-- Deleting the darts of `B'` outside `Bc` leaves `Bc`. -/
lemma dset_eq_child {e : ℕ → α} {m : ℕ} {B' Bc : Finset α} {DF : ℕ → ℕ}
    (hBe : ∀ x ∈ B', ∃ i < m, e i = x) (hBc : Bc ⊆ B')
    (hDF : ∀ i < m, e i ∈ B' → (0 < DF i ↔ e i ∉ Bc)) : dset e DF B' m = Bc := by
  ext d
  simp only [dset, mem_filter]
  constructor
  · rintro ⟨hd, hj⟩
    by_contra hdc
    obtain ⟨i, hi, rfl⟩ := hBe d hd
    exact hj i hi ((hDF i hi hd).2 hdc) rfl
  · intro hd
    exact ⟨hBc hd, fun j hj hpos h => (hDF j hj (h ▸ hBc hd)).1 hpos (h ▸ hd)⟩

lemma con_apply' (ι σ : Perm α) (B : Finset α) (x : α) :
    con ι σ B x = ret (σ * ι) B (ι x) := by
  simp only [con, Perm.mul_apply]

end Math

/-! ### The program -/

/-- The bases `A + k m` of the eight arrays in `r6201 … r6208`. -/
def crS0 : Stmt := block [.addN 6202 6201 6200, .addN 6203 6202 6200, .addN 6204 6203 6200,
  .addN 6205 6204 6200, .addN 6206 6205 6200, .addN 6207 6206 6200, .addN 6208 6207 6200]

/-- Gather `NX[i] := SG[RV[i]]`. -/
def crS1 : Stmt := block [.copyN 6210 6200, .copyN 6211 6202, .copyN 6212 6201, .copyN 6213 6205]

/-- Scatter `PR[NX[i]] := i` (all `i`: `LF[i] < 2`). -/
def crS2 : Stmt :=
  block [.copyN 6220 6200, .copyN 6221 6205, .copyN 6222 6203, .constN 6223 2, .copyN 6224 6206]

/-- Delete the darts of `L` (flags `LF`) from `NX`, `PR`. -/
def crS3 : Stmt := block [.copyN 6240 6200, .copyN 6241 6203, .copyN 6242 6205, .copyN 6243 6206]

/-- Gather `CN[i] := NX[RV[i]]`. -/
def crS4 : Stmt := block [.copyN 6210 6200, .copyN 6211 6202, .copyN 6212 6205, .copyN 6213 6207]

/-- Scatter `PR[CN[i]] := i` for `LF[i] < 1`. -/
def crS5 : Stmt :=
  block [.copyN 6220 6200, .copyN 6221 6207, .copyN 6222 6203, .constN 6223 1, .copyN 6224 6206]

/-- `DF[i] := (1 - LF[i]) - CF[i]`. -/
def crS6 : Stmt := block [.copyN 6230 6200, .copyN 6231 6203, .copyN 6232 6204, .copyN 6233 6208]

/-- Delete the flagged darts (`DF`) from `CN`, `PR`. -/
def crS7 : Stmt := block [.copyN 6240 6200, .copyN 6241 6208, .copyN 6242 6207, .copyN 6243 6206]

/-- **The rotation of a child piece map** (see the module docstring). -/
def crProg : Stmt :=
  .seq crS0 (.seq crS1 (.seq lgProg (.seq crS2 (.seq lsProg (.seq crS3 (.seq ldProg
    (.seq crS4 (.seq lgProg (.seq crS5 (.seq lsProg (.seq crS6 (.seq lmProg
      (.seq crS7 ldProg)))))))))))))

/-! ### The stages -/

/-- The registers of `crProg` after `crS0`: `m`, `A` and the bases `A + k m`. -/
structure CRegs (c : Config) (m A : ℕ) : Prop where
  r0 : c.nreg 6200 = m
  r1 : c.nreg 6201 = A
  r2 : c.nreg 6202 = A + m
  r3 : c.nreg 6203 = A + 2 * m
  r4 : c.nreg 6204 = A + 3 * m
  r5 : c.nreg 6205 = A + 4 * m
  r6 : c.nreg 6206 = A + 5 * m
  r7 : c.nreg 6207 = A + 6 * m
  r8 : c.nreg 6208 = A + 7 * m

lemma CRegs.keep {c c' : Config} {m A : ℕ} (h : CRegs c m A)
    (hk : ∀ x, (x < 6210 ∨ 6250 < x) → c'.nreg x = c.nreg x) : CRegs c' m A :=
  ⟨by rw [hk _ (by omega), h.r0], by rw [hk _ (by omega), h.r1], by rw [hk _ (by omega), h.r2],
    by rw [hk _ (by omega), h.r3], by rw [hk _ (by omega), h.r4], by rw [hk _ (by omega), h.r5],
    by rw [hk _ (by omega), h.r6], by rw [hk _ (by omega), h.r7], by rw [hk _ (by omega), h.r8]⟩

/-- What a stage keeps: memory outside `[lo, hi)`, registers outside `6210 … 6250`, reals and
output. -/
def CFr (c c' : Config) (lo hi : ℕ) : Prop :=
  (∀ a, ¬ (lo ≤ a ∧ a < hi) → c'.nmem a = c.nmem a) ∧
    (∀ x, (x < 6210 ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output

section Exec

variable {P : Input} {W : ℕ}

theorem crS0_exec (c : Config) (hc : WordsBounded W c) {m A : ℕ} (r0 : c.nreg 6200 = m)
    (r1 : c.nreg 6201 = A) (hW : A + 8 * m ≤ W) :
    ∃ c' k, Exec P W crS0 c c' k ∧ k = 7 ∧ CRegs c' m A ∧
      (∀ x, (x < 6202 ∨ 6208 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold crS0
  exec_block
  all_goals try (config_simp; simp only [r0, r1]; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r0, r1])
  all_goals (try omega)
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

/-- Stage 1: `NX[i] := SG[RV[i]]`. -/
theorem crSt1 (c : Config) (hc : WordsBounded W c) {m A : ℕ} (h : CRegs c m A)
    (hW : A + 8 * m ≤ W) (hm : m + 1 ≤ W) (hRV : ∀ j < m, c.nmem (A + m + j) < m) :
    ∃ c₁ k₁ c' k₂, Exec P W crS1 c c₁ k₁ ∧ Exec P W lgProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 9 * m + 8 ∧
      (∀ j < m, c'.nmem (A + 4 * m + j) = c.nmem (A + c.nmem (A + m + j))) ∧
      CFr c c' (A + 4 * m) (A + 5 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS1 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6210 = m ∧ c₁.nreg 6211 = A + m ∧
      c₁.nreg 6212 = A ∧ c₁.nreg 6213 = A + 4 * m ∧
      (∀ x, (x < 6210 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS1
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r1, h.r2, h.r5])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lgProg_exec (P := P) c₁ e₁.wb_right s0 s1 s2
    s3 (by omega) (by omega) hm (fun j hj => by rw [gm₁]; have := hRV j hj; omega)
    (fun j hj h' => by omega) (fun j hj h' => by rw [gm₁] at h'; have := hRV j hj; omega)
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, fun j hj => by rw [o1 j hj, gm₁], ?_⟩
  refine ⟨fun a ha => by rw [o2 a (fun h' => ha ⟨h'.1, by omega⟩), gm₁], fun x hx => ?_, by rw [o4, gr₁], by rw [o5, grm₁],
    by rw [o6, go₁]⟩
  rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 2: `PR[NX[i]] := i` for all `i` (`LF[i] ≤ 1 < 2`). -/
theorem crSt2 (c : Config) (hc : WordsBounded W c) {m A : ℕ} (h : CRegs c m A)
    (hW : A + 8 * m ≤ W) (hm : m + 2 ≤ W) (hNX : ∀ j < m, c.nmem (A + 4 * m + j) < m)
    (hLF : ∀ j < m, c.nmem (A + 2 * m + j) ≤ 1)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (A + 4 * m + i) = c.nmem (A + 4 * m + j) → i = j) :
    ∃ c₁ k₁ c' k₂, Exec P W crS2 c c₁ k₁ ∧ Exec P W lsProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 11 * m + 9 ∧
      (∀ i < m, c'.nmem (A + 5 * m + c.nmem (A + 4 * m + i)) = i) ∧
      CFr c c' (A + 5 * m) (A + 6 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, s4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS2 c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 6220 = m ∧ c₁.nreg 6221 = A + 4 * m ∧
      c₁.nreg 6222 = A + 2 * m ∧ c₁.nreg 6223 = 2 ∧ c₁.nreg 6224 = A + 5 * m ∧
      (∀ x, (x < 6220 ∨ 6224 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS2
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r3, h.r5, h.r6])
    simp only [upd_apply]; split_ifs <;> omega
  have hsel : ∀ i < m, c₁.nmem (A + 2 * m + i) < 2 := fun i hi => by
    rw [gm₁]; have := hLF i hi; omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lsProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 s3 s4 (by omega) (by omega) (by omega)
    (fun j hj _ => by rw [gm₁]; have := hNX j hj; omega)
    (fun i hi j hj _ _ he => hinj i hi j hj (by rw [gm₁] at he; exact he))
    (fun i hi _ j hj h' => by rw [gm₁] at h'; have := hNX i hi; omega)
    (fun i hi _ j hj h' => by rw [gm₁] at h'; have := hNX i hi; omega)
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, fun i hi => by
    rw [← gm₁]; exact o1 i hi (hsel i hi), ?_⟩
  refine ⟨fun a ha => ?_, fun x hx => ?_, by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  · rw [o2 a (fun i hi _ h' => ha ⟨by omega, by rw [gm₁] at h'; have := hNX i hi; omega⟩), gm₁]
  · rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 3: delete the darts of `L` (flags `LF`) from `NX`, `PR`. -/
theorem crSt3 {α : Type*} [Fintype α] [DecidableEq α] (c : Config) (hc : WordsBounded W c)
    {m A : ℕ} (h : CRegs c m A) (hW : A + 8 * m ≤ W) (hm : m + 2 ≤ W)
    {e : ℕ → α} {G : Perm α} {R : Finset α} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hdel : ∀ j < m, 0 < c.nmem (A + 2 * m + j) → e j ∈ R)
    (hrep : RetRep e m G R c.nmem (A + 4 * m) (A + 5 * m)) :
    ∃ c₁ k₁ c' k₂, Exec P W crS3 c c₁ k₁ ∧ Exec P W ldProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 14 * m + 9 ∧
      RetRep e m G (dset e (fun j => c.nmem (A + 2 * m + j)) R m) c'.nmem (A + 4 * m)
        (A + 5 * m) ∧
      CFr c c' (A + 4 * m) (A + 6 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS3 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6240 = m ∧ c₁.nreg 6241 = A + 2 * m ∧
      c₁.nreg 6242 = A + 4 * m ∧ c₁.nreg 6243 = A + 5 * m ∧
      (∀ x, (x < 6240 ∨ 6243 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS3
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r3, h.r5, h.r6])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := ldProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 s3 (by omega) (by omega) (by omega) (by omega) (fun j hj k hk => by omega)
    (fun j hj k hk => by omega) (fun j hj k hk => by omega) he
    (fun j hj hp => hdel j hj (by rw [gm₁] at hp; exact hp)) (by rw [gm₁]; exact hrep)
  rw [gm₁] at o1
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, o1, ?_⟩
  refine ⟨fun a ha => ?_, fun x hx => ?_, by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  · rw [o2 a (fun h' => ha ⟨h'.1, by omega⟩) (fun h' => ha ⟨by omega, by omega⟩), gm₁]
  · rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 4: `CN[i] := NX[RV[i]]`. -/
theorem crSt4 (c : Config) (hc : WordsBounded W c) {m A : ℕ} (h : CRegs c m A)
    (hW : A + 8 * m ≤ W) (hm : m + 1 ≤ W) (hRV : ∀ j < m, c.nmem (A + m + j) < m) :
    ∃ c₁ k₁ c' k₂, Exec P W crS4 c c₁ k₁ ∧ Exec P W lgProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 9 * m + 8 ∧
      (∀ j < m, c'.nmem (A + 6 * m + j) = c.nmem (A + 4 * m + c.nmem (A + m + j))) ∧
      CFr c c' (A + 6 * m) (A + 7 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS4 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6210 = m ∧ c₁.nreg 6211 = A + m ∧
      c₁.nreg 6212 = A + 4 * m ∧ c₁.nreg 6213 = A + 6 * m ∧
      (∀ x, (x < 6210 ∨ 6213 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS4
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r2, h.r5, h.r7])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lgProg_exec (P := P) c₁ e₁.wb_right s0 s1 s2
    s3 (by omega) (by omega) hm (fun j hj => by rw [gm₁]; have := hRV j hj; omega)
    (fun j hj h' => by omega) (fun j hj h' => by rw [gm₁] at h'; have := hRV j hj; omega)
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, fun j hj => by rw [o1 j hj, gm₁], ?_⟩
  refine ⟨fun a ha => by rw [o2 a (fun h' => ha ⟨h'.1, by omega⟩), gm₁], fun x hx => ?_,
    by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 5: `PR[CN[i]] := i` for the `i` with `LF[i] < 1`. -/
theorem crSt5 (c : Config) (hc : WordsBounded W c) {m A : ℕ} (h : CRegs c m A)
    (hW : A + 8 * m ≤ W) (hm : m + 2 ≤ W)
    (hCN : ∀ j < m, c.nmem (A + 2 * m + j) < 1 → c.nmem (A + 6 * m + j) < m)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (A + 2 * m + i) < 1 → c.nmem (A + 2 * m + j) < 1 →
      c.nmem (A + 6 * m + i) = c.nmem (A + 6 * m + j) → i = j) :
    ∃ c₁ k₁ c' k₂, Exec P W crS5 c c₁ k₁ ∧ Exec P W lsProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 11 * m + 9 ∧
      (∀ i < m, c.nmem (A + 2 * m + i) < 1 →
        c'.nmem (A + 5 * m + c.nmem (A + 6 * m + i)) = i) ∧
      CFr c c' (A + 5 * m) (A + 6 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, s4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS5 c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 6220 = m ∧ c₁.nreg 6221 = A + 6 * m ∧
      c₁.nreg 6222 = A + 2 * m ∧ c₁.nreg 6223 = 1 ∧ c₁.nreg 6224 = A + 5 * m ∧
      (∀ x, (x < 6220 ∨ 6224 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS5
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r3, h.r7, h.r6])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lsProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 s3 s4 (by omega) (by omega) (by omega)
    (fun j hj hs => by rw [gm₁] at hs ⊢; have := hCN j hj hs; omega)
    (fun i hi j hj hsi hsj he => hinj i hi j hj (by rw [gm₁] at hsi; exact hsi)
      (by rw [gm₁] at hsj; exact hsj) (by rw [gm₁] at he; exact he))
    (fun i hi hs j hj h' => by rw [gm₁] at h' hs; have := hCN i hi hs; omega)
    (fun i hi hs j hj h' => by rw [gm₁] at h' hs; have := hCN i hi hs; omega)
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, fun i hi hs => by
    rw [← gm₁]; exact o1 i hi (by rw [gm₁]; exact hs), ?_⟩
  refine ⟨fun a ha => ?_, fun x hx => ?_, by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  · rw [o2 a (fun i hi hs h' => ha ⟨by omega, by
      rw [gm₁] at h' hs; have := hCN i hi hs; omega⟩), gm₁]
  · rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 6: `DF[i] := (1 - LF[i]) - CF[i]`. -/
theorem crSt6 (c : Config) (hc : WordsBounded W c) {m A : ℕ} (h : CRegs c m A)
    (hW : A + 8 * m ≤ W) (hm : m + 1 ≤ W) :
    ∃ c₁ k₁ c' k₂, Exec P W crS6 c c₁ k₁ ∧ Exec P W lmProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 11 * m + 8 ∧
      (∀ j < m, c'.nmem (A + 7 * m + j) =
        1 - c.nmem (A + 2 * m + j) - c.nmem (A + 3 * m + j)) ∧
      CFr c c' (A + 7 * m) (A + 8 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS6 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6230 = m ∧ c₁.nreg 6231 = A + 2 * m ∧
      c₁.nreg 6232 = A + 3 * m ∧ c₁.nreg 6233 = A + 7 * m ∧
      (∀ x, (x < 6230 ∨ 6233 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS6
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r3, h.r4, h.r8])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lmProg_exec (P := P) c₁ e₁.wb_right s0 s1 s2
    s3 (by omega) (by omega) (by omega) hm (fun j hj h' => by omega) (fun j hj h' => by omega)
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, fun j hj => by rw [o1 j hj, gm₁], ?_⟩
  refine ⟨fun a ha => by rw [o2 a (fun h' => ha ⟨h'.1, by omega⟩), gm₁], fun x hx => ?_,
    by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  rw [o3 x (by omega), gn₁ x (by omega)]

/-- Stage 7: delete the flagged darts (`DF`) from `CN`, `PR`. -/
theorem crSt7 {α : Type*} [Fintype α] [DecidableEq α] (c : Config) (hc : WordsBounded W c)
    {m A : ℕ} (h : CRegs c m A) (hW : A + 8 * m ≤ W) (hm : m + 2 ≤ W)
    {e : ℕ → α} {G : Perm α} {R : Finset α} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hdel : ∀ j < m, 0 < c.nmem (A + 7 * m + j) → e j ∈ R)
    (hrep : RetRep e m G R c.nmem (A + 6 * m) (A + 5 * m)) :
    ∃ c₁ k₁ c' k₂, Exec P W crS7 c c₁ k₁ ∧ Exec P W ldProg c₁ c' k₂ ∧ k₁ + k₂ ≤ 14 * m + 9 ∧
      RetRep e m G (dset e (fun j => c.nmem (A + 7 * m + j)) R m) c'.nmem (A + 6 * m)
        (A + 5 * m) ∧
      CFr c c' (A + 5 * m) (A + 7 * m) := by
  obtain ⟨c₁, k₁, e₁, hk₁, s0, s1, s2, s3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W crS7 c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 6240 = m ∧ c₁.nreg 6241 = A + 7 * m ∧
      c₁.nreg 6242 = A + 6 * m ∧ c₁.nreg 6243 = A + 5 * m ∧
      (∀ x, (x < 6240 ∨ 6243 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold crS7
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [h.r0, h.r8, h.r7, h.r6])
    simp only [upd_apply]; split_ifs <;> omega
  obtain ⟨c', k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := ldProg_exec (P := P) c₁ e₁.wb_right s0 s1
    s2 s3 (by omega) (by omega) (by omega) (by omega) (fun j hj k hk => by omega)
    (fun j hj k hk => by omega) (fun j hj k hk => by omega) he
    (fun j hj hp => hdel j hj (by rw [gm₁] at hp; exact hp)) (by rw [gm₁]; exact hrep)
  rw [gm₁] at o1
  refine ⟨c₁, k₁, c', k₂, e₁, e₂, by omega, o1, ?_⟩
  refine ⟨fun a ha => ?_, fun x hx => ?_, by rw [o4, gr₁], by rw [o5, grm₁], by rw [o6, go₁]⟩
  · rw [o2 a (fun h' => ha ⟨by omega, by omega⟩) (fun h' => ha ⟨h'.1, by omega⟩), gm₁]
  · rw [o3 x (by omega), gn₁ x (by omega)]

end Exec

lemma CFr.mem_lt {c c' : Config} {lo hi b : ℕ} (h : CFr c c' lo hi) (hb : b ≤ lo) :
    ∀ a < b, c'.nmem a = c.nmem a := fun a ha => h.1 a (fun h' => by omega)

section Exec

variable {P : Input} {W : ℕ}

/-- **The rotation of a child piece map on the machine** (see the module docstring): within
`79 m + 70` steps, for every index `i < m` of a dart of the child `Bc`, `CN[i] < m` and
`e (CN[i]) = childRot M σ B L Bc (e i)`. Hypotheses: `e` enumerates the darts `B` of the parent
piece map without repetition, `σ` keeps `B`, `B` and `L` are closed under reversal, `Bc ⊆ B \ L`;
`SG`, `RV` hold the indices of `σ` and of the reversal, `LF`, `CF` the flags of `L` and `Bc`. -/
theorem crProg_childRot {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (σ : Perm D) (B : Finset D) (L : List D) (Bc : Finset D)
    (c : Config) (hc : WordsBounded W c) {m A : ℕ} (r0 : c.nreg 6200 = m)
    (r1 : c.nreg 6201 = A) (hW : A + 8 * m ≤ W) (hm : m + 2 ≤ W)
    {e : ℕ → D} (he : ∀ i < m, ∀ j < m, e i = e j → i = j) (heB : ∀ i < m, e i ∈ B)
    (hBe : ∀ x ∈ B, ∃ i < m, e i = x)
    (hσ : Stable σ B) (hrB : ∀ x ∈ B, M.rev x ∈ B) (hrL : ∀ x ∈ L, M.rev x ∈ L)
    (hBc : Bc ⊆ B \ L.toFinset)
    (hSG : ∀ i < m, c.nmem (A + i) < m ∧ e (c.nmem (A + i)) = σ (e i))
    (hRV : ∀ i < m, c.nmem (A + m + i) < m ∧ e (c.nmem (A + m + i)) = M.rev (e i))
    (hLF : ∀ i < m, c.nmem (A + 2 * m + i) = if e i ∈ L.toFinset then 1 else 0)
    (hCF : ∀ i < m, c.nmem (A + 3 * m + i) = if e i ∈ Bc then 1 else 0) :
    ∃ c' k, Exec P W crProg c c' k ∧ k ≤ 79 * m + 70 ∧
      (∀ i < m, e i ∈ Bc → c'.nmem (A + 6 * m + i) < m ∧
        e (c'.nmem (A + 6 * m + i)) = childRot M σ B L Bc (e i)) ∧
      (∀ a, ¬ (A + 4 * m ≤ a ∧ a < A + 8 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6202 ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set G : Perm D := σ * revPerm M with hG
  set B' : Finset D := B \ L.toFinset with hB'
  set Cn : Perm D := con (revPerm M) σ B' with hCn
  have hGs : Stable G B := fun x hx => hσ _ (hrB x hx)
  have hB'r : Stable (revPerm M) B' := fun x hx => by
    rw [mem_sdiff] at hx ⊢
    refine ⟨hrB _ hx.1, fun h => hx.2 ?_⟩
    have := hrL _ (List.mem_toFinset.1 h)
    rw [revPerm_apply, M.rev_rev] at this
    exact List.mem_toFinset.2 this
  have hCs : Stable Cn B' := stable_con (revPerm_isInv M) hB'r
  have hB'e : ∀ x ∈ B', ∃ i < m, e i = x := fun x hx => hBe x (mem_sdiff.1 hx).1
  have hLF1 : ∀ i < m, c.nmem (A + 2 * m + i) ≤ 1 := fun i hi => by
    rw [hLF i hi]; split_ifs <;> omega
  have hLF0 : ∀ i < m, c.nmem (A + 2 * m + i) < 1 ↔ e i ∈ B' := fun i hi => by
    rw [hLF i hi, mem_sdiff]
    constructor
    · intro h; split_ifs at h with hL
      · omega
      · exact ⟨heB i hi, hL⟩
    · rintro ⟨-, hL⟩; rw [iteF hL]; omega
  -- stage 0
  obtain ⟨c0, k0, x0, hk0, R0, gn0, gm0, gr0, grm0, go0⟩ :=
    crS0_exec (P := P) c hc r0 r1 hW
  -- stage 1
  obtain ⟨c1a, k1a, c1, k1b, x1a, x1b, hk1, o1, F1⟩ := crSt1 (P := P) c0 x0.wb_right R0 hW
    (by omega) (fun j hj => by rw [gm0]; exact (hRV j hj).1)
  have R1 : CRegs c1 m A := R0.keep F1.2.1
  have nx1 : ∀ j < m, c1.nmem (A + 4 * m + j) < m ∧
      e (c1.nmem (A + 4 * m + j)) = G (e j) := fun j hj => by
    rw [o1 j hj, gm0]
    obtain ⟨a1, a2⟩ := hRV j hj
    obtain ⟨b1, b2⟩ := hSG _ a1
    refine ⟨b1, ?_⟩
    rw [b2, a2, hG, Perm.mul_apply, revPerm_apply]
  have in1 : ∀ a < A + 4 * m, c1.nmem a = c.nmem a := fun a ha => by
    rw [F1.mem_lt le_rfl a ha, gm0]
  -- stage 2
  obtain ⟨c2a, k2a, c2, k2b, x2a, x2b, hk2, o2, F2⟩ := crSt2 (P := P) c1 x1b.wb_right R1 hW hm
    (fun j hj => (nx1 j hj).1) (fun j hj => by rw [in1 _ (by omega)]; exact hLF1 j hj)
    (fun i hi j hj h => he i hi j hj (G.injective (by
      rw [← (nx1 i hi).2, ← (nx1 j hj).2, h])))
  have R2 : CRegs c2 m A := R1.keep F2.2.1
  have nx2 : ∀ j < m, c2.nmem (A + 4 * m + j) = c1.nmem (A + 4 * m + j) := fun j hj =>
    F2.1 _ (fun h' => by omega)
  have in2 : ∀ a < A + 4 * m, c2.nmem a = c.nmem a := fun a ha => by
    rw [F2.mem_lt (by omega) a ha, in1 a ha]
  have rep2 : RetRep e m G B c2.nmem (A + 4 * m) (A + 5 * m) :=
    retRep_init he hBe hGs (fun i hi _ => by rw [nx2 i hi]; exact nx1 i hi)
      (fun i hi _ => by rw [nx2 i hi]; exact o2 i hi)
  -- stage 3
  obtain ⟨c3a, k3a, c3, k3b, x3a, x3b, hk3, rep3, F3⟩ := crSt3 (P := P) c2 x2b.wb_right R2 hW hm
    he (fun j hj _ => heB j hj) rep2
  have hds : dset e (fun j => c2.nmem (A + 2 * m + j)) B m = B' :=
    dset_eq_sdiff hBe (fun i hi => by rw [in2 _ (by omega)]; exact hLF i hi)
  rw [hds] at rep3
  have R3 : CRegs c3 m A := R2.keep F3.2.1
  have in3 : ∀ a < A + 4 * m, c3.nmem a = c.nmem a := fun a ha => by
    rw [F3.mem_lt le_rfl a ha, in2 a ha]
  -- stage 4
  obtain ⟨c4a, k4a, c4, k4b, x4a, x4b, hk4, o4, F4⟩ := crSt4 (P := P) c3 x3b.wb_right R3 hW
    (by omega) (fun j hj => by rw [in3 _ (by omega)]; exact (hRV j hj).1)
  have R4 : CRegs c4 m A := R3.keep F4.2.1
  have in4 : ∀ a < A + 4 * m, c4.nmem a = c.nmem a := fun a ha => by
    rw [F4.mem_lt (by omega) a ha, in3 a ha]
  have cn4 : ∀ i < m, e i ∈ B' → c4.nmem (A + 6 * m + i) < m ∧
      e (c4.nmem (A + 6 * m + i)) = Cn (e i) := fun i hi hiB => by
    rw [o4 i hi, in3 (A + m + i) (by omega)]
    obtain ⟨a1, a2⟩ := hRV i hi
    have hrv : e (c.nmem (A + m + i)) ∈ B' := by rw [a2]; exact hB'r _ hiB
    obtain ⟨b1, -, b3, -⟩ := rep3 _ a1 hrv
    refine ⟨b1, ?_⟩
    rw [b3, a2, hCn, con_apply', revPerm_apply]
  -- stage 5
  obtain ⟨c5a, k5a, c5, k5b, x5a, x5b, hk5, o5, F5⟩ := crSt5 (P := P) c4 x4b.wb_right R4 hW hm
    (fun j hj hs => (cn4 j hj ((hLF0 j hj).1 (by rw [← in4 _ (by omega)]; exact hs))).1)
    (fun i hi j hj hsi hsj h => by
      have hi' := (hLF0 i hi).1 (by rw [← in4 _ (by omega)]; exact hsi)
      have hj' := (hLF0 j hj).1 (by rw [← in4 _ (by omega)]; exact hsj)
      exact he i hi j hj (Cn.injective (by rw [← (cn4 i hi hi').2, ← (cn4 j hj hj').2, h])))
  have R5 : CRegs c5 m A := R4.keep F5.2.1
  have cn5 : ∀ j < m, c5.nmem (A + 6 * m + j) = c4.nmem (A + 6 * m + j) := fun j hj =>
    F5.1 _ (fun h' => by omega)
  have in5 : ∀ a < A + 4 * m, c5.nmem a = c.nmem a := fun a ha => by
    rw [F5.mem_lt (by omega) a ha, in4 a ha]
  have rep5 : RetRep e m Cn B' c5.nmem (A + 6 * m) (A + 5 * m) :=
    retRep_init he hB'e hCs (fun i hi hiB => by rw [cn5 i hi]; exact cn4 i hi hiB)
      (fun i hi hiB => by
        rw [cn5 i hi]
        exact o5 i hi (by rw [in4 _ (by omega)]; exact (hLF0 i hi).2 hiB))
  -- stage 6
  obtain ⟨c6a, k6a, c6, k6b, x6a, x6b, hk6, o6, F6⟩ := crSt6 (P := P) c5 x5b.wb_right R5 hW
    (by omega)
  have R6 : CRegs c6 m A := R5.keep F6.2.1
  have rep6 : RetRep e m Cn B' c6.nmem (A + 6 * m) (A + 5 * m) :=
    retRep_congr rep5 (fun i hi => F6.1 _ (fun h' => by omega))
      (fun i hi => F6.1 _ (fun h' => by omega))
  have df6 : ∀ j < m, c6.nmem (A + 7 * m + j) =
      1 - c.nmem (A + 2 * m + j) - c.nmem (A + 3 * m + j) := fun j hj => by
    rw [o6 j hj, in5 _ (by omega), in5 _ (by omega)]
  -- stage 7
  obtain ⟨c7a, k7a, c7, k7b, x7a, x7b, hk7, rep7, F7⟩ := crSt7 (P := P) c6 x6b.wb_right R6 hW hm
    he (fun j hj hp => by
      rw [df6 j hj] at hp
      exact (hLF0 j hj).1 (by omega)) rep6
  have hdc : dset e (fun j => c6.nmem (A + 7 * m + j)) B' m = Bc := by
    refine dset_eq_child hB'e hBc (fun i hi hiB => ?_)
    rw [df6 i hi, hCF i hi]
    have h0 := (hLF0 i hi).2 hiB
    constructor
    · intro hp hc'; rw [iteT hc'] at hp; omega
    · intro hc'; rw [iteF hc']; omega
  rw [hdc] at rep7
  refine ⟨c7, _, .seq x0 (.seq x1a (.seq x1b (.seq x2a (.seq x2b (.seq x3a (.seq x3b
    (.seq x4a (.seq x4b (.seq x5a (.seq x5b (.seq x6a (.seq x6b (.seq x7a x7b))))))))))))),
    by omega, fun i hi hic => ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, -, a3, -⟩ := rep7 i hi hic
    exact ⟨a1, by rw [a3]; rfl⟩
  · rw [F7.1 a (fun h' => ha ⟨by omega, by omega⟩), F6.1 a (fun h' => ha ⟨by omega, by omega⟩),
      F5.1 a (fun h' => ha ⟨by omega, by omega⟩), F4.1 a (fun h' => ha ⟨by omega, by omega⟩),
      F3.1 a (fun h' => ha ⟨by omega, by omega⟩), F2.1 a (fun h' => ha ⟨by omega, by omega⟩),
      F1.1 a (fun h' => ha ⟨by omega, by omega⟩), gm0]
  · rw [F7.2.1 x (by omega), F6.2.1 x (by omega), F5.2.1 x (by omega), F4.2.1 x (by omega),
      F3.2.1 x (by omega), F2.2.1 x (by omega), F1.2.1 x (by omega), gn0 x (by omega)]
  · rw [F7.2.2.1, F6.2.2.1, F5.2.2.1, F4.2.2.1, F3.2.2.1, F2.2.2.1, F1.2.2.1, gr0]
  · rw [F7.2.2.2.1, F6.2.2.2.1, F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1, grm0]
  · rw [F7.2.2.2.2, F6.2.2.2.2, F5.2.2.2.2, F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2, go0]

end Exec

end BKMNW

end PlanarFlow
