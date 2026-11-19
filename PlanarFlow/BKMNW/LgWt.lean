module

public import PlanarFlow.BKMNW.LocalE

/-!
# The weights of the certificate of a large piece, in closed form (stage 4 of `sepL`, pure part)

The certificate of a piece (`pcertD`) runs `scertD` on the piece map of the core `B` with the
weights `ex d = pcExf K d + lmoved (pcExf K) pcLs d`. Every attached set of `pcLs` is a pair
`{y, rev y}` off `B`, where `pcExf` vanishes; so it carries weight `2`, and

**`lmoved_pcLs`**: `lmoved (pcExf …) (pcLs …) d = 2 · #{E ∈ pcEs | d = ancD (rep E)}`

— a program computes the weights by one scatter-add of `2` at the anchor of every pair (counted
once, at its representative `rep E`) plus `K` at the anchor dart of every touched hole (`pcExf`,
`pcExf_fiF`). Also `pcExf_of_not_mem` and `pcEs_pair`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

lemma pcExf_of_not_mem {pc : PcChoice D V} {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    {K : ℕ} {d : D} (h : d ∉ pdarts M (core M Q P) Hs) : pcExf M pc Q P Hs K d = 0 := by
  classical
  unfold pcExf
  rw [iteF (fun h' => h h'.1)]

lemma pcEs_pair {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {E : Finset D}
    (hE : E ∈ pcEs M Q P Hs) :
    ∃ y ∈ pcNf M Q P Hs \ pdarts M (core M Q P) Hs, E = {y, M.rev y} := by
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hE
  exact ⟨y, hy, rfl⟩

/-- **The weights moved to the anchors**: `2` per attached pair. -/
theorem lmoved_pcLs (pc : PcChoice D V) {Q : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (K : ℕ) (hord : (pc.ord (pcEs M Q P Hs)).Nodup ∧
      (pc.ord (pcEs M Q P Hs)).toFinset = pcEs M Q P Hs)
    (hB : ∀ x ∈ pdarts M (core M Q P) Hs, M.rev x ∈ pdarts M (core M Q P) Hs) (d : D) :
    lmoved (pcExf M pc Q P Hs K) (pcLs M pc Q P Hs) d =
      2 * ((pcEs M Q P Hs).filter fun E => d = pc.ancD P Hs (pc.rep E)).card := by
  classical
  have key : ∀ E ∈ pcEs M Q P Hs, ∑ x ∈ E, (1 + pcExf M pc Q P Hs K x) = 2 := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := pcEs_pair hE
    have hyB : y ∉ pdarts M (core M Q P) Hs := (mem_sdiff.1 hy).2
    have hrB : M.rev y ∉ pdarts M (core M Q P) Hs := fun h => hyB (by
      have := hB _ h; rwa [M.rev_rev] at this)
    rw [sum_pair (M.rev_ne y).symm, pcExf_of_not_mem hyB, pcExf_of_not_mem hrB]
  unfold lmoved pcLs
  rw [List.map_map]
  rw [← List.sum_toFinset _ hord.1, hord.2]
  rw [sum_congr rfl fun E hE => show ((fun e : Finset D × Finset V × D =>
      if d = e.2.2 then ∑ x ∈ e.1, (1 + pcExf M pc Q P Hs K x) else 0) ∘
      (fun E => (E, cls Hs (avQ M Q (pc.rep E)), pc.ancD P Hs (pc.rep E)))) E =
      if d = pc.ancD P Hs (pc.rep E) then 2 else 0 by
    simp only [Function.comp_apply]; rw [key E hE]]
  rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]

end BKMNW

end PlanarFlow
