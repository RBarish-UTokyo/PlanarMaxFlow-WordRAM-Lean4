module

public import PlanarFlow.NegSSSP.LinNode
public import PlanarFlow.NegSSSP.FaceMonge

/-!
# The corner orders of the one-face instances on the machine

At a node of the decomposition by simple cycles the dense distance graph of each part satisfies
the crossing inequality in the order of the shared vertices `B` along the face of a one-face
instance of the part (`PlanarFlow.NegSSSP.crossing_step_parts`, from
`FaceInst.crossingO_childDDG`): sources at increasing positions of the face cycle `g`. Klein's
trip answers the source `b` from its position on the face (`msspK`: the index `i < k` with
`tail (g i) = j b`, unique by `MSSP.FaceCycle.inj`), the source index of the call.

* `cornerProg`: from the vertex numbers of the sources (any order) and the position on the face
  of each source (a table indexed by the vertex numbers), the sources in the order of the face
  and their positions, by a table of the `k` positions of the face cleared, filled and scanned
  (`cornerProg_exec`, `19 k + 10 b + 10` steps).
* `cornerProg_face`: **on a one-face instance**: from an enumeration of `B` by vertex numbers and
  the positions of the sources on the face of the instance, `cornerProg` writes an enumeration
  `β` of `B` (`IsEnum`) by its vertex numbers, at increasing positions of the face cycle, and the
  positions, which are the source indices of Klein's trip; in this order the dense distance graph
  of the part satisfies `Monge.CrossingO` for every implementation of multiple-source shortest
  paths (`cornerProg_crossingO`).

The positions of the sources on the face of the instance are an input: computing them (walking
the separator cycle bounding the side in the subdivided piece map, the face of the instance of
`side_oneFace`) is not done here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Finset

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- Clearing the table: `A[t] := 0` (`r744` the base of the table, `r747` the counter). -/
def czBody : Stmt := block [.addN 748 744 747, .constN 749 0, .storeN 748 749, .addN 747 747 10]

/-- Filling the table: `A[pos[L[i]]] := L[i] + 1` (`r742` the base of `L`, `r743` of `pos`). -/
def cpBody : Stmt :=
  block [.addN 748 742 747, .loadN 749 748, .addN 748 743 749, .loadN 750 748, .addN 748 744 750,
    .addN 749 749 10, .storeN 748 749, .addN 747 747 10]

/-- Emitting the occupied position `t`: `O[n] := A[t] - 1`, `S[n] := t`, `n := n + 1` (`r745`
the base of `O`, `r746` of `S`, `r751` the count). -/
def ccEmit : Stmt :=
  block [.subN 749 749 10, .addN 748 745 751, .storeN 748 749, .addN 748 746 751, .storeN 748 747,
    .addN 751 751 10]

/-- Scanning the table. -/
def ccBody : Stmt :=
  .seq (block [.addN 748 744 747, .loadN 749 748]) <|
    .seq (.ifLtN 749 10 .skip ccEmit) (.instr (.addN 747 747 10))

/-- **The sources in the order of the face** (`r740 = k`, `r741 = b`). -/
def cornerProg : Stmt :=
  .seq (.instr (.constN 747 0)) <| .seq (.whileLtN 747 740 czBody) <|
  .seq (.instr (.constN 747 0)) <| .seq (.whileLtN 747 741 cpBody) <|
  .seq (.instr (.constN 747 0)) <| .seq (.instr (.constN 751 0)) (.whileLtN 747 740 ccBody)

/-- The registers and the source array of `cornerProg`. -/
structure CornerIn (k b Lb Pb Ab Ob Sb : ℕ) (L : ℕ → ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r740 : c.nreg 740 = k
  r741 : c.nreg 741 = b
  r742 : c.nreg 742 = Lb
  r743 : c.nreg 743 = Pb
  r744 : c.nreg 744 = Ab
  r745 : c.nreg 745 = Ob
  r746 : c.nreg 746 = Sb
  src : ∀ i < b, c.nmem (Lb + i) = L i

/-- The layout of `cornerProg`: the source numbers below `w`; the table `[Ab, Ab + k)` apart from
the sources `[Lb, Lb + b)` and the positions `[Pb, Pb + w)`; the outputs `[Ob, Ob + k)`,
`[Sb, Sb + k)` apart from the table and from each other. -/
structure CornerLay (k b w Lb Pb Ab Ob Sb W : ℕ) (L : ℕ → ℕ) : Prop where
  lt : ∀ i < b, L i < w
  aL : Ab + k ≤ Lb ∨ Lb + b ≤ Ab
  aP : Ab + k ≤ Pb ∨ Pb + w ≤ Ab
  oA : Ob + k ≤ Ab ∨ Ab + k ≤ Ob
  oS : Ob + k ≤ Sb ∨ Sb + k ≤ Ob
  sA : Sb + k ≤ Ab ∨ Ab + k ≤ Sb
  wA : Ab + k ≤ W
  wO : Ob + k ≤ W
  wS : Sb + k ≤ W
  wL : Lb + b ≤ W
  wP : Pb + w ≤ W
  ww : w + 1 ≤ W
  wk : k + 1 ≤ W
  wb : b + 1 ≤ W

/-- The frame of `cornerProg`. -/
structure CFr (c c' : Config) : Prop where
  nreg : ∀ r, r < 747 ∨ 751 < r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem CFr.trans {c c' c'' : Config} (h : CFr c c') (h' : CFr c' c'') : CFr c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

/-- One step of the scan of the table: position `t` read, emitted when occupied. -/
theorem ccBody_exec {k Ab Ob Sb t : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e744 : c₁.nreg 744 = Ab) (e745 : c₁.nreg 745 = Ob) (e746 : c₁.nreg 746 = Sb)
    (e10 : c₁.nreg 10 = 1) (ha : c₁.nreg 747 = t) (ht : t < k) (hn : c₁.nreg 751 ≤ t)
    (wA : Ab + k ≤ W) (wO : Ob + k ≤ W) (wS : Sb + k ≤ W) (wk : k + 1 ≤ W) :
    ∃ c' s, Exec P W ccBody c₁ c' s ∧ s ≤ 11 ∧ c'.nreg 747 = t + 1 ∧
      (∀ r, r < 747 ∨ 751 < r → c'.nreg r = c₁.nreg r) ∧ c'.rreg = c₁.rreg ∧
      c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      ((c₁.nmem (Ab + t) = 0 ∧ c'.nreg 751 = c₁.nreg 751 ∧ c'.nmem = c₁.nmem) ∨
        (c₁.nmem (Ab + t) ≠ 0 ∧ c'.nreg 751 = c₁.nreg 751 + 1 ∧
          c'.nmem = upd (upd c₁.nmem (Ob + c₁.nreg 751) (c₁.nmem (Ab + t) - 1))
            (Sb + c₁.nreg 751) t)) := by
  unfold ccBody
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [e744, ha]); omega)
  refine spec_seq ?_
  by_cases hz : c₁.nmem (Ab + t) = 0
  · refine spec_ifLtN_true (by config_simp; simp only [e744, e10, ha, hz]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› 747 747 10 (by config_simp; simp only [e10, ha]; omega))
      fun _ => ?_
    config_simp
    simp only [e10, ha]
    and_intros
    all_goals first | omega | exact Or.inl hz |
      (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
  · refine spec_ifLtN_false (by config_simp; simp only [e744, e10, ha]; omega) ?_
    unfold ccEmit
    exec_block
    all_goals try ((try config_simp); (try simp only [e744, e745, e746, e10, ha]); omega)
    refine spec_instr (Exec.addN ‹_› 747 747 10 (by config_simp; simp only [e10, ha]; omega))
      fun _ => ?_
    config_simp
    simp only [e744, e745, e746, e10, ha]
    and_intros
    all_goals first | omega | exact Or.inr ⟨hz, trivial, trivial⟩ | exact hz |
      (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp

/-- **The sources in the order of their positions, on the machine.** From `b` source numbers
`L i` at `Lb` and their positions `pos[L i] < k` at `Pb + L i`, distinct for distinct sources,
`cornerProg` writes, with `n = r751`, the sources `O[x]` at `Ob + x` and their positions `S[x]`
at `Sb + x` (`x < n`) in increasing order of position, each source once, within
`19 k + 10 b + 10` steps. -/
theorem cornerProg_exec {k b w Lb Pb Ab Ob Sb : ℕ} {L : ℕ → ℕ}
    (hL : CornerLay k b w Lb Pb Ab Ob Sb W L) (c : Config) (hc : WordsBounded W c)
    (hI : CornerIn k b Lb Pb Ab Ob Sb L c) (hpos : ∀ i < b, c.nmem (Pb + L i) < k)
    (hinj : ∀ i < b, ∀ i' < b, c.nmem (Pb + L i) = c.nmem (Pb + L i') → i = i') :
    ∃ c' t, Exec P W cornerProg c c' t ∧ t ≤ 19 * k + 10 * b + 10 ∧
      (∀ x < c'.nreg 751, ∃ i < b, c'.nmem (Ob + x) = L i ∧
        c.nmem (Pb + L i) = c'.nmem (Sb + x)) ∧
      (∀ i < b, ∃ x < c'.nreg 751, c'.nmem (Ob + x) = L i) ∧
      (∀ x x', x < x' → x' < c'.nreg 751 → c'.nmem (Sb + x) < c'.nmem (Sb + x')) ∧
      (∀ x < c'.nreg 751, c'.nmem (Sb + x) < k) ∧
      (∀ a, (a < Ab ∨ Ab + k ≤ a) → (a < Ob ∨ Ob + k ≤ a) → (a < Sb ∨ Sb + k ≤ a) →
        c'.nmem a = c.nmem a) ∧
      CFr c c' := by
  have := hL.wA; have := hL.wO; have := hL.wS; have := hL.wL; have := hL.wP; have := hL.ww
  have := hL.wk; have := hL.wb; have := hL.aL; have := hL.aP; have := hL.oA; have := hL.oS
  have := hL.sA
  unfold cornerProg
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 747 0 (by omega)) fun hw₁ => ?_
  -- clearing the table
  let J : ℕ → Config → Prop := fun i c' =>
    CFr c c' ∧ (∀ a, (a < Ab ∨ Ab + k ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ t < i, c'.nmem (Ab + t) = 0)
  have hJ0 : J 0 { c with nreg := upd c.nreg 747 0 } :=
    ⟨⟨fun r hr => upd_other _ _ _ (by omega), rfl, rfl, rfl⟩, fun _ _ => rfl,
      fun t ht => absurd ht (by omega)⟩
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 747) (bR := 740) (body := czBody) J (K := 4)
    (n := k) _ hw₁ (by config_simp) (by config_simp; exact hI.r740) hJ0
    (fun i c₁ hi hw ha hb ⟨fr, fo, fv⟩ => by
      have g : ∀ r, r < 747 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have e744 := (g 744 (by omega)).trans hI.r744
      have e10 := (g 10 (by omega)).trans hI.r10
      unfold czBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e744, e10, ha]); omega)
      dsimp only [J]
      config_simp
      simp only [e744, e10, ha]
      and_intros
      all_goals try trivial
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
          exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro a h1
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a h1]
      · intro t ht
        simp only [upd_apply]
        by_cases hti : t = i
        · subst hti; simp
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fv t (by omega)])) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨_, fr₂, fo₂, fv₂⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 747 0 (by omega)) fun hw₃ => ?_
  -- filling the table
  let J' : ℕ → Config → Prop := fun i c' =>
    CFr c c' ∧ (∀ a, (a < Ab ∨ Ab + k ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ i' < i, c'.nmem (Ab + c.nmem (Pb + L i')) = L i' + 1) ∧
    (∀ t < k, c'.nmem (Ab + t) ≠ 0 → ∃ i' < i, c.nmem (Pb + L i') = t)
  have hJ0' : J' 0 { c₂ with nreg := upd c₂.nreg 747 0 } :=
    ⟨fr₂.trans ⟨fun r hr => upd_other _ _ _ (by omega), rfl, rfl, rfl⟩, fo₂,
      fun i' hi' => absurd hi' (by omega), fun t ht h => absurd (fv₂ t ht) h⟩
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 747) (bR := 741) (body := cpBody) J' (K := 8)
    (n := b) _ hw₃ (by config_simp) (by config_simp; rw [fr₂.nreg 741 (by omega)]; exact hI.r741)
    hJ0' (fun i c₁ hi hw ha hb ⟨fr, fo, fv, fz⟩ => by
      have g : ∀ r, r < 747 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have e742 := (g 742 (by omega)).trans hI.r742
      have e743 := (g 743 (by omega)).trans hI.r743
      have e744 := (g 744 (by omega)).trans hI.r744
      have e10 := (g 10 (by omega)).trans hI.r10
      have l0 := hL.lt i hi
      have p0 := hpos i hi
      have xL : c₁.nmem (Lb + i) = L i := by rw [fo _ (by omega)]; exact hI.src i hi
      have xP : c₁.nmem (Pb + L i) = c.nmem (Pb + L i) := fo _ (by omega)
      unfold cpBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e742, e743, e744, e10, ha, xL, xP]); omega)
      dsimp only [J']
      config_simp
      simp only [e742, e743, e744, e10, ha, xL, xP]
      and_intros
      all_goals try trivial
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
          exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro a h1
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a h1]
      · intro i' hi'
        simp only [upd_apply]
        by_cases hii : i' = i
        · subst hii; simp
        · have hne : c.nmem (Pb + L i') ≠ c.nmem (Pb + L i) := fun h =>
            hii (hinj i' (by omega) i hi h)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fv i' (by omega)]
      · intro t ht hnz
        simp only [upd_apply] at hnz
        by_cases hti : t = c.nmem (Pb + L i)
        · exact ⟨i, by omega, hti.symm⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hnz
          obtain ⟨i', hi', e⟩ := fz t ht hnz
          exact ⟨i', by omega, e⟩)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨_, fr₄, fo₄, fv₄, fz₄⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₄ 747 0 (by omega)) fun hw₅ => ?_
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₅ 751 0 (by omega)) fun hw₆ => ?_
  -- scanning the table
  let J'' : ℕ → Config → Prop := fun t c' =>
    CFr c c' ∧ (∀ a, (a < Ob ∨ Ob + k ≤ a) → (a < Sb ∨ Sb + k ≤ a) → c'.nmem a = c₄.nmem a) ∧
    c'.nreg 751 ≤ t ∧
    (∀ x < c'.nreg 751, c'.nmem (Sb + x) < t ∧ c₄.nmem (Ab + c'.nmem (Sb + x)) ≠ 0 ∧
      c'.nmem (Ob + x) + 1 = c₄.nmem (Ab + c'.nmem (Sb + x))) ∧
    (∀ x x', x < x' → x' < c'.nreg 751 → c'.nmem (Sb + x) < c'.nmem (Sb + x')) ∧
    (∀ t' < t, c₄.nmem (Ab + t') ≠ 0 → ∃ x < c'.nreg 751, c'.nmem (Sb + x) = t')
  have hJ0'' : J'' 0 { { c₄ with nreg := upd c₄.nreg 747 0 } with
      nreg := upd (upd c₄.nreg 747 0) 751 0 } :=
    ⟨fr₄.trans ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> omega,
      rfl, rfl, rfl⟩, fun _ _ _ => rfl, by simp,
      fun x hx => absurd hx (by config_simp; omega),
      fun x x' _ hx' => absurd hx' (by config_simp; omega),
      fun t' ht' => absurd ht' (by omega)⟩
  refine spec_use (forLoop_exec (P := P) (a := 747) (bR := 740) (body := ccBody) J'' (K := 11)
    (n := k) _ hw₆ (by config_simp)
    (by config_simp; rw [fr₄.nreg 740 (by omega)]; exact hI.r740)
    hJ0'' (fun t c₁ ht hw ha hb ⟨fr, fo, fn, fv, fm, fcov⟩ => by
      have g : ∀ r, r < 747 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have e744 := (g 744 (by omega)).trans hI.r744
      have e745 := (g 745 (by omega)).trans hI.r745
      have e746 := (g 746 (by omega)).trans hI.r746
      have e10 := (g 10 (by omega)).trans hI.r10
      have xA : c₁.nmem (Ab + t) = c₄.nmem (Ab + t) := fo _ (by omega) (by omega)
      obtain ⟨c', s, hex, hs, h747, hreg, hrr, hrm, hout, hcase⟩ :=
        ccBody_exec (P := P) c₁ hw e744 e745 e746 e10 ha ht (by omega) hL.wA hL.wO hL.wS hL.wk
      refine ⟨c', s, hex, hs, h747, by rw [hreg 740 (by omega)]; exact hb, ?_⟩
      have fr' : CFr c c' := fr.trans ⟨hreg, hrr, hrm, hout⟩
      rcases hcase with ⟨hz, h751, hm⟩ | ⟨hz, h751, hm⟩
      · refine ⟨fr', fun a h1 h2 => by rw [hm]; exact fo a h1 h2, by omega, fun x hx => ?_,
          fun x x' hxx hx' => ?_, fun t' ht' hnz => ?_⟩
        · rw [h751] at hx; rw [hm]; obtain ⟨a1, a2, a3⟩ := fv x hx; exact ⟨by omega, a2, a3⟩
        · rw [h751] at hx'; rw [hm]; exact fm x x' hxx hx'
        · rw [h751, hm]
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | h
          · exact fcov t' h hnz
          · subst h; rw [xA] at hz; exact absurd hz hnz
      · set n := c₁.nreg 751 with hn
        have hnk : n < k := by omega
        have hSx : ∀ x < n, c'.nmem (Sb + x) = c₁.nmem (Sb + x) := fun x hx => by
          rw [hm]; simp only [upd_apply]; split_ifs <;> omega
        have hOx : ∀ x < n, c'.nmem (Ob + x) = c₁.nmem (Ob + x) := fun x hx => by
          rw [hm]; simp only [upd_apply]; split_ifs <;> omega
        have hSn : c'.nmem (Sb + n) = t := by
          rw [hm]; simp only [upd_apply]; split_ifs <;> omega
        have hOn : c'.nmem (Ob + n) = c₁.nmem (Ab + t) - 1 := by
          rw [hm]; simp only [upd_apply]; split_ifs <;> omega
        refine ⟨fr', fun a h1 h2 => ?_, by omega, fun x hx => ?_, fun x x' hxx hx' => ?_,
          fun t' ht' hnz => ?_⟩
        · rw [hm]; simp only [upd_apply]
          split_ifs <;> first | omega | exact fo a h1 h2
        · rw [h751] at hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h | h
          · obtain ⟨a1, a2, a3⟩ := fv x h
            rw [hSx x h, hOx x h]; exact ⟨by omega, a2, a3⟩
          · subst h; rw [hSn, hOn, ← xA]; exact ⟨by omega, hz, by omega⟩
        · rw [h751] at hx'
          rcases Nat.lt_succ_iff_lt_or_eq.1 hx' with h | h
          · rw [hSx x (by omega), hSx x' h]; exact fm x x' hxx h
          · subst h; rw [hSx x hxx, hSn]; exact (fv x hxx).1
        · rw [h751]
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | h
          · obtain ⟨x, hx, e⟩ := fcov t' h hnz
            exact ⟨x, by omega, by rw [hSx x hx, e]⟩
          · subst h; exact ⟨n, by omega, hSn⟩)) ?_
  intro c₆ k₆ hk₆ hw₆' ⟨_, fr₆, fo₆, fn₆, fv₆, fm₆, fcov₆⟩
  refine ⟨by omega, fun x hx => ?_, fun i hi => ?_, fm₆, fun x hx => (fv₆ x hx).1,
    fun a h1 h2 h3 => (fo₆ a h2 h3).trans (fo₄ a h1), fr₆⟩
  · obtain ⟨s1, s2, s3⟩ := fv₆ x hx
    obtain ⟨i, hi, e⟩ := fz₄ _ s1 s2
    refine ⟨i, by omega, ?_, e⟩
    have := fv₄ i (by omega)
    rw [e] at this
    omega
  · have hp := hpos i hi
    have h1 := fv₄ i hi
    obtain ⟨x, hx, e⟩ := fcov₆ _ hp (by omega)
    refine ⟨x, hx, ?_⟩
    have := (fv₆ x hx).2.2
    rw [e, h1] at this
    omega

/-! ### On a one-face instance -/

section Face

universe u v w'

variable {D : Type u} {V : Type v} {F : Type w'} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F} {X : Finset D} {B : Finset V} {q k : ℕ}
  {DQ VQ FQ : Type u} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
  [Fintype FQ] [DecidableEq FQ] {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D}
  {e : D → DQ} {j : V → VQ}

/-- **The corner order of a one-face instance on the machine.** For a one-face instance of the
part `X` with sources `B` (face `g` of `k` darts), an enumeration `src` of `B` given by its
vertex numbers `ν (src i)` at `Lb`, and the position on the face of each source at
`Pb + ν (src i)` (`tail (g pos) = j (src i)`), `cornerProg` ends within `19 k + 10 b + 10` steps
with `r751 = b`, an enumeration `β` of `B` by its vertex numbers `ν (β x)` at `Ob + x`, and the
positions of the `β x` on the face at `Sb + x`, increasing: the order of `FaceInst.exists_corners`.
The position of `β x` is its only one on the face: the source index of the call of Klein's trip
from `β x` (`msspK_eq`). -/
theorem cornerProg_face (h : FaceInst N X B q k Q g P' e j) {b : ℕ} {src : ℕ → V}
    (hsrc : IsEnum b src B) {ν : V → ℕ} {w Lb Pb Ab Ob Sb : ℕ}
    (hL : CornerLay k b w Lb Pb Ab Ob Sb W fun i => ν (src i)) (c : Config)
    (hc : WordsBounded W c) (hI : CornerIn k b Lb Pb Ab Ob Sb (fun i => ν (src i)) c)
    (hpos : ∀ i < b, c.nmem (Pb + ν (src i)) < k ∧
      Q.tail (g (c.nmem (Pb + ν (src i)))) = j (src i)) :
    ∃ c' t, ∃ β : ℕ → V, Exec P W cornerProg c c' t ∧ t ≤ 19 * k + 10 * b + 10 ∧
      c'.nreg 751 = b ∧ IsEnum b β B ∧ (∀ x < b, c'.nmem (Ob + x) = ν (β x)) ∧
      (∀ x x', x < x' → x' < b → c'.nmem (Sb + x) < c'.nmem (Sb + x')) ∧
      (∀ x < b, c'.nmem (Sb + x) < k ∧ j (β x) = Q.tail (g (c'.nmem (Sb + x)))) ∧
      (∀ x < b, ∀ i < k, Q.tail (g i) = j (β x) → i = c'.nmem (Sb + x)) ∧
      (∀ a, (a < Ab ∨ Ab + k ≤ a) → (a < Ob ∨ Ob + k ≤ a) → (a < Sb ∨ Sb + k ≤ a) →
        c'.nmem a = c.nmem a) ∧
      CFr c c' := by
  classical
  have hinj : ∀ i < b, ∀ i' < b, c.nmem (Pb + ν (src i)) = c.nmem (Pb + ν (src i')) →
      i = i' := by
    intro i hi i' hi' hp
    have e1 := (hpos i hi).2
    have e2 := (hpos i' hi').2
    rw [hp] at e1
    exact hsrc.inj i hi i' hi' (h.injJ' (Finset.mem_union_right _ (hsrc.mem i hi))
      (Finset.mem_union_right _ (hsrc.mem i' hi')) (e1.symm.trans e2))
  obtain ⟨c', t, hex, ht, ha, hb, hm, hk, hfr, hcf⟩ :=
    cornerProg_exec (P := P) hL c hc hI (fun i hi => (hpos i hi).1) hinj
  choose! ι hι using ha
  set n := c'.nreg 751 with hn
  set β : ℕ → V := fun x => src (ι x) with hβ
  have hβB : ∀ x < n, β x ∈ B := fun x hx => hsrc.mem _ (hι x hx).1
  have hβj : ∀ x < n, j (β x) = Q.tail (g (c'.nmem (Sb + x))) := fun x hx => by
    obtain ⟨h1, -, h3⟩ := hι x hx
    rw [← h3]; exact ((hpos _ h1).2).symm
  have hen : IsEnum n β B := by
    refine ⟨hβB, fun v hv => ?_, fun x hx x' hx' ex => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := hsrc.surj v hv
      obtain ⟨x, hx, ex⟩ := hb i hi
      obtain ⟨h1, h2, -⟩ := hι x hx
      refine ⟨x, hx, ?_⟩
      show src (ι x) = src i
      rw [hinj (ι x) h1 i hi (by rw [← h2, ex])]
    · have e' : Q.tail (g (c'.nmem (Sb + x))) = Q.tail (g (c'.nmem (Sb + x'))) := by
        rw [← hβj x hx, ← hβj x' hx', ex]
      have := h.cycle.inj _ (hk x hx) _ (hk x' hx') e'
      rcases lt_trichotomy x x' with hl | hl | hl
      · exact absurd this (hm x x' hl hx').ne
      · exact hl
      · exact absurd this (hm x' x hl hx).ne'
  have hnb : n = b := hen.card.trans hsrc.card.symm
  refine ⟨c', t, β, hex, ht, hnb, hnb ▸ hen, fun x hx => (hι x (hnb ▸ hx)).2.1,
    fun x x' hxx hx' => hm x x' hxx (hnb ▸ hx'), fun x hx => ⟨hk x (hnb ▸ hx), hβj x (hnb ▸ hx)⟩,
    fun x hx i hi ei => h.cycle.inj _ hi _ (hk x (hnb ▸ hx)) (ei.trans (hβj x (hnb ▸ hx))),
    hfr, hcf⟩

/-- **The dense distance graph of the part satisfies the crossing inequality in the order
written by `cornerProg`** (`FaceInst.crossingO_childDDG`), for every implementation of
multiple-source shortest paths and every potential making the reduced lengths of the part
nonnegative: the order `β₀` (or `β₁`) of `crossing_step_parts`, as an array of vertex numbers. -/
theorem cornerProg_crossingO (h : FaceInst N X B q k Q g P' e j) {b : ℕ} {src : ℕ → V}
    (hsrc : IsEnum b src B) {ν : V → ℕ} {w Lb Pb Ab Ob Sb : ℕ}
    (hL : CornerLay k b w Lb Pb Ab Ob Sb W fun i => ν (src i)) (c : Config)
    (hc : WordsBounded W c) (hI : CornerIn k b Lb Pb Ab Ob Sb (fun i => ν (src i)) c)
    (hpos : ∀ i < b, c.nmem (Pb + ν (src i)) < k ∧
      Q.tail (g (c.nmem (Pb + ν (src i)))) = j (src i)) :
    ∃ c' t, ∃ β : ℕ → V, Exec P W cornerProg c c' t ∧ t ≤ 19 * k + 10 * b + 10 ∧
      c'.nreg 751 = b ∧ IsEnum b β B ∧ (∀ x < b, c'.nmem (Ob + x) = ν (β x)) ∧
      (∀ x < b, c'.nmem (Sb + x) < k ∧ j (β x) = Q.tail (g (c'.nmem (Sb + x)))) ∧
      (∀ {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}, PieceMSSPSpec N mssp →
        ∀ {ℓ : D → ℤ} {δ : V → ℤ}, (∀ d ∈ X, 0 ≤ redLen N ℓ δ d) →
          Monge.CrossingO b (fun i i' => (childDDG N mssp X ℓ δ B).len (β i) (β i'))) ∧
      (∀ a, (a < Ab ∨ Ab + k ≤ a) → (a < Ob ∨ Ob + k ≤ a) → (a < Sb ∨ Sb + k ≤ a) →
        c'.nmem a = c.nmem a) ∧
      CFr c c' := by
  obtain ⟨c', t, β, hex, ht, hb, hen, hO, hm, hS, -, hfr, hcf⟩ :=
    cornerProg_face (P := P) h hsrc hL c hc hI hpos
  exact ⟨c', t, β, hex, ht, hb, hen, hO, hS, fun hmssp _ _ hnn =>
    h.crossingO_childDDG hmssp hnn hm (fun x hx => (hS x hx).1) hen.mem
      (fun x hx => (hS x hx).2), hfr, hcf⟩

end Face

end NegSSSP

end PlanarFlow
