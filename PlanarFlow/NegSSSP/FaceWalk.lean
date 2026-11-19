module

public import PlanarFlow.NegSSSP.FacePos
public import PlanarFlow.NegSSSP.CornerProg
public import PlanarFlow.NegSSSP.SepFull

/-!
# The walk of the separator cycle bounding a side, on the machine

`PlanarFlow.NegSSSP.side_faceInst` gives the one-face instance of a side `W` of the stellar
subdivision `kst N K` of a piece map, its face `g` running along a cycle `C'` whose darts are
exactly the darts `δ` of `kst N K` with `Out W δ` (face of `δ` off `W`, face of its reverse in
`W`). Here the positions of the vertices on that face are computed on the machine, from the
plain encoding (`Enc`) of the piece map and a mark per dart of the piece map telling whether its
triangle lies in `W` (as `sepRun` leaves them at `B₀ + 22 m`).

* `faceWalk`: a scan of the darts of the piece map recovers the darts `Out W` of the stellar
  subdivision (the old dart `x`, the spoke `up (φ x)` and the spoke `down x` of the triangle of
  `x`, numbered `3 x`, `3 x + 1`, `3 x + 2` as in `stCode`), counts them and records, per tail
  vertex, the head and the number of the dart; then a walk from one of them follows the cycle,
  writing the position of each vertex (`P`), the number of each dart (`Cy`) and each vertex
  (`Vy`) in the order of the walk (`faceWalk_exec`, on abstract arrays forming a cycle `WCyc`,
  `72 m + 13 k + 18` steps).
* `wArr_st`, `wCyc_of`: the darts out of the scan are the darts `Out W` of the stellar
  subdivision, and they form the cycle `C'` of `exists_disc_faceCycle_out` (`out_iff_cyc`).
* `FaceInst.shift`: a one-face instance stays one with its face cycle started anywhere.
* `faceWalk_faceInst`: **for a side of a cycle cut**: `faceWalk` ends with `k = C.k` darts and a
  one-face instance of the side (as `side_faceInst`) whose face starts at the first dart of the
  walk, the position written for every source being its position on that face: the hypothesis
  `hpos` of `cornerProg_face` (with `ν b = vn (ψ b)`).
* `marks_sides`, `sep_run_cyc`: the separator run `sepRun prog10` with its cycle exposed: the
  marks it leaves at `B₀ + 22 m` give the hypotheses `hz` (`sv = 1` for `Z`, `0` for `Zᶜ`), `hbd`
  and `hBs` of `faceWalk_faceInst` for both sides.

`sepRun_exec` states no frame for the encoding of the piece map at `B₀`, so running `faceWalk`
after `sepRun` on the same configuration needs that encoding kept elsewhere (above the word bound
of `sepRun`, by `Exec.lift`); this composition is not done here.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

universe u v w

/-! ### Rotating a face cycle -/

lemma mod_add_inj {k a i j : ℕ} (hi : i < k) (hj : j < k) (h : (a + i) % k = (a + j) % k) :
    i = j := by
  have := Nat.ModEq.add_left_cancel' a h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

lemma exists_shift_idx {k i₀ i : ℕ} (hi₀ : i₀ < k) (hi : i < k) : ∃ t < k, (i₀ + t) % k = i := by
  by_cases h : i₀ ≤ i
  · exact ⟨i - i₀, by omega, by rw [show i₀ + (i - i₀) = i by omega, Nat.mod_eq_of_lt hi]⟩
  · refine ⟨i + k - i₀, by omega, ?_⟩
    rw [show i₀ + (i + k - i₀) = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

section Shift

variable {DQ VQ FQ : Type*} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
  [Fintype FQ] [DecidableEq FQ] {Q : CombMap DQ VQ FQ}

/-- **A face cycle started at `g i₀`.** -/
theorem faceCycle_shift {k : ℕ} {g : ℕ → DQ} (h : MSSP.FaceCycle Q k g) (i₀ : ℕ) :
    MSSP.FaceCycle Q k (fun t => g ((i₀ + t) % k)) where
  two_le := h.two_le
  face i _ := by
    have := h.two_le
    rw [h.face _ (Nat.mod_lt _ (by omega)), h.face _ (Nat.mod_lt _ (by omega))]
  next i _ := by
    have := h.two_le
    rw [h.next _ (Nat.mod_lt _ (by omega)), Nat.mod_add_mod, Nat.add_mod_mod, add_assoc]
  inj i hi j hj e := by
    have := h.two_le
    exact mod_add_inj hi hj (h.inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) e)

end Shift

section ShiftInst

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
  {DQ VQ FQ : Type u} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
  [Fintype FQ] [DecidableEq FQ] {Q : CombMap DQ VQ FQ}

/-- **A one-face instance with its face started at `g i₀`.** -/
theorem FaceInst.shift {X : Finset D} {B : Finset V} {q k : ℕ} {g : ℕ → DQ} {P' : Finset D}
    {e : D → DQ} {j : V → VQ} (h : FaceInst N X B q k Q g P' e j) {i₀ : ℕ} (hi₀ : i₀ < k) :
    FaceInst N X B q k Q (fun t => g ((i₀ + t) % k)) P' e j :=
  { h with
    cycle := faceCycle_shift h.cycle i₀
    src := fun b hb => by
      obtain ⟨i, hi, hgi⟩ := h.src b hb
      obtain ⟨t, ht, et⟩ := exists_shift_idx hi₀ hi
      exact ⟨t, ht, by rw [et]; exact hgi⟩ }

end ShiftInst

/-! ### The darts `Out` are the darts of the cycle -/

section OutCyc

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] {M : Map X P}

/-- **The darts with their face off `Z` and that of their reverse in `Z` are exactly the darts of
the cycle `C'`**, when the boundary of `Z` is the cycle `C` and `C'` runs along `C` with every
dart `Out Z`. -/
theorem out_iff_cyc {C C' : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d)
    (hmem : ∀ d, C'.Mem d ↔ C.Mem d) (hout : ∀ i < C'.k, Out Z (C'.d i)) (δ : X) :
    Out Z δ ↔ ∃ i < C'.k, C'.d i = δ := by
  constructor
  · intro h
    have hm : C.Mem δ := by
      by_contra hn
      exact h.1 (((hbd δ).2 hn).2 h.2)
    obtain ⟨i, hi, e | e⟩ := (hmem δ).2 hm
    · exact ⟨i, hi, e.symm⟩
    · exact absurd (e ▸ h.2 : M.face (M.α (M.α (C'.d i))) ∈ Z)
        (by rw [M.α_α]; exact (hout i hi).1)
  · rintro ⟨i, hi, rfl⟩
    exact hout i hi

end OutCyc

/-! ### The program -/

variable {P : Input} {W : ℕ}

/-- `if r_a = r_b then t else e`. -/
def ifEqN (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e (.ifLtN b a e t)

theorem ifEqN_eq {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} (h : c.nreg a = c.nreg b)
    (ht : Exec P W t c c' k) : Exec P W (ifEqN a b t e) c c' (k + 2 + 2) :=
  .ifLtN_false (by omega) (.ifLtN_false (by omega) ht)

theorem ifEqN_ne {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} (h : c.nreg a ≠ c.nreg b)
    (he : Exec P W e c c' k) : ∃ k', Exec P W (ifEqN a b t e) c c' k' ∧ k' ≤ k + 3 := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact ⟨_, .ifLtN_true h he, by omega⟩
  · exact ⟨_, .ifLtN_false (by omega) (.ifLtN_true h he), by omega⟩

/-- The setup: `n' = nV + nF` (`r820`), the bases of the tables `H = T₀` (`r821`), `G` (`r822`),
`P` (`r823`), `Cy` (`r824`) of `n'`, `n'`, `n'`, `3 m` words and `Vy` (`r825`), the constant `3`
(`r826`), the slot `x = 0` (`r827`), `3 x = 0` (`r828`), the count (`r829`) and the start
(`r830`). -/
def fwInit : Stmt :=
  block [.addN 820 807 808, .copyN 821 810, .addN 822 821 820, .addN 823 822 820,
    .addN 824 823 820, .constN 826 3, .mulN 825 800 826, .addN 825 824 825,
    .constN 827 0, .constN 828 0, .constN 829 0, .constN 830 0]

/-- Recording a dart `Out`: `H[tl] := hd`, `G[tl] := code`, one more, start at `tl`
(`tl`, `hd`, `code` in `r835`, `r836`, `r837`). -/
def fwRec : Stmt :=
  block [.addN 831 821 835, .storeN 831 836, .addN 831 822 835, .storeN 831 837,
    .addN 829 829 10, .copyN 830 835]

/-- One of the three darts of the triangle of `x`: its neighbour `nb` read in the array at `r_ra`
(`α`, `φ` or `φ⁻¹`), and when the triangle of `nb` is in the side (`z[nb] = sv`), the dart is
recorded with the tail, head and number set by `setB`. -/
def fwPart (ra : ℕ) (setB : List Instr) : Stmt :=
  .seq (block [.addN 831 ra 827, .loadN 833 831, .addN 831 806 833, .loadN 834 831])
    (ifEqN 834 809 (.seq (block setB) fwRec) .skip)

/-- The old dart `x`: tail `vn x`, head `vn (α x)`, number `3 x`. -/
def setO : List Instr :=
  [.addN 831 804 827, .loadN 835 831, .addN 831 804 833, .loadN 836 831, .copyN 837 828]

/-- The spoke `up (φ x)`: tail `vn (φ x)`, head `nV + fn x`, number `3 x + 1`. -/
def setU : List Instr :=
  [.addN 831 804 833, .loadN 835 831, .addN 831 805 827, .loadN 836 831, .addN 836 836 807,
    .addN 837 828 10]

/-- The spoke `down x`: tail `nV + fn x`, head `vn x`, number `3 x + 2`. -/
def setD : List Instr :=
  [.addN 831 805 827, .loadN 835 831, .addN 835 835 807, .addN 831 804 827, .loadN 836 831,
    .addN 837 828 10, .addN 837 837 10]

/-- The three darts of the triangle of `x`. -/
def fwOut : Stmt := .seq (fwPart 801 setO) (.seq (fwPart 802 setU) (fwPart 803 setD))

/-- The slot `x`: when the triangle of `x` is off the side, its three darts. -/
def fwBody : Stmt :=
  .seq (block [.addN 831 806 827, .loadN 832 831])
    (.seq (ifEqN 832 809 .skip fwOut) (block [.addN 828 828 826, .addN 827 827 10]))

/-- One step of the walk at the vertex `v` (`r839`), step `t` (`r838`): `P[v] := t`,
`Cy[t] := G[v]`, `Vy[t] := v`, `v := H[v]`. -/
def fwStep : Stmt :=
  block [.addN 831 823 839, .storeN 831 838, .addN 831 822 839, .loadN 840 831,
    .addN 831 824 838, .storeN 831 840, .addN 831 825 838, .storeN 831 839,
    .addN 831 821 839, .loadN 839 831, .addN 838 838 10]

/-- **The walk of the cycle bounding a side.** Inputs: `r800 = m`, the arrays `α`, `φ`, `φ⁻¹`,
vertex and face numbers of the piece map at `r801`–`r805`, the marks at `r806`, `r807 = nV`,
`r808 = nF`, `r809 = sv` (a triangle is in the side iff its mark is `sv`), `r810 = T₀` the base
of the tables; `r10 = 1`. -/
def faceWalk : Stmt :=
  .seq fwInit <| .seq (.whileLtN 827 800 fwBody) <|
    .seq (block [.constN 838 0, .copyN 839 830]) (.whileLtN 838 829 fwStep)


/-! ### The blocks -/

lemma ite_of_pos {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

lemma ite_of_neg {α : Sort*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-- A frame: the registers outside `[lo, hi]`, the real registers and memory and the output
unchanged. -/
structure SFr (lo hi : ℕ) (c c' : Config) : Prop where
  nreg : ∀ r, r < lo ∨ hi < r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem SFr.trans {lo hi : ℕ} {c c' c'' : Config} (h : SFr lo hi c c') (h' : SFr lo hi c' c'') :
    SFr lo hi c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

theorem SFr.mono {lo hi lo' hi' : ℕ} {c c' : Config} (h : SFr lo hi c c') (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : SFr lo' hi' c c' :=
  ⟨fun r hr => h.nreg r (by omega), h.rreg, h.rmem, h.out⟩

theorem SFr.refl (lo hi : ℕ) (c : Config) : SFr lo hi c c := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setO_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg 804 + c.nreg 827 ≤ W)
    (h2 : c.nreg 804 + c.nreg 833 ≤ W) :
    ∃ c' s, Exec P W (block setO) c c' s ∧ s ≤ 7 ∧
      c'.nreg 835 = c.nmem (c.nreg 804 + c.nreg 827) ∧
      c'.nreg 836 = c.nmem (c.nreg 804 + c.nreg 833) ∧ c'.nreg 837 = c.nreg 828 ∧
      SFr 831 840 c c' ∧ c'.nmem = c.nmem := by
  unfold setO
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  and_intros
  all_goals first | omega | rfl | exact ⟨fun r hr => by
    simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩

theorem setU_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg 804 + c.nreg 833 ≤ W)
    (h2 : c.nreg 805 + c.nreg 827 ≤ W) (h3 : c.nmem (c.nreg 805 + c.nreg 827) + c.nreg 807 ≤ W)
    (h4 : c.nreg 828 + c.nreg 10 ≤ W) :
    ∃ c' s, Exec P W (block setU) c c' s ∧ s ≤ 7 ∧
      c'.nreg 835 = c.nmem (c.nreg 804 + c.nreg 833) ∧
      c'.nreg 836 = c.nmem (c.nreg 805 + c.nreg 827) + c.nreg 807 ∧
      c'.nreg 837 = c.nreg 828 + c.nreg 10 ∧ SFr 831 840 c c' ∧ c'.nmem = c.nmem := by
  unfold setU
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  and_intros
  all_goals first | omega | rfl | exact ⟨fun r hr => by
    simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩

theorem setD_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg 805 + c.nreg 827 ≤ W)
    (h2 : c.nmem (c.nreg 805 + c.nreg 827) + c.nreg 807 ≤ W) (h3 : c.nreg 804 + c.nreg 827 ≤ W)
    (h4 : c.nreg 828 + c.nreg 10 + c.nreg 10 ≤ W) :
    ∃ c' s, Exec P W (block setD) c c' s ∧ s ≤ 7 ∧
      c'.nreg 835 = c.nmem (c.nreg 805 + c.nreg 827) + c.nreg 807 ∧
      c'.nreg 836 = c.nmem (c.nreg 804 + c.nreg 827) ∧
      c'.nreg 837 = c.nreg 828 + c.nreg 10 + c.nreg 10 ∧ SFr 831 840 c c' ∧
      c'.nmem = c.nmem := by
  unfold setD
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  and_intros
  all_goals first | omega | rfl | exact ⟨fun r hr => by
    simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩

theorem fwRec_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg 821 + c.nreg 835 ≤ W)
    (h2 : c.nreg 822 + c.nreg 835 ≤ W) (h3 : c.nreg 829 + c.nreg 10 ≤ W) :
    ∃ c' s, Exec P W fwRec c c' s ∧ s ≤ 6 ∧ c'.nreg 829 = c.nreg 829 + c.nreg 10 ∧
      c'.nreg 830 = c.nreg 835 ∧ SFr 829 840 c c' ∧
      c'.nmem = upd (upd c.nmem (c.nreg 821 + c.nreg 835) (c.nreg 836))
        (c.nreg 822 + c.nreg 835) (c.nreg 837) := by
  unfold fwRec
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  and_intros
  all_goals first | omega | rfl | exact ⟨fun r hr => by
    simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩


/-- **One dart of the triangle of `x`**: recorded iff the triangle of its neighbour `nb` is in the
side. -/
theorem fwPart_exec {ra : ℕ} {setB : List Instr} (c : Config) (hw : WordsBounded W c)
    {nb TL HD CD : ℕ} (h1 : c.nreg ra + c.nreg 827 ≤ W)
    (hnb : c.nmem (c.nreg ra + c.nreg 827) = nb) (h2 : c.nreg 806 + nb ≤ W)
    (hset : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 833 = nb →
      (∀ r, r < 831 → c₂.nreg r = c.nreg r) → c₂.nmem = c.nmem →
      ∃ c₃ s, Exec P W (block setB) c₂ c₃ s ∧ s ≤ 7 ∧ c₃.nreg 835 = TL ∧ c₃.nreg 836 = HD ∧
        c₃.nreg 837 = CD ∧ SFr 831 840 c₂ c₃ ∧ c₃.nmem = c₂.nmem)
    (h3 : c.nreg 821 + TL ≤ W) (h4 : c.nreg 822 + TL ≤ W) (h5 : c.nreg 829 + 1 ≤ W)
    (h10 : c.nreg 10 = 1) :
    ∃ c' s, Exec P W (fwPart ra setB) c c' s ∧ s ≤ 21 ∧ SFr 829 840 c c' ∧
      c'.nreg 829 = (if c.nmem (c.nreg 806 + nb) = c.nreg 809 then c.nreg 829 + 1
        else c.nreg 829) ∧
      c'.nreg 830 = (if c.nmem (c.nreg 806 + nb) = c.nreg 809 then TL else c.nreg 830) ∧
      c'.nmem = (if c.nmem (c.nreg 806 + nb) = c.nreg 809 then
        upd (upd c.nmem (c.nreg 821 + TL) HD) (c.nreg 822 + TL) CD else c.nmem) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q833, q834, qfr, qm⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 831 ra 827, .loadN 833 831, .addN 831 806 833, .loadN 834 831]) c c₁ k₁ ∧
      k₁ ≤ 4 ∧ c₁.nreg 833 = nb ∧ c₁.nreg 834 = c.nmem (c.nreg 806 + nb) ∧
      SFr 831 840 c c₁ ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try ((try config_simp); (try simp only [hnb]); omega)
    config_simp
    simp only [hnb]
    and_intros
    all_goals first | omega | rfl | trivial | exact ⟨fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  have hw₁ := e₁.wb_right
  have g : ∀ r, r < 831 → c₁.nreg r = c.nreg r := fun r hr => qfr.nreg r (by omega)
  by_cases hz : c.nmem (c.nreg 806 + nb) = c.nreg 809
  · obtain ⟨c₃, k₃, e₃, hk₃, t835, t836, t837, tfr, tm⟩ := hset c₁ hw₁ q833 g qm
    have u : ∀ r, r < 831 → c₃.nreg r = c.nreg r := fun r hr =>
      (tfr.nreg r (by omega)).trans (g r hr)
    obtain ⟨c₄, k₄, e₄, hk₄, v829, v830, vfr, vm⟩ := fwRec_exec (P := P) c₃ e₃.wb_right
      (by rw [u 821 (by omega), t835]; exact h3) (by rw [u 822 (by omega), t835]; exact h4)
      (by rw [u 829 (by omega), u 10 (by omega)]; omega)
    refine ⟨c₄, _, .seq e₁ (ifEqN_eq (by rw [q834, g 809 (by omega)]; exact hz)
      (.seq e₃ e₄)), by omega, (qfr.mono (lo' := 829) (by omega) le_rfl).trans
        ((tfr.mono (lo' := 829) (by omega) le_rfl).trans vfr), ?_, ?_, ?_⟩
    · rw [ite_of_pos hz, v829, u 829 (by omega), u 10 (by omega), h10]
    · rw [ite_of_pos hz, v830, t835]
    · rw [ite_of_pos hz, vm, tm, qm, u 821 (by omega), u 822 (by omega), t835, t836, t837]
  · obtain ⟨k₂, e₂, hk₂⟩ := ifEqN_ne (a := 834) (b := 809) (t := .seq (block setB) fwRec)
      (by rw [q834, g 809 (by omega)]; exact hz) (Exec.skip hw₁ (P := P))
    refine ⟨c₁, _, .seq e₁ e₂, by omega, qfr.mono (by omega) le_rfl, ?_, ?_, ?_⟩
    · rw [ite_of_neg hz, qfr.nreg 829 (by omega)]
    · rw [ite_of_neg hz, qfr.nreg 830 (by omega)]
    · rw [ite_of_neg hz, qm]


/-! ### The scan, on abstract arrays -/

/-- The arrays read by `faceWalk`: the mark `z` of each dart of the piece map, its reverse `a`,
`p = φ`, `q = φ⁻¹`, its vertex number `vn` and face number `fn`; `sv` the mark of the side, `nV`
the number of vertices. -/
structure WArr where
  sv : ℕ
  nV : ℕ
  z : ℕ → ℕ
  a : ℕ → ℕ
  p : ℕ → ℕ
  q : ℕ → ℕ
  vn : ℕ → ℕ
  fn : ℕ → ℕ

namespace WArr

variable (A : WArr)

/-- The dart `t` of the triangle of `x` (`0`: old dart, `1`: `up (φ x)`, `2`: `down x`) is out:
the triangle of `x` off the side, that across the dart in it. -/
def out (x : ℕ) : ℕ → Prop
  | 0 => A.z x ≠ A.sv ∧ A.z (A.a x) = A.sv
  | 1 => A.z x ≠ A.sv ∧ A.z (A.p x) = A.sv
  | _ => A.z x ≠ A.sv ∧ A.z (A.q x) = A.sv

instance (x t : ℕ) : Decidable (A.out x t) := by
  unfold out; split <;> infer_instance

/-- Its tail. -/
def tl (x : ℕ) : ℕ → ℕ
  | 0 => A.vn x
  | 1 => A.vn (A.p x)
  | _ => A.nV + A.fn x

/-- Its head. -/
def hd (x : ℕ) : ℕ → ℕ
  | 0 => A.vn (A.a x)
  | 1 => A.nV + A.fn x
  | _ => A.vn x

/-- The record of the dart `t` of `x` in the tables `H` at `rH`, `G` at `rG`. -/
def u (rH rG x t : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  if A.out x t then upd (upd mem (rH + A.tl x t) (A.hd x t)) (rG + A.tl x t) (3 * x + t)
  else mem

/-- The records of the three darts of `x`. -/
def wu (rH rG x : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ := A.u rH rG x 2 (A.u rH rG x 1 (A.u rH rG x 0 mem))

/-- The number of darts out among the three of `x`. -/
def nO (x : ℕ) : ℕ :=
  (if A.out x 0 then 1 else 0) + (if A.out x 1 then 1 else 0) + (if A.out x 2 then 1 else 0)

/-- The start after `x`. -/
def st (x s : ℕ) : ℕ :=
  if A.out x 2 then A.tl x 2 else if A.out x 1 then A.tl x 1 else if A.out x 0 then A.tl x 0
  else s

lemma not_out_of {x : ℕ} (h : A.z x = A.sv) (t : ℕ) : ¬ A.out x t := by
  unfold out; split <;> exact fun h' => h'.1 h

lemma u_low {rH rG x t : ℕ} {mem : ℕ → ℕ} {a : ℕ} (h1 : a < rH) (h2 : a < rG) :
    A.u rH rG x t mem a = mem a := by
  unfold u; split_ifs
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · rfl

lemma wu_low {rH rG x : ℕ} {mem : ℕ → ℕ} {a : ℕ} (h1 : a < rH) (h2 : a < rG) :
    A.wu rH rG x mem a = mem a := by
  unfold wu; rw [A.u_low h1 h2, A.u_low h1 h2, A.u_low h1 h2]

end WArr

/-- The layout of `faceWalk`: the arrays of the inputs below `T₀`, their values in range, the
tables `[T₀, T₀ + 3 (nV + nF) + 6 m)` below the word bound. -/
structure WLay (A : WArr) (m bα bφ bφi bvn bfn bz nF T₀ W : ℕ) : Prop where
  a_lt : ∀ x < m, A.a x < m
  p_lt : ∀ x < m, A.p x < m
  q_lt : ∀ x < m, A.q x < m
  vn_lt : ∀ x < m, A.vn x < A.nV
  fn_lt : ∀ x < m, A.fn x < nF
  bα : bα + m ≤ T₀
  bφ : bφ + m ≤ T₀
  bφi : bφi + m ≤ T₀
  bvn : bvn + m ≤ T₀
  bfn : bfn + m ≤ T₀
  bz : bz + m ≤ T₀
  wT : T₀ + 3 * (A.nV + nF) + 6 * m + 3 ≤ W

/-- The input registers and arrays of `faceWalk`. -/
structure WCtx (A : WArr) (m bα bφ bφi bvn bfn bz nF T₀ : ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r800 : c.nreg 800 = m
  r801 : c.nreg 801 = bα
  r802 : c.nreg 802 = bφ
  r803 : c.nreg 803 = bφi
  r804 : c.nreg 804 = bvn
  r805 : c.nreg 805 = bfn
  r806 : c.nreg 806 = bz
  r807 : c.nreg 807 = A.nV
  r808 : c.nreg 808 = nF
  r809 : c.nreg 809 = A.sv
  r810 : c.nreg 810 = T₀
  mz : ∀ x < m, c.nmem (bz + x) = A.z x
  ma : ∀ x < m, c.nmem (bα + x) = A.a x
  mp : ∀ x < m, c.nmem (bφ + x) = A.p x
  mq : ∀ x < m, c.nmem (bφi + x) = A.q x
  mvn : ∀ x < m, c.nmem (bvn + x) = A.vn x
  mfn : ∀ x < m, c.nmem (bfn + x) = A.fn x

/-- The registers set by `fwInit`. -/
structure WIni (A : WArr) (m nF T₀ : ℕ) (c : Config) : Prop where
  r820 : c.nreg 820 = A.nV + nF
  r821 : c.nreg 821 = T₀
  r822 : c.nreg 822 = T₀ + (A.nV + nF)
  r823 : c.nreg 823 = T₀ + 2 * (A.nV + nF)
  r824 : c.nreg 824 = T₀ + 3 * (A.nV + nF)
  r825 : c.nreg 825 = T₀ + 3 * (A.nV + nF) + 3 * m
  r826 : c.nreg 826 = 3

section Ctx

variable {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}

theorem WCtx.of {c c' : Config} (h : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c)
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (hr : ∀ r, r < 820 → c'.nreg r = c.nreg r)
    (hm : ∀ a < T₀, c'.nmem a = c.nmem a) : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c' := by
  have := hL.bα; have := hL.bφ; have := hL.bφi; have := hL.bvn; have := hL.bfn; have := hL.bz
  exact ⟨by rw [hr 10 (by omega)]; exact h.r10, by rw [hr 800 (by omega)]; exact h.r800,
    by rw [hr 801 (by omega)]; exact h.r801, by rw [hr 802 (by omega)]; exact h.r802,
    by rw [hr 803 (by omega)]; exact h.r803, by rw [hr 804 (by omega)]; exact h.r804,
    by rw [hr 805 (by omega)]; exact h.r805, by rw [hr 806 (by omega)]; exact h.r806,
    by rw [hr 807 (by omega)]; exact h.r807, by rw [hr 808 (by omega)]; exact h.r808,
    by rw [hr 809 (by omega)]; exact h.r809, by rw [hr 810 (by omega)]; exact h.r810,
    fun x hx => by rw [hm _ (by omega)]; exact h.mz x hx,
    fun x hx => by rw [hm _ (by omega)]; exact h.ma x hx,
    fun x hx => by rw [hm _ (by omega)]; exact h.mp x hx,
    fun x hx => by rw [hm _ (by omega)]; exact h.mq x hx,
    fun x hx => by rw [hm _ (by omega)]; exact h.mvn x hx,
    fun x hx => by rw [hm _ (by omega)]; exact h.mfn x hx⟩

theorem WIni.of {c c' : Config} (h : WIni A m nF T₀ c)
    (hr : ∀ r, 820 ≤ r → r ≤ 826 → c'.nreg r = c.nreg r) : WIni A m nF T₀ c' :=
  ⟨by rw [hr 820 le_rfl (by omega)]; exact h.r820, by rw [hr 821 (by omega) (by omega)]; exact h.r821,
    by rw [hr 822 (by omega) (by omega)]; exact h.r822,
    by rw [hr 823 (by omega) (by omega)]; exact h.r823,
    by rw [hr 824 (by omega) (by omega)]; exact h.r824,
    by rw [hr 825 (by omega) (by omega)]; exact h.r825,
    by rw [hr 826 (by omega) le_rfl]; exact h.r826⟩

end Ctx


theorem fwPartO_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c) {i : ℕ} (hi : i < m)
    (h827 : c.nreg 827 = i) (h828 : c.nreg 828 = 3 * i) (h829 : c.nreg 829 ≤ 3 * i + 2)
    (hz : A.z i ≠ A.sv) :
    ∃ c' s, Exec P W (fwPart 801 setO) c c' s ∧ s ≤ 21 ∧ SFr 829 840 c c' ∧
      c'.nreg 829 = (if A.out i 0 then c.nreg 829 + 1 else c.nreg 829) ∧
      c'.nreg 830 = (if A.out i 0 then A.tl i 0 else c.nreg 830) ∧
      c'.nmem = A.u T₀ (T₀ + (A.nV + nF)) i 0 c.nmem := by
  have := hL.bα; have := hL.bφ; have := hL.bφi; have := hL.bvn; have := hL.bfn; have := hL.bz
  have := hL.wT; have := hL.a_lt i hi; have := hL.p_lt i hi; have := hL.q_lt i hi
  have := hL.vn_lt i hi; have := hL.fn_lt i hi
  have := hL.vn_lt _ (hL.p_lt i hi)
  have e0 : (c.nmem (c.nreg 806 + A.a i) = c.nreg 809) ↔ A.out i 0 := by
    rw [hC.r806, hC.mz _ (by omega), hC.r809]; exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  obtain ⟨c', s, e, hs, fr, q829, q830, qm⟩ := fwPart_exec (P := P) (ra := 801) (setB := setO)
    c hw (nb := A.a i) (TL := A.vn i) (HD := A.vn (A.a i)) (CD := 3 * i + 0)
    (by rw [hC.r801, h827]; omega) (by rw [hC.r801, h827]; exact hC.ma i hi)
    (by rw [hC.r806]; omega)
    (fun c₂ hw₂ h833 hg hm => by
      have g := fun r hr => hg r hr
      obtain ⟨c₃, s₃, e₃, hs₃, t835, t836, t837, tfr, tm⟩ := setO_exec (P := P) c₂ hw₂
        (by rw [g 804 (by omega), g 827 (by omega), hC.r804, h827]; omega)
        (by rw [g 804 (by omega), hC.r804, h833]; omega)
      refine ⟨c₃, s₃, e₃, hs₃, ?_, ?_, ?_, tfr, tm⟩
      · rw [t835]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> exact hC.mvn i hi
      · rw [t836]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> exact hC.mvn _ (by omega)
      · rw [t837]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> omega)
    (by rw [hJ.r821]; omega) (by rw [hJ.r822]; omega) (by omega) hC.r10
  refine ⟨c', s, e, hs, fr, by rw [q829, if_congr e0 rfl rfl],
    by rw [q830, if_congr e0 rfl rfl]; rfl, ?_⟩
  rw [qm, if_congr e0 rfl rfl, hJ.r821, hJ.r822]
  rfl

theorem fwPartU_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c) {i : ℕ} (hi : i < m)
    (h827 : c.nreg 827 = i) (h828 : c.nreg 828 = 3 * i) (h829 : c.nreg 829 ≤ 3 * i + 2)
    (hz : A.z i ≠ A.sv) :
    ∃ c' s, Exec P W (fwPart 802 setU) c c' s ∧ s ≤ 21 ∧ SFr 829 840 c c' ∧
      c'.nreg 829 = (if A.out i 1 then c.nreg 829 + 1 else c.nreg 829) ∧
      c'.nreg 830 = (if A.out i 1 then A.tl i 1 else c.nreg 830) ∧
      c'.nmem = A.u T₀ (T₀ + (A.nV + nF)) i 1 c.nmem := by
  have := hL.bα; have := hL.bφ; have := hL.bφi; have := hL.bvn; have := hL.bfn; have := hL.bz
  have := hL.wT; have := hL.a_lt i hi; have := hL.p_lt i hi; have := hL.q_lt i hi
  have := hL.vn_lt i hi; have := hL.fn_lt i hi
  have := hL.vn_lt _ (hL.p_lt i hi)
  have e0 : (c.nmem (c.nreg 806 + A.p i) = c.nreg 809) ↔ A.out i 1 := by
    rw [hC.r806, hC.mz _ (by omega), hC.r809]; exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  obtain ⟨c', s, e, hs, fr, q829, q830, qm⟩ := fwPart_exec (P := P) (ra := 802) (setB := setU)
    c hw (nb := A.p i) (TL := A.vn (A.p i)) (HD := A.nV + A.fn i) (CD := 3 * i + 1)
    (by rw [hC.r802, h827]; omega) (by rw [hC.r802, h827]; exact hC.mp i hi)
    (by rw [hC.r806]; omega)
    (fun c₂ hw₂ h833 hg hm => by
      have g := fun r hr => hg r hr
      obtain ⟨c₃, s₃, e₃, hs₃, t835, t836, t837, tfr, tm⟩ := setU_exec (P := P) c₂ hw₂
        (by rw [g 804 (by omega), hC.r804, h833]; omega)
        (by rw [g 805 (by omega), g 827 (by omega), hC.r805, h827]; omega)
        (by simp (disch := omega) only [hm, g, hC.r805, h827, hC.r807, hC.mfn i hi]; omega)
        (by rw [g 828 (by omega), g 10 (by omega), h828, hC.r10]; omega)
      refine ⟨c₃, s₃, e₃, hs₃, ?_, ?_, ?_, tfr, tm⟩
      · rw [t835]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> exact hC.mvn _ (by omega)
      · rw [t836]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> (rw [hC.mfn i hi]; omega)
      · rw [t837]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> omega)
    (by rw [hJ.r821]; omega) (by rw [hJ.r822]; omega) (by omega) hC.r10
  refine ⟨c', s, e, hs, fr, by rw [q829, if_congr e0 rfl rfl],
    by rw [q830, if_congr e0 rfl rfl]; rfl, ?_⟩
  rw [qm, if_congr e0 rfl rfl, hJ.r821, hJ.r822]
  rfl

theorem fwPartD_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c) {i : ℕ} (hi : i < m)
    (h827 : c.nreg 827 = i) (h828 : c.nreg 828 = 3 * i) (h829 : c.nreg 829 ≤ 3 * i + 2)
    (hz : A.z i ≠ A.sv) :
    ∃ c' s, Exec P W (fwPart 803 setD) c c' s ∧ s ≤ 21 ∧ SFr 829 840 c c' ∧
      c'.nreg 829 = (if A.out i 2 then c.nreg 829 + 1 else c.nreg 829) ∧
      c'.nreg 830 = (if A.out i 2 then A.tl i 2 else c.nreg 830) ∧
      c'.nmem = A.u T₀ (T₀ + (A.nV + nF)) i 2 c.nmem := by
  have := hL.bα; have := hL.bφ; have := hL.bφi; have := hL.bvn; have := hL.bfn; have := hL.bz
  have := hL.wT; have := hL.a_lt i hi; have := hL.p_lt i hi; have := hL.q_lt i hi
  have := hL.vn_lt i hi; have := hL.fn_lt i hi
  have := hL.vn_lt _ (hL.p_lt i hi)
  have e0 : (c.nmem (c.nreg 806 + A.q i) = c.nreg 809) ↔ A.out i 2 := by
    rw [hC.r806, hC.mz _ (by omega), hC.r809]; exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  obtain ⟨c', s, e, hs, fr, q829, q830, qm⟩ := fwPart_exec (P := P) (ra := 803) (setB := setD)
    c hw (nb := A.q i) (TL := A.nV + A.fn i) (HD := A.vn i) (CD := 3 * i + 2)
    (by rw [hC.r803, h827]; omega) (by rw [hC.r803, h827]; exact hC.mq i hi)
    (by rw [hC.r806]; omega)
    (fun c₂ hw₂ h833 hg hm => by
      have g := fun r hr => hg r hr
      obtain ⟨c₃, s₃, e₃, hs₃, t835, t836, t837, tfr, tm⟩ := setD_exec (P := P) c₂ hw₂
        (by rw [g 805 (by omega), g 827 (by omega), hC.r805, h827]; omega)
        (by simp (disch := omega) only [hm, g, hC.r805, h827, hC.r807, hC.mfn i hi]; omega)
        (by rw [g 804 (by omega), g 827 (by omega), hC.r804, h827]; omega)
        (by rw [g 828 (by omega), g 10 (by omega), h828, hC.r10]; omega)
      refine ⟨c₃, s₃, e₃, hs₃, ?_, ?_, ?_, tfr, tm⟩
      · rw [t835]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> (rw [hC.mfn i hi]; omega)
      · rw [t836]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> exact hC.mvn i hi
      · rw [t837]; simp (disch := omega) only [hm, g, hC.r804, hC.r805, hC.r807, hC.r10, h827, h828,
          h833] <;> omega)
    (by rw [hJ.r821]; omega) (by rw [hJ.r822]; omega) (by omega) hC.r10
  refine ⟨c', s, e, hs, fr, by rw [q829, if_congr e0 rfl rfl],
    by rw [q830, if_congr e0 rfl rfl]; rfl, ?_⟩
  rw [qm, if_congr e0 rfl rfl, hJ.r821, hJ.r822]
  rfl


lemma WArr.nO_of (A : WArr) {i : ℕ} (h : A.z i = A.sv) : A.nO i = 0 := by
  simp [WArr.nO, A.not_out_of h]

lemma WArr.st_of (A : WArr) {i : ℕ} (h : A.z i = A.sv) (s : ℕ) : A.st i s = s := by
  simp [WArr.st, A.not_out_of h]

lemma WArr.wu_of (A : WArr) {i : ℕ} (h : A.z i = A.sv) (rH rG : ℕ) (mem : ℕ → ℕ) :
    A.wu rH rG i mem = mem := by
  simp [WArr.wu, WArr.u, A.not_out_of h]

lemma WArr.nO_le (A : WArr) (i : ℕ) : A.nO i ≤ 3 := by
  unfold WArr.nO; split_ifs <;> omega

/-- **The three darts of the triangle of `x`**, when it is off the side. -/
theorem fwOut_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c) {i : ℕ} (hi : i < m)
    (h827 : c.nreg 827 = i) (h828 : c.nreg 828 = 3 * i) (h829 : c.nreg 829 ≤ 3 * i)
    (hz : A.z i ≠ A.sv) :
    ∃ c' s, Exec P W fwOut c c' s ∧ s ≤ 63 ∧ SFr 829 840 c c' ∧
      c'.nreg 829 = c.nreg 829 + A.nO i ∧ c'.nreg 830 = A.st i (c.nreg 830) ∧
      c'.nmem = A.wu T₀ (T₀ + (A.nV + nF)) i c.nmem := by
  have := hL.wT
  obtain ⟨c₁, s₁, e₁, hs₁, f₁, a₁, b₁, m₁⟩ :=
    fwPartO_exec (P := P) hL c hw hC hJ hi h827 h828 (by omega) hz
  have n₁ : ∀ r, r < 829 → c₁.nreg r = c.nreg r := fun r hr => f₁.nreg r (by omega)
  have hC₁ := hC.of hL (fun r hr => n₁ r (by omega))
    (fun a ha => by rw [m₁]; exact A.u_low (by omega) (by omega))
  have hJ₁ := hJ.of (fun r _ h2 => n₁ r (by omega))
  obtain ⟨c₂, s₂, e₂, hs₂, f₂, a₂, b₂, m₂⟩ :=
    fwPartU_exec (P := P) hL c₁ e₁.wb_right hC₁ hJ₁ hi (by rw [n₁ 827 (by omega)]; exact h827)
      (by rw [n₁ 828 (by omega)]; exact h828) (by rw [a₁]; split_ifs <;> omega) hz
  have n₂ : ∀ r, r < 829 → c₂.nreg r = c₁.nreg r := fun r hr => f₂.nreg r (by omega)
  have hC₂ := hC₁.of hL (fun r hr => n₂ r (by omega))
    (fun a ha => by rw [m₂]; exact A.u_low (by omega) (by omega))
  have hJ₂ := hJ₁.of (fun r _ h2 => n₂ r (by omega))
  obtain ⟨c₃, s₃, e₃, hs₃, f₃, a₃, b₃, m₃⟩ :=
    fwPartD_exec (P := P) hL c₂ e₂.wb_right hC₂ hJ₂ hi
      (by rw [n₂ 827 (by omega), n₁ 827 (by omega)]; exact h827)
      (by rw [n₂ 828 (by omega), n₁ 828 (by omega)]; exact h828)
      (by rw [a₂, a₁]; split_ifs <;> omega) hz
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, f₁.trans (f₂.trans f₃), ?_, ?_, ?_⟩
  · rw [a₃, a₂, a₁]; unfold WArr.nO; split_ifs <;> omega
  · rw [b₃, b₂, b₁]; rfl
  · rw [m₃, m₂, m₁]; rfl

/-- **One slot of the scan.** -/
theorem fwBody_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c) {i : ℕ} (hi : i < m)
    (h827 : c.nreg 827 = i) (h828 : c.nreg 828 = 3 * i) (h829 : c.nreg 829 ≤ 3 * i) :
    ∃ c' s, Exec P W fwBody c c' s ∧ s ≤ 70 ∧ SFr 827 840 c c' ∧ c'.nreg 827 = i + 1 ∧
      c'.nreg 828 = 3 * i + 3 ∧ c'.nreg 829 = c.nreg 829 + A.nO i ∧
      c'.nreg 830 = A.st i (c.nreg 830) ∧ c'.nmem = A.wu T₀ (T₀ + (A.nV + nF)) i c.nmem := by
  have := hL.wT; have := hL.bz
  obtain ⟨c₁, k₁, e₁, hk₁, q832, qfr, qm⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 831 806 827, .loadN 832 831]) c c₁ k₁ ∧ k₁ ≤ 2 ∧ c₁.nreg 832 = A.z i ∧
      SFr 831 840 c c₁ ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try ((try config_simp); (try simp only [hC.r806, h827]); omega)
    config_simp
    simp only [hC.r806, h827, hC.mz i hi]
    and_intros
    all_goals first | omega | rfl | trivial | exact ⟨fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  have n₁ : ∀ r, r < 831 → c₁.nreg r = c.nreg r := fun r hr => qfr.nreg r (by omega)
  have hw₁ := e₁.wb_right
  -- the test and the three darts
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, a₂, b₂, m₂⟩ : ∃ c₂ k₂, Exec P W (ifEqN 832 809 .skip fwOut) c₁ c₂ k₂ ∧
      k₂ ≤ 66 ∧ SFr 829 840 c₁ c₂ ∧ c₂.nreg 829 = c.nreg 829 + A.nO i ∧
      c₂.nreg 830 = A.st i (c.nreg 830) ∧ c₂.nmem = A.wu T₀ (T₀ + (A.nV + nF)) i c.nmem := by
    by_cases hz : A.z i = A.sv
    · refine ⟨c₁, _, ifEqN_eq (by rw [q832, n₁ 809 (by omega), hC.r809]; exact hz)
        (Exec.skip hw₁), by omega, SFr.refl _ _ _, ?_, ?_, ?_⟩
      · rw [A.nO_of hz, n₁ 829 (by omega)]; rfl
      · rw [A.st_of hz, n₁ 830 (by omega)]
      · rw [A.wu_of hz, qm]
    · have hC₁ := hC.of hL (fun r hr => n₁ r (by omega)) (fun a _ => by rw [qm])
      have hJ₁ := hJ.of (fun r _ h2 => n₁ r (by omega))
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, a₂, b₂, m₂⟩ := fwOut_exec (P := P) hL c₁ hw₁ hC₁ hJ₁ hi
        (by rw [n₁ 827 (by omega)]; exact h827) (by rw [n₁ 828 (by omega)]; exact h828)
        (by rw [n₁ 829 (by omega)]; exact h829) hz
      obtain ⟨k', e', hk'⟩ := ifEqN_ne (a := 832) (b := 809) (t := .skip)
        (by rw [q832, n₁ 809 (by omega), hC.r809]; exact hz) e₂
      refine ⟨c₂, k', e', by omega, f₂, ?_, ?_, ?_⟩
      · rw [a₂, n₁ 829 (by omega)]
      · rw [b₂, n₁ 830 (by omega)]
      · rw [m₂, qm]
  have g₂ : ∀ r, r < 829 → c₂.nreg r = c.nreg r := fun r hr =>
    (f₂.nreg r (by omega)).trans (n₁ r (by omega))
  have := A.nO_le i
  obtain ⟨c₃, k₃, e₃, hk₃, r827, r828, fr₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.addN 828 828 826, .addN 827 827 10]) c₂ c₃ k₃ ∧ k₃ ≤ 2 ∧ c₃.nreg 827 = i + 1 ∧
      c₃.nreg 828 = 3 * i + 3 ∧ SFr 827 828 c₂ c₃ ∧ c₃.nmem = c₂.nmem := by
    have u826 : c₂.nreg 826 = 3 := by rw [g₂ 826 (by omega)]; exact hJ.r826
    have u10 : c₂.nreg 10 = 1 := by rw [g₂ 10 (by omega)]; exact hC.r10
    have u827 : c₂.nreg 827 = i := by rw [g₂ 827 (by omega)]; exact h827
    have u828 : c₂.nreg 828 = 3 * i := by rw [g₂ 828 (by omega)]; exact h828
    have hw₂ := e₂.wb_right
    exec_block
    all_goals try ((try config_simp); (try simp only [u826, u10, u827, u828]); omega)
    config_simp
    simp only [u826, u10, u827, u828]
    and_intros
    all_goals first | omega | rfl | trivial | exact ⟨fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    (qfr.mono (lo' := 827) (by omega) le_rfl).trans ((f₂.mono (lo' := 827) (by omega) le_rfl).trans
      (fr₃.mono le_rfl (by omega))), r827, r828, ?_, ?_, ?_⟩
  · rw [fr₃.nreg 829 (by omega), a₂]
  · rw [fr₃.nreg 830 (by omega), b₂]
  · rw [m₃, m₂]


namespace WArr

variable (A : WArr)

/-- The tables after the slots `< i`. -/
def sc (rH rG : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => mem
  | i + 1 => A.wu rH rG i (sc rH rG mem i)

/-- The start after the slots `< i`. -/
def sst (s : ℕ) : ℕ → ℕ
  | 0 => s
  | i + 1 => A.st i (sst s i)

lemma sc_low {rH rG : ℕ} {mem : ℕ → ℕ} {a : ℕ} (h1 : a < rH) (h2 : a < rG) (i : ℕ) :
    A.sc rH rG mem i a = mem a := by
  induction i with
  | zero => rfl
  | succ i ih => rw [sc, A.wu_low h1 h2, ih]

lemma sum_nO_le (i : ℕ) : ∑ x ∈ range i, A.nO x ≤ 3 * i := by
  induction i with
  | zero => simp
  | succ i ih => rw [sum_range_succ]; have := A.nO_le i; omega

end WArr

/-- **The scan of the darts of the piece map.** -/
theorem fwScan_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) (hJ : WIni A m nF T₀ c)
    (h827 : c.nreg 827 = 0) (h828 : c.nreg 828 = 0) (h829 : c.nreg 829 = 0) :
    ∃ c' s, Exec P W (.whileLtN 827 800 fwBody) c c' s ∧ s ≤ 72 * m + 2 ∧ SFr 827 840 c c' ∧
      c'.nreg 829 = ∑ x ∈ range m, A.nO x ∧ c'.nreg 830 = A.sst (c.nreg 830) m ∧
      c'.nmem = A.sc T₀ (T₀ + (A.nV + nF)) c.nmem m := by
  have := hL.wT
  let J : ℕ → Config → Prop := fun i c' =>
    SFr 827 840 c c' ∧ c'.nreg 828 = 3 * i ∧ c'.nreg 829 = ∑ x ∈ range i, A.nO x ∧
      c'.nreg 830 = A.sst (c.nreg 830) i ∧ c'.nmem = A.sc T₀ (T₀ + (A.nV + nF)) c.nmem i
  obtain ⟨c', s, e, hs, -, fr, r828, r829, r830, hm⟩ := forLoop_exec (P := P) (a := 827) (bR := 800)
    (body := fwBody) J (K := 70) (n := m) c hw h827 hC.r800
    ⟨SFr.refl _ _ _, h828, by rw [h829]; simp, rfl, rfl⟩
    (fun i c₁ hi hw₁ ha hb ⟨fr, q828, q829, q830, qm⟩ => by
      have g : ∀ r, r < 827 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have hC₁ := hC.of hL (fun r hr => g r (by omega))
        (fun a ha => by rw [qm]; exact A.sc_low (by omega) (by omega) i)
      have hJ₁ := hJ.of (fun r _ h2 => g r (by omega))
      obtain ⟨c₂, k₂, e₂, hk₂, f₂, a827, a828, a829, a830, m₂⟩ :=
        fwBody_exec (P := P) hL c₁ hw₁ hC₁ hJ₁ hi ha q828
          (by rw [q829]; exact A.sum_nO_le i)
      refine ⟨c₂, k₂, e₂, hk₂, a827, by rw [f₂.nreg 800 (by omega)]; exact hb,
        fr.trans f₂, a828, ?_, ?_, ?_⟩
      · rw [a829, q829, sum_range_succ]
      · rw [a830, q830]; rfl
      · rw [m₂, qm]; rfl)
  exact ⟨c', s, e, by nlinarith, fr, r829, r830, hm⟩


/-- **The walk**: from the vertex `v₀` (`r839`), `k = r829` steps along the table `H` at `T₀`,
writing the position `t` of the `t`-th vertex in `P` (at `T₀ + 2 n'`), its record of `G` (at
`T₀ + n'`) in `Cy` (at `T₀ + 3 n'`) and itself in `Vy` (at `T₀ + 3 n' + 3 m`). -/
theorem fwWalk_exec {A : WArr} {m nF T₀ : ℕ} (c : Config) (hw : WordsBounded W c)
    (hJ : WIni A m nF T₀ c) (h10 : c.nreg 10 = 1) {k : ℕ} (h829 : c.nreg 829 = k)
    (h838 : c.nreg 838 = 0) (hk : k ≤ 3 * m) (hW : T₀ + 3 * (A.nV + nF) + 6 * m + 3 ≤ W)
    (hlt : ∀ t < k, (fun v => c.nmem (T₀ + v))^[t] (c.nreg 839) < A.nV + nF)
    (hinj : ∀ t < k, ∀ t' < k, (fun v => c.nmem (T₀ + v))^[t] (c.nreg 839) =
      (fun v => c.nmem (T₀ + v))^[t'] (c.nreg 839) → t = t') :
    ∃ c' s, Exec P W (.whileLtN 838 829 fwStep) c c' s ∧ s ≤ 13 * k + 2 ∧ SFr 831 840 c c' ∧
      (∀ t < k, c'.nmem (T₀ + 2 * (A.nV + nF) + (fun v => c.nmem (T₀ + v))^[t] (c.nreg 839)) = t) ∧
      (∀ t < k, c'.nmem (T₀ + 3 * (A.nV + nF) + t) =
        c.nmem (T₀ + (A.nV + nF) + (fun v => c.nmem (T₀ + v))^[t] (c.nreg 839))) ∧
      (∀ t < k, c'.nmem (T₀ + 3 * (A.nV + nF) + 3 * m + t) =
        (fun v => c.nmem (T₀ + v))^[t] (c.nreg 839)) ∧
      (∀ a, a < T₀ + 2 * (A.nV + nF) ∨ T₀ + 3 * (A.nV + nF) + 6 * m ≤ a →
        c'.nmem a = c.nmem a) := by
  set n' := A.nV + nF with hn'
  set H : ℕ → ℕ := fun v => c.nmem (T₀ + v) with hH
  set v₀ := c.nreg 839
  let J : ℕ → Config → Prop := fun i c' =>
    SFr 831 840 c c' ∧ c'.nreg 839 = H^[i] v₀ ∧
      (∀ a, a < T₀ + 2 * n' ∨ T₀ + 3 * n' + 6 * m ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ t < i, c'.nmem (T₀ + 2 * n' + H^[t] v₀) = t) ∧
      (∀ t < i, c'.nmem (T₀ + 3 * n' + t) = c.nmem (T₀ + n' + H^[t] v₀)) ∧
      (∀ t < i, c'.nmem (T₀ + 3 * n' + 3 * m + t) = H^[t] v₀)
  obtain ⟨c', s, e, hs, -, fr, -, fo, fP, fC, fV⟩ := forLoop_exec (P := P) (a := 838) (bR := 829)
    (body := fwStep) J (K := 11) (n := k) c hw h838 h829
    ⟨SFr.refl _ _ _, rfl, fun _ _ => rfl, fun t ht => absurd ht (by omega),
      fun t ht => absurd ht (by omega), fun t ht => absurd ht (by omega)⟩
    (fun i c₁ hi hw₁ ha hb ⟨fr, q839, qo, qP, qC, qV⟩ => by
      have g : ∀ r, r < 831 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
      have u821 : c₁.nreg 821 = T₀ := by rw [g 821 (by omega)]; exact hJ.r821
      have u822 : c₁.nreg 822 = T₀ + n' := by rw [g 822 (by omega)]; exact hJ.r822
      have u823 : c₁.nreg 823 = T₀ + 2 * n' := by rw [g 823 (by omega)]; exact hJ.r823
      have u824 : c₁.nreg 824 = T₀ + 3 * n' := by rw [g 824 (by omega)]; exact hJ.r824
      have u825 : c₁.nreg 825 = T₀ + 3 * n' + 3 * m := by rw [g 825 (by omega)]; exact hJ.r825
      have u10 : c₁.nreg 10 = 1 := by rw [g 10 (by omega)]; exact h10
      have hv := hlt i hi
      rw [← q839] at hv
      unfold fwStep
      exec_block
      all_goals try ((try config_simp); (try simp only [u821, u822, u823, u824, u825, u10, ha]); omega)
      dsimp only [J]
      config_simp
      simp only [u821, u822, u823, u824, u825, u10, ha]
      have e1 : T₀ + n' + c₁.nreg 839 ≠ T₀ + 2 * n' + c₁.nreg 839 := by omega
      have e2 : T₀ + c₁.nreg 839 ≠ T₀ + 3 * n' + 3 * m + i := by omega
      have e3 : T₀ + c₁.nreg 839 ≠ T₀ + 3 * n' + i := by omega
      have e4 : T₀ + c₁.nreg 839 ≠ T₀ + 2 * n' + c₁.nreg 839 := by omega
      simp only [upd_other _ _ _ e1, upd_other _ _ _ e2, upd_other _ _ _ e3,
        upd_other _ _ _ e4]
      have qH : c₁.nmem (T₀ + c₁.nreg 839) = H (H^[i] v₀) := by
        rw [qo _ (Or.inl (by omega)), q839]
      have qG : c₁.nmem (T₀ + n' + c₁.nreg 839) = c.nmem (T₀ + n' + H^[i] v₀) := by
        rw [qo _ (Or.inl (by omega)), q839]
      refine ⟨by omega, trivial, by omega, ⟨fun r hr => ?_, fr.rreg, fr.rmem, fr.out⟩, ?_, ?_, ?_, ?_,
        ?_⟩
      · simp only [upd_apply]; split_ifs <;> first | omega | exact fr.nreg r hr
      · rw [qH, Function.iterate_succ_apply']
      · intro a ha'
        simp only [upd_apply]
        split_ifs <;> first | omega | exact qo a ha'
      · intro t ht
        simp only [upd_apply]
        rw [q839]
        by_cases hti : t = i
        · subst hti; split_ifs <;> first | omega | rfl
        · have hne : H^[t] v₀ ≠ H^[i] v₀ := fun h => hti (hinj t (by omega) i hi h)
          have := hlt t (by omega)
          split_ifs <;> first | omega | exact qP t (by omega)
      · intro t ht
        simp only [upd_apply]
        by_cases hti : t = i
        · subst hti; split_ifs <;> first | omega | exact qG
        · split_ifs <;> first | omega | exact qC t (by omega)
      · intro t ht
        simp only [upd_apply]
        by_cases hti : t = i
        · subst hti; split_ifs <;> first | omega | exact q839
        · split_ifs <;> first | omega | exact qV t (by omega))
  exact ⟨c', s, e, by nlinarith, fr, fP, fC, fV, fo⟩


/-! ### The tables after the scan -/

namespace WArr

variable (A : WArr)

lemma u_eq_of {rH rG x t : ℕ} {mem : ℕ → ℕ} {a : ℕ}
    (h : A.out x t → a ≠ rH + A.tl x t ∧ a ≠ rG + A.tl x t) : A.u rH rG x t mem a = mem a := by
  unfold u; split_ifs with ho
  · obtain ⟨h1, h2⟩ := h ho
    rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  · rfl

lemma u_H {rH rG x t : ℕ} {mem : ℕ → ℕ} (h : A.out x t) (hne : rH + A.tl x t ≠ rG + A.tl x t) :
    A.u rH rG x t mem (rH + A.tl x t) = A.hd x t := by
  unfold u; rw [ite_of_pos h, upd_other _ _ _ hne, upd_same]

lemma u_G {rH rG x t : ℕ} {mem : ℕ → ℕ} (h : A.out x t) :
    A.u rH rG x t mem (rG + A.tl x t) = 3 * x + t := by
  unfold u; rw [ite_of_pos h, upd_same]

/-- **The tables after the scan**: every dart out recorded at its tail, when the tails of the
darts out are distinct and below `n`. -/
lemma sc_spec {m n rH : ℕ} {mem : ℕ → ℕ}
    (hU : ∀ x < m, ∀ t < 3, ∀ x' < m, ∀ t' < 3, A.out x t → A.out x' t' →
      A.tl x t = A.tl x' t' → x = x' ∧ t = t')
    (htl : ∀ x < m, ∀ t < 3, A.out x t → A.tl x t < n) :
    ∀ i ≤ m, ∀ x < i, ∀ t < 3, A.out x t →
      A.sc rH (rH + n) mem i (rH + A.tl x t) = A.hd x t ∧
      A.sc rH (rH + n) mem i (rH + n + A.tl x t) = 3 * x + t := by
  intro i
  induction i with
  | zero => intro _ x hx; omega
  | succ i ih =>
    intro hi x hx t ht ho
    have hxm : x < m := by omega
    have hl := htl x hxm t ht ho
    -- the records of the slot `i` at other tails
    have hfix : ∀ t' < 3, (x ≠ i ∨ t' ≠ t) → ∀ (mem' : ℕ → ℕ) (a : ℕ),
        (a = rH + A.tl x t ∨ a = rH + n + A.tl x t) → A.u rH (rH + n) i t' mem' a = mem' a := by
      intro t' ht' hne mem' a ha
      refine A.u_eq_of fun ho' => ?_
      have hl' := htl i (by omega) t' ht' ho'
      have hd : A.tl x t ≠ A.tl i t' := fun e => by
        obtain ⟨e1, e2⟩ := hU x hxm t ht i (by omega) t' ht' ho ho' e
        omega
      omega
    rw [sc, wu]
    rcases Nat.lt_or_ge x i with hxi | hxi
    · have hne : x ≠ i := by omega
      rw [hfix 2 (by omega) (Or.inl hne) _ _ (Or.inl rfl),
        hfix 1 (by omega) (Or.inl hne) _ _ (Or.inl rfl),
        hfix 0 (by omega) (Or.inl hne) _ _ (Or.inl rfl),
        hfix 2 (by omega) (Or.inl hne) _ _ (Or.inr rfl),
        hfix 1 (by omega) (Or.inl hne) _ _ (Or.inr rfl),
        hfix 0 (by omega) (Or.inl hne) _ _ (Or.inr rfl)]
      exact ih (by omega) x hxi t ht ho
    · have hxe : x = i := by omega
      subst hxe
      have hHG : rH + A.tl x t ≠ rH + n + A.tl x t := by omega
      interval_cases t
      · rw [hfix 2 (by omega) (Or.inr (by omega)) _ _ (Or.inl rfl),
          hfix 1 (by omega) (Or.inr (by omega)) _ _ (Or.inl rfl),
          hfix 2 (by omega) (Or.inr (by omega)) _ _ (Or.inr rfl),
          hfix 1 (by omega) (Or.inr (by omega)) _ _ (Or.inr rfl)]
        exact ⟨A.u_H ho hHG, A.u_G ho⟩
      · rw [hfix 2 (by omega) (Or.inr (by omega)) _ _ (Or.inl rfl),
          hfix 2 (by omega) (Or.inr (by omega)) _ _ (Or.inr rfl)]
        exact ⟨A.u_H ho hHG, A.u_G ho⟩
      · exact ⟨A.u_H ho hHG, A.u_G ho⟩

lemma sc_high {rH n : ℕ} {mem : ℕ → ℕ} {m : ℕ} (htl : ∀ x < m, ∀ t < 3, A.out x t → A.tl x t < n)
    {a : ℕ} (ha : a < rH ∨ rH + 2 * n ≤ a) : ∀ i ≤ m, A.sc rH (rH + n) mem i a = mem a := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hfix : ∀ t < 3, ∀ mem' : ℕ → ℕ, A.u rH (rH + n) i t mem' a = mem' a := fun t ht mem' =>
      A.u_eq_of fun ho => by have := htl i (by omega) t ht ho; omega
    rw [sc, wu, hfix 2 (by omega), hfix 1 (by omega), hfix 0 (by omega), ih (by omega)]

/-- The start after the scan is the tail of a dart out, if there is one. -/
lemma sst_spec (s : ℕ) : ∀ i, (∃ x < i, ∃ t < 3, A.out x t) →
    ∃ x < i, ∃ t < 3, A.out x t ∧ A.sst s i = A.tl x t := by
  intro i
  induction i with
  | zero => rintro ⟨x, hx, -⟩; omega
  | succ i ih =>
    intro ⟨x, hx, t, ht, ho⟩
    rw [sst, st]
    split_ifs with h2 h1 h0
    · exact ⟨i, by omega, 2, by omega, h2, rfl⟩
    · exact ⟨i, by omega, 1, by omega, h1, rfl⟩
    · exact ⟨i, by omega, 0, by omega, h0, rfl⟩
    · have hxi : x < i := by
        by_contra hc
        have : x = i := by omega
        subst this
        interval_cases t <;> contradiction
      obtain ⟨x', hx', t', ht', ho', e⟩ := ih ⟨x, hxi, t, ht, ho⟩
      exact ⟨x', by omega, t', ht', ho', e⟩

/-- The count of the scan: the darts out among the `3 i` first numbers. -/
lemma sum_nO_eq (i : ℕ) :
    ∑ x ∈ range i, A.nO x = ((range (3 * i)).filter fun s => A.out (s / 3) (s % 3)).card := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih, card_filter, card_filter,
      show 3 * (i + 1) = 3 * i + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ]
    have e0 : 3 * i / 3 = i := by omega
    have e0' : 3 * i % 3 = 0 := by omega
    have e1 : (3 * i + 1) / 3 = i := by omega
    have e1' : (3 * i + 1) % 3 = 1 := by omega
    have e2 : (3 * i + 1 + 1) / 3 = i := by omega
    have e2' : (3 * i + 1 + 1) % 3 = 2 := by omega
    rw [e0, e0', e1, e1', e2, e2', nO]
    omega

end WArr

/-- **The cycle of the darts out**, numbered `3 x + t`: `K` darts `cy i`, every dart out among
them, the head of each the tail of the next, the tails distinct. -/
structure WCyc (A : WArr) (m K : ℕ) (cy : ℕ → ℕ) : Prop where
  lt : ∀ i < K, cy i < 3 * m
  out : ∀ i < K, A.out (cy i / 3) (cy i % 3)
  all : ∀ x < m, ∀ t < 3, A.out x t → ∃ i < K, cy i = 3 * x + t
  next : ∀ i < K, A.hd (cy i / 3) (cy i % 3) = A.tl (cy ((i + 1) % K) / 3) (cy ((i + 1) % K) % 3)
  inj : ∀ i < K, ∀ j < K, A.tl (cy i / 3) (cy i % 3) = A.tl (cy j / 3) (cy j % 3) → i = j


/-- The tail of the dart numbered `s`. -/
def WArr.tlS (A : WArr) (s : ℕ) : ℕ := A.tl (s / 3) (s % 3)

set_option maxHeartbeats 1600000 in
theorem fwInit_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ : ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (c : Config) (hw : WordsBounded W c)
    (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) :
    ∃ c' s, Exec P W fwInit c c' s ∧ s ≤ 12 ∧ WIni A m nF T₀ c' ∧ c'.nreg 827 = 0 ∧
      c'.nreg 828 = 0 ∧ c'.nreg 829 = 0 ∧ c'.nreg 830 = 0 ∧ SFr 820 830 c c' ∧
      c'.nmem = c.nmem := by
  have := hL.wT
  obtain ⟨c', s, e, hs, r820, r821, r822, r823, r824, r825, r826, r827, r828, r829, r830, fr, hm⟩ :
      ∃ c' s, Exec P W fwInit c c' s ∧ s ≤ 12 ∧ c'.nreg 820 = A.nV + nF ∧ c'.nreg 821 = T₀ ∧
        c'.nreg 822 = T₀ + (A.nV + nF) ∧ c'.nreg 823 = T₀ + (A.nV + nF) + (A.nV + nF) ∧
        c'.nreg 824 = T₀ + (A.nV + nF) + (A.nV + nF) + (A.nV + nF) ∧
        c'.nreg 825 = T₀ + (A.nV + nF) + (A.nV + nF) + (A.nV + nF) + m * 3 ∧
        c'.nreg 826 = 3 ∧ c'.nreg 827 = 0 ∧ c'.nreg 828 = 0 ∧ c'.nreg 829 = 0 ∧
        c'.nreg 830 = 0 ∧ SFr 820 830 c c' ∧ c'.nmem = c.nmem := by
    unfold fwInit
    exec_block
    all_goals try ((try config_simp); (try simp only [hC.r807, hC.r808, hC.r810, hC.r800]); omega)
    config_simp
    simp only [hC.r807, hC.r808, hC.r810, hC.r800]
    and_intros
    all_goals first | omega | rfl | trivial | exact ⟨fun r hr => by
        simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  exact ⟨c', s, e, hs, ⟨r820, r821, r822, by rw [r823]; ring, by rw [r824]; ring,
    by rw [r825]; ring, r826⟩, r827, r828, r829, r830, fr, hm⟩

/-- **The walk of the cycle of the darts out, on abstract arrays.** For `K ≥ 1` darts out forming
a cycle `cy` (`WCyc`), `faceWalk` ends within `72 m + 13 K + 18` steps with `r829 = K` and, for
some start `i₀ < K`, the `t`-th dart of the walk is `cy ((i₀ + t) % K)`: its number at
`T₀ + 3 n' + t`, its tail at `T₀ + 3 n' + 3 m + t`, and the position `t` at `T₀ + 2 n'` plus its
tail (`n' = nV + nF`); the memory outside `[T₀, T₀ + 3 n' + 6 m)` is unchanged. -/
theorem faceWalk_exec {A : WArr} {m bα bφ bφi bvn bfn bz nF T₀ K : ℕ} {cy : ℕ → ℕ}
    (hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W) (hY : WCyc A m K cy) (hK : 0 < K)
    (c : Config) (hw : WordsBounded W c) (hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c) :
    ∃ c' s i₀, Exec P W faceWalk c c' s ∧ s ≤ 72 * m + 13 * K + 18 ∧ i₀ < K ∧
      c'.nreg 829 = K ∧ SFr 820 840 c c' ∧
      (∀ t < K, c'.nmem (T₀ + 2 * (A.nV + nF) + A.tlS (cy ((i₀ + t) % K))) = t) ∧
      (∀ t < K, c'.nmem (T₀ + 3 * (A.nV + nF) + t) = cy ((i₀ + t) % K)) ∧
      (∀ t < K, c'.nmem (T₀ + 3 * (A.nV + nF) + 3 * m + t) = A.tlS (cy ((i₀ + t) % K))) ∧
      (∀ a, a < T₀ ∨ T₀ + 3 * (A.nV + nF) + 6 * m ≤ a → c'.nmem a = c.nmem a) := by
  have := hL.wT
  set n' := A.nV + nF with hn'
  -- the facts on the darts out
  have htl : ∀ x < m, ∀ t < 3, A.out x t → A.tl x t < n' := by
    intro x hx t ht _
    have := hL.vn_lt x hx; have := hL.fn_lt x hx; have := hL.vn_lt _ (hL.p_lt x hx)
    interval_cases t <;> simp only [WArr.tl] <;> omega
  have hdm : ∀ i < K, cy i / 3 < m ∧ cy i % 3 < 3 := fun i hi => by
    have := hY.lt i hi; omega
  have hU : ∀ x < m, ∀ t < 3, ∀ x' < m, ∀ t' < 3, A.out x t → A.out x' t' →
      A.tl x t = A.tl x' t' → x = x' ∧ t = t' := by
    intro x hx t ht x' hx' t' ht' ho ho' e
    obtain ⟨i, hi, ei⟩ := hY.all x hx t ht ho
    obtain ⟨j, hj, ej⟩ := hY.all x' hx' t' ht' ho'
    have e1 : cy i / 3 = x := by omega
    have e2 : cy i % 3 = t := by omega
    have e3 : cy j / 3 = x' := by omega
    have e4 : cy j % 3 = t' := by omega
    have := hY.inj i hi j hj (by rw [e1, e2, e3, e4]; exact e)
    subst this
    omega
  have hcount : ∑ x ∈ range m, A.nO x = K := by
    rw [A.sum_nO_eq]
    have : ((range (3 * m)).filter fun s => A.out (s / 3) (s % 3)) = (range K).image cy := by
      ext s
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hs, ho⟩
        obtain ⟨i, hi, ei⟩ := hY.all (s / 3) (by omega) (s % 3) (by omega) ho
        exact ⟨i, hi, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hY.lt i hi, hY.out i hi⟩
    rw [this, card_image_of_injOn, card_range]
    intro i hi j hj e
    exact hY.inj i (by simpa using hi) j (by simpa using hj) (by rw [e])
  -- the run
  obtain ⟨c₁, s₁, e₁, hs₁, hJ₁, a827, a828, a829, a830, f₁, m₁⟩ :=
    fwInit_exec (P := P) hL c hw hC
  have hC₁ := hC.of hL (fun r hr => f₁.nreg r (by omega)) (fun a _ => by rw [m₁])
  obtain ⟨c₂, s₂, e₂, hs₂, f₂, b829, b830, m₂⟩ :=
    fwScan_exec (P := P) hL c₁ e₁.wb_right hC₁ hJ₁ a827 a828 a829
  rw [hcount, a830] at *
  have hJ₂ := hJ₁.of (fun r h1 h2 => f₂.nreg r (by omega))
  obtain ⟨c₃, k₃, e₃, hk₃, d838, d839, f₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.constN 838 0, .copyN 839 830]) c₂ c₃ k₃ ∧ k₃ ≤ 2 ∧ c₃.nreg 838 = 0 ∧
      c₃.nreg 839 = c₂.nreg 830 ∧ SFr 838 839 c₂ c₃ ∧ c₃.nmem = c₂.nmem := by
    have hw₂ := e₂.wb_right
    exec_block
    all_goals try ((try config_simp); omega)
    config_simp
    and_intros
    all_goals first | omega | rfl | trivial | exact ⟨fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩
  have hJ₃ := hJ₂.of (fun r h1 h2 => f₃.nreg r (by omega))
  -- the start
  obtain ⟨x₀, hx₀, t₀, ht₀, ho₀, est⟩ := A.sst_spec 0 m
    ⟨cy 0 / 3, (hdm 0 hK).1, cy 0 % 3, (hdm 0 hK).2, hY.out 0 hK⟩
  obtain ⟨i₀, hi₀, ei₀⟩ := hY.all x₀ hx₀ t₀ ht₀ ho₀
  have hv₀ : c₃.nreg 839 = A.tlS (cy i₀) := by
    rw [d839, b830, est, WArr.tlS, ei₀, show (3 * x₀ + t₀) / 3 = x₀ by omega,
      show (3 * x₀ + t₀) % 3 = t₀ by omega]
  -- the tables
  have hsc := A.sc_spec (rH := T₀) (mem := c.nmem) hU htl m le_rfl
  have hH : ∀ i < K, c₃.nmem (T₀ + A.tlS (cy i)) = A.tlS (cy ((i + 1) % K)) := by
    intro i hi
    rw [m₃, m₂, m₁]
    exact ((hsc _ (hdm i hi).1 _ (hdm i hi).2 (hY.out i hi)).1).trans (hY.next i hi)
  have hG : ∀ i < K, c₃.nmem (T₀ + n' + A.tlS (cy i)) = cy i := by
    intro i hi
    rw [m₃, m₂, m₁]
    exact ((hsc _ (hdm i hi).1 _ (hdm i hi).2 (hY.out i hi)).2).trans (by omega)
  have hit : ∀ t, (fun v => c₃.nmem (T₀ + v))^[t] (c₃.nreg 839) = A.tlS (cy ((i₀ + t) % K)) := by
    intro t
    induction t with
    | zero => rw [Function.iterate_zero_apply, hv₀, Nat.add_zero, Nat.mod_eq_of_lt hi₀]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih, hH _ (Nat.mod_lt _ hK), Nat.mod_add_mod, add_assoc]
  have hlt' : ∀ i < K, A.tlS (cy i) < n' := fun i hi =>
    htl _ (hdm i hi).1 _ (hdm i hi).2 (hY.out i hi)
  obtain ⟨c₄, s₄, e₄, hs₄, f₄, wP, wC, wV, wo⟩ :=
    fwWalk_exec (P := P) (k := K) c₃ e₃.wb_right hJ₃
      (by rw [f₃.nreg 10 (by omega), f₂.nreg 10 (by omega), f₁.nreg 10 (by omega)]; exact hC.r10)
      (by rw [f₃.nreg 829 (by omega), b829]) d838
      (by have := fun i hi => hY.lt i hi; by_contra hc
          have := hY.lt 0 hK
          have hinjc : Set.InjOn cy (range K) := fun i hi j hj e =>
            hY.inj i (by simpa using hi) j (by simpa using hj) (by rw [e])
          have := card_le_card_of_injOn cy (t := range (3 * m))
            (fun i hi => by simpa using hY.lt i (by simpa using hi)) hinjc
          simp only [card_range] at this; omega)
      (by rw [← hn']; omega)
      (fun t ht => by rw [hit t]; exact hlt' _ (Nat.mod_lt _ hK))
      (fun t ht t' ht' e => by
        rw [hit, hit] at e
        exact mod_add_inj ht ht' (hY.inj _ (Nat.mod_lt _ hK) _ (Nat.mod_lt _ hK) e))
  refine ⟨c₄, _, i₀, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hi₀,
    by rw [f₄.nreg 829 (by omega), f₃.nreg 829 (by omega), b829],
    ((f₁.mono le_rfl (by omega)).trans ((f₂.mono (by omega) le_rfl).trans
      ((f₃.mono (by omega) (by omega)).trans (f₄.mono (by omega) le_rfl)))),
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun a ha => ?_⟩
  · have := wP t ht; rwa [hit] at this
  · rw [wC t ht, hit, hG _ (Nat.mod_lt _ hK)]
  · rw [wV t ht, hit]
  · rw [wo a (by omega), m₃, m₂, A.sc_high htl (by omega) m le_rfl, m₁]


/-! ### The darts out of the stellar subdivision -/

section Conc

open PlanarSeparator.MillerProg

variable {X Q : Type*} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q] {M : Map X Q}
  {m nV nF : ℕ} {c : X ≃ Fin m} {vn : Q ≃ Fin nV} {fn : M.Face ≃ Fin nF}

/-- The arrays of `faceWalk`, read from the memory `mem`. -/
def wArr (mem : ℕ → ℕ) (sv nV bα bφ bφi bvn bfn bz : ℕ) : WArr :=
  ⟨sv, nV, fun u => mem (bz + u), fun u => mem (bα + u), fun u => mem (bφ + u),
    fun u => mem (bφi + u), fun u => mem (bvn + u), fun u => mem (bfn + u)⟩

/-- **The dart numbered `stCode δ` in the scan is the dart `δ` of the stellar subdivision**: it is
out iff `Out Z δ`, its tail and head are the numbers (`stVi`) of the ends of `δ`. -/
theorem wArr_st {mem : ℕ → ℕ} {bα bφ bφi bvn bfn bz sv : ℕ}
    (hE : Enc M c vn fn mem bα bφ bφi bvn bfn) {Z : Finset M.stellar.Face}
    (hz : ∀ d, (M.stellar.face (old d) ∈ Z ↔ mem (bz + c d) = sv)) (δ : StDart X) :
    ((wArr mem sv nV bα bφ bφi bvn bfn bz).out (M.stCode c δ / 3) (M.stCode c δ % 3) ↔
        Out Z δ) ∧
      (wArr mem sv nV bα bφ bφi bvn bfn bz).tl (M.stCode c δ / 3) (M.stCode c δ % 3) =
        M.stVi vn fn (M.stellar.vert δ) ∧
      (wArr mem sv nV bα bφ bφi bvn bfn bz).hd (M.stCode c δ / 3) (M.stCode c δ % 3) =
        M.stVi vn fn (M.stellar.vert (M.stellar.α δ)) := by
  have hz' : ∀ d, (M.stellar.face (old d) ∉ Z ↔ mem (bz + c d) ≠ sv) := fun d =>
    not_congr (hz d)
  cases δ with
  | old d =>
    have e1 : (M.stCode c (old d) : ℕ) / 3 = c d := by rw [stCode_val]; simp only [stNum]; omega
    have e2 : (M.stCode c (old d) : ℕ) % 3 = 0 := by rw [stCode_val]; simp only [stNum]; omega
    rw [e1, e2]
    simp only [WArr.out, WArr.tl, WArr.hd, wArr, Out, stellar_α, stα_old, stellar_vert_old,
      stVi_inl, hE.α d, hE.vn d, hE.vn (M.α d)]
    exact ⟨and_congr (hz' d).symm (hz (M.α d)).symm, trivial, trivial⟩
  | up e =>
    have e1 : (M.stCode c (up e) : ℕ) / 3 = c (M.φ.symm e) := by
      rw [stCode_val]; simp only [stNum]; omega
    have e2 : (M.stCode c (up e) : ℕ) % 3 = 1 := by rw [stCode_val]; simp only [stNum]; omega
    rw [e1, e2]
    simp only [WArr.out, WArr.tl, WArr.hd, wArr, Out, stellar_α, stα_up, stellar_vert_up,
      stellar_vert_down, stVi_inl, stVi_inr, hE.φ (M.φ.symm e), Equiv.apply_symm_apply, hE.vn e,
      hE.fn (M.φ.symm e), face_φ_symm, stellar_face_up, stellar_face_down]
    exact ⟨and_congr (hz' _).symm (hz e).symm, trivial, trivial⟩
  | down d =>
    have e1 : (M.stCode c (down d) : ℕ) / 3 = c d := by rw [stCode_val]; simp only [stNum]; omega
    have e2 : (M.stCode c (down d) : ℕ) % 3 = 2 := by rw [stCode_val]; simp only [stNum]; omega
    rw [e1, e2]
    simp only [WArr.out, WArr.tl, WArr.hd, wArr, Out, stellar_α, stα_down, stellar_vert_up,
      stellar_vert_down, stVi_inl, stVi_inr, hE.φi d, hE.vn d, hE.fn d, stellar_face_up,
      stellar_face_down]
    exact ⟨and_congr (hz' _).symm (hz _).symm, trivial, trivial⟩



/-- **The darts `Out Z` of the stellar subdivision form the cycle of the scan**, numbered by
`stCode`, when the boundary of `Z` is the cycle `C` and `C'` runs along `C` with every dart
`Out Z`. -/
theorem wCyc_of {mem : ℕ → ℕ} {bα bφ bφi bvn bfn bz sv : ℕ}
    (hE : Enc M c vn fn mem bα bφ bφi bvn bfn) {Z : Finset M.stellar.Face}
    (hz : ∀ d, (M.stellar.face (old d) ∈ Z ↔ mem (bz + c d) = sv))
    {C C' : M.stellar.SCycle}
    (hbd : ∀ d, (M.stellar.face d ∈ Z ↔ M.stellar.face (M.stellar.α d) ∈ Z) ↔ ¬ C.Mem d)
    (hmem : ∀ d, C'.Mem d ↔ C.Mem d) (hout : ∀ i < C'.k, Out Z (C'.d i)) :
    WCyc (wArr mem sv nV bα bφ bφi bvn bfn bz) m C'.k (fun i => M.stCode c (C'.d i)) where
  lt i _ := (M.stCode c (C'.d i)).isLt
  out i hi := (wArr_st hE hz (C'.d i)).1.2 (hout i hi)
  all x hx t ht ho := by
    set δ := (M.stCode c).symm ⟨3 * x + t, by omega⟩ with hδ
    have e : (M.stCode c δ : ℕ) = 3 * x + t := by simp [hδ]
    have hO : Out Z δ := by
      refine (wArr_st hE hz δ).1.1 ?_
      rw [e, show (3 * x + t) / 3 = x by omega, show (3 * x + t) % 3 = t by omega]
      exact ho
    obtain ⟨i, hi, hiδ⟩ := (out_iff_cyc hbd hmem hout δ).1 hO
    exact ⟨i, hi, by rw [hiδ, e]⟩
  next i hi := by
    rw [(wArr_st hE hz (C'.d i)).2.2, (wArr_st hE hz _).2.1, C'.vert_α i hi]
  inj i hi j hj h := by
    rw [(wArr_st hE hz _).2.1, (wArr_st hE hz _).2.1] at h
    exact C'.inj i hi j hj ((M.stVi vn fn).injective (Fin.ext h))


/-- **The marks of `sepRun` for both sides**: from a mark `1` on the triangles of `Z` (by their
numbers `stFn`, as `sepRun_exec` leaves them), the triangle of `x` is in `Z` iff the mark of `x`
is `1`, and in `Zᶜ` iff it is `0`: the hypothesis `hz` of `faceWalk_faceInst` for `sv = 1` and
`sv = 0`. -/
theorem marks_sides {mem : ℕ → ℕ} {bz : ℕ} {Z : Finset M.stellar.Face}
    (h : ∀ f, mem (bz + M.stFn c f) = if f ∈ Z then 1 else 0) :
    (∀ x, M.stellar.face (old x) ∈ Z ↔ mem (bz + c x) = 1) ∧
      (∀ x, M.stellar.face (old x) ∈ Zᶜ ↔ mem (bz + c x) = 0) := by
  have e : ∀ x, mem (bz + c x) = if M.stellar.face (old x) ∈ Z then 1 else 0 := fun x => by
    have := h (M.stTri x)
    rwa [stFn_stTri] at this
  refine ⟨fun x => ?_, fun x => ?_⟩ <;> rw [e x] <;> by_cases hx : M.stellar.face (old x) ∈ Z <;>
    simp [hx]

end Conc

section Side

open PlanarSeparator.MillerProg Orbit BKMNW

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

set_option maxHeartbeats 1000000 in
/-- **The walk of the cycle bounding a side, for the one-face instance of the side.** In the
setting of `side_faceInst` (a side `Z` of the stellar subdivision of the piece map of `K`, bounded
by the simple cycle `C`), from the plain encoding (`Enc`) of the piece map and the marks of its
darts (`z[x] = sv` iff the triangle of `x` is in `Z`), all below `T₀`, `faceWalk` ends within
`72 m + 13 C.k + 18` steps with `r829 = C.k`, the memory below `T₀` and from
`T₀ + 3 (nV + nF) + 6 m` on unchanged, and a one-face instance of the side (as `side_faceInst`,
its face started at the first dart of the walk) such that the position written at
`T₀ + 2 (nV + nF) + vn (ψ b)` for a source `b` is its position on the face: the hypothesis `hpos`
of `cornerProg_face` (with `ν b = vn (ψ b)`). The darts of the walk, along the cycle `C'` of
`side_faceInst`, are numbered (`stCode`) at `T₀ + 3 (nV + nF)`. -/
theorem faceWalk_faceInst (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K))
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) {bα bφ bφi bvn bfn bz sv T₀ : ℕ} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem bα bφ bφi bvn bfn)
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hlay : bα + m ≤ T₀ ∧ bφ + m ≤ T₀ ∧ bφi + m ≤ T₀ ∧ bvn + m ≤ T₀ ∧ bfn + m ≤ T₀ ∧
      bz + m ≤ T₀)
    (hW : T₀ + 3 * (nV + nF) + 6 * m + 3 ≤ W) (hw : WordsBounded W c₀)
    (h10 : c₀.nreg 10 = 1) (h800 : c₀.nreg 800 = m) (h801 : c₀.nreg 801 = bα)
    (h802 : c₀.nreg 802 = bφ) (h803 : c₀.nreg 803 = bφi) (h804 : c₀.nreg 804 = bvn)
    (h805 : c₀.nreg 805 = bfn) (h806 : c₀.nreg 806 = bz) (h807 : c₀.nreg 807 = nV)
    (h808 : c₀.nreg 808 = nF) (h809 : c₀.nreg 809 = sv) (h810 : c₀.nreg 810 = T₀) :
    ∃ c' t, Exec P W faceWalk c₀ c' t ∧ t ≤ 72 * m + 13 * C.k + 18 ∧ c'.nreg 829 = C.k ∧
      SFr 820 840 c₀ c' ∧
      (∀ a, a < T₀ ∨ T₀ + 3 * (nV + nF) + 6 * m ≤ a → c'.nmem a = c₀.nmem a) ∧
      ∃ (C' : (kst N K).SCycle) (i₀ : ℕ), C'.k = C.k ∧ (∀ δ, C'.Mem δ ↔ C.Mem δ) ∧
        (∀ i < C.k, Out Z (C'.d i)) ∧ i₀ < C.k ∧
        (∀ t < C.k, c'.nmem (T₀ + 3 * (nV + nF) + t) = (kmap N K).stCode c (C'.d ((i₀ + t) % C.k))) ∧
      ∃ (DQ VQ FQ : Type u) (_ : Fintype DQ) (_ : DecidableEq DQ) (_ : Fintype VQ)
        (_ : DecidableEq VQ) (_ : Fintype FQ) (_ : DecidableEq FQ) (Q : CombMap DQ VQ FQ)
        (g : ℕ → DQ) (P' : Finset D) (e : D → DQ) (j : V → VQ),
        FaceInst N (side N K Z ∪ R) Bs (18 * K.card) C.k Q g P' e j ∧
        (∀ t < C.k, ∀ v, (kst N K).vert (C'.d ((i₀ + t) % C.k)) = .inl (ψ v) →
          Q.tail (g t) = j v) ∧
        ∀ b ∈ Bs, c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) < C.k ∧
          Q.tail (g (c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)))) = j b := by
  obtain ⟨C', hk', hmem', hout', DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hFI, hpC⟩ :=
    side_faceInst hM hrot hface hKr hK0 hK hψ hbd hBs hR
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  set A := wArr c₀.nmem sv nV bα bφ bφi bvn bfn bz with hA
  obtain ⟨e1, e2, e3, e4, e5⟩ := enc_lt hE
  have hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W :=
    ⟨e1, e2, e3, e4, e5, l1, l2, l3, l4, l5, l6, hW⟩
  have hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c₀ :=
    ⟨h10, h800, h801, h802, h803, h804, h805, h806, h807, h808, h809, h810,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩
  have hY := wCyc_of (nV := nV) (sv := sv) (bz := bz) hE hz hbd hmem' (hk' ▸ hout')
  have hkpos : 0 < C'.k := C'.pos
  obtain ⟨c', s, i₀, ex, hs, hi₀, r829, fr, wP, wC, -, wo⟩ :=
    faceWalk_exec (P := P) hL hY hkpos c₀ hw hC
  rw [hk'] at hs hi₀ r829 wP wC
  have htlS : ∀ i, A.tlS ((kmap N K).stCode c (C'.d i)) = (kmap N K).stVi vn fn
      ((kst N K).vert (C'.d i)) := fun i => (wArr_st hE hz (C'.d i)).2.1
  refine ⟨c', s, ex, hs, r829, fr, wo, C', i₀, hk', hmem', hout', hi₀, wC, DQ, VQ, FQ, i1, i2,
    i3, i4, i5, i6, Q, _, P', e, j, hFI.shift hi₀,
    fun t ht v hv => hpC _ (Nat.mod_lt _ C.pos) v hv, fun b hb => ?_⟩
  -- the position of a source on the cycle
  obtain ⟨i, hi, hvi⟩ : ∃ i < C.k, (kst N K).vert (C'.d i) = .inl (ψ b) := by
    obtain ⟨i, hi, hvi⟩ := C.mem_verts.1 (hBs b hb).2
    obtain ⟨i', hi', h1 | h1⟩ := (hmem' (C.d i)).2 ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i', hk' ▸ hi', by rw [← h1]; exact hvi⟩
    · refine ⟨(i' + 1) % C'.k, hk' ▸ Nat.mod_lt _ C'.pos, ?_⟩
      rw [← C'.vert_α i' hi', ← h1]; exact hvi
  obtain ⟨t, ht, et⟩ := exists_shift_idx hi₀ hi
  have hP : c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) = t := by
    have := wP t ht
    rw [et, htlS i, hvi, stVi_inl] at this
    exact this
  rw [hP]
  exact ⟨ht, by rw [et]; exact hpC i hi b hvi⟩

end Side


/-! ### The cycle of the separator run -/

section SepCyc

open PlanarSeparator.MillerProg Orbit BKMNW Classical

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

set_option maxHeartbeats 4000000 in
/-- **The separator run with its cycle exposed.** As `sep_run_split_full`, and the run leaves the
marks of both sides in the form of `faceWalk_faceInst` (`sv = 1` for `Z`, `sv = 0` for `Zᶜ`), the
simple cycle `C` bounding both sides (`hbd` of `faceWalk_faceInst` for `Z` and `Zᶜ`), and the
shared vertices on both sides and on `C` (`hBs` of `faceWalk_faceInst` for both sides). -/
theorem sep_run_cyc (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (hm1 : 1 ≤ m)
    {W : ℕ} {P : Input} {B₀ : ℕ} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m))
    (hfl : ∀ d, c₀.nmem (B₀ + 5 * m + c d) = flK N K d)
    (hB : aEnd10 (3 * m) (nV + nF + m) ≤ B₀) (hW : B₀ + 23 * m + nV + nF + 2 ≤ W)
    (hc : WordsBounded W c₀) (h390 : c₀.nreg 390 = m) (h391 : c₀.nreg 391 = nV)
    (h392 : c₀.nreg 392 = nF) (h393 : c₀.nreg 393 = B₀) :
    ∃ c' t, Exec P W (sepRun prog10) c₀ c' t ∧
      t ≤ (1746 * K.card + 156) * (Nat.log 2 K.card + 3) + 16772 * K.card + 1849 ∧
      ∃ (C : (kst N K).SCycle) (Z : Finset (kst N K).Face),
        (∀ x, (kst N K).face (old x) ∈ Z ↔ c'.nmem (B₀ + 22 * m + c x) = 1) ∧
        (∀ x, (kst N K).face (old x) ∈ Zᶜ ↔ c'.nmem (B₀ + 22 * m + c x) = 0) ∧
        (∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ) ∧
        (∀ δ, ((kst N K).face δ ∈ Zᶜ ↔ (kst N K).face ((kst N K).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ) ∧
        (∀ b ∈ bdry N (side N K Z) (side N K Zᶜ), b ∈ verts N (side N K Z) ∧
          b ∈ verts N (side N K Zᶜ) ∧ Sum.inl (ψ b) ∈ C.verts) ∧
        side N K Z ∪ side N K Zᶜ = K ∧ Disjoint (side N K Z) (side N K Zᶜ) ∧
        C.k ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
        3 * (side N K Z).card ≤ 2 * K.card + 12 * C.k ∧
        3 * (side N K Zᶜ).card ≤ 2 * K.card + 12 * C.k ∧
        (bdry N (side N K Z) (side N K Zᶜ)).card ≤ C.k := by
  obtain ⟨d₀, hd₀⟩ := hK0
  have hd₀' : d₀ ∈ rcl N K := subset_rcl K hd₀
  have hfl0 : 0 < flK N K ⟨d₀, hd₀'⟩ := by simp [flK, hd₀]
  have hS := kmap_isPlane hM hrot hface ⟨d₀, hd₀⟩ hK
  have hl := kmap_loopless hrot hKr
  have hX := prog10_spec10 (P := P) (W := W) (kmap N K) c vn fn (flK N K) hm1 hS hl (flK_le K)
    hfl0 hB (by omega)
  have hB' : aEnd (3 * m) (nV + nF + m) ≤ B₀ := by unfold aEnd10 at hB; omega
  obtain ⟨c', t, e, ht, C, Z, hmk, hk, hsep, hin, hout⟩ :=
    sepRun_exec (P := P) (W := W) (kmap N K) c vn fn (flK N K) hm1 hS hl (flK_le K) hE hfl hB'
      hW hc h390 h391 h392 h393 hX
  rw [flagS_flK] at hin hout
  have hcardP : Fintype.card (SVert (kσ N K) (rcl N K) ⊕ (kmap N K).Face) = nV + nF := by
    rw [Fintype.card_sum, Fintype.card_congr vn, Fintype.card_congr fn, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := exists_cycle_cut_of hM hrot hface hKr ⟨d₀, hd₀⟩ hK
    (C := C) (Z := Z) (by rw [hcardP]; exact hk) hsep hin hout
  obtain ⟨z1, z2⟩ := marks_sides hmk
  refine ⟨c', t, e, ?_, C, Z, z1, z2, hsep.bd, bd_compl hsep.bd, fun b hb =>
    ⟨(mem_inter.1 hb).1, (mem_inter.1 hb).2, mem_cycle_of_bdry hψ hsep hb⟩, h1, h2, h3, h4, h5,
    h6⟩
  -- the sizes in terms of `|K|`
  set κ := K.card with hκ
  have hκ1 : 1 ≤ κ := card_pos.2 ⟨d₀, hd₀⟩
  have hc1 : Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face ≤
      2 * (rcl N K).card := card_pieceSep_le _ _
  have hc2 := card_rcl_le (N := N) K
  have hcm : m = (rcl N K).card := by
    rw [← Fintype.card_fin m, ← Fintype.card_congr c]; exact Fintype.card_coe _
  have hcV : nV = Fintype.card (SVert (kσ N K) (rcl N K)) := by
    rw [← Fintype.card_fin nV, ← Fintype.card_congr vn]
  have hcF : nF = Fintype.card (kmap N K).Face := by
    rw [← Fintype.card_fin nF, ← Fintype.card_congr fn]
  have hm2 : m ≤ 2 * κ := by omega
  have hn6 : nV + nF + m ≤ 6 * κ := by omega
  have hlog : Nat.log 2 (nV + nF + m) ≤ Nat.log 2 κ + 3 := by
    have h8 : Nat.log 2 (κ * 2 * 2 * 2) = Nat.log 2 κ + 3 := by
      rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
        Nat.log_mul_base (by norm_num) (by omega)]
    rw [← h8]; exact Nat.log_mono_right (by omega)
  have hmul : (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) ≤
      (1746 * κ + 156) * (Nat.log 2 κ + 3) := Nat.mul_le_mul (by omega) hlog
  unfold T10 at ht
  have hexp : (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) =
      (693 * m + 60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) +
        4 * Nat.log 2 (nV + nF + m) := by ring
  clear * - ht hmul hexp hm2 hn6
  generalize (693 * m + 60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) = P₁ at ht hexp
  generalize (693 * m + 60 * (nV + nF + m) + 156) * Nat.log 2 (nV + nF + m) = P₂ at hmul hexp
  generalize Nat.log 2 (nV + nF + m) = A at ht hexp
  generalize (1746 * κ + 156) * (Nat.log 2 κ + 3) = Q at hmul ⊢
  omega

end SepCyc

end NegSSSP

end PlanarFlow
