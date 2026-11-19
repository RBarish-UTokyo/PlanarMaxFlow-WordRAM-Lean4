module

public import PlanarFlow.BKMNW.SmSegsC
public import PlanarFlow.BKMNW.SgSem

/-!
# `SegsOut'` for the small separator: the start vertices of the parts

* **`smD_node_vert`** (pure): at a node of `smD`, a part `σ` with `σ.k = 0` (`peelSep`'s point, the
  pendant edge's point) has its vertex `v = σ.p 0` off the holes, on the path, the only vertex of
  the path off the holes, and the tail of a dart of the piece map;
* `SegsOut.congr'` (`SegsOut` reads only `[Gb, Gb + 1 + 2 s + L)`);
* **`smV`** (after `smSegs`): `VH[i] = VF[i] · [HL[i] = 0]` on the frame (`VF` the path's vertex
  flags at `Sb + 2 m`, `HL` the frame's hole labels at `d + 4 + 5 m`), a compaction (`lkProg`),
  then `mem (Gb + 3 + k₀) := k₀ · mem (Gb + 3) + (1 - k₀) · IXV[0]` (`k₀ = mem (Gb + 2)`, the
  darts of the part); registers `7240 … 7249`, `6300 … 6309`, `6520 … 6529`; scratch
  `[Gb + 5 + 2 m + 2 k, Gb + 5 + 5 m + 2 k)`; **`smV_exec`** (`24 m + 60` steps);
* **`segsOut'_sm`** (pure): the memory after `smSegs ; smV` is `SegsOut'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset

section Pure

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The vertex of a part without darts of a node of `smD`** (see the module docstring). -/
theorem smD_node_vert {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) {P : Finset D} {Hs : List (Finset V)}
    {l r : ADec M} {π : HSep M} (h : smD M pk S T P Hs = .node l r π) :
    ∀ σ ∈ π.segs, σ.k = 0 → σ.p 0 ∉ hunion Hs ∧ σ.p 0 ∈ π.path.mverts ∧
      (∀ w ∈ π.path.mverts, w ∉ hunion Hs → w = σ.p 0) ∧
      ∃ y ∈ pdarts M P Hs, M.tail y = σ.p 0 := by
  rw [smD] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9
  -- the peel
  · injection h with _ _ eπ
    subst eπ
    intro σ hσ hk
    simp only [peelSep, List.mem_singleton] at hσ
    subst hσ
    obtain ⟨hxP, hxt, hxh⟩ := mem_filter.1 (hpk _ h2)
    have hm : (peelSep _ h3).path.mverts = {M.tail (pk (smX M S T P Hs)),
        M.head (pk (smX M S T P Hs))} := HPath.toH_ofDart_mverts _ h3
    rw [hm]
    refine ⟨fun hh => hxt (mem_union_right _ hh), mem_insert_self _ _, fun w hw hwh => ?_,
      _, hxP, rfl⟩
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rfl
    · exact absurd hxh hwh
  -- the dump
  · injection h with _ _ eπ
    subst eπ
    intro σ hσ; simp [holeSep] at hσ
  -- the pendant edge at a terminal
  · injection h with _ _ eπ
    subst eπ
    have hB : (smB M S T P Hs).Nonempty := by
      push Not at h1; obtain ⟨-, d, hd, hb⟩ := h1; exact ⟨d, mem_filter.2 ⟨hd, hb⟩⟩
    obtain ⟨hyP, hyt⟩ := mem_filter.1 (hpk _ hB)
    intro σ hσ hk
    simp only [SPath.toSep, List.mem_singleton] at hσ
    subst hσ
    have hm : (SPath.point (M' := M) (pk (smB M S T P Hs))
        (M.tail (pk (smB M S T P Hs)))).toSep.path.mverts = {M.tail (pk (smB M S T P Hs))} :=
      HPath.toH_point_mverts _ _
    rw [hm]
    refine ⟨fun hh => hyt (mem_union_right _ hh), mem_singleton_self _, fun w hw _ => ?_,
      _, hyP, rfl⟩
    exact mem_singleton.1 hw
  -- the edge: its part has a dart
  · injection h with _ _ eπ
    subst eπ
    intro σ hσ hk
    simp only [SPath.toSep, List.mem_singleton] at hσ
    subst hσ
    simp [SPath.ofDart] at hk

end Pure

namespace MfDrv

open Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

section Congr

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- `SegsOut` reads only `[Gb, Gb + 1 + 2 s + L)`. -/
lemma SegsOut.congr' {en : ℕ → D} {m : ℕ} {π : HSep M} {lo hi Gb : ℕ} {mem mem' : ℕ → ℕ}
    (h : SegsOut M en m π lo hi Gb mem)
    (he : ∀ a, Gb ≤ a → a < Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum →
      mem' a = mem a) :
    SegsOut M en m π lo hi Gb mem' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [he _ le_rfl (by omega)]; exact h2, h3, fun j hj => ?_⟩
  obtain ⟨g1, g2, g3⟩ := h4 j hj
  have hk : ((π.segs.take j).map SPath.k).sum + (π.segs[j]).k ≤ (π.segs.map SPath.k).sum := by
    have e : π.segs.take (j + 1) = π.segs.take j ++ [π.segs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    have := sum_take_le_sum (π.segs.map SPath.k) (j + 1)
    rw [← List.map_take, e, List.map_append, List.sum_append] at this
    simpa using this
  refine ⟨by rw [he _ (by omega) (by omega)]; exact g1, by rw [he _ (by omega) (by omega)]; exact g2,
    fun l hl => ?_⟩
  rw [he _ (by omega) (by omega)]
  exact g3 l hl

end Congr

/-- The bases of `smV`. -/
def smV0 : Stmt :=
  block [.loadN 7240 3004, .constN 7241 1, .addN 7242 3004 7241, .loadN 7243 7242,
    .addN 7244 7240 7240, .addN 7244 7244 7244, .addN 7244 7244 7240, .addN 7244 7244 3004,
    .constN 7241 4, .addN 7244 7244 7241, .addN 7245 3120 7240, .addN 7245 7245 7240,
    .addN 7246 6502 7240, .addN 7246 7246 7240, .addN 7246 7246 7243, .addN 7246 7246 7243,
    .constN 7241 5, .addN 7246 7246 7241, .copyN 6300 7240, .copyN 6301 7246,
    .addN 6302 7246 7240, .addN 6303 6302 7240, .constN 6521 1]

/-- `VH[i] = VF[i] · (1 - HL[i] / HL[i])`. -/
def vbSV : Stmt :=
  block [.addN 6524 7245 6520, .loadN 6524 6524, .addN 6525 7244 6520, .loadN 6525 6525,
    .divN 6526 6525 6525, .subN 6526 6521 6526, .mulN 6523 6524 6526]

/-- The store of the start vertex. -/
def smV1 : Stmt :=
  block [.constN 7241 2, .addN 7247 6502 7241, .loadN 7247 7247, .constN 7241 3,
    .addN 7248 6502 7241, .addN 7248 7248 7247, .loadN 7249 6303, .addN 7242 6502 7241,
    .loadN 7242 7242, .mulN 7242 7242 7247, .constN 7241 1, .subN 7243 7241 7247,
    .mulN 7249 7249 7243, .addN 7249 7249 7242, .storeN 7248 7249]

/-- **The start vertex of the small part.** -/
def smV : Stmt := .seq smV0 (.seq (mapRunS vbSV 7240 7246) (.seq lkProg smV1))

/-- The value of `vbSV`. -/
def vhF (v h : ℕ) : ℕ := v * (1 - h / h)

lemma vhF_pos {v h : ℕ} (hv : v ≤ 1) : 0 < vhF v h ↔ v = 1 ∧ h = 0 := by
  unfold vhF
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp; omega
  · rw [Nat.div_self hh]; simp; omega

section Exec

variable {P : Input} {W : ℕ}

theorem smV0_exec (c : Config) (hc : WordsBounded W c) {d Sb Gb m k : ℕ}
    (r04 : c.nreg 3004 = d) (r20 : c.nreg 3120 = Sb) (r02 : c.nreg 6502 = Gb)
    (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k) (l1 : d + 4 + 6 * m ≤ Gb)
    (l2 : Sb + 3 * m ≤ Gb) (w : Gb + 5 + 5 * m + 2 * k ≤ W) :
    ∃ c' t, Exec P W smV0 c c' t ∧ t = 23 ∧ c'.nreg 7240 = m ∧ c'.nreg 7244 = d + 4 + 5 * m ∧
      c'.nreg 7245 = Sb + 2 * m ∧ c'.nreg 7246 = Gb + 5 + 2 * m + 2 * k ∧
      c'.nreg 6300 = m ∧ c'.nreg 6301 = Gb + 5 + 2 * m + 2 * k ∧
      c'.nreg 6302 = Gb + 5 + 3 * m + 2 * k ∧ c'.nreg 6303 = Gb + 5 + 4 * m + 2 * k ∧
      c'.nreg 6521 = 1 ∧ c'.nmem = c.nmem ∧
      (∀ x, (x < 6300 ∨ (6303 < x ∧ x ≠ 6521 ∧ x < 7240) ∨ 7246 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smV0
  exec_block
  all_goals try (config_simp; (try simp only [r04, r20, r02, hm, hk]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r04, r20, r02, hm, hk]); done)
  all_goals try (config_simp; (try simp only [r04, r20, r02, hm, hk]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other])

theorem vbSV_exec (c : Config) (hc : WordsBounded W c) {i VFb HLb v h : ℕ}
    (r20 : c.nreg 6520 = i) (r45 : c.nreg 7245 = VFb) (r44 : c.nreg 7244 = HLb)
    (r21 : c.nreg 6521 = 1) (hv : c.nmem (VFb + i) = v) (hh : c.nmem (HLb + i) = h)
    (hv1 : v ≤ 1) (w1 : VFb + i ≤ W) (w2 : HLb + i ≤ W) :
    ∃ c' k, Exec P W vbSV c c' k ∧ k ≤ 7 ∧ c'.nreg 6523 = vhF v h ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 : h / h ≤ 1 := sg_nz_le h
  have b2 : v * (1 - h / h) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hv1 with rfl | rfl <;> simp
  have b3 := hc.1 6521
  unfold vbSV
  exec_block
  all_goals try (config_simp; (try simp only [r20, r45, r44, r21, hv, hh]); omega)
  refine ⟨by norm_num, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r20, r45, r44, r21, hv, hh, vhF]
  · have := vb_frame_aux hx
    config_simp
    simp (disch := omega) only [upd_other]

theorem smV1_exec (c : Config) (hc : WordsBounded W c) {Gb k0 x0 v Y : ℕ}
    (r02 : c.nreg 6502 = Gb) (r03 : c.nreg 6303 = Y)
    (h2 : c.nmem (Gb + 2) = k0) (h3 : c.nmem (Gb + 3) = x0) (hY : c.nmem Y = v) (hk0 : k0 ≤ 1)
    (w : Gb + 4 ≤ W) (wY : Y ≤ W) :
    ∃ c' t, Exec P W smV1 c c' t ∧ t = 15 ∧
      c'.nmem = upd c.nmem (Gb + 3 + k0) (v * (1 - k0) + x0 * k0) ∧
      (∀ x, (x < 7241 ∨ 7249 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have bx := hc.2 (Gb + 3)
  have bv := hc.2 Y
  rw [h3] at bx; rw [hY] at bv
  have m1 : x0 * k0 ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk0 with rfl | rfl <;> simp <;> omega
  have m2 : v * (1 - k0) ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk0 with rfl | rfl <;> simp <;> omega
  have m3 : v * (1 - k0) + x0 * k0 ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk0 with rfl | rfl <;> simp <;> omega
  unfold smV1
  exec_block
  all_goals try (config_simp; (try simp only [r02, r03, h2, h3, hY]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r02, r03, h2, h3, hY]
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 2000000 in
/-- **The start vertex of the small part** (see the module docstring). -/
theorem smV_exec (c : Config) (hc : WordsBounded W c) {d Sb Gb m k : ℕ}
    (r04 : c.nreg 3004 = d) (r20 : c.nreg 3120 = Sb) (r02 : c.nreg 6502 = Gb)
    (hm : c.nmem d = m) (hk : c.nmem (d + 1) = k) (hk0 : c.nmem (Gb + 2) ≤ 1)
    (hv1 : ∀ i < m, c.nmem (Sb + 2 * m + i) ≤ 1)
    (lay : d + 4 + 6 * m ≤ Gb ∧ Sb + 3 * m ≤ Gb ∧ Gb + 5 + 5 * m + 2 * k ≤ W) :
    ∃ c' t, Exec P W smV c c' t ∧ t ≤ 24 * m + 60 ∧
      (∃ v, c'.nmem (Gb + 3 + c.nmem (Gb + 2)) =
          v * (1 - c.nmem (Gb + 2)) + c.nmem (Gb + 3) * c.nmem (Gb + 2) ∧
        ∀ i < m, 0 < vhF (c.nmem (Sb + 2 * m + i)) (c.nmem (d + 4 + 5 * m + i)) →
          cnt (fun j => vhF (c.nmem (Sb + 2 * m + j)) (c.nmem (d + 4 + 5 * m + j))) i = 0 →
          v = i) ∧
      (∀ a, a ≠ Gb + 3 + c.nmem (Gb + 2) → ¬ (Gb + 5 + 2 * m + 2 * k ≤ a ∧
        a < Gb + 5 + 5 * m + 2 * k) → c'.nmem a = c.nmem a) ∧
      c'.nreg 6502 = Gb ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 7240) ∨ 7249 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  unfold smV
  obtain ⟨c₁, t₁, e₁, ht₁, a40, a44, a45, a46, a0, a1, a2, a3, a21, m1, n1, rr1, rm1, o1⟩ :=
    smV0_exec (P := P) c hc r04 r20 r02 hm hk l1 l2 l3
  set VH : ℕ → ℕ := fun j => vhF (c.nmem (Sb + 2 * m + j)) (c.nmem (d + 4 + 5 * m + j)) with hVH
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := mapRun_exec (P := P) c₁ e₁.wb_right
    (vb := vbSV) (bnd := 7240) (ob := 7246) (m := m) (Ob := Gb + 5 + 2 * m + 2 * k) (B := 7) VH
    a40 a21 a46 (by omega) (by omega) (by unfold vscr; omega) (by unfold vscr; omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm' => by
      obtain ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩ := vbSV_exec (P := P) c' hw h20
        ((hr 7245 (by unfold vscr; omega) (by omega) (by omega)).trans a45)
        ((hr 7244 (by unfold vscr; omega) (by omega) (by omega)).trans a44)
        ((hr 6521 (by unfold vscr; omega) (by omega) (by omega)).trans a21)
        (v := c.nmem (Sb + 2 * m + i)) (h := c.nmem (d + 4 + 5 * m + i))
        (by rw [hm' _ (by omega), m1]) (by rw [hm' _ (by omega), m1]) (hv1 i hi) (by omega)
        (by omega)
      exact ⟨c'', k', e', hk', v, nn, mm, rr, rm, oo⟩)
  have q2 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₂.nreg x = c₁.nreg x := fn2
  obtain ⟨c₃, t₃, e₃, ht₃, d6, dIX, dm, dn, dr, drm, do'⟩ := lkProg_exec (P := P) c₂ e₂.wb_right
    ((q2 6300 (by unfold vscr; omega) (by omega) (by omega)).trans a0)
    ((q2 6301 (by unfold vscr; omega) (by omega) (by omega)).trans a1)
    ((q2 6302 (by unfold vscr; omega) (by omega) (by omega)).trans a2)
    ((q2 6303 (by unfold vscr; omega) (by omega) (by omega)).trans a3) (by omega) (by omega)
    (by omega) (by omega)
  have hF : ∀ j < m, c₂.nmem (Gb + 5 + 2 * m + 2 * k + j) = VH j := f2
  have hc3 : ∀ i ≤ m, cnt (fun j => c₂.nmem (Gb + 5 + 2 * m + 2 * k + j)) i = cnt VH i :=
    fun i hi => cnt_ext fun j hj => hF j (by omega)
  have m3 : ∀ a, a < Gb + 5 + 2 * m + 2 * k → c₃.nmem a = c.nmem a := fun a ha => by
    rw [dm a (by omega), fm2 a (by omega), m1]
  have r3 : ∀ x, (x < 6304 ∨ 6309 < x) → ¬ vscr x → x ≠ 6522 → x ≠ 6520 →
      c₃.nreg x = c₁.nreg x := fun x h1 h2 h3 h4 => by rw [dn x h1, q2 x h2 h3 h4]
  obtain ⟨c₄, t₄, e₄, ht₄, gm, gn, gr, grm, go⟩ := smV1_exec (P := P) c₃ e₃.wb_right
    (Y := Gb + 5 + 4 * m + 2 * k) (v := c₃.nmem (Gb + 5 + 4 * m + 2 * k))
    ((r3 6502 (by omega) (by unfold vscr; omega) (by omega) (by omega)).trans
      ((n1 6502 (by omega)).trans r02))
    ((r3 6303 (by omega) (by unfold vscr; omega) (by omega) (by omega)).trans a3)
    (m3 _ (by omega)) (m3 _ (by omega)) rfl hk0 (by omega) (by omega)
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_,
    ⟨c₃.nmem (Gb + 5 + 4 * m + 2 * k), by rw [gm, upd_same], fun i hi hpos h0 => ?_⟩,
    fun a h1 h2 => ?_, ?_, fun x hx => ?_, by rw [gr, dr, fr2, rr1], by rw [grm, drm, frm2, rm1],
    by rw [go, do', fo2, o1]⟩
  · clear * - ht₁ ht₂ ht₃ ht₄; omega
  · have := (dIX i hi (by rw [hF i hi]; exact hpos)).2
    rw [hc3 i hi.le, h0, Nat.add_zero] at this
    exact this
  · rw [gm, upd_other _ _ _ h1, dm a (by omega),
      fm2 a (by omega), m1]
  · rw [gn _ (by omega), r3 _ (by omega) (by unfold vscr; omega) (by omega) (by omega),
      n1 _ (by omega)]; exact r02
  · rw [gn x (by omega), r3 x (by omega) (by unfold vscr; omega) (by omega) (by omega),
      n1 x (by omega)]

end Exec

section SemV

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma smD_segs_len {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) {P : Finset D} {Hs : List (Finset V)}
    (hrc : RevClosed M P) {l r : ADec M} {π : HSep M} (h : smD M pk S T P Hs = .node l r π) :
    π.segs = [] ∨ ∃ σ, π.segs = [σ] := by
  rcases smD_node_segs hpk hrc h with h1 | h2 | h3 | h4
  · exact Or.inl h1.1
  · obtain ⟨y, v, e⟩ := h2.2.2; exact Or.inr ⟨_, e⟩
  · obtain ⟨y, v, e⟩ := h3.2.2; exact Or.inr ⟨_, e⟩
  · obtain ⟨x, hx, -, -, -, -, e⟩ := h4.2; exact Or.inr ⟨_, e⟩

/-- **`smSegs ; smV` write `SegsOut'`** (see the module docstring). -/
theorem segsOut'_sm {gid : D → ℕ} {pk : Finset D → D} {S T : Finset V} (hpk : PkMin gid pk)
    {P : Finset D} {Hs : List (Finset V)} (hrc : RevClosed M P) {l r : ADec M} {π : HSep M}
    (hsm : smD M pk S T P Hs = .node l r π) {en : ℕ → D} {m : ℕ}
    (hem : ∀ i < m, en i ∈ pdarts M P Hs) (hes : ∀ y ∈ pdarts M P Hs, ∃ i < m, en i = y)
    (hmono : ∀ i j, i < j → j < m → gid (en i) < gid (en j)) {PF HF VF HL mem₀ mem : ℕ → ℕ}
    (hPF : ∀ i < m, PF i = bf (en i ∈ π.path.darts.toFinset))
    (hHF : ∀ j < Hs.length, HF j = bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts))
    (hVF : ∀ i < m, VF i = bf (M.tail (en i) ∈ π.path.mverts))
    (hHL : ∀ i < m, HL i = hlab Hs (M.tail (en i)))
    {lo hi Gb : ℕ} (hlo : lo ≤ Gb) (hhi : Gb + 5 ≤ hi)
    (m0 : mem₀ Gb = sgS (cnt PF m) (cnt HF Hs.length)) (m1 : mem₀ (Gb + 1) = 0)
    (m2 : mem₀ (Gb + 2) = sgK (cnt PF m) (cnt HF Hs.length))
    (m3 : ∀ i < m, 0 < PF i → cnt PF i = 0 → mem₀ (Gb + 3) = i)
    (hkeep : ∀ a, Gb ≤ a → a < Gb + 3 + mem₀ (Gb + 2) → mem a = mem₀ a)
    (hV : ∃ v, mem (Gb + 3 + mem₀ (Gb + 2)) =
        v * (1 - mem₀ (Gb + 2)) + mem₀ (Gb + 3) * mem₀ (Gb + 2) ∧
      ∀ i < m, 0 < vhF (VF i) (HL i) → cnt (fun j => vhF (VF j) (HL j)) i = 0 → v = i) :
    SegsOut' M en m π lo hi Gb mem := by
  have hpk' : ∀ X : Finset D, X.Nonempty → pk X ∈ X := fun X hX => (hpk X hX).1
  have hS := segsOut_sm hpk hrc hsm hem hes hmono hPF hHF hlo (show Gb + 4 ≤ hi by omega) m0 m1 m2 m3
  have hk0 : mem₀ (Gb + 2) ≤ 1 := by rw [m2, sgK_eq]; split_ifs <;> omega
  obtain ⟨-, hS0, hS1, hS2⟩ := id hS
  rcases smD_segs_len hpk' hrc hsm with e | ⟨σ, e⟩
  · refine ⟨SegsOut.congr' hS fun a h1 h2 => hkeep a h1 ?_, ?_, fun j hj => ?_⟩
    · rw [e] at h2; simp only [List.length_nil, List.map_nil, List.sum_nil] at h2; omega
    · rw [e]; simp; omega
    · rw [e] at hj; simp at hj
  · have hl : π.segs.length = 1 := by rw [e]; rfl
    obtain ⟨o1, o2, o3⟩ := hS2 0 (by omega)
    have ek : (π.segs[0]).k = σ.k := by simp [e]
    have hsum : (π.segs.map SPath.k).sum = σ.k := by rw [e]; simp
    have hk : mem₀ (Gb + 2) = σ.k := by
      have h' := o2; rw [ek] at h'
      rwa [show Gb + 1 + π.segs.length + 0 = Gb + 2 by rw [hl]] at h'
    refine ⟨SegsOut.congr' hS fun a h1 h2 => hkeep a h1 ?_, ?_, fun j hj => ?_⟩
    · rw [hl, hsum] at h2; omega
    · rw [hl, hsum]; omega
    · obtain rfl : j = 0 := by omega
      rw [show Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + 0 =
        Gb + 3 + mem₀ (Gb + 2) by rw [hl, hsum]; omega]
      obtain ⟨v, hv1, hv2⟩ := hV
      have hσ : π.segs[0] = σ := by simp [e]
      rw [hσ, hv1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk0 with h0 | h1
      · -- a part without darts: the least frame dart with its tail on the path off the holes
        rw [h0] at hk ⊢
        simp only [Nat.sub_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
        obtain ⟨hvh, hvm, huniq, y, hy, hyt⟩ := smD_node_vert hpk' hsm σ (by rw [e]; simp)
          hk.symm
        obtain ⟨i0, hi0, rfl⟩ := hes y hy
        have hpos0 : 0 < vhF (VF i0) (HL i0) := by
          rw [hVF i0 hi0, hHL i0 hi0, vhF_pos (bf_le_one7 _), hyt]
          refine ⟨by unfold bf; simp [hvm], ?_⟩
          by_contra hne; exact hvh (hlab_pos_iff.1 (Nat.pos_of_ne_zero hne))
        obtain ⟨i, hi, hpos, hc⟩ := cnt_surj (fun j => vhF (VF j) (HL j)) m 0
          (lt_of_lt_of_le (Nat.zero_lt_one) (by
            have := cnt_lt_of (fun j => vhF (VF j) (HL j)) hi0 hpos0
            have := cnt_mono (fun j => vhF (VF j) (HL j)) (show i0 + 1 ≤ m by omega)
            rw [cnt_succ, iteT hpos0] at this
            omega))
        rw [hv2 i hi hpos hc]
        refine ⟨hi, ?_⟩
        rw [hVF i hi, hHL i hi, vhF_pos (bf_le_one7 _)] at hpos
        obtain ⟨p1, p2⟩ := hpos
        have hm : M.tail (en i) ∈ π.path.mverts := by
          unfold bf at p1; split_ifs at p1 with hh; exact hh
        exact huniq _ hm fun hu => by have := hlab_pos_iff.2 hu; omega
      · -- the part of one dart: its dart
        rw [h1] at hk ⊢
        simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
        have h3 := o3 0 (by omega)
        rw [show Gb + 1 + 2 * π.segs.length + ((π.segs.take 0).map SPath.k).sum + 0 = Gb + 3 by
          rw [hl]; simp] at h3
        obtain ⟨b1, b2⟩ := h3
        rw [hσ] at b2
        refine ⟨b1, ?_⟩
        rw [b2]
        exact σ.tail_d 0 (by omega)

end SemV

end MfDrv

end BKMNW

end PlanarFlow
