module

public import PlanarFlow.BKMNW.NrFrB
public import PlanarFlow.BKMNW.NrWFrame
public import PlanarFlow.BKMNW.NpSeg

/-!
# The core of the push-backs `retP`, `frmP` at a call

**`fcore = fcA ; fcB ; fJ ; btL ; fK ; pchP`**: from the frame of a call (`r3004 = d`, scratch from
`b`, `r3006 = b + 5`), the part `j = r6800` of the separator (`SegsAtV`, base `r6807`) and the flag
value `kfr = r9185`: the bounds `Kd + β` (`β = 0` on `negSet g πj.verts`, `div g` elsewhere,
`btL`), the free flags `[KR = kfr]` and the push-back `pchP`.

* `foldl_push_inv`, **`pchCall_bnd`** (the push-back keeps the bound `|g| ≤ Z`);
* `fcCost m n = pchCost m n + 130 m + 170`;
* **`fcore_exec`**: the flow array becomes
  `Z + pchCall gid x h (fun v => if v ∈ negSet g πj.verts then 0 else div g v) Fr g` for any
  `Fr` described by `[lrk S T (holes) (tail) = kfr]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv Orbit

/-- **The core of `retP`/`frmP`.** -/
def fcore : Stmt := .seq fcA (.seq fcB (.seq fJ (.seq btL (.seq fK pchP))))

/-- The steps of the core. -/
def fcCost (m n : ℕ) : ℕ := pchCost m n + 130 * m + 170

/-- **The core never writes the registers of the driver and of the step.** -/
theorem fcA_dests : (Stmt.nDests fcA).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

theorem fcB_dests : (Stmt.nDests fcB).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

theorem fcore_dests : (Stmt.nDests fcore).all
    (fun x => decide (x < 3000 ∨ (3012 < x ∧ x < 6800) ∨ 6819 < x)) = true := by decide +kernel

section Gen

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

/-- The visits keep the antisymmetry and the conformality to an acyclic flow. -/
lemma foldl_push_inv {Mp : CombMap D' V' F'} {outs : V' → List D'} (houts : OutsOK Mp outs)
    (β : V' → ℤ) (Fr : Finset V') {g₀ : D' → ℤ} (ha₀ : Mp.IsAntisymm g₀)
    (hac : ∀ v, ¬ Relation.TransGen (Pos Mp g₀) v v) :
    ∀ (K : List V') (g : D' → ℤ), Mp.IsAntisymm g → Conf g₀ g →
      Mp.IsAntisymm (K.foldl (pushAtL Mp outs β Fr) g) ∧
        Conf g₀ (K.foldl (pushAtL Mp outs β Fr) g)
  | [], g, ha, hc => ⟨ha, hc⟩
  | v :: K, g, ha, hc => by
    obtain ⟨a, b⟩ := nr_push_inv houts β Fr ha₀ hac ha hc v
    exact foldl_push_inv houts β Fr ha₀ hac K _ a b

end Gen

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The machine's push-back keeps the bound `|g| ≤ Z`** and the antisymmetry. -/
theorem pchCall_bnd {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap h).IsPlane) (hm : 0 < m)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hZ : ∀ e, -(Z : ℤ) ≤ g e ∧ g e ≤ Z) (β : SVert x.2.2 (pdarts M x.1.piece x.2.1) → ℤ)
    (Fr : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))) :
    (pmap h).IsAntisymm (NsStep.pchCall gid x h β Fr g) ∧
      ∀ e, -(Z : ℤ) ≤ NsStep.pchCall gid x h β Fr g e ∧ NsStep.pchCall gid x h β Fr g e ≤ Z := by
  classical
  have hnd : ((List.range m).map (edF hL hm)).Nodup :=
    (List.nodup_range).map_on fun a ha b hb e => by
      have := congrArg Subtype.val e
      rw [edF_val hL hm (List.mem_range.1 ha), edF_val hL hm (List.mem_range.1 hb)] at this
      exact hL.en_inj (List.mem_range.1 ha) (List.mem_range.1 hb) this
  have hall : ∀ y, y ∈ (List.range m).map (edF hL hm) := fun y => by
    obtain ⟨i, hi, rfl⟩ := hL.edF_surj hm y
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  obtain ⟨a₀, c₀, -, ac₀⟩ := cancelR_spec hpl (frRef_spec _) ((pmap h).face (edF hL hm 0)) hg
  have hb₀ := nr_conf_bnd hg a₀ c₀ hZ
  rw [hL.pchCall_eq h hm]
  unfold pushFwdL
  obtain ⟨a₁, c₁⟩ := foldl_push_inv (outsL_ok hnd hall) β Fr a₀ ac₀ _ _ a₀ (Conf.refl _)
  exact ⟨a₁, nr_conf_bnd a₀ a₁ c₁ hb₀⟩

variable {P : Input} {W : ℕ}

lemma flHas_sum {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en mem g) :
    ∑ j ∈ range m, mem (d + 6 * m + 4 + j) ≤ 2 * (m * Z) := by
  have hZg := flHas_bnd hL h hg hfl
  calc ∑ j ∈ range m, mem (d + 6 * m + 4 + j) ≤ ∑ _j ∈ range m, 2 * Z :=
        sum_le_sum fun j hj => by
          have hj' := mem_range.1 hj
          have := hfl j hj'
          rw [fext_mem g (hL.en_mem j hj')] at this
          have := hZg ⟨en j, hL.en_mem j hj'⟩
          rw [show d + 6 * m + 4 + j = d + 4 + 6 * m + j by omega]; omega
    _ = 2 * (m * Z) := by rw [sum_const, card_range, smul_eq_mul]; ring

/-- The part flag from the marks. -/
lemma mkv_le (v₀ : ℕ) (val : ℕ → ℕ) (k v : ℕ) : mkv v₀ val k v ≤ 1 := by
  unfold mkv; split_ifs <;> omega

lemma mkv_eq_one {v₀ : ℕ} {val : ℕ → ℕ} {k v : ℕ} :
    mkv v₀ val k v = 1 ↔ v = v₀ ∨ ∃ l < k, val l = v := by
  unfold mkv; split_ifs with h <;> simp [h]

/-- The darts of a part listed by distinct frame indices: at most `m` of them. -/
lemma part_k_le {P : SPath M} {m : ℕ} {E : ℕ → ℕ} {en : ℕ → D}
    (hE : ∀ l < P.k, E l < m ∧ en (E l) = P.d l) : P.k ≤ m := by
  classical
  have := Finset.card_le_card_of_injOn E (s := range P.k) (t := range m)
    (fun l hl => mem_range.2 (hE l (mem_range.1 hl)).1)
    (fun a ha b hb e => by
      have ha' := mem_range.1 ha
      have hb' := mem_range.1 hb
      have h1 : P.d a = P.d b := by rw [← (hE a ha').2, ← (hE b hb').2, e]
      have h2 : P.p a = P.p b := by rw [← P.tail_d a ha', ← P.tail_d b hb', h1]
      exact P.inj a ha'.le b hb'.le h2)
  simpa using this

set_option maxHeartbeats 8000000 in
/-- **The core of `retP`/`frmP` at a call** (see the module docstring). -/
theorem fcore_exec {x : MCall M} {m : ℕ} {en : ℕ → D} {d b e j : ℕ} (c : Config)
    (hc : WordsBounded W c) (hL : Lay M gid u S T Z x m en d c.nmem)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane) (hm : 0 < m)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    (hfl : FLHas Z m d en c.nmem g) (r3004 : c.nreg 3004 = d) (r3006 : c.nreg 3006 = b + 5)
    {kfr : ℕ} (r85 : c.nreg 9185 = kfr) {Fr : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))}
    (hFr : ∀ i (hi : i < m), lrk S T (hunion x.2.1) (M.tail (en i)) = kfr ↔
      (pmap h).tail (vDart hL hi) ∈ Fr)
    {π : HSep M} (hS : SegsAtV M en m π e b c) (r6800 : c.nreg 6800 = j)
    (hj : j < π.segs.length) (hP : Disjoint (π.segs[j]).verts (hunion x.2.1))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (w : b + 40 * m + 10 ≤ W)
    (wK : 3 * (m * Z) + 3 * Z + 1 ≤ W) :
    ∃ c' t, Exec P W fcore c c' t ∧ t ≤ fcCost m (rcnt (olab (nxFP d m c.nmem)) m) ∧
      FLHas Z m d en c'.nmem (NsStep.pchCall gid x h
        (fun v => if v ∈ negSet (pmap h) g
            (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) then 0
          else (pmap h).div g v) Fr g) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < b ∨ b + 40 * m + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hZg := flHas_bnd hL h hg hfl
  have hFLs := flHas_sum hL h hg hfl
  have hA : d + 4 + 7 * m ≤ b := by unfold fsz at hde; omega
  -- the part
  obtain ⟨Gb, hGb⟩ : ∃ Gb, c.nreg 6807 = Gb := ⟨_, rfl⟩
  obtain ⟨⟨s1, s2, s3, s4⟩, s5, s6⟩ := hS
  rw [hGb] at s1 s2 s3 s4 s5 s6
  obtain ⟨ns, hns⟩ : ∃ ns, π.segs.length = ns := ⟨_, rfl⟩
  obtain ⟨L, hLs⟩ : ∃ L, (π.segs.map SPath.k).sum = L := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o, ((π.segs.take j).map SPath.k).sum = o := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, (π.segs[j]).k = k := ⟨_, rfl⟩
  have hjs : j < ns := by rw [← hns]; exact hj
  rw [hns, hLs] at s3 s5
  rw [hns] at s2
  obtain ⟨u1, u2, u3⟩ := s4 j hj
  simp only [ho, hns] at u1 u2 u3
  simp only [hk] at u2
  have hok : o + k ≤ L := by
    rw [← ho, ← hk, ← hLs]; exact sum_take_add_getElem π.segs hj
  have hns1 : ns - 1 < π.segs.length := by rw [hns]; omega
  obtain ⟨w1, w2, -⟩ := s4 (ns - 1) hns1
  have hLL : c.nmem (Gb + ns) + c.nmem (Gb + ns + ns) = L := by
    have e1 : Gb + 1 + (ns - 1) = Gb + ns := by omega
    have e2 : Gb + 1 + π.segs.length + (ns - 1) = Gb + ns + ns := by rw [hns]; omega
    rw [e1] at w1; rw [e2] at w2
    rw [w1, w2, ← sum_take_succ π.segs hns1, show ns - 1 + 1 = π.segs.length by rw [hns]; omega,
      List.take_length, hLs]
  obtain ⟨st, hst⟩ : ∃ st, c.nmem (Gb + 1 + 2 * ns + L + j) = st := ⟨_, rfl⟩
  obtain ⟨st1, st2⟩ := s6 j hj
  rw [hns, hLs, hst] at st1 st2
  -- phase A
  obtain ⟨c₁, t₁, e₁, ht₁, R₁, r3004₁, vl₁, dva₁, fr₁, mem₁, rr₁, rm₁, o₁⟩ :=
    fcA_exec (P := P) c hc r3004 r3006 r85 hL.hm hL.hz hL.permOn_sg hA w hFLs
      (by clear * - wK; omega)
  have sk₁ := sreg_keepW e₁ fcA_dests
  have lo₁ : ∀ a, a < b → c₁.nmem a = c.nmem a := fun a ha => mem₁ a (Or.inl ha)
  -- phase B
  have hRV : ∀ i < m, c.nmem (d + 4 + m + i) < m := fun i hi => (hL.rv i hi).1
  have hreg : Gb + 1 + 2 * ns + L + ns ≤ b := s5
  have hD : ∀ l < k, Gb + 1 + 2 * ns + o + l < b := fun l hl => by clear * - hl hok hreg; omega
  obtain ⟨c₂, t₂, e₂, ht₂, R₂, r90₂, pv₂, mem₂, rr₂, rm₂, o₂⟩ :=
    fcB_exec (P := P) c₁ e₁.wb_right R₁ (by rw [sk₁ _ (by decide)]; exact hGb)
      (by rw [sk₁ _ (by decide)]; exact r6800) (by rw [lo₁ _ (by clear * - s1 heb hreg; omega)]; exact s2)
      hjs (by rw [lo₁ _ (by clear * - hreg hjs; omega)]; exact u1)
      (by rw [lo₁ _ (by clear * - hreg hjs; omega)]; exact u2)
      (by rw [lo₁ _ (by clear * - hreg hjs; omega), lo₁ _ (by clear * - hreg hjs; omega)]; exact hLL)
      (by rw [lo₁ _ (by clear * - hreg hjs; omega)]; exact hst) st1 hok
      (fun l hl => by rw [lo₁ _ (hD l hl)]; exact (u3 l (by rw [hk]; exact hl)).1)
      (fun i hi => by rw [lo₁ _ (by clear * - hi hA; omega)]; exact hRV i hi)
      (fun i hi => by rw [vl₁ i hi]; exact olab_lt hL.permOn_sg hi)
      hreg (by clear * - s1 hde; unfold fsz at hde; omega) hA w
  have sk₂ := sreg_keepW e₂ fcB_dests
  -- the part flag
  have hpart : ∀ i (hi : i < m), (pmap h).tail (vDart hL hi) ∈
      vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts ↔
      c₂.nmem (b + 8 * m + i) = 1 := fun i hi => by
    rw [pv₂ i hi, mkv_eq_one, vl₁ i hi, vl₁ st st1,
      hL.mem_part_iff h hP st1 st2 (E := fun l => c.nmem (Gb + 1 + 2 * ns + o + l))
        (fun l hl => by rw [hk] at hl; exact u3 l (by rw [hk]; exact hl)) hi]
    apply or_congr Iff.rfl
    rw [hk]
    apply exists_congr; intro l
    apply and_congr_right; intro hl
    have h1 := hD l hl
    have h2 := (u3 l (by rw [hk]; exact hl)).1
    have h3 := hRV _ h2
    have hv : c₁.nmem (b + 3 * m + c₁.nmem (d + 4 + m + c₁.nmem (Gb + 1 + 2 * ns + o + l))) =
        olab (sgF d m c.nmem) (c.nmem (d + 4 + m + c.nmem (Gb + 1 + 2 * ns + o + l))) := by
      rw [lo₁ (Gb + 1 + 2 * ns + o + l) h1,
        lo₁ (d + 4 + m + c.nmem (Gb + 1 + 2 * ns + o + l)) (by clear * - h2 hA; omega)]
      exact vl₁ _ h3
    beta_reduce
    rw [hv]
    exact eq_comm
  have hpv : ∀ i < m, c₂.nmem (b + 8 * m + i) ≤ 1 := fun i hi => by
    rw [pv₂ i hi]; exact mkv_le _ _ _ _
  have hkm : k ≤ m := by
    rw [← hk]; exact part_k_le (E := fun l => c.nmem (Gb + 1 + 2 * ns + o + l)) (en := en)
      (fun l hl => u3 l hl)
  -- `fJ ; btL`: the bounds
  obtain ⟨c₃, t₃, e₃, ht₃, a88, a89, a90, a91, a93, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    fJ_exec (P := P) c₂ e₂.wb_right (by rw [r90₂, R₂.r81]; clear * - w hA; omega)
      (by rw [r90₂, R₂.r81]; clear * - w hA; omega)
  rw [R₂.r81] at a88; rw [R₂.r88] at a89; rw [r90₂, R₂.r81] at a90; rw [r90₂, R₂.r81] at a91
  rw [R₂.r84] at a93
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, k₄, f₄, rr₄, rm₄, o₄⟩ := btL_exec (P := P) c₃ e₃.wb_right
    a88 a89 a90 a91 a93 (Or.inl (by clear * -; omega)) (Or.inl (by clear * -; omega))
    (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (fun i hi => by
      rw [m₃, show b + 7 * m + m + i = b + 8 * m + i by clear * -; omega]; exact hpv i hi)
  have k91 : c₄.nreg 9291 = c₃.nreg 9291 := Exec.nreg_keepW e₄ (by decide)
  have q4 : ∀ x, x < 9287 → c₄.nreg x = c₃.nreg x := fun x hx => f₄ x (Or.inl hx)
  have q3 : ∀ x, 9180 ≤ x → x ≤ 9189 → c₃.nreg x = c₂.nreg x := fun x h1 h2 =>
    f₃ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega) (by clear * - h2; omega)
  -- `fK ; pchP`
  obtain ⟨c₅, t₅, e₅, ht₅, b00, b01, b02, b03, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    fK_exec (P := P) c₄ e₄.wb_right
      (by rw [k91, a91, q4 _ (by decide), q3 _ (by decide) (by decide), R₂.r81]; clear * - w hA; omega)
  rw [k91, a91, q4 _ (by decide), q3 _ (by decide) (by decide), R₂.r81] at b00
  rw [k91, a91] at b01
  rw [q4 _ (by decide), q3 _ (by decide) (by decide), R₂.r89] at b02
  rw [q4 _ (by decide), q3 _ (by decide) (by decide), R₂.r84] at b03
  have m5 : ∀ a, (a < b + 7 * m + m + m ∨ b + 7 * m + m + m + m ≤ a) → c₅.nmem a = c₂.nmem a :=
    fun a ha => by rw [m₅, k₄ a ha, m₃]
  have lo5 : ∀ a, a < b → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m5 a (by clear * - ha; omega), mem₂ a (by clear * - ha; omega), lo₁ a ha]
  have hL₅ : Lay M gid u S T Z x m en d c₅.nmem :=
    hL.congr fun a h1 h2 => lo5 a (by clear * - h2 hA; omega)
  have hfl₅ : FLHas Z m d en c₅.nmem g := fun i hi => by
    rw [lo5 _ (by clear * - hi hA; omega)]; exact hfl i hi
  have r3004₅ : c₅.nreg 3004 = d := by
    rw [Exec.nreg_keepW e₅ (by decide), Exec.nreg_keepW e₄ (by decide),
      Exec.nreg_keepW e₃ (by decide), sk₂ _ (by decide), r3004₁]
  have hBT : ∀ i (hi : i < m), (c₅.nmem (b + 7 * m + m + m + i) : ℤ) = ((m * Z + Z : ℕ) : ℤ) +
      (fun v => if v ∈ negSet (pmap h) g
          (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) then 0
        else (pmap h).div g v) ((pmap h).tail (vDart hL₅ hi)) := by
    intro i hi
    have hdv := dvP_div hL h hfl hi
    have hcz : Z * dvC (olab (sgF d m c.nmem)) m (olab (sgF d m c.nmem) i) ≤ m * Z :=
      (Nat.mul_le_mul_left _ (dvC_le _ _ _)).trans (le_of_eq (Nat.mul_comm _ _))
    have ha : ((c₁.nmem (b + 5 * m + i) : ℕ) : ℤ) = ((m * Z + Z : ℕ) : ℤ) +
        (pmap h).div g ((pmap h).tail (vDart hL hi)) := by
      rw [dva₁ i hi, ← hdv]; push_cast; clear * - hcz; omega
    have e1 : c₅.nmem (b + 7 * m + m + m + i) = c₁.nmem (b + 5 * m + i) -
        c₂.nmem (b + 8 * m + i) * (c₁.nmem (b + 5 * m + i) - (m * Z + Z)) := by
      rw [m₅, v₄ i hi, m₃, show b + 7 * m + m + i = b + 8 * m + i by clear * -; omega,
        mem₂ (b + 5 * m + i) (by clear * - hi; omega)]
    rw [e1, btVal ha (hpv i hi)]
    show _ = _ + (if (pmap h).tail (vDart hL hi) ∈ negSet (pmap h) g
          (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) then 0
        else (pmap h).div g ((pmap h).tail (vDart hL hi)))
    congr 1
    have hc : (c₂.nmem (b + 8 * m + i) = 1 ∧ 0 < (pmap h).div g ((pmap h).tail (vDart hL hi))) ↔
        (pmap h).tail (vDart hL hi) ∈ negSet (pmap h) g
          (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) := by
      rw [mem_negSet, ← hpart i hi]
    by_cases hx : (pmap h).tail (vDart hL hi) ∈ negSet (pmap h) g
        (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts)
    · rw [iteT hx, iteT (hc.2 hx)]
    · rw [iteF hx, iteF (fun h' => hx (hc.1 h'))]
  have hFR' : ∀ i (hi : i < m), c₅.nmem (b + 6 * m + i) = 0 ↔
      (pmap h).tail (vDart hL₅ hi) ∉ Fr := by
    intro i hi
    rw [m5 _ (by clear * - hi; omega), mem₂ _ (by clear * - hi; omega), fr₁ i hi,
      hL.kr i hi]
    have := hFr i hi
    by_cases e : lrk S T (hunion x.2.1) (M.tail (en i)) = kfr
    · rw [iteT e]; simp only [one_ne_zero, false_iff, not_not]; exact this.1 e
    · rw [iteF e]; simp only [true_iff]; exact fun h' => e (this.2 h')
  obtain ⟨c₆, t₆, e₆, ht₆, FL₆, k₆, f₆, r3004₆, rr₆, rm₆, o₆⟩ :=
    pchP_exec (P := P) c₅ e₅.wb_right hL₅ h hpl hm hg hfl₅ (Fr := Fr)
      (β := fun v => if v ∈ negSet (pmap h) g
          (vimg M x.2.2 (pdarts M x.1.piece x.2.1) (π.segs[j]).verts) then 0
        else (pmap h).div g v) r3004₅ b00 b01 b02 b03
      hBT hFR' (by clear * - hA; omega) (Or.inr (by clear * - hA; omega))
      (Or.inl (by clear * -; omega)) (Or.inr (by clear * - hA; omega))
      (Or.inl (by clear * -; omega)) (by clear * - w hA; omega) (by clear * - w hA; omega)
      (by clear * - w hA; omega) le_rfl (by clear * - wK; omega)
  have hnx : rcnt (olab (nxFP d m c₅.nmem)) m = rcnt (olab (nxFP d m c.nmem)) m := by
    have hp5 : PermOn (nxFP d m c₅.nmem) m := hL₅.permOn_face hL₅.faceArr_nx
    refine rcnt_olab_congr hp5 fun i hi => ?_
    have := (hL.rv i hi).1
    unfold nxFP
    rw [lo5 (d + 4 + m + i) (by clear * - hi hA; omega), lo5 _ (by clear * - this hA; omega)]
  rw [hnx] at ht₆
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, FL₆, fun a h1 h2 => ?_,
    sreg_keepW (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))) fcore_dests,
    by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · unfold fcCost; clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ hkm; omega
  · rw [k₆ a h1 (by clear * - h2; omega), m5 a (by clear * - h2; omega),
      mem₂ a (by clear * - h2; omega), mem₁ a (by clear * - h2; omega)]

end MfDrv

end BKMNW

end PlanarFlow
