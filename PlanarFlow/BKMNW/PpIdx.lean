module

public import PlanarFlow.BKMNW.PpHyp
public import PlanarFlow.BKMNW.OrbLab

/-!
# The preprocessed map at the level of indices: explicit pendant darts, slots

For a map `M` with darts `Fin n` (the drawing's encoding), this file fixes **computable** pendant
darts and numbers the darts of `lpreMapX M e he` by **slots** (natural numbers below `7 n`):

* the pendant edge at a vertex `w` of `nlMap M` is drawn before `old (vRep w)`, `vRep w` the dart
  of least index leaving `w` (`vRep`); at the centre of a face `f`, before `down (fRep f)`,
  `fRep f` the dart of least index on the boundary walk of `f` (`fRep`, through the orbit label
  `olab` of the index-level face permutation `phI`);
* `pe M`, `pe_tail`: the pendant darts and their tails;
* `enc`: the slot of a dart: `3 x`, `3 x + 1`, `3 x + 2` for `old x`, `up x`, `down x`; `3 n + 2 x`
  and `3 n + 2 x + 1` for the pendant edge at the vertex of its chosen dart `x`; `5 n + 2 x`,
  `5 n + 2 x + 1` for the pendant edge at the centre of the face of its chosen dart `x`;
* the index-level functions (`rvI`, `sgI`, `phI`, `piI`, `flI`, `vminI`) used by the programs.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap PlanarSeparator.StDart

variable {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (M : CombMap (Fin n) V F)

/-! ### Index-level functions -/

/-- A function on the darts, extended by `0` to all naturals. -/
def xt (f : Fin n → ℕ) (x : ℕ) : ℕ := if h : x < n then f ⟨x, h⟩ else 0

lemma xt_fin (f : Fin n → ℕ) (x : Fin n) : xt f x = f x := by simp [xt, x.2]

/-- `x` is the index of a dart that is not a loop. -/
def IsNl (x : ℕ) : Prop := ∃ h : x < n, (⟨x, h⟩ : Fin n) ∈ nlDarts M

lemma isNl_fin {x : Fin n} : IsNl M x ↔ x ∈ nlDarts M :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

lemma IsNl.lt {x : ℕ} (h : IsNl M x) : x < n := h.1

/-- The reverse, at index level. -/
def rvI : ℕ → ℕ := xt fun d => (M.rev d).val

/-- The tail, at index level (`none` out of range). -/
def tlF (x : ℕ) : Option V := if h : x < n then some (M.tail ⟨x, h⟩) else none

open Classical in
/-- The rotation of the loop-free map (`nlRot`), at index level (identity on the loops). -/
noncomputable def sgI (x : ℕ) : ℕ := if h : IsNl M x then (nlRot M ⟨x, h.1⟩).val else x

open Classical in
/-- The face permutation of the loop-free map (`next = nlRot ∘ rev`), at index level (identity
on the loops). -/
noncomputable def phI (x : ℕ) : ℕ := if IsNl M x then sgI M (rvI M x) else x

open Classical in
/-- The least index of a dart that is not a loop leaving the vertex `v`. -/
noncomputable def vminV (v : V) : ℕ :=
  if h : ∃ y, IsNl M y ∧ tlF M y = some v then Nat.find h else 0

open Classical in
/-- The least index of a dart that is not a loop with the tail of `x`. -/
noncomputable def vminI (x : ℕ) : ℕ := if h : x < n then vminV M (M.tail ⟨x, h⟩) else 0

/-- The face label at index level: the least index on the forward orbit under `phI`. -/
noncomputable def flI (x : ℕ) : ℕ := OrbLab.olab (phI M) x

/-! ### The face permutation at index level -/

lemma nlRot_mem {d : Fin n} (hd : d ∈ nlDarts M) : nlRot M d ∈ nlDarts M := ret_mem hd

lemma rev_mem_nl {d : Fin n} (hd : d ∈ nlDarts M) : M.rev d ∈ nlDarts M :=
  stable_rev_nlDarts d hd

lemma rvI_fin (d : Fin n) : rvI M d = (M.rev d).val := xt_fin _ d

lemma sgI_fin {d : Fin n} (hd : d ∈ nlDarts M) : sgI M d = (nlRot M d).val := by
  unfold sgI; rw [ppDiteT ((isNl_fin M).2 hd)]

lemma phI_fin {d : Fin n} (hd : d ∈ nlDarts M) : phI M d = (nlRot M (M.rev d)).val := by
  unfold phI; rw [ppIteT ((isNl_fin M).2 hd), rvI_fin, sgI_fin M (rev_mem_nl M hd)]

lemma phI_not {x : ℕ} (hx : ¬ IsNl M x) : phI M x = x := by unfold phI; rw [ppIteF hx]

lemma isNl_phI {x : ℕ} (hx : IsNl M x) : IsNl M (phI M x) := by
  obtain ⟨h, hd⟩ := hx
  have e := phI_fin M (d := ⟨x, h⟩) hd
  simp only at e
  rw [e]
  exact (isNl_fin M).2 (nlRot_mem M (rev_mem_nl M hd))

lemma phI_lt {x : ℕ} (hx : x < n) : phI M x < n := by
  by_cases h : IsNl M x
  · exact (isNl_phI M h).lt
  · rw [phI_not M h]; exact hx

lemma phI_permOn : OrbLab.PermOn (phI M) n := by
  refine ⟨fun x hx => phI_lt M hx, fun x hx y hy e => ?_⟩
  by_cases h1 : IsNl M x <;> by_cases h2 : IsNl M y
  · obtain ⟨_, hdx⟩ := h1
    obtain ⟨_, hdy⟩ := h2
    rw [phI_fin M (d := ⟨x, hx⟩) hdx, phI_fin M (d := ⟨y, hy⟩) hdy] at e
    have := (nlRot M).injective (Fin.ext e)
    exact congrArg Fin.val (M.rev_injective this)
  · rw [phI_not M h2] at e
    exact absurd (e ▸ isNl_phI M h1) h2
  · rw [phI_not M h1] at e
    exact absurd (e.symm ▸ isNl_phI M h2) h1
  · rwa [phI_not M h1, phI_not M h2] at e

/-! ### The pendant darts -/

lemma tlF_fin (d : Fin n) : tlF M d = some (M.tail d) := by simp [tlF, d.2]

lemma exists_nl_tail (w : SVert (nlRot M) (nlDarts M)) :
    ∃ y, IsNl M y ∧ tlF M y = some (nlVert M w) := by
  induction w using Quotient.inductionOn with
  | h x => exact ⟨x.1.val, (isNl_fin M).2 x.2, by rw [tlF_fin]; rfl⟩

open Classical in
lemma vminV_spec {v : V} (h : ∃ y, IsNl M y ∧ tlF M y = some v) :
    IsNl M (vminV M v) ∧ tlF M (vminV M v) = some v := by
  unfold vminV; rw [ppDiteT h]; exact Nat.find_spec h

open Classical in
lemma vminV_min {v : V} (h : ∃ y, IsNl M y ∧ tlF M y = some v) {y : ℕ} (hy : IsNl M y)
    (ht : tlF M y = some v) : vminV M v ≤ y := by
  unfold vminV; rw [ppDiteT h]; exact Nat.find_min' h ⟨hy, ht⟩

/-- **The chosen dart at a vertex** of the loop-free map: the dart of least index leaving it. -/
noncomputable def vRep (w : SVert (nlRot M) (nlDarts M)) : SDart (nlDarts M) :=
  ⟨⟨vminV M (nlVert M w), (vminV_spec M (exists_nl_tail M w)).1.lt⟩,
    (vminV_spec M (exists_nl_tail M w)).1.2⟩

lemma vRep_val (w : SVert (nlRot M) (nlDarts M)) : (vRep M w).1.val = vminV M (nlVert M w) := rfl

lemma tail_vRep (w : SVert (nlRot M) (nlDarts M)) : M.tail (vRep M w).1 = nlVert M w := by
  have h := (vminV_spec M (exists_nl_tail M w)).2
  rw [show vminV M (nlVert M w) = ((vRep M w).1 : ℕ) from rfl, tlF_fin] at h
  exact Option.some.inj h

lemma nlMap_tail_vRep (hrot : M.RotTrans) (w : SVert (nlRot M) (nlDarts M)) :
    (nlMap M).tail (vRep M w) = w :=
  nlVert_injective hrot (by rw [nlVert_tail, tail_vRep])

/-- The index-level face permutation is the face permutation of the loop-free map. -/
lemma phI_phi (y : SDart (nlDarts M)) :
    phI M y.1 = (((nlMap M).toSep nlMap_rotTrans).φ y).1.val := by
  rw [phI_fin M y.2, PlanarSeparator.Map.φ_apply, toSep_σ, toSep_α]
  have e := subMap_rot (σ := nlRot M) (B := nlDarts M) (revPerm_isInv M) (stable_ret _ _)
    stable_rev_nlDarts ((nlMap M).rev y)
  exact congrArg Fin.val e.symm

lemma phI_iter_phi (y : SDart (nlDarts M)) (t : ℕ) :
    (phI M)^[t] y.1 = ((((nlMap M).toSep nlMap_rotTrans).φ)^[t] y).1.val := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih => rw [iterate_succ_apply, iterate_succ_apply, ← ih, phI_phi]

lemma isNl_phI_iter {x : ℕ} (hx : IsNl M x) (t : ℕ) : IsNl M ((phI M)^[t] x) := by
  induction t with
  | zero => exact hx
  | succ t ih => rw [iterate_succ_apply']; exact isNl_phI M ih

lemma isNl_olab {x : ℕ} (hx : IsNl M x) : IsNl M (OrbLab.olab (phI M) x) := by
  obtain ⟨t, ht⟩ := OrbLab.olab_mem (phI M) x
  rw [← ht]; exact isNl_phI_iter M hx t

lemma olab_respect (y y' : SDart (nlDarts M))
    (h : (((nlMap M).toSep nlMap_rotTrans).φ).SameCycle y y') :
    OrbLab.olab (phI M) y.1 = OrbLab.olab (phI M) y'.1 := by
  obtain ⟨t, ht⟩ := sameCycle_iff.1 h
  have e := phI_iter_phi M y t
  rw [ht] at e
  rw [← e, OrbLab.olab_iter (phI_permOn M) y.1.2]

/-- The dart of index the face label of `y`. -/
noncomputable def flD (y : SDart (nlDarts M)) : SDart (nlDarts M) :=
  ⟨⟨OrbLab.olab (phI M) y.1, (isNl_olab M ((isNl_fin M).2 y.2)).lt⟩,
    (isNl_olab M ((isNl_fin M).2 y.2)).2⟩

/-- **The chosen dart on the boundary of a face** of the loop-free map: the dart of least index on
its boundary walk. -/
noncomputable def fRep (f : ((nlMap M).toSep nlMap_rotTrans).Face) : SDart (nlDarts M) :=
  Quotient.lift (flD M) (fun y y' h => Subtype.ext (Fin.ext (olab_respect M y y' h))) f

lemma fRep_face (y : SDart (nlDarts M)) :
    fRep M (((nlMap M).toSep nlMap_rotTrans).face y) = flD M y := rfl

lemma face_fRep (f : ((nlMap M).toSep nlMap_rotTrans).Face) :
    ((nlMap M).toSep nlMap_rotTrans).face (fRep M f) = f := by
  induction f using Quotient.inductionOn with
  | h y =>
    show ((nlMap M).toSep nlMap_rotTrans).face (flD M y) = ((nlMap M).toSep nlMap_rotTrans).face y
    obtain ⟨t, ht⟩ := OrbLab.olab_mem (phI M) y.1
    have e : flD M y = (((nlMap M).toSep nlMap_rotTrans).φ)^[t] y := by
      apply Subtype.ext; apply Fin.ext
      show OrbLab.olab (phI M) y.1 = _
      rw [← ht, phI_iter_phi]
    rw [e, PlanarSeparator.Map.face_eq_face_iff, ← Equiv.Perm.coe_pow]
    exact (Equiv.Perm.SameCycle.refl _ _).symm.trans ⟨-(t : ℤ), by simp⟩

/-- **The explicit pendant darts**: before `old (vRep w)` at a vertex `w`, before
`down (fRep f)` at the centre of a face `f`. -/
noncomputable def pe : PVert M → TDart M
  | .inl w => old (vRep M w)
  | .inr f => down (fRep M f)

lemma pe_tail (hrot : M.RotTrans) : ∀ p, (tnlMap M).tail (pe M p) = p
  | .inl w => by
    show (Sum.inl ((nlMap M).tail (vRep M w)) : PVert M) = _
    rw [nlMap_tail_vRep M hrot]
  | .inr f => by
    show (Sum.inr (((nlMap M).toSep nlMap_rotTrans).face (fRep M f)) : PVert M) = _
    rw [face_fRep]

/-! ### The triangulated loop-free map -/

lemma tnl_rot_old (y : SDart (nlDarts M)) :
    (tnlMap M).rot (old y) = up ((nlMap M).rot y) := ofSep_rot _ _

lemma tnl_rot_up (y : SDart (nlDarts M)) : (tnlMap M).rot (up y) = old y := ofSep_rot _ _

lemma tnl_rot_down (y : SDart (nlDarts M)) :
    (tnlMap M).rot (down y) = down (((nlMap M).toSep nlMap_rotTrans).φ.symm y) := ofSep_rot _ _

lemma nlMap_rot_val (y : SDart (nlDarts M)) : ((nlMap M).rot y).1.val = sgI M y.1 := by
  rw [sgI_fin M y.2]
  exact congrArg Fin.val (subMap_rot (σ := nlRot M) (B := nlDarts M) (revPerm_isInv M)
    (stable_ret _ _) stable_rev_nlDarts y)

lemma nlMap_rev_val (y : SDart (nlDarts M)) : ((nlMap M).rev y).1.val = rvI M y.1 := by
  rw [rvI_fin]; rfl

open Classical in
/-- The inverse of the face permutation of the loop-free map, at index level (identity on the
loops). -/
noncomputable def piI (x : ℕ) : ℕ :=
  if h : IsNl M x then (((nlMap M).toSep nlMap_rotTrans).φ.symm ⟨⟨x, h.1⟩, h.2⟩).1.val else x

lemma piI_val (y : SDart (nlDarts M)) :
    piI M y.1 = (((nlMap M).toSep nlMap_rotTrans).φ.symm y).1.val := by
  unfold piI; rw [ppDiteT ((isNl_fin M).2 y.2)]

/-- `x` is the chosen dart of its vertex. -/
def CvI (x : ℕ) : Prop := IsNl M x ∧ vminI M x = x

/-- `x` is the chosen dart of its face. -/
def CfI (x : ℕ) : Prop := IsNl M x ∧ flI M x = x

lemma vRep_tail_val (y : SDart (nlDarts M)) :
    (vRep M ((nlMap M).tail y)).1.val = vminI M y.1 := by
  rw [vRep_val, nlVert_tail]
  unfold vminI; rw [ppDiteT y.1.2]

lemma fRep_face_val (y : SDart (nlDarts M)) :
    (fRep M (((nlMap M).toSep nlMap_rotTrans).face y)).1.val = flI M y.1 := rfl

lemma vRep_eq_iff (y : SDart (nlDarts M)) : vRep M ((nlMap M).tail y) = y ↔ CvI M y.1 := by
  constructor
  · intro h; refine ⟨(isNl_fin M).2 y.2, ?_⟩; rw [← vRep_tail_val, h]
  · intro h; apply Subtype.ext; apply Fin.ext; rw [vRep_tail_val]; exact h.2

lemma fRep_eq_iff (y : SDart (nlDarts M)) :
    fRep M (((nlMap M).toSep nlMap_rotTrans).face y) = y ↔ CfI M y.1 := by
  constructor
  · intro h; refine ⟨(isNl_fin M).2 y.2, ?_⟩; rw [← fRep_face_val, h]
  · intro h; apply Subtype.ext; apply Fin.ext; rw [fRep_face_val]; exact h.2

/-! ### Slots -/

/-- The bit of a pendant dart: `0` from the vertex, `1` towards it. -/
def bt (b : Bool) : ℕ := if b then 0 else 1

/-- **The slot of a dart** of the preprocessed map (see the module docstring). -/
noncomputable def enc : TDart M ⊕ (PVert M × Bool) → ℕ
  | .inl (old y) => 3 * y.1.val
  | .inl (up y) => 3 * y.1.val + 1
  | .inl (down y) => 3 * y.1.val + 2
  | .inr (.inl w, b) => 3 * n + 2 * (vRep M w).1.val + bt b
  | .inr (.inr f, b) => 5 * n + 2 * (fRep M f).1.val + bt b

open Classical in
/-- **The rotation on slots.** -/
noncomputable def rotS (s : ℕ) : ℕ :=
  if s < 3 * n then
    if s % 3 = 0 then 3 * sgI M (s / 3) + 1
    else if s % 3 = 1 then (if CvI M (s / 3) then 3 * n + 2 * (s / 3) else 3 * (s / 3))
    else (if CfI M (piI M (s / 3)) then 5 * n + 2 * piI M (s / 3) else 3 * piI M (s / 3) + 2)
  else if s < 5 * n then (if (s - 3 * n) % 2 = 0 then 3 * ((s - 3 * n) / 2) else s)
  else (if (s - 5 * n) % 2 = 0 then 3 * ((s - 5 * n) / 2) + 2 else s)

variable (hrot : M.RotTrans)

/-- The preprocessed map with the explicit pendant darts `pe`. -/
noncomputable abbrev LP := lpreMapX M (pe M) (pe_tail M hrot)

lemma enc_rot_old (y : SDart (nlDarts M)) :
    enc M (rotPerm (LP M hrot) (.inl (old y))) = rotS M (enc M (.inl (old y))) := by
  have hy := y.1.2
  rw [rotPerm_apply, pendant_rot_inl, tnl_rot_old]
  have hne : up ((nlMap M).rot y) ≠ pe M ((tnlMap M).tail (old y)) := by
    cases ((tnlMap M).tail (old y)) <;> simp [pe]
  rw [ppIteF hne]
  show 3 * ((nlMap M).rot y).1.val + 1 = rotS M (3 * y.1.val)
  unfold rotS
  rw [nlMap_rot_val, ppIteT (by omega), ppIteT (by omega), show 3 * y.1.val / 3 = y.1.val by omega]

open Classical in
lemma enc_rot_up (y : SDart (nlDarts M)) :
    enc M (rotPerm (LP M hrot) (.inl (up y))) = rotS M (enc M (.inl (up y))) := by
  have hy := y.1.2
  rw [rotPerm_apply, pendant_rot_inl, tnl_rot_up]
  have ht : (tnlMap M).tail (up y) = .inl ((nlMap M).tail y) := rfl
  rw [ht]
  have hR : rotS M (3 * y.1.val + 1) =
      if CvI M y.1 then 3 * n + 2 * y.1.val else 3 * y.1.val := by
    unfold rotS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteT (by omega),
      show (3 * y.1.val + 1) / 3 = y.1.val by omega]
  show _ = rotS M (3 * y.1.val + 1)
  rw [hR]
  by_cases hc : CvI M y.1
  · have e : old y = pe M (.inl ((nlMap M).tail y)) := by
      show old y = old (vRep M ((nlMap M).tail y)); rw [(vRep_eq_iff M y).2 hc]
    rw [ppIteT e, ppIteT hc]
    show 3 * n + 2 * (vRep M ((nlMap M).tail y)).1.val + 0 = _
    rw [(vRep_eq_iff M y).2 hc]; rfl
  · have e : old y ≠ pe M (.inl ((nlMap M).tail y)) := by
      show old y ≠ old (vRep M ((nlMap M).tail y))
      intro h; exact hc ((vRep_eq_iff M y).1 (old.inj h).symm)
    rw [ppIteF e, ppIteF hc]; rfl

lemma face_phi_symm (y : SDart (nlDarts M)) :
    ((nlMap M).toSep nlMap_rotTrans).face (((nlMap M).toSep nlMap_rotTrans).φ.symm y) =
      ((nlMap M).toSep nlMap_rotTrans).face y := PlanarSeparator.Map.face_φ_symm _ _

open Classical in
lemma enc_rot_down (y : SDart (nlDarts M)) :
    enc M (rotPerm (LP M hrot) (.inl (down y))) = rotS M (enc M (.inl (down y))) := by
  have hy := y.1.2
  rw [rotPerm_apply, pendant_rot_inl, tnl_rot_down]
  have ht : (tnlMap M).tail (down y) = .inr (((nlMap M).toSep nlMap_rotTrans).face y) := rfl
  rw [ht]
  have hR : rotS M (3 * y.1.val + 2) =
      if CfI M (piI M y.1) then 5 * n + 2 * piI M y.1 else 3 * piI M y.1 + 2 := by
    unfold rotS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteF (by omega),
      show (3 * y.1.val + 2) / 3 = y.1.val by omega]
  show _ = rotS M (3 * y.1.val + 2)
  rw [hR, piI_val]
  set z := ((nlMap M).toSep nlMap_rotTrans).φ.symm y with hz
  have hf : ((nlMap M).toSep nlMap_rotTrans).face y = ((nlMap M).toSep nlMap_rotTrans).face z :=
    (face_phi_symm M y).symm
  by_cases hc : CfI M z.1
  · have e : down z = pe M (.inr (((nlMap M).toSep nlMap_rotTrans).face y)) := by
      show down z = down (fRep M _); rw [hf, (fRep_eq_iff M z).2 hc]
    rw [ppIteT e, ppIteT hc]
    show 5 * n + 2 * (fRep M (((nlMap M).toSep nlMap_rotTrans).face y)).1.val + 0 = _
    rw [hf, (fRep_eq_iff M z).2 hc]; rfl
  · have e : down z ≠ pe M (.inr (((nlMap M).toSep nlMap_rotTrans).face y)) := by
      show down z ≠ down (fRep M _)
      intro h; rw [hf] at h; exact hc ((fRep_eq_iff M z).1 (down.inj h).symm)
    rw [ppIteF e, ppIteF hc]; rfl

lemma vRep_lt (w : SVert (nlRot M) (nlDarts M)) : (vRep M w).1.val < n := (vRep M w).1.2

lemma fRep_lt (f : ((nlMap M).toSep nlMap_rotTrans).Face) : (fRep M f).1.val < n := (fRep M f).1.2

lemma enc_rot_pv (w : SVert (nlRot M) (nlDarts M)) (b : Bool) :
    enc M (rotPerm (LP M hrot) (.inr (.inl w, b))) = rotS M (enc M (.inr (.inl w, b))) := by
  have hl := vRep_lt M w
  cases b
  · show enc M (.inr (.inl w, false)) = _
    show _ = rotS M (3 * n + 2 * (vRep M w).1.val + 1)
    unfold rotS
    rw [ppIteF (by omega), ppIteT (by omega), ppIteF (by omega)]; rfl
  · show enc M (.inl (old (vRep M w))) = _
    show _ = rotS M (3 * n + 2 * (vRep M w).1.val + 0)
    unfold rotS
    rw [ppIteF (by omega), ppIteT (by omega), ppIteT (by omega)]
    show 3 * (vRep M w).1.val = _
    congr 1; omega

lemma enc_rot_pf (f : ((nlMap M).toSep nlMap_rotTrans).Face) (b : Bool) :
    enc M (rotPerm (LP M hrot) (.inr (.inr f, b))) = rotS M (enc M (.inr (.inr f, b))) := by
  have hl := fRep_lt M f
  cases b
  · show enc M (.inr (.inr f, false)) = _
    show _ = rotS M (5 * n + 2 * (fRep M f).1.val + 1)
    unfold rotS
    rw [ppIteF (by omega), ppIteF (by omega), ppIteF (by omega)]; rfl
  · show enc M (.inl (down (fRep M f))) = _
    show _ = rotS M (5 * n + 2 * (fRep M f).1.val + 0)
    unfold rotS
    rw [ppIteF (by omega), ppIteF (by omega), ppIteT (by omega)]
    show 3 * (fRep M f).1.val + 2 = _
    congr 2; omega

/-- **The slot of the rotation** of a dart of the preprocessed map is `rotS` of its slot. -/
theorem enc_rot (y : TDart M ⊕ (PVert M × Bool)) :
    enc M (rotPerm (LP M hrot) y) = rotS M (enc M y) := by
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · exact enc_rot_old M hrot y
  · exact enc_rot_up M hrot y
  · exact enc_rot_down M hrot y
  · exact enc_rot_pv M hrot w b
  · exact enc_rot_pf M hrot f b

/-! ### The reversal and the root rotation on slots -/

/-- **The reversal on slots.** -/
def revS (s : ℕ) : ℕ :=
  if s < 3 * n then
    (if s % 3 = 0 then 3 * rvI M (s / 3) else if s % 3 = 1 then s + 1 else s - 1)
  else (if (s - 3 * n) % 2 = 0 then s + 1 else s - 1)

/-- **The slot of the reverse** of a dart is `revS` of its slot. -/
theorem enc_rev (y : TDart M ⊕ (PVert M × Bool)) :
    enc M ((LP M hrot).rev y) = revS M (enc M y) := by
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · have hy := y.1.2
    show 3 * ((nlMap M).rev y).1.val = revS M (3 * y.1.val)
    unfold revS
    rw [ppIteT (by omega), ppIteT (by omega), show 3 * y.1.val / 3 = y.1.val by omega,
      nlMap_rev_val]
  · have hy := y.1.2
    show 3 * y.1.val + 2 = revS M (3 * y.1.val + 1)
    unfold revS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteT (by omega)]
  · have hy := y.1.2
    show 3 * y.1.val + 1 = revS M (3 * y.1.val + 2)
    unfold revS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteF (by omega)]; omega
  · have hl := vRep_lt M w
    cases b
    · show 3 * n + 2 * (vRep M w).1.val + 0 = revS M (3 * n + 2 * (vRep M w).1.val + 1)
      unfold revS
      rw [ppIteF (by omega), ppIteF (by omega)]; omega
    · show 3 * n + 2 * (vRep M w).1.val + 1 = revS M (3 * n + 2 * (vRep M w).1.val + 0)
      unfold revS
      rw [ppIteF (by omega), ppIteT (by omega)]
  · have hl := fRep_lt M f
    cases b
    · show 5 * n + 2 * (fRep M f).1.val + 0 = revS M (5 * n + 2 * (fRep M f).1.val + 1)
      unfold revS
      rw [ppIteF (by omega), ppIteF (by omega)]; omega
    · show 5 * n + 2 * (fRep M f).1.val + 1 = revS M (5 * n + 2 * (fRep M f).1.val + 0)
      unfold revS
      rw [ppIteF (by omega), ppIteT (by omega)]

/-- **The root rotation on slots** (the rotation of the triangulated map, the pendant darts
skipped). -/
noncomputable def rtS (s : ℕ) : ℕ :=
  if s < 3 * n then
    (if s % 3 = 0 then 3 * sgI M (s / 3) + 1 else if s % 3 = 1 then s - 1
      else 3 * piI M (s / 3) + 2)
  else s

/-- **The root rotation of the preprocessed map on the darts of the triangulated map** is the
rotation of the triangulated map. -/
lemma rootRot_inl (t : TDart M) :
    rootRot (LP M hrot) (pendQ _) (.inl t) = .inl ((tnlMap M).rot t) := by
  unfold rootRot
  set K := core (LP M hrot) (pendQ (PVert M)) univ
  have hK : ∀ t : TDart M, (Sum.inl t : TDart M ⊕ (PVert M × Bool)) ∈ K := fun t =>
    (mem_core_pendant (pe_tail M hrot)).2 rfl
  have hr := pendant_rot_inl (pe_tail M hrot) t
  by_cases h : (tnlMap M).rot t = pe M ((tnlMap M).tail t)
  · rw [ppIteT h] at hr
    have h2 : (rotPerm (LP M hrot))^[2] (Sum.inl t) = Sum.inl ((tnlMap M).rot t) := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
      simp only [rotPerm_apply]
      rw [hr, h]
      rfl
    rw [ret_eq_of (hK _) (n := 2) (by norm_num) (by rw [h2]; exact hK _)
      (fun m h0 h1 => by
        rw [show m = 1 by omega, Function.iterate_one, rotPerm_apply, hr,
          mem_core_pendant (pe_tail M hrot)]
        simp), h2]
  · rw [ppIteF h] at hr
    rw [ret_eq_self_of (hK _) (by rw [rotPerm_apply, hr]; exact hK _), rotPerm_apply, hr]

/-- **The slot of the root rotation** of a dart of the core is `rtS` of its slot. -/
theorem enc_rt (t : TDart M) :
    enc M (rootRot (LP M hrot) (pendQ _) (.inl t)) = rtS M (enc M (.inl t)) := by
  rw [rootRot_inl]
  rcases t with y | y | y
  · have hy := y.1.2
    rw [tnl_rot_old]
    show 3 * ((nlMap M).rot y).1.val + 1 = rtS M (3 * y.1.val)
    unfold rtS
    rw [ppIteT (by omega), ppIteT (by omega), show 3 * y.1.val / 3 = y.1.val by omega,
      nlMap_rot_val]
  · have hy := y.1.2
    rw [tnl_rot_up]
    show 3 * y.1.val = rtS M (3 * y.1.val + 1)
    unfold rtS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteT (by omega)]; omega
  · have hy := y.1.2
    rw [tnl_rot_down]
    show 3 * (((nlMap M).toSep nlMap_rotTrans).φ.symm y).1.val + 2 = rtS M (3 * y.1.val + 2)
    unfold rtS
    rw [ppIteT (by omega), ppIteF (by omega), ppIteF (by omega),
      show (3 * y.1.val + 2) / 3 = y.1.val by omega, piI_val]

/-! ### Capacities, ranks and vertex keys on slots -/

section Tail

variable (cpN : Fin n → ℕ) (S T : Finset V)

/-- The total capacity of the darts that are not loops (the capacity of the pendant edges of the
terminals). -/
noncomputable def bigN : ℕ := ∑ y : SDart (nlDarts M), cpN y.1

/-- The tail of the dart of index `x` is in `X`. -/
def TlIn (X : Finset V) (x : ℕ) : Prop := ∃ h : x < n, M.tail ⟨x, h⟩ ∈ X

open Classical in
/-- **The capacities on slots.** -/
noncomputable def capS (s : ℕ) : ℕ :=
  if s < 3 * n then (if s % 3 = 0 then xt cpN (s / 3) else 0)
  else if s < 5 * n then (if TlIn M (S ∪ T) ((s - 3 * n) / 2) then bigN M cpN else 0) else 0

lemma sum_triCap {D : Type*} [Fintype D] (u : D → ℤ) :
    ∑ x : PlanarSeparator.StDart D, triCap u x = ∑ d, u d := by
  rw [← Equiv.sum_comp PlanarSeparator.StDart.equivSum.symm]
  simp [Fintype.sum_sum_type, triCap, PlanarSeparator.StDart.equivSum]

lemma tlIn_vRep (X : Finset V) (w : SVert (nlRot M) (nlDarts M)) :
    TlIn M X (vRep M w).1.val ↔ nlVert M w ∈ X := by
  constructor
  · rintro ⟨h, hx⟩; rw [← tail_vRep M w]; exact hx
  · intro hx; exact ⟨(vRep M w).1.2, by rw [show (⟨(vRep M w).1.val, (vRep M w).1.2⟩ : Fin n) =
      (vRep M w).1 from rfl, tail_vRep]; exact hx⟩

lemma mem_nlTerm_iff (X : Finset V) (w : SVert (nlRot M) (nlDarts M)) :
    w ∈ nlTerm M X ↔ nlVert M w ∈ X := by simp [nlTerm]

open Classical in
/-- **The capacity of a dart is `capS` of its slot.** -/
theorem enc_cap (y : TDart M ⊕ (PVert M × Bool)) :
    (capS M cpN S T (enc M y) : ℤ) =
      preCap (hrot := nlMap_rotTrans) (fun y => (cpN y.1 : ℤ)) (nlTerm M S) (nlTerm M T) y := by
  unfold preCap
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · have hy := y.1.2
    show (capS M cpN S T (3 * y.1.val) : ℤ) = (cpN y.1 : ℤ)
    unfold capS
    rw [ppIteT (by omega), ppIteT (by omega), show 3 * y.1.val / 3 = y.1.val by omega, xt_fin]
  · have hy := y.1.2
    show (capS M cpN S T (3 * y.1.val + 1) : ℤ) = 0
    unfold capS
    rw [ppIteT (by omega), ppIteF (by omega)]; rfl
  · have hy := y.1.2
    show (capS M cpN S T (3 * y.1.val + 2) : ℤ) = 0
    unfold capS
    rw [ppIteT (by omega), ppIteF (by omega)]; rfl
  · have hl := vRep_lt M w
    show (capS M cpN S T (3 * n + 2 * (vRep M w).1.val + bt b) : ℤ) =
      if Sum.inl w ∈ (nlTerm M S).image Sum.inl ∪ (nlTerm M T).image Sum.inl then
        ∑ x, triCap (fun y : SDart (nlDarts M) => (cpN y.1 : ℤ)) x else 0
    have hb : bt b ≤ 1 := by cases b <;> simp [bt]
    have hx : (3 * n + 2 * (vRep M w).1.val + bt b - 3 * n) / 2 = (vRep M w).1.val := by omega
    have hiff : Sum.inl w ∈ (nlTerm M S).image (Sum.inl (β := ((nlMap M).toSep nlMap_rotTrans).Face))
        ∪ (nlTerm M T).image Sum.inl ↔ TlIn M (S ∪ T) (vRep M w).1.val := by
      rw [tlIn_vRep, mem_union, mem_image, mem_image, mem_union, ← mem_nlTerm_iff,
        ← mem_nlTerm_iff]
      simp
    unfold capS
    rw [ppIteF (by omega), ppIteT (by omega), hx, sum_triCap]
    by_cases h : TlIn M (S ∪ T) (vRep M w).1.val
    · rw [ppIteT h, ppIteT (hiff.2 h), bigN]; push_cast; rfl
    · rw [ppIteF h, ppIteF (fun h' => h (hiff.1 h'))]; rfl
  · have hl := fRep_lt M f
    show (capS M cpN S T (5 * n + 2 * (fRep M f).1.val + bt b) : ℤ) =
      if Sum.inr f ∈ (nlTerm M S).image Sum.inl ∪ (nlTerm M T).image Sum.inl then
        ∑ x, triCap (fun y : SDart (nlDarts M) => (cpN y.1 : ℤ)) x else 0
    have hb : bt b ≤ 1 := by cases b <;> simp [bt]
    unfold capS
    rw [ppIteF (by omega), ppIteF (by omega), ppIteF (by simp)]; rfl

open Classical in
/-- **The ranks on slots**: `0` at the pendant vertex of a source, `2` of a sink, `3` elsewhere. -/
noncomputable def krS (s : ℕ) : ℕ :=
  if 3 * n ≤ s ∧ s < 5 * n ∧ (s - 3 * n) % 2 = 1 then
    (if TlIn M S ((s - 3 * n) / 2) then 0 else if TlIn M T ((s - 3 * n) / 2) then 2 else 3)
  else 3

open Classical in
/-- **The rank of the tail of a dart is `krS` of its slot.** -/
theorem enc_kr (y : TDart M ⊕ (PVert M × Bool)) :
    krS M S T (enc M y) = lrk (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
      (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) (hunion []) ((LP M hrot).tail y) := by
  have h3 : ∀ x, x ∉ preTerm (hrot := nlMap_rotTrans) (nlTerm M S) →
      x ∉ preTerm (hrot := nlMap_rotTrans) (nlTerm M T) →
      lrk (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
        (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) (hunion []) x = 3 := by
    intro x h1 h2; unfold lrk; simp [h1, h2, hunion_nil']
  have hl : ∀ p : PVert M, Sum.inl p ∉ preTerm (hrot := nlMap_rotTrans) (nlTerm M S) ∧
      Sum.inl p ∉ preTerm (hrot := nlMap_rotTrans) (nlTerm M T) := fun p => by
    simp [preTerm]
  have hlo : ∀ s, ¬ (3 * n ≤ s ∧ s < 5 * n ∧ (s - 3 * n) % 2 = 1) → krS M S T s = 3 := by
    intro s h; unfold krS; rw [ppIteF h]
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · have hy := y.1.2
    rw [h3 ((LP M hrot).tail (.inl (old y))) (hl _).1 (hl _).2]
    exact hlo _ (by show ¬ (3 * n ≤ 3 * y.1.val ∧ _ ∧ _); omega)
  · have hy := y.1.2
    rw [h3 ((LP M hrot).tail (.inl (up y))) (hl _).1 (hl _).2]
    exact hlo _ (by show ¬ (3 * n ≤ 3 * y.1.val + 1 ∧ _ ∧ _); omega)
  · have hy := y.1.2
    rw [h3 ((LP M hrot).tail (.inl (down y))) (hl _).1 (hl _).2]
    exact hlo _ (by show ¬ (3 * n ≤ 3 * y.1.val + 2 ∧ _ ∧ _); omega)
  · have hlt := vRep_lt M w
    cases b
    · show krS M S T (3 * n + 2 * (vRep M w).1.val + 1) =
        lrk (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
          (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) (hunion []) (Sum.inr (Sum.inl w))
      have hx : (3 * n + 2 * (vRep M w).1.val + 1 - 3 * n) / 2 = (vRep M w).1.val := by omega
      have hmS : Sum.inr (Sum.inl w) ∈ preTerm (hrot := nlMap_rotTrans) (nlTerm M S) ↔
          TlIn M S (vRep M w).1.val := by
        rw [tlIn_vRep, ← mem_nlTerm_iff]; simp [preTerm]
      have hmT : Sum.inr (Sum.inl w) ∈ preTerm (hrot := nlMap_rotTrans) (nlTerm M T) ↔
          TlIn M T (vRep M w).1.val := by
        rw [tlIn_vRep, ← mem_nlTerm_iff]; simp [preTerm]
      unfold krS lrk
      rw [ppIteT (by omega), hx]
      simp only [hmS, hmT, hunion_nil', Finset.notMem_empty, ite_false]
    · rw [h3 ((LP M hrot).tail (.inr (.inl w, true))) (hl _).1 (hl _).2]
      exact hlo _ (by show ¬ (_ ∧ _ ∧ (3 * n + 2 * (vRep M w).1.val + 0 - 3 * n) % 2 = 1); omega)
  · have hlt := fRep_lt M f
    have hb : bt b ≤ 1 := by cases b <;> simp [bt]
    rw [hlo _ (by show ¬ (_ ∧ 5 * n + 2 * (fRep M f).1.val + bt b < 5 * n ∧ _); omega)]
    cases b
    · symm; exact h3 (Sum.inr (Sum.inr f)) (by simp [preTerm]) (by simp [preTerm])
    · symm; exact h3 ((LP M hrot).tail (.inr (.inr f, true))) (hl _).1 (hl _).2

end Tail

/-! ### Vertex numbers and keys -/

section Key

variable (vn : V → ℕ) (K : ℕ)

/-- The number of a vertex of the triangulated loop-free map: `2 vn v` at a vertex `v` of `M`,
`2 (K + x)` at the centre of the face of chosen dart `x`. -/
noncomputable def νb : PVert M → ℕ
  | .inl w => 2 * vn (nlVert M w)
  | .inr f => 2 * (K + (fRep M f).1.val)

/-- **The vertex numbering of the preprocessed map**: `νb` on the vertices of the triangulated
map, `νb + 1` on the pendant vertices (odd). -/
noncomputable def νX : PVert M ⊕ PVert M → ℕ
  | .inl p => νb M vn K p
  | .inr p => νb M vn K p + 1

/-- **The keys on slots**: the number of the tail of the dart. -/
noncomputable def keyS (s : ℕ) : ℕ :=
  if s < 3 * n then
    (if s % 3 = 2 then 2 * (K + flI M (s / 3)) else 2 * xt (fun d => vn (M.tail d)) (s / 3))
  else if s < 5 * n then 2 * xt (fun d => vn (M.tail d)) ((s - 3 * n) / 2) + (s - 3 * n) % 2
  else 2 * (K + (s - 5 * n) / 2) + (s - 5 * n) % 2

lemma xt_vn_vRep (w : SVert (nlRot M) (nlDarts M)) :
    xt (fun d => vn (M.tail d)) (vRep M w).1.val = vn (nlVert M w) := by
  rw [xt_fin (fun d => vn (M.tail d)) (vRep M w).1, tail_vRep]

/-- **The key of a dart's slot is the number of its tail.** -/
theorem enc_key (y : TDart M ⊕ (PVert M × Bool)) :
    keyS M vn K (enc M y) = νX M vn K ((LP M hrot).tail y) := by
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · have hy := y.1.2
    show keyS M vn K (3 * y.1.val) = 2 * vn (nlVert M ((nlMap M).tail y))
    unfold keyS
    rw [ppIteT (by omega), ppIteF (by omega), show 3 * y.1.val / 3 = y.1.val by omega,
      xt_fin (fun d => vn (M.tail d)) y.1, nlVert_tail]
  · have hy := y.1.2
    show keyS M vn K (3 * y.1.val + 1) = 2 * vn (nlVert M ((nlMap M).tail y))
    unfold keyS
    rw [ppIteT (by omega), ppIteF (by omega), show (3 * y.1.val + 1) / 3 = y.1.val by omega,
      xt_fin (fun d => vn (M.tail d)) y.1, nlVert_tail]
  · have hy := y.1.2
    show keyS M vn K (3 * y.1.val + 2) =
      2 * (K + (fRep M (((nlMap M).toSep nlMap_rotTrans).face y)).1.val)
    unfold keyS
    rw [ppIteT (by omega), ppIteT (by omega), show (3 * y.1.val + 2) / 3 = y.1.val by omega,
      fRep_face_val]
  · have hl := vRep_lt M w
    cases b
    · show keyS M vn K (3 * n + 2 * (vRep M w).1.val + 1) = 2 * vn (nlVert M w) + 1
      unfold keyS
      rw [ppIteF (by omega), ppIteT (by omega),
        show (3 * n + 2 * (vRep M w).1.val + 1 - 3 * n) / 2 = (vRep M w).1.val by omega,
        show (3 * n + 2 * (vRep M w).1.val + 1 - 3 * n) % 2 = 1 by omega, xt_vn_vRep]
    · show keyS M vn K (3 * n + 2 * (vRep M w).1.val + 0) = 2 * vn (nlVert M w)
      unfold keyS
      rw [ppIteF (by omega), ppIteT (by omega),
        show (3 * n + 2 * (vRep M w).1.val + 0 - 3 * n) / 2 = (vRep M w).1.val by omega,
        show (3 * n + 2 * (vRep M w).1.val + 0 - 3 * n) % 2 = 0 by omega, xt_vn_vRep]
      rfl
  · have hl := fRep_lt M f
    cases b
    · show keyS M vn K (5 * n + 2 * (fRep M f).1.val + 1) = 2 * (K + (fRep M f).1.val) + 1
      unfold keyS
      rw [ppIteF (by omega), ppIteF (by omega),
        show (5 * n + 2 * (fRep M f).1.val + 1 - 5 * n) / 2 = (fRep M f).1.val by omega,
        show (5 * n + 2 * (fRep M f).1.val + 1 - 5 * n) % 2 = 1 by omega]
    · show keyS M vn K (5 * n + 2 * (fRep M f).1.val + 0) = 2 * (K + (fRep M f).1.val)
      unfold keyS
      rw [ppIteF (by omega), ppIteF (by omega),
        show (5 * n + 2 * (fRep M f).1.val + 0 - 5 * n) / 2 = (fRep M f).1.val by omega,
        show (5 * n + 2 * (fRep M f).1.val + 0 - 5 * n) % 2 = 0 by omega]
      rfl

lemma fRep_injective : Injective (fRep M) := fun f g h => by
  rw [← face_fRep M f, ← face_fRep M g, h]

include hrot in
lemma vRep_injective : Injective (vRep M) := fun v w h => by
  rw [← nlMap_tail_vRep M hrot v, ← nlMap_tail_vRep M hrot w, h]

include hrot in
lemma νb_injective (hvn : Injective vn) (hK : ∀ v, vn v < K) : Injective (νb M vn K) := by
  intro p q h
  rcases p with v | f <;> rcases q with w | g
  · have e : vn (nlVert M v) = vn (nlVert M w) := by simp only [νb] at h; omega
    exact congrArg Sum.inl (nlVert_injective hrot (hvn e))
  · have := hK (nlVert M v); simp only [νb] at h; omega
  · have := hK (nlVert M w); simp only [νb] at h; omega
  · have e : (fRep M f).1.val = (fRep M g).1.val := by simp only [νb] at h; omega
    exact congrArg Sum.inr (fRep_injective M (Subtype.ext (Fin.ext e)))

include hrot in
/-- **The vertex numbering is injective.** -/
theorem νX_injective (hvn : Injective vn) (hK : ∀ v, vn v < K) : Injective (νX M vn K) := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q <;> simp only [νX] at h
  · exact congrArg Sum.inl (νb_injective M hrot vn K hvn hK h)
  · have : νb M vn K p % 2 = 0 := by rcases p with v | f <;> simp [νb]
    have : νb M vn K q % 2 = 0 := by rcases q with v | f <;> simp [νb]
    omega
  · have : νb M vn K p % 2 = 0 := by rcases p with v | f <;> simp [νb]
    have : νb M vn K q % 2 = 0 := by rcases q with v | f <;> simp [νb]
    omega
  · exact congrArg Sum.inr (νb_injective M hrot vn K hvn hK (by omega))

/-- **The pendant vertices have odd numbers.** -/
theorem qpar_νX : MfDrv.QPar (pendQ (PVert M)) (νX M vn K) := by
  intro v
  have h0 : ∀ p, νb M vn K p % 2 = 0 := fun p => by rcases p with v | f <;> simp [νb]
  rcases v with p | p
  · simp only [inl_not_mem_pendQ, false_iff, νX]; have := h0 p; omega
  · simp only [pendQ, mem_image, mem_univ, true_and, Sum.inr.injEq, exists_eq, true_iff, νX]
    have := h0 p; omega

end Key

/-! ### The slots are a numbering of the darts -/

/-- **The valid slots**: the darts `old`, `up`, `down` of the darts that are not loops, and the
pendant darts at their chosen darts. -/
def ValidS (s : ℕ) : Prop :=
  (s < 3 * n ∧ IsNl M (s / 3)) ∨ (3 * n ≤ s ∧ s < 5 * n ∧ CvI M ((s - 3 * n) / 2)) ∨
    (5 * n ≤ s ∧ s < 7 * n ∧ CfI M ((s - 5 * n) / 2))

include hrot in
lemma cvI_vRep (w : SVert (nlRot M) (nlDarts M)) : CvI M (vRep M w).1.val := by
  have h := (vRep_eq_iff M (vRep M w)).1
  rw [nlMap_tail_vRep M hrot] at h
  exact h rfl

lemma cfI_fRep (f : ((nlMap M).toSep nlMap_rotTrans).Face) : CfI M (fRep M f).1.val := by
  have h := (fRep_eq_iff M (fRep M f)).1
  rw [face_fRep] at h
  exact h rfl

include hrot in
/-- **Every slot of a dart is valid.** -/
theorem enc_valid (y : TDart M ⊕ (PVert M × Bool)) : ValidS M (enc M y) := by
  rcases y with (y | y | y) | ⟨w | f, b⟩
  · have hy := y.1.2
    show ValidS M (3 * y.1.val)
    refine Or.inl ⟨show 3 * y.1.val < 3 * n by omega, ?_⟩
    rw [show 3 * y.1.val / 3 = y.1.val by omega]; exact (isNl_fin M).2 y.2
  · have hy := y.1.2
    show ValidS M (3 * y.1.val + 1)
    refine Or.inl ⟨show 3 * y.1.val + 1 < 3 * n by omega, ?_⟩
    rw [show (3 * y.1.val + 1) / 3 = y.1.val by omega]; exact (isNl_fin M).2 y.2
  · have hy := y.1.2
    show ValidS M (3 * y.1.val + 2)
    refine Or.inl ⟨show 3 * y.1.val + 2 < 3 * n by omega, ?_⟩
    rw [show (3 * y.1.val + 2) / 3 = y.1.val by omega]; exact (isNl_fin M).2 y.2
  · have hl := vRep_lt M w
    have hb : bt b ≤ 1 := by cases b <;> simp [bt]
    show ValidS M (3 * n + 2 * (vRep M w).1.val + bt b)
    refine Or.inr (Or.inl ⟨show 3 * n ≤ 3 * n + 2 * (vRep M w).1.val + bt b by omega,
      show 3 * n + 2 * (vRep M w).1.val + bt b < 5 * n by omega, ?_⟩)
    rw [show (3 * n + 2 * (vRep M w).1.val + bt b - 3 * n) / 2 = (vRep M w).1.val by omega]
    exact cvI_vRep M hrot w
  · have hl := fRep_lt M f
    have hb : bt b ≤ 1 := by cases b <;> simp [bt]
    show ValidS M (5 * n + 2 * (fRep M f).1.val + bt b)
    refine Or.inr (Or.inr ⟨show 5 * n ≤ 5 * n + 2 * (fRep M f).1.val + bt b by omega,
      show 5 * n + 2 * (fRep M f).1.val + bt b < 7 * n by omega, ?_⟩)
    rw [show (5 * n + 2 * (fRep M f).1.val + bt b - 5 * n) / 2 = (fRep M f).1.val by omega]
    exact cfI_fRep M f

/-- The dart that is not a loop of index `x`. -/
def sdOf {x : ℕ} (h : IsNl M x) : SDart (nlDarts M) := ⟨⟨x, h.1⟩, h.2⟩

/-- **Every valid slot is the slot of a dart.** -/
theorem valid_enc {s : ℕ} (hs : ValidS M s) : ∃ y, enc M y = s := by
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hm : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (show s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 by omega) with h | h | h
    · exact ⟨.inl (old (sdOf M h2)), by show 3 * (s / 3) = s; omega⟩
    · exact ⟨.inl (up (sdOf M h2)), by show 3 * (s / 3) + 1 = s; omega⟩
    · exact ⟨.inl (down (sdOf M h2)), by show 3 * (s / 3) + 2 = s; omega⟩
  · have hv := (vRep_eq_iff M (sdOf M h3.1)).2 h3
    have hv' : (vRep M ((nlMap M).tail (sdOf M h3.1))).1.val = (s - 3 * n) / 2 := by rw [hv]; rfl
    rcases (show (s - 3 * n) % 2 = 0 ∨ (s - 3 * n) % 2 = 1 by omega) with h | h
    · refine ⟨.inr (.inl ((nlMap M).tail (sdOf M h3.1)), true), ?_⟩
      show 3 * n + 2 * (vRep M _).1.val + 0 = s
      rw [hv']; omega
    · refine ⟨.inr (.inl ((nlMap M).tail (sdOf M h3.1)), false), ?_⟩
      show 3 * n + 2 * (vRep M _).1.val + 1 = s
      rw [hv']; omega
  · have hv := (fRep_eq_iff M (sdOf M h3.1)).2 h3
    have hv' : (fRep M (((nlMap M).toSep nlMap_rotTrans).face (sdOf M h3.1))).1.val =
        (s - 5 * n) / 2 := by rw [hv]; rfl
    rcases (show (s - 5 * n) % 2 = 0 ∨ (s - 5 * n) % 2 = 1 by omega) with h | h
    · refine ⟨.inr (.inr (((nlMap M).toSep nlMap_rotTrans).face (sdOf M h3.1)), true), ?_⟩
      show 5 * n + 2 * (fRep M _).1.val + 0 = s
      rw [hv']; omega
    · refine ⟨.inr (.inr (((nlMap M).toSep nlMap_rotTrans).face (sdOf M h3.1)), false), ?_⟩
      show 5 * n + 2 * (fRep M _).1.val + 1 = s
      rw [hv']; omega

include hrot in
/-- **The slots number the darts injectively.** -/
theorem enc_injective : Injective (enc M) := by
  have hb : ∀ b, bt b ≤ 1 := fun b => by cases b <;> simp [bt]
  have hbi : ∀ b c, bt b = bt c → b = c := fun b c => by cases b <;> cases c <;> simp [bt]
  have hsd : ∀ y z : SDart (nlDarts M), y.1.val = z.1.val → y = z :=
    fun y z h => Subtype.ext (Fin.ext h)
  intro p q h
  rcases p with (y | y | y) | ⟨v | f, b⟩ <;> rcases q with (z | z | z) | ⟨w | g, c⟩ <;>
    simp only [enc] at h <;>
    first
    | (have := y.1.2; have := z.1.2; omega)
    | (have := y.1.2; have := vRep_lt M w; have := hb c; omega)
    | (have := y.1.2; have := fRep_lt M g; have := hb c; omega)
    | (have := z.1.2; have := vRep_lt M v; have := hb b; omega)
    | (have := z.1.2; have := fRep_lt M f; have := hb b; omega)
    | (have := vRep_lt M v; have := fRep_lt M g; have := hb b; have := hb c; omega)
    | (have := fRep_lt M f; have := vRep_lt M w; have := hb b; have := hb c; omega)
    | skip
  · rw [hsd y z (by omega)]
  · rw [hsd y z (by omega)]
  · rw [hsd y z (by omega)]
  · have h1 := hb b; have h2 := hb c
    have e1 : (vRep M v).1.val = (vRep M w).1.val := by omega
    have e2 : bt b = bt c := by omega
    rw [vRep_injective M hrot (hsd _ _ e1), hbi b c e2]
  · have h1 := hb b; have h2 := hb c
    have e1 : (fRep M f).1.val = (fRep M g).1.val := by omega
    have e2 : bt b = bt c := by omega
    rw [fRep_injective M (hsd _ _ e1), hbi b c e2]

end Pp

end BKMNW

end PlanarFlow
