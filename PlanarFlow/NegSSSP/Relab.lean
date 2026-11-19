module

public import PlanarFlow.NegSSSP.NegRoot

/-!
# Relabeling the darts: the root frame for any numbering of the darts

The kept darts `PlanarFlow.NegSSSP.reps` choose, among the darts with the same ends, the one
whose edge has the least key `ekey`, and `ekey` uses the numbering `Fintype.equivFin D`, which a
machine cannot know. This file removes that dependence **without restating the recursion**:

* `CombMap.relab N π`: the map with its darts renamed by a permutation `π` (the dart `π x` of the
  new map is the dart `x` of `N`); planarity, transitive rotations and faces, the dual and the
  feasible potentials of the graph are preserved (`isPlane_relab`, `rotTrans_relab`,
  `faceTrans_relab`, `relab_dual`, `potOut_relab`);
* `ekeyN N μ`, **`repsN N μ`**: the kept darts for an arbitrary numbering `μ` of the darts (the
  numbering of the machine), a decidable filter (computable); **`reps_relab`**: for a numbering
  `μ : D ≃ Fin #D` and `π = μ.trans (equivFin D).symm`, `reps (N.relab π) = (repsN N μ).map π`;
* `minLen_relab`, `rtL_relab`, `GIds.relab` (the identifiers renamed), and the canonical numbering
  of a frame (`cL`, `rL`, `fL`, `cδ`, `cα`, `cσ` (with the first return `ret`), `ck`) renamed;
* `rootMemP`, `rootCfgP`: the root memory and configuration of `NegRoot.lean` with the piece `P`
  as a parameter; **`rootCfg_relab`**: the root configuration of the renamed map and identifiers
  is `rootCfgP g M ℓ₀ (repsN M.dual μ)`, a configuration whose words are those of the frame of
  `repsN M.dual μ` in the numbering of `g` — computable from the arrays of the map and `μ`;
* **`BKMNW.cMach_negsssp_exec_num`**: `cMach_negsssp_exec` from `rootCfgP g M ℓ₀ (repsN M.dual μ)`
  for every numbering `μ`: the same bounds, a `PotOut` outcome of `M.dual.graph ℓ₀` (the original
  map), written in the outcome region (`Res` for `repsN M.dual μ` in the original map).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset Function Equiv

/-! ### Lists -/

lemma List.idxOf_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Injective f) (l : List α) (a : α) : (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    by_cases h : b = a
    · subst h; simp
    · have : f b ≠ f a := fun e => h (hf e)
      simp [h, this]

namespace CombMap

variable {D V F : Type*}

/-- **The map with its darts renamed by `π`**: the dart `π x` of the new map is the dart `x`. -/
def relab (N : CombMap D V F) (π : Perm D) : CombMap D V F where
  rev d := π (N.rev (π.symm d))
  rev_rev d := by simp [N.rev_rev]
  rev_ne d h := N.rev_ne (π.symm d) (by
    have := congrArg π.symm h; simpa using this)
  tail d := N.tail (π.symm d)
  face d := N.face (π.symm d)
  next d := π (N.next (π.symm d))
  next_injective a b h := by
    have := N.next_injective (π.injective h)
    simpa using congrArg π this
  face_next d := by simp [N.face_next]
  tail_next d := by simp [N.tail_next]

variable (N : CombMap D V F) (π : Perm D)

@[simp] lemma relab_rev (x : D) : (N.relab π).rev (π x) = π (N.rev x) := by simp [relab]
@[simp] lemma relab_tail (x : D) : (N.relab π).tail (π x) = N.tail x := by simp [relab]
@[simp] lemma relab_face (x : D) : (N.relab π).face (π x) = N.face x := by simp [relab]
@[simp] lemma relab_next (x : D) : (N.relab π).next (π x) = π (N.next x) := by simp [relab]
@[simp] lemma relab_head (x : D) : (N.relab π).head (π x) = N.head x := by
  show (N.relab π).tail ((N.relab π).rev (π x)) = N.tail (N.rev x)
  rw [relab_rev, relab_tail]
@[simp] lemma relab_rot (x : D) : (N.relab π).rot (π x) = π (N.rot x) := by
  simp [rot]

lemma relab_rot_iter (k : ℕ) (x : D) : (N.relab π).rot^[k] (π x) = π (N.rot^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, relab_rot, ih]

lemma relab_next_iter (k : ℕ) (x : D) : (N.relab π).next^[k] (π x) = π (N.next^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, iterate_succ_apply, relab_next, ih]

/-- Two maps with the same reversal, tails, faces and boundary walks are equal. -/
lemma ext_fields {A B : CombMap D V F} (h1 : A.rev = B.rev) (h2 : A.tail = B.tail)
    (h3 : A.face = B.face) (h4 : A.next = B.next) : A = B := by
  cases A; cases B; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

/-- The dual of the renamed map is the renamed dual. -/
theorem relab_dual : (N.relab π).dual = N.dual.relab π := by
  refine ext_fields rfl rfl rfl (funext fun d => ?_)
  show (N.relab π).rot d = π (N.rot (π.symm d))
  conv_lhs => rw [← π.apply_symm_apply d]
  exact relab_rot N π _

lemma relab_adj : (N.relab π).Adj = N.Adj := by
  funext a b
  apply propext
  constructor
  · rintro ⟨d, h1, h2⟩
    refine ⟨π.symm d, ?_, ?_⟩
    · rw [← relab_tail N π, π.apply_symm_apply]; exact h1
    · rw [← relab_head N π, π.apply_symm_apply]; exact h2
  · rintro ⟨d, h1, h2⟩
    exact ⟨π d, by rw [relab_tail]; exact h1, by rw [relab_head]; exact h2⟩

lemma relab_dualAdj : (N.relab π).DualAdj = N.DualAdj := by
  funext a b
  apply propext
  constructor
  · rintro ⟨d, h1, h2⟩
    refine ⟨π.symm d, ?_, ?_⟩
    · rw [← relab_face N π, π.apply_symm_apply]; exact h1
    · rw [← relab_face N π, ← relab_rev, π.apply_symm_apply]; exact h2
  · rintro ⟨d, h1, h2⟩
    exact ⟨π d, by rw [relab_face]; exact h1, by rw [relab_rev, relab_face]; exact h2⟩

variable {N} in
theorem isPlane_relab [Fintype D] [Fintype V] [Fintype F] (h : N.IsPlane) :
    (N.relab π).IsPlane :=
  ⟨h.nonempty, by rw [relab_adj]; exact h.conn, by rw [relab_dualAdj]; exact h.dualConn,
    h.euler⟩

variable {N} in
theorem rotTrans_relab (h : N.RotTrans) : (N.relab π).RotTrans := by
  intro d d' e
  rw [← π.apply_symm_apply d, ← π.apply_symm_apply d', relab_tail, relab_tail] at e
  obtain ⟨k, hk⟩ := h _ _ e
  refine ⟨k, ?_⟩
  rw [← π.apply_symm_apply d, relab_rot_iter, hk, π.apply_symm_apply]

variable {N} in
theorem faceTrans_relab (h : N.FaceTrans) : (N.relab π).FaceTrans := by
  intro d d' e
  rw [← π.apply_symm_apply d, ← π.apply_symm_apply d', relab_face, relab_face] at e
  obtain ⟨k, hk⟩ := h _ _ e
  refine ⟨k, ?_⟩
  rw [← π.apply_symm_apply d, relab_next_iter, hk, π.apply_symm_apply]

/-- **Feasible potentials are preserved**: the graph of the renamed map with the renamed lengths
has the feasible potentials of the graph of the map. -/
theorem isPot_relab (ℓ : D → ℤ) (p : V → ℤ) :
    ((N.relab π).graph (ℓ ∘ π.symm)).IsPot p ↔ (N.graph ℓ).IsPot p := by
  constructor
  · intro h a
    have := h (π a)
    simpa [graph] using this
  · intro h a
    obtain ⟨x, rfl⟩ := π.surjective a
    simpa [graph] using h x

theorem potOut_relab [Fintype V] [DecidableEq V] (ℓ : D → ℤ) (o : Option (V → ℤ)) :
    NegSSSP.PotOut ((N.relab π).graph (ℓ ∘ π.symm)) o ↔ NegSSSP.PotOut (N.graph ℓ) o := by
  cases o with
  | none => simp only [NegSSSP.PotOut, isPot_relab]
  | some p => simp only [NegSSSP.PotOut, isPot_relab]

end CombMap

namespace Orbit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The first return commutes with a renaming**: if `σ' ∘ π = π ∘ σ` and `π y ∈ A' ↔ y ∈ A`,
the first return of `σ'` to `A'` at `π x` is `π` of the first return of `σ` to `A` at `x`. -/
lemma ret_conj {σ σ' : Perm α} {A A' : Finset α} (π : Perm α) (hσ : ∀ y, σ' (π y) = π (σ y))
    (hA : ∀ y, π y ∈ A' ↔ y ∈ A) (x : α) : ret σ' A' (π x) = π (ret σ A x) := by
  have hit : ∀ k y, σ'^[k] (π y) = π (σ^[k] y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih => intro y; rw [iterate_succ_apply, iterate_succ_apply, hσ, ih]
  by_cases hx : x ∈ A
  · have hx' : π x ∈ A' := (hA x).2 hx
    have e : retIdx σ' A' (π x) = retIdx σ A x := by
      refine le_antisymm (retIdx_le hx' (retIdx_pos x) ?_) (retIdx_le hx (retIdx_pos _) ?_)
      · rw [hit]; exact (hA _).2 (iterate_retIdx_mem hx)
      · rw [← hA, ← hit]; exact iterate_retIdx_mem hx'
    rw [ret_apply_of_mem hx', ret_apply_of_mem hx, e, hit]
  · have hx' : π x ∉ A' := fun h => hx ((hA x).1 h)
    rw [ret_apply_of_not_mem hx', ret_apply_of_not_mem hx]

end Orbit

namespace NegSSSP

open CombMap BKMNW Orbit

section Reps

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (N : CombMap D V F)

/-- The key of the edge of a dart for a numbering `μ` of the darts. -/
def ekeyN (μ : D → ℕ) (d : D) : ℕ := min (μ d) (μ (N.rev d))

/-- **The kept darts for a numbering `μ`**: the darts that are not loops and whose edge has the
least key `ekeyN N μ` among the darts with the same ends (`reps` is `repsN` for the numbering
`Fintype.equivFin D`). A decidable filter: computable from the arrays of the map and `μ`. -/
def repsN (μ : D → ℕ) : Finset D :=
  univ.filter fun d => N.tail d ≠ N.head d ∧
    ∀ x, N.tail x = N.tail d → N.head x = N.head d → ekeyN N μ d ≤ ekeyN N μ x

variable {N}

lemma mem_repsN {μ : D → ℕ} {d : D} : d ∈ repsN N μ ↔ N.tail d ≠ N.head d ∧
    ∀ x, N.tail x = N.tail d → N.head x = N.head d → ekeyN N μ d ≤ ekeyN N μ x := by
  simp [repsN]

variable (N)

/-- The renaming of a numbering: `π = μ.trans (equivFin D).symm`, so that `equivFin (π x) = μ x`. -/
noncomputable def numPerm (μ : D ≃ Fin (Fintype.card D)) : Perm D :=
  μ.trans (Fintype.equivFin D).symm

lemma ekey_relab (μ : D ≃ Fin (Fintype.card D)) (x : D) :
    ekey (N.relab (numPerm μ)) (numPerm μ x) = ekeyN N (fun d => (μ d : ℕ)) x := by
  unfold ekey ekeyN
  rw [relab_rev]
  simp [numPerm]

/-- **The kept darts of the renamed map are the renamed kept darts of the numbering.** -/
theorem reps_relab (μ : D ≃ Fin (Fintype.card D)) :
    reps (N.relab (numPerm μ)) = (repsN N (fun d => (μ d : ℕ))).map (numPerm μ).toEmbedding := by
  ext y
  obtain ⟨x, rfl⟩ := (numPerm μ).surjective y
  rw [mem_reps, Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_repsN, relab_tail,
    relab_head, ekey_relab]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun z hz1 hz2 => ?_⟩
    have := h2 (numPerm μ z) (by rw [relab_tail]; exact hz1) (by rw [relab_head]; exact hz2)
    rwa [ekey_relab] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun y hy1 hy2 => ?_⟩
    obtain ⟨z, rfl⟩ := (numPerm μ).surjective y
    rw [relab_tail] at hy1
    rw [relab_head] at hy2
    rw [ekey_relab]
    exact h2 z hy1 hy2

/-- The least lengths of the renamed map with the renamed lengths. -/
theorem minLen_relab (π : Perm D) (ℓ : D → ℤ) (x : D) :
    minLen (N.relab π) (ℓ ∘ π.symm) (π x) = minLen N ℓ x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨z, h1, h2, e⟩ := exists_minLen (N := N) ℓ x
    have := minLen_le (N := N.relab π) (ℓ ∘ π.symm) (d := π x) (x := π z)
      (by rw [relab_tail, relab_tail]; exact h1) (by rw [relab_head, relab_head]; exact h2)
    rw [e]
    simpa using this
  · obtain ⟨y, h1, h2, e⟩ := exists_minLen (N := N.relab π) (ℓ ∘ π.symm) (π x)
    obtain ⟨z, rfl⟩ := π.surjective y
    rw [relab_tail, relab_tail] at h1
    rw [relab_head, relab_head] at h2
    rw [e]
    simpa using minLen_le (N := N) ℓ h1 h2

end Reps

end NegSSSP

namespace NegSSSP

namespace Frame

open CombMap BKMNW Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **The identifiers renamed**: the list of darts renamed by `π`, the vertex identifiers kept. -/
def GIds.relab (g : GIds D V) (π : Perm D) : GIds D V where
  uL := g.uL.map π
  nodup := g.nodup.map π.injective
  comp d := List.mem_map.2 ⟨π.symm d, g.comp _, by simp⟩
  gv := g.gv
  gv_inj := g.gv_inj
  G := g.G
  gv_lt := g.gv_lt
  d₀ := π g.d₀

variable (g : GIds D V) (π : Perm D) (N : CombMap D V F)

@[simp] lemma GIds.relab_gv : (g.relab π).gv = g.gv := rfl
@[simp] lemma GIds.relab_G : (g.relab π).G = g.G := rfl

@[simp] lemma gd_relab (x : D) : (g.relab π).gd (π x) = g.gd x :=
  List.idxOf_map_of_injective π.injective _ _

lemma mem_map_perm {P : Finset D} {y : D} : π y ∈ P.map π.toEmbedding ↔ y ∈ P := by
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

lemma cL_relab (P : Finset D) : cL (g.relab π) (P.map π.toEmbedding) = (cL g P).map π := by
  unfold cL
  show (g.uL.map π).filter _ = _
  rw [List.filter_map]
  congr 2
  funext a
  simp only [Function.comp_apply, mem_map_perm]

lemma rL_relab (P : Finset D) :
    rL (g.relab π) (N.relab π) (P.map π.toEmbedding) = (rL g N P).map π := by
  unfold rL
  rw [cL_relab, List.filter_map, List.map_map, List.map_map]
  have e1 : ((fun d => decide ((N.relab π).rev d ∉ P.map π.toEmbedding)) ∘ π) =
      fun d => decide (N.rev d ∉ P) := by
    funext a; simp only [Function.comp_apply, relab_rev, mem_map_perm]
  have e2 : (N.relab π).rev ∘ π = π ∘ N.rev := by funext a; simp
  rw [e1, e2]

lemma fL_relab (P : Finset D) :
    fL (g.relab π) (N.relab π) (P.map π.toEmbedding) = (fL g N P).map π := by
  unfold fL; rw [cL_relab, rL_relab, List.map_append]

lemma cδ_relab (P : Finset D) (h : ℕ) :
    cδ (g.relab π) (N.relab π) (P.map π.toEmbedding) h = π (cδ g N P h) := by
  unfold cδ
  rw [fL_relab, show (g.relab π).d₀ = π g.d₀ from rfl, List.getD_map]

lemma cα_relab (P : Finset D) (h : ℕ) :
    cα (g.relab π) (N.relab π) (P.map π.toEmbedding) h = cα g N P h := by
  unfold cα
  rw [cδ_relab, fL_relab, relab_rev]
  exact List.idxOf_map_of_injective π.injective _ _

lemma rcl_relab (P : Finset D) :
    rcl (N.relab π) (P.map π.toEmbedding) = (rcl N P).map π.toEmbedding := by
  ext y
  obtain ⟨x, rfl⟩ := π.surjective y
  rw [mem_rcl, mem_map_perm, relab_rev, mem_map_perm, mem_map_perm, mem_rcl]

lemma cσ_relab (P : Finset D) (h : ℕ) :
    cσ (g.relab π) (N.relab π) (P.map π.toEmbedding) h = cσ g N P h := by
  unfold cσ
  rw [cδ_relab, fL_relab, rcl_relab,
    ret_conj (σ := rotPerm N) π (fun y => by simp only [rotPerm_apply, relab_rot]) (fun y => mem_map_perm π)]
  exact List.idxOf_map_of_injective π.injective _ _

lemma ck_relab (P : Finset D) : ck (N.relab π) (P.map π.toEmbedding) = ck N P := by
  unfold ck; rw [rcl_relab, card_map]

lemma verts_relab (P : Finset D) : verts (N.relab π) (P.map π.toEmbedding) = verts N P := by
  unfold verts
  rw [Finset.map_eq_image, image_image, image_image]
  congr 1 <;> congr 1 <;> funext x <;> simp

/-- The outcome region of the renamed frame is that of the frame. -/
lemma res_relab (L : ℕ) (P : Finset D) (o : Option (V → ℤ)) (d e : ℕ) (c : WordRAM.Config) :
    Res (g.relab π) (N.relab π) L (P.map π.toEmbedding) o d e c ↔ Res g N L P o d e c := by
  unfold Res
  rw [card_map, ck_relab, verts_relab]
  rfl

end Frame

end NegSSSP

namespace NegSSSP

open Finset WordRAM WordRAM.Machine PlanarFlow.NegSSSP.Driver PlanarFlow.NegSSSP.Frame CombMap

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- The length bound of the root is unchanged by a renaming. -/
theorem rtL_relab (M : CombMap D V F) (π : Perm D) (ℓ₀ : D → ℤ) :
    rtL (M.relab π) (ℓ₀ ∘ π.symm) = rtL M ℓ₀ := by
  unfold rtL
  rw [relab_dual, ← Equiv.sum_comp π]
  simp_rw [minLen_relab]

/-- **The root memory with the piece `P` as a parameter** (`rootMem` is `rootMemP` at
`reps M.dual`). -/
noncomputable def rootMemP (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) (P : Finset D) :
    ℕ → ℕ :=
  let n := Fintype.card D
  let L := rtL M ℓ₀
  let m := P.card
  let k := ck M.dual P
  let Hb := rtHb n L g.G
  let d := Hb + 5
  blk (Hb + 2) 1 (fun _ => d + fsz m k) <|
  blk d 1 (fun _ => n) <| blk (d + 1) 1 (fun _ => m) <| blk (d + 2) 1 (fun _ => k) <|
  blk (d + 3) 1 (fun _ => L) <|
  blk (d + 4) k (fun h => g.gd (cδ g M.dual P h)) <|
  blk (d + 4 + k) k (fun h => cα g M.dual P h) <|
  blk (d + 4 + 2 * k) k (fun h => cσ g M.dual P h) <|
  blk (d + 4 + 3 * k) k (fun h => g.gv (M.dual.tail (cδ g M.dual P h))) <|
  blk (d + 4 + 4 * k) k (fun h => g.gv (M.dual.head (cδ g M.dual P h))) <|
  blk (d + 4 + 5 * k) m (fun h => (minLen M.dual ℓ₀ (cδ g M.dual P h) + L).toNat) <|
  fun _ => 0

theorem rootMem_eq (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) :
    rootMem g M ℓ₀ = rootMemP g M ℓ₀ (reps M.dual) := rfl

/-- **The root configuration with the piece `P` as a parameter**: registers `3001 = 1`,
`3002 = Hb`, `3003 = h`, the memory `rootMemP`, reals zero, empty output. -/
noncomputable def rootCfgP (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) (P : Finset D) :
    Config where
  pc := 0
  nreg := upd (upd (upd (fun _ => 0) 3001 1) 3002 (rtHb (Fintype.card D) (rtL M ℓ₀) g.G)) 3003
    (rtH (Fintype.card D) (rtL M ℓ₀) g.G P.card (ck M.dual P))
  rreg := fun _ => 0
  nmem := rootMemP g M ℓ₀ P
  rmem := fun _ => 0
  output := []

theorem rootCfg_eq (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) :
    rootCfg g M ℓ₀ = rootCfgP g M ℓ₀ (reps M.dual) := rfl

theorem rootMemP_relab (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) (π : Perm D)
    (P : Finset D) :
    rootMemP (g.relab π) (M.relab π) (ℓ₀ ∘ π.symm) (P.map π.toEmbedding) = rootMemP g M ℓ₀ P := by
  unfold rootMemP
  rw [rtL_relab, relab_dual]
  simp only [card_map, ck_relab, cδ_relab, gd_relab, cα_relab, cσ_relab, relab_tail, relab_head,
    minLen_relab, GIds.relab_gv, GIds.relab_G]

theorem rootCfgP_relab (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ) (π : Perm D)
    (P : Finset D) :
    rootCfgP (g.relab π) (M.relab π) (ℓ₀ ∘ π.symm) (P.map π.toEmbedding) = rootCfgP g M ℓ₀ P := by
  have h1 := rootMemP_relab g M ℓ₀ π P
  unfold rootCfgP
  rw [h1, rtL_relab, relab_dual, card_map, ck_relab, GIds.relab_G]

/-- **The root configuration of the renamed map is the root configuration of the kept darts of
the numbering**: for a numbering `μ` of the darts and `π = numPerm μ`, the root configuration of
`M.relab π` with the renamed identifiers and lengths is `rootCfgP g M ℓ₀ (repsN M.dual μ)`, whose
frame is that of `repsN M.dual μ` in the numbering of `g`. -/
theorem rootCfg_relab (g : GIds D F) (M : CombMap D V F) (ℓ₀ : D → ℤ)
    (μ : D ≃ Fin (Fintype.card D)) :
    rootCfg (g.relab (numPerm μ)) (M.relab (numPerm μ)) (ℓ₀ ∘ (numPerm μ).symm) =
      rootCfgP g M ℓ₀ (repsN M.dual fun d => (μ d : ℕ)) := by
  rw [rootCfg_eq, relab_dual, reps_relab, rootCfgP_relab]

end NegSSSP

namespace BKMNW

open Finset WordRAM WordRAM.Machine NegSSSP NegSSSP.Driver NegSSSP.Frame CombMap

universe w

/-- **The field `negsssp` of `cMach` from the root frame of any numbering of the darts**: as
`cMach_negsssp_exec`, from `rootCfgP g M ℓ₀ (repsN M.dual μ)` (the frame of the kept darts for
the numbering `μ`, which a machine can compute) instead of `rootCfg g M ℓ₀` (the frame of
`reps M.dual`, defined through `Fintype.equivFin D`): within the same bound, under the same word
bound, the outcome `o` is a feasible potential of the dual with lengths `ℓ₀`, or `none` when there
is none (`PotOut`), written in the outcome region of the frame of `repsN M.dual μ` (`Res`). The
proof runs `cMach_negsssp_exec` on the map with its darts renamed by `numPerm μ`
(`rootCfg_relab`). -/
theorem cMach_negsssp_exec_num (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d) (I : Input)
    (μ : D ≃ Fin (Fintype.card D)) :
    ∃ (c' : Config) (t : ℕ) (o : Option (F → ℤ)),
      Exec I (rtW (Fintype.card D) (rtL M ℓ₀) g.G) negFix
        (rootCfgP g M ℓ₀ (repsN M.dual fun d => (μ d : ℕ))) c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 +
        (12 * Fintype.card D + 4610) ∧
      PotOut (M.dual.graph ℓ₀) o ∧
      Res g M.dual (rtL M ℓ₀) (repsN M.dual fun d => (μ d : ℕ)) o
        (rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5)
        (rtH (Fintype.card D) (rtL M ℓ₀) g.G (repsN M.dual fun d => (μ d : ℕ)).card
          (ck M.dual (repsN M.dual fun d => (μ d : ℕ)))) c' ∧
      c'.output = [] := by
  set π := numPerm μ with hπ
  have hM' : (M.relab π).dual.IsPlane := by rw [relab_dual]; exact isPlane_relab π hM
  have hrot' : (M.relab π).dual.RotTrans := by rw [relab_dual]; exact rotTrans_relab π hrot
  have hface' : (M.relab π).dual.FaceTrans := by rw [relab_dual]; exact faceTrans_relab π hface
  have hneg' : ∀ d, (M.relab π).dual.tail d = (M.relab π).dual.head d →
      0 ≤ (ℓ₀ ∘ π.symm) d := by
    rw [relab_dual]
    intro d hd
    obtain ⟨x, rfl⟩ := π.surjective d
    rw [relab_tail, relab_head] at hd
    simpa using hneg x hd
  obtain ⟨c', t, o, ex, ht, hpot, hres, hout⟩ :=
    cMach_negsssp_exec C C₀ hC (g.relab π) hM' hrot' hface' hneg' I
  rw [rootCfg_relab, rtL_relab, GIds.relab_G] at ex
  rw [relab_dual, potOut_relab] at hpot
  rw [rtL_relab, GIds.relab_G, relab_dual, reps_relab, card_map, ck_relab, res_relab] at hres
  exact ⟨c', t, o, ex, ht, hpot, hres, hout⟩

end BKMNW

namespace NegSSSP

open PlanarFlow.NegSSSP.Frame

universe w'

variable {D F : Type w'} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- **The numbering of the darts by their identifiers** (`gd d`, the index of `d` in `g.uL`), as
an equivalence with `Fin #D`. -/
noncomputable def gdEquiv (g : GIds D F) : D ≃ Fin (Fintype.card D) :=
  Equiv.ofBijective (fun d => ⟨g.gd d, by rw [← uL_length g]; exact g.gd_lt d⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => g.gd_inj (congrArg Fin.val h), (Fintype.card_fin _).symm⟩)

@[simp] lemma gdEquiv_val (g : GIds D F) (d : D) : (gdEquiv g d : ℕ) = g.gd d := rfl

end NegSSSP

namespace BKMNW

open Finset WordRAM WordRAM.Machine NegSSSP NegSSSP.Driver NegSSSP.Frame CombMap

universe w

/-- **The field `negsssp` of `cMach` from the root frame of the kept darts in the numbering of
the identifiers**: `cMach_negsssp_exec_num` with `μ = gdEquiv g`, so that the kept darts are
`repsN M.dual g.gd` (the least identifier `min (gd d) (gd (rev d))` per pair of ends). -/
theorem cMach_negsssp_exec_gd (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d) (I : Input) :
    ∃ (c' : Config) (t : ℕ) (o : Option (F → ℤ)),
      Exec I (rtW (Fintype.card D) (rtL M ℓ₀) g.G) negFix (rootCfgP g M ℓ₀ (repsN M.dual g.gd))
        c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 +
        (12 * Fintype.card D + 4610) ∧
      PotOut (M.dual.graph ℓ₀) o ∧
      Res g M.dual (rtL M ℓ₀) (repsN M.dual g.gd) o (rtHb (Fintype.card D) (rtL M ℓ₀) g.G + 5)
        (rtH (Fintype.card D) (rtL M ℓ₀) g.G (repsN M.dual g.gd).card
          (ck M.dual (repsN M.dual g.gd))) c' ∧
      c'.output = [] :=
  cMach_negsssp_exec_num C C₀ hC g hM hrot hface hneg I (gdEquiv g)

end BKMNW

end PlanarFlow
