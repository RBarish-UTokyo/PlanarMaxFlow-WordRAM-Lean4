module

public import PlanarFlow.BKMNW.EncProg
public import PlanarFlow.BKMNW.SepM

/-!
# Miller's separator from the index arrays of a piece: encode, run, decode on the machine

`encProg ; msep`: from the index arrays of a map (`REV[c d] = c (α d)`, `SIG[c d] = c (σ d)`,
`EX[c d] = ex d` for a numbering `c` of the darts), the machine builds the plain encoding
(`encProg_exec`) and runs Miller's program on it (`msep_spec`). The numberings of the vertices and
faces are the machine's own (orbit labels renumbered contiguously); they are equivalences
(`exists_num`), so `msep_spec` applies with them.

* `EncArr M c ex mem B₀ SIGb EXb` (the input arrays), `encWt M ex` (the weights: `Σ ex` on a
  vertex, the number of darts on a face), `arr_iter`, `arr_rel`, `exists_num`, `saF_reindex`,
  `aEnd10_mono`.
* **`encMsep_exec`**: the run of `encProg ; msep` within `encT m + msT m (#Q + #Face)` steps ends
  with Miller's separator of `M.stellar` in the output form, `SepOK (wR (encWt M ex))
  (6 √(#Q + #Face) + 4)`; **`encMsep_dec`** (decoded: `decSep (stCode c) (stFn c) c' = some R`).
* the frame image `encIn` (arrays at `B₀ = aEnd10 m (2m)`, `B₀ + 7m`, `B₀ + 8m`, scratch at
  `B₀ + 9m`), **`encRun`** (encode on the machine, run `msep`, decode), **`encRun_spec`**;
  **`sepE M : SepFn M`** (`encRun` on `psep`, weights `coreWt (fun _ => 1) (coreExW τ N ex)` are
  `encWt`), **`sepE_ok`**, **`maxflow_plane_cost_decME`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset PlanarSeparator PlanarSeparator.Map PlanarSeparator.MillerProg
  WordRAM WordRAM.Machine Relation

section Generic

variable {D Q X : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- The input arrays of `encProg` for a numbering `c` of the darts. -/
structure EncArr (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) (mem : ℕ → ℕ)
    (B₀ SIGb EXb : ℕ) : Prop where
  rev : ∀ d, mem (B₀ + c d) = c (M.α d)
  sig : ∀ d, mem (SIGb + c d) = c (M.σ d)
  ex : ∀ d, mem (EXb + c d) = ex d

/-- The weights of the stellar subdivision: `Σ ex` of its darts on a vertex, the number of its
darts on a face. -/
def encWt (M : Map D Q) (ex : D → ℕ) : Q ⊕ M.Face → ℕ :=
  Sum.elim (fun v => ∑ d with M.vert d = v, ex d) (fun f => ∑ d with M.face d = f, 1)

lemma encWt_sum (M : Map D Q) (ex : D → ℕ) :
    ∑ x, encWt M ex x = ∑ d, ex d + Fintype.card D := by
  rw [Fintype.sum_sum_type]
  simp only [encWt, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_fiberwise (s := univ) (g := M.vert) (f := ex),
    Finset.sum_fiberwise (s := univ) (g := M.face) (f := fun _ => 1)]
  simp

lemma idx_surj {m : ℕ} (c : D ≃ Fin m) {j : ℕ} (hj : j < m) : ∃ d, (c d : ℕ) = j :=
  ⟨c.symm ⟨j, hj⟩, by simp⟩

/-- Iterates of an index array realizing a permutation. -/
lemma arr_iter {m : ℕ} (c : D ≃ Fin m) {f : ℕ → ℕ} {π : Equiv.Perm D}
    (hf : ∀ d, f (c d) = c (π d)) (k : ℕ) (d : D) : f^[k] (c d) = c ((π ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hf, pow_succ', Equiv.Perm.mul_apply]

lemma arr_rel {m : ℕ} (c : D ≃ Fin m) {f : ℕ → ℕ} {π : Equiv.Perm D}
    (hf : ∀ d, f (c d) = c (π d)) (d d' : D) :
    (∃ k, f^[k] (c d) = c d') ↔ π.SameCycle d d' := by
  constructor
  · rintro ⟨k, hk⟩
    rw [arr_iter c hf] at hk
    exact ⟨k, by rw [zpow_natCast]; exact c.injective (Fin.ext hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, by rw [arr_iter c hf, hk]⟩

/-- A numbering by keys that are equal exactly on the fibres of a surjection and onto `[0, n)`
is an equivalence. -/
lemma exists_num {f : D → X} (hf : Function.Surjective f) (key : D → ℕ) {n : ℕ}
    (hk : ∀ d d', key d = key d' ↔ f d = f d') (hlt : ∀ d, key d < n)
    (hon : ∀ r < n, ∃ d, key d = r) : ∃ e : X ≃ Fin n, ∀ d, (e (f d) : ℕ) = key d := by
  classical
  let s : X → D := fun x => (hf x).choose
  have hs : ∀ x, f (s x) = x := fun x => (hf x).choose_spec
  let g : X → Fin n := fun x => ⟨key (s x), hlt _⟩
  have hinj : Function.Injective g := fun x y h => by
    have : key (s x) = key (s y) := congrArg Fin.val h
    rw [hk, hs, hs] at this; exact this
  have hsur : Function.Surjective g := fun r => by
    obtain ⟨d, hd⟩ := hon r r.2
    refine ⟨f d, Fin.ext ?_⟩
    show key (s (f d)) = r
    rw [(hk _ _).2 (hs (f d)), hd]
  refine ⟨Equiv.ofBijective g ⟨hinj, hsur⟩, fun d => ?_⟩
  show key (s (f d)) = key d
  exact (hk _ _).2 (hs (f d))

/-- The sums of `saF` over the dart numbers. -/
lemma saF_reindex {m : ℕ} (c : D ≃ Fin m) (key val : ℕ → ℕ) (k : ℕ) :
    saF key val m k = ∑ d with key (c d) = k, val (c d) := by
  unfold saF
  rw [sum_filter, sum_filter, ← Fin.sum_univ_eq_sum_range (fun j => if key j = k then val j else 0)]
  exact (Fintype.sum_equiv c _ _ (fun d => rfl)).symm

lemma aEnd10_mono {k n n' : ℕ} (h : n ≤ n') : aEnd10 k n ≤ aEnd10 k n' := by
  unfold aEnd10 aEnd
  have h1 : Nat.log 2 n ≤ Nat.log 2 n' := Nat.log_mono_right h
  have h2 : (Nat.log 2 n + 2) * n ≤ (Nat.log 2 n' + 2) * n' :=
    Nat.mul_le_mul (by omega) h
  omega

end Generic

section Run

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
variable {P : Input} {W : ℕ}

lemma sum_range_reindex {m : ℕ} (c : D ≃ Fin m) (f : ℕ → ℕ) :
    ∑ j ∈ range m, f j = ∑ d, f (c d) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Fintype.sum_equiv c _ _ (fun d => rfl)).symm

set_option maxHeartbeats 1600000 in
/-- **Encode on the machine and run Miller's program**: from the index arrays of a plane map
without loops (`EncArr`), `encProg ; msep` ends within `encT m + msT m (#Q + #Face)` steps with
a separator `R` of `M.stellar` in the output form (`r641 = R.1.k`, the dart numbers `stCode c`
at `r640`, the face marks at `r642`) meeting `SepOK (wR (encWt M ex)) (6 √(#Q + #Face) + 4)`. -/
theorem encMsep_exec (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) (c₀ : Config)
    (hc : WordsBounded W c₀) {B₀ SIGb EXb Sb : ℕ}
    (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (r60 : c₀.nreg 4660 = m) (r61 : c₀.nreg 4661 = B₀) (r62 : c₀.nreg 4662 = SIGb)
    (r63 : c₀.nreg 4663 = EXb) (r64 : c₀.nreg 4664 = Sb)
    (hA : EncArr M c ex c₀.nmem B₀ SIGb EXb)
    (lay : B₀ + 7 * m ≤ SIGb ∧ SIGb + m ≤ EXb ∧ EXb + m ≤ Sb ∧ Sb + 13 * m + 7 ≤ W)
    (hB : aEnd10 m (2 * m) ≤ B₀)
    (hz5 : ∀ a, B₀ + 5 * m ≤ a → a < B₀ + 7 * m → c₀.nmem a = 0)
    (hzS : ∀ a, Sb ≤ a → a < Sb + 13 * m + 7 → c₀.nmem a = 0)
    (hWt : 11 * m + 3 * (∑ d, ex d + m) + 4 ≤ W) :
    ∃ c' t, Exec P W (.seq encProg msep) c₀ c' t ∧
      t ≤ encT m + msT m (Fintype.card Q + Fintype.card M.Face) ∧
      ∃ R : M.stellar.SCycle × Finset M.stellar.Face,
        c'.nreg 641 = R.1.k ∧
        (∀ i < R.1.k, c'.nmem (c'.nreg 640 + i) = M.stCode c (R.1.d i)) ∧
        (∀ G, G ∈ R.2 ↔ (c'.nmem (c'.nreg 642 + M.stFn c G) ≠ c'.nreg 643 ↔
          c'.nreg 644 = 1)) ∧
        SepOK (wR (encWt M ex)) (6 * Nat.sqrt (Fintype.card Q + Fintype.card M.Face) + 4) R := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  have hcd : ∀ d, (c d : ℕ) < m := fun d => (c d).2
  have hD : Fintype.card D = m := by rw [Fintype.card_congr c, Fintype.card_fin]
  -- the arrays
  have hR : PermArr (fun u => c₀.nmem (B₀ + u)) (fun u => c₀.nmem (B₀ + u)) m := by
    refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩ <;>
      obtain ⟨d, rfl⟩ := idx_surj c hu <;> simp only [hA.rev, M.α_α, hcd]
  have hSl : ∀ j < m, c₀.nmem (SIGb + j) < m := fun j hj => by
    obtain ⟨d, rfl⟩ := idx_surj c hj; rw [hA.sig]; exact hcd _
  have hSi : ∀ i < m, ∀ j < m, c₀.nmem (SIGb + i) = c₀.nmem (SIGb + j) → i = j := by
    intro i hi j hj e
    obtain ⟨d, rfl⟩ := idx_surj c hi
    obtain ⟨d', rfl⟩ := idx_surj c hj
    rw [hA.sig, hA.sig] at e
    rw [M.σ.injective (c.injective (Fin.ext e))]
  have hsum : ∑ j ∈ range m, c₀.nmem (EXb + j) ≤ W := by
    rw [sum_range_reindex c]; simp only [hA.ex]; omega
  obtain ⟨c₁, k₁, e₁, hk₁, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, p0, p3, pV, pF, -, -,
    -, -⟩ := encProg_exec (P := P) c₀ hc r60 r61 r62 r63 r64 ⟨l1, l2, l3, l4⟩ hR hSl hSi
      hz5 hzS hsum
  have hw₁ := e₁.wb_right
  set nV := c₁.nreg 391 with hnV
  set nF := c₁.nreg 392 with hnF
  -- the vertex numbering
  have hsig : ∀ d, (fun u => c₀.nmem (SIGb + u)) (c d) = c (M.σ d) := fun d => hA.sig d
  have hvert : ∀ d d', M.vert d = M.vert d' ↔ M.σ.SameCycle d d' := fun d d' =>
    ⟨M.sameCycle d d', fun h => by
      obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq; exact (M.vert_σ_pow k d).symm⟩
  obtain ⟨vn, hvn⟩ := exists_num (f := M.vert) hM.exists_dart
    (fun d => c₁.nmem (B₀ + 3 * m + c d)) (n := nV)
    (fun d d' => by rw [o3 _ (hcd d) _ (hcd d'), arr_rel c hsig, hvert])
    (fun d => o4 _ (hcd d))
    (fun r hr => by obtain ⟨j, hj, e⟩ := o5 r hr; obtain ⟨d, rfl⟩ := idx_surj c hj; exact ⟨d, e⟩)
  -- the face numbering
  have hphi : ∀ d, (fun u => c₀.nmem (SIGb + c₀.nmem (B₀ + u))) (c d) = c (M.φ d) := fun d => by
    simp only [hA.rev, hA.sig, φ_apply]
  obtain ⟨fn, hfn⟩ := exists_num (f := M.face) M.face_surjective
    (fun d => c₁.nmem (B₀ + 4 * m + c d)) (n := nF)
    (fun d d' => by rw [o6 _ (hcd d) _ (hcd d'), arr_rel c hphi, face_eq_face_iff])
    (fun d => o7 _ (hcd d))
    (fun r hr => by obtain ⟨j, hj, e⟩ := o8 r hr; obtain ⟨d, rfl⟩ := idx_surj c hj; exact ⟨d, e⟩)
  have hQ : Fintype.card Q = nV := by rw [Fintype.card_congr vn, Fintype.card_fin]
  have hF : Fintype.card M.Face = nF := by rw [Fintype.card_congr fn, Fintype.card_fin]
  -- the encoding
  have hE : Enc M c vn fn c₁.nmem B₀ (B₀ + m) (B₀ + 2 * m) (B₀ + 3 * m) (B₀ + 4 * m) := by
    refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_⟩
    · rw [o0 _ (hcd d), hA.rev]
    · rw [o1 _ (hcd d), hA.rev, hA.sig, φ_apply]
    · have := o2 _ (hcd (M.φ.symm d))
      rwa [hA.rev, hA.sig, ← φ_apply, Equiv.apply_symm_apply] at this
    · rw [hvn d]
    · rw [hfn d]
  have hw : ∀ x, c₁.nmem (B₀ + 5 * m + M.stVi vn fn x) = encWt M ex x := by
    rintro (v | f)
    · rw [stVi_inl, o9 _ (vn v).2, saF_reindex c]
      simp only [encWt, Sum.elim_inl]
      refine sum_congr (by ext d; simp only [mem_filter, mem_univ, true_and]
                           rw [← hvn d]; exact ⟨fun h => vn.injective (Fin.ext h),
                             fun h => by rw [h]⟩) (fun d _ => hA.ex d)
    · rw [stVi_inr, ← Nat.add_assoc, o10 _ (fn f).2, saF_reindex c]
      simp only [encWt, Sum.elim_inr]
      refine sum_congr (by ext d; simp only [mem_filter, mem_univ, true_and]
                           rw [← hfn d]; exact ⟨fun h => fn.injective (Fin.ext h),
                             fun h => by rw [h]⟩) (fun d _ => rfl)
  have hS : ∑ x, encWt M ex x = ∑ d, ex d + m := by rw [encWt_sum, hD]
  have hnVm : nV + nF ≤ 2 * m := by omega
  obtain ⟨c₂, t₂, e₂, ht₂, R, h1, h2, h3, h4, -⟩ := msep_spec (P := P) (W := W) M c vn fn
    (encWt M ex) hM hl hm2 (by rw [hS]; omega) hE hw
    (le_trans (aEnd10_mono hnVm) hB) (by omega) (by rw [hS]; omega) hw₁ p0 rfl rfl p3
  refine ⟨c₂, k₁ + t₂, .seq e₁ e₂, ?_, R, h1, h2, h3, ?_⟩
  · rw [hQ, hF]; omega
  · rw [hQ, hF]; exact h4

/-- **Decoded**: the final configuration of `encProg ; msep` decodes (`decSep` with `stCode c`,
`stFn c`) to a separator meeting `SepOK (wR (encWt M ex)) (6 √(#Q + #Face) + 4)`. -/
theorem encMsep_dec (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) (c₀ : Config)
    (hc : WordsBounded W c₀) {B₀ SIGb EXb Sb : ℕ}
    (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m)
    (r60 : c₀.nreg 4660 = m) (r61 : c₀.nreg 4661 = B₀) (r62 : c₀.nreg 4662 = SIGb)
    (r63 : c₀.nreg 4663 = EXb) (r64 : c₀.nreg 4664 = Sb)
    (hA : EncArr M c ex c₀.nmem B₀ SIGb EXb)
    (lay : B₀ + 7 * m ≤ SIGb ∧ SIGb + m ≤ EXb ∧ EXb + m ≤ Sb ∧ Sb + 13 * m + 7 ≤ W)
    (hB : aEnd10 m (2 * m) ≤ B₀)
    (hz5 : ∀ a, B₀ + 5 * m ≤ a → a < B₀ + 7 * m → c₀.nmem a = 0)
    (hzS : ∀ a, Sb ≤ a → a < Sb + 13 * m + 7 → c₀.nmem a = 0)
    (hWt : 11 * m + 3 * (∑ d, ex d + m) + 4 ≤ W) :
    ∃ c' t, Exec P W (.seq encProg msep) c₀ c' t ∧
      t ≤ encT m + msT m (Fintype.card Q + Fintype.card M.Face) ∧
      ∃ R, decSep (M.stCode c) (M.stFn c) c' = some R ∧
        SepOK (wR (encWt M ex)) (6 * Nat.sqrt (Fintype.card Q + Fintype.card M.Face) + 4) R := by
  obtain ⟨c', t, e, ht, R, h1, h2, h3, h4⟩ := encMsep_exec (P := P) M c ex c₀ hc hM hl hm2
    r60 r61 r62 r63 r64 hA lay hB hz5 hzS hWt
  obtain ⟨C, hC, hk, hd⟩ := decSep_eq (M.stCode c) (M.stFn c) R h1 h2 h3
  exact ⟨c', t, e, ht, (C, R.2), hC, sepOK_congr hk hd h4⟩

end Run

section Frame

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

/-- The base of the encoding in the frame image. -/
abbrev encB' (m : ℕ) : ℕ := aEnd10 m (2 * m)

/-- The word bound of the run from the frame image. -/
abbrev encWE (m S : ℕ) : ℕ := encB' m + 22 * m + 3 * S + 14

/-- **The frame image of a piece**: the index arrays `REV` at `B₀ = aEnd10 m (2m)`, `SIG` at
`B₀ + 7m`, `EX` at `B₀ + 8m` (everything else zero, scratch at `B₀ + 9m`), the registers
`4660 … 4664` of `encProg`. -/
noncomputable def encIn (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ) : Config where
  pc := 0
  nreg r := if r = 4660 then m else if r = 4661 then encB' m else
    if r = 4662 then encB' m + 7 * m else if r = 4663 then encB' m + 8 * m else
    if r = 4664 then encB' m + 9 * m else 0
  rreg _ := 0
  nmem a :=
    if encB' m ≤ a ∧ a < encB' m + m then darr c (fun d => c (M.α d)) (a - encB' m) else
    if encB' m + 7 * m ≤ a ∧ a < encB' m + 8 * m then
      darr c (fun d => c (M.σ d)) (a - (encB' m + 7 * m)) else
    if encB' m + 8 * m ≤ a ∧ a < encB' m + 9 * m then darr c ex (a - (encB' m + 8 * m))
    else 0
  rmem _ := 0
  output := []

lemma darr_le_sum {m : ℕ} (c : D ≃ Fin m) (f : D → ℕ) (i : ℕ) : darr c f i ≤ ∑ d, f d := by
  unfold darr
  split_ifs
  · exact single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_univ _)
  · exact Nat.zero_le _

lemma darr_lt {m : ℕ} (c : D ≃ Fin m) (f : D → D) (i : ℕ) : darr c (fun d => c (f d)) i ≤ m := by
  unfold darr
  split_ifs
  · exact (c _).2.le
  · exact Nat.zero_le _

variable (M : Map D Q) {m : ℕ} (c : D ≃ Fin m) (ex : D → ℕ)

lemma encIn_wb : WordsBounded (encWE m (∑ d, ex d + m)) (encIn M c ex) := by
  refine ⟨fun r => ?_, fun a => ?_⟩
  · simp only [encIn, encWE]; split_ifs <;> omega
  · have h1 := darr_lt c M.α (a - encB' m)
    have h2 := darr_lt c M.σ (a - (encB' m + 7 * m))
    have h3 := darr_le_sum c ex (a - (encB' m + 8 * m))
    simp only [encIn, encWE]; split_ifs <;> omega

lemma encIn_arr : EncArr M c ex (encIn M c ex).nmem (encB' m) (encB' m + 7 * m)
    (encB' m + 8 * m) := by
  have hd := fun d => (c d).2
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩ <;> (have := hd d; simp only [encIn])
  · rw [iteT ⟨by omega, by omega⟩, show encB' m + c d - encB' m = c d by omega, darr_c]
  · rw [iteF (by omega), iteT ⟨by omega, by omega⟩,
      show encB' m + 7 * m + c d - (encB' m + 7 * m) = c d by omega, darr_c]
  · rw [iteF (by omega), iteF (by omega), iteT ⟨by omega, by omega⟩,
      show encB' m + 8 * m + c d - (encB' m + 8 * m) = c d by omega, darr_c]

/-- **Miller's separator from the frame image of a piece**: run `encProg ; msep` on `encIn` and
decode. The encoding is computed by machine instructions from the index arrays. -/
noncomputable def encRun : Option (M.stellar.SCycle × Finset M.stellar.Face) :=
  (runOut (.seq encProg msep) msP (encWE m (∑ d, ex d + m)) (encIn M c ex)).bind
    (decSep (M.stCode c) (M.stFn c))

/-- **The run from the frame image**: within `encT m + msT m (#Q + #Face)` steps, and its decoded
output is a separator. -/
theorem encRun_exec (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m) :
    ∃ c' t, Exec msP (encWE m (∑ d, ex d + m)) (.seq encProg msep) (encIn M c ex) c' t ∧
      t ≤ encT m + msT m (Fintype.card Q + Fintype.card M.Face) ∧
      ∃ R, encRun M c ex = some R ∧
        SepOK (wR (encWt M ex)) (6 * Nat.sqrt (Fintype.card Q + Fintype.card M.Face) + 4) R := by
  obtain ⟨c', t, e, ht, R, hR, hok⟩ := encMsep_dec (P := msP) M c ex (encIn M c ex)
    (B₀ := encB' m) (SIGb := encB' m + 7 * m) (EXb := encB' m + 8 * m) (Sb := encB' m + 9 * m)
    (encIn_wb M c ex) hM hl hm2 (by simp [encIn]) (by simp [encIn]) (by simp [encIn])
    (by simp [encIn]) (by simp [encIn]) (encIn_arr M c ex) ⟨by omega, by omega, by omega,
      by unfold encWE; omega⟩ le_rfl
    (fun a h1 h2 => by simp only [encIn]; rw [iteF (by omega), iteF (by omega), iteF (by omega)])
    (fun a h1 h2 => by simp only [encIn]; rw [iteF (by omega), iteF (by omega), iteF (by omega)])
    (by unfold encWE; omega)
  refine ⟨c', t, e, ht, R, ?_, hok⟩
  rw [encRun, runOut_eq e, Option.bind_some, hR]

theorem encRun_spec (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hm2 : 2 ≤ m) :
    ∃ R, encRun M c ex = some R ∧
      SepOK (wR (encWt M ex)) (6 * Nat.sqrt (Fintype.card Q + Fintype.card M.Face) + 4) R := by
  obtain ⟨-, -, -, -, h⟩ := encRun_exec M c ex hM hl hm2
  exact h

end Frame

section Piece

open Function Equiv Orbit CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

open Classical in
/-- **The separator of the split chain with the encoding built by the machine**: `encRun` (the
index arrays of the piece map `psep M hσ hB` in the frame, numbered by `Fintype.equivFin`; the
machine builds the plain encoding (`encProg`), runs `msep`, the output is decoded). -/
noncomputable def sepE (M : CombMap D V F) : SepFn M := fun N τ hσ hB ex =>
  encRun (psep M hσ hB) (Fintype.equivFin _) (fun x => ex x.1)

variable {M : CombMap D V F}

open Classical in
lemma encWt_psep {N : Finset D} {τ : Perm D} (hσ : Stable τ N) (hB : Stable (revPerm M) N)
    (ex : D → ℕ) :
    encWt (psep M hσ hB) (fun x => ex x.1) = coreWt hσ hB (fun _ => 1) (coreExW τ N ex) := by
  funext x
  rcases x with q | f
  · simp only [encWt, coreWt, coreExW, Sum.elim_inl]
    convert rfl
    exact (psep_vert hσ hB _).symm
  · simp only [encWt, coreWt, Sum.elim_inr]
    try convert rfl

open Classical in
/-- **The machine's separator from the frame image meets the specification of the split chain**
(on a map without loops). -/
theorem sepE_ok (hloopM : ∀ d, M.head d ≠ M.tail d) (Hs : List (Finset V)) :
    SepFnOK M (sepE M) Hs := by
  intro N τ hN ex hne _
  obtain ⟨x₀, hx₀⟩ := hne
  have hl : ∀ d, (psep M hN.stable hN.rev).vert ((psep M hN.stable hN.rev).α d) ≠
      (psep M hN.stable hN.rev).vert d := by
    intro d h
    have h' := (hN.vert _ ((psep M hN.stable hN.rev).α d).2 _ d.2).1 ((psep_vert_eq _ _).1 h)
    rw [psep_α, CombMap.tail_rev] at h'
    rcases h' with e | ⟨H, hH, h1, h2⟩
    · exact hloopM d.1 e
    · exact hN.inner d.1 d.2 ⟨H, hH, h2, h1⟩
  have hP := psep_isPlane hN.stable hN.rev hx₀ hN.conn' hN.gap
  have hm2 : 2 ≤ Fintype.card (SDart N) := by
    rw [Fintype.card_coe]
    have hr : M.rev x₀ ∈ N := hN.rev x₀ hx₀
    have hsub : ({x₀, M.rev x₀} : Finset D) ⊆ N := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hx₀
      · exact hr
    have := card_le_card hsub
    rwa [card_pair (M.rev_ne x₀).symm] at this
  obtain ⟨R, hR, hok⟩ := encRun_spec (psep M hN.stable hN.rev) (Fintype.equivFin _)
    (fun x => ex x.1) hP hl hm2
  rw [encWt_psep] at hok
  obtain ⟨h1, h2, h3, h4⟩ := coreSep_of_sepOK hN.stable hN.rev (fun _ => 1) (coreExW τ N ex)
    le_rfl hok
  exact ⟨R.1, R.2, hR, h1, h2, h3, h4⟩

end Piece

section Head

open Function Equiv Orbit CombMap

universe w

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Maximum flow in plane graphs in `O(n log³ n)` with Miller's separator and its input encoding
computed by the machine**: `maxflow_plane_cost_decE` for `sepF = sepE (lpreMap M)` (the index
arrays of the piece map in the frame; `encProg` builds the plain encoding, `msep` the separator).
Parameters: an enumeration `e` of the darts of `lpreMap M` and a dart `d₀`. Constants as in
`maxflow_plane_cost`. -/
theorem maxflow_plane_cost_decME (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepE (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost_decE hM hrot hface hu hST e hsurj d₀ (sepE (lpreMap M))
    (fun Hs => sepE_ok (preMap_loopless nlMap_loopless nlE_tail) Hs) hc

end Head

end BKMNW

end PlanarFlow
