module

public import PlanarFlow.NegSSSP.Enc.SdNum

/-!
# The plain arrays of the one-face instance of a side, from flags and prefix counts

The one-face instance `sideFD` of a side `Z` (`PlanarFlow/NegSSSP/KEncConcrete.lean`) is the disc
`discMap (kst N K) Z` of `Z` in the stellar subdivision of the piece map, with face
`discFace hbd i₀`, darts `side N K Z` embedded by `sideE hbd`. The encoder
(`fencNatNL_Dk_exec`) reads its plain arrays `RV`, `NT`, `NF`, `IS`, `LN`, `G` at
`I0, I0 + nD, …, I0 + 5 nD` for some numberings `σ₀`, `νv₀`, `τ₀`.

Here the machine's description of those arrays, in terms of the plain encoding of the piece map
(numbering `c` of its darts, `stCode c` of the darts of the stellar subdivision), is shown to
**be** those arrays:

* `sdInf mem bz bA sv y`: the flag "the dart of code `y` is a dart of the disc" (its face or that
  of its reverse marked `sv` at `bz`; the reverse read at `bA`); `sdUse`: the flag "the vertex
  number `v` is the vertex of a dart of the disc"; `sdMk`: the flag "the triangle `x` is in `Z`".
* **`sd_arrays`**: if the output memory holds, at the prefix count of every dart of the disc, the
  prefix counts of its reverse, of its vertex, of its triangle (or the count of all triangles in
  `Z`, for the outer face), its source flag and its length, and the prefix counts of the darts
  of the walk, then these are the six arrays of `fencNatNL_Dk_exec` for some numberings
  `σ₀ νv₀ τ₀`, with `#DQ`, `#VQ`, `#FQ` the three final counts (`#FQ` one more than the triangles
  in `Z`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

universe u v w

/-- The flag of the darts of the disc, by code: the triangle of the code or that of its reverse
(read at `bA`) is marked `sv` (marks at `bz`, indexed by the code divided by three). -/
def sdInf (mem : ℕ → ℕ) (bz bA sv y : ℕ) : ℕ :=
  sdOr (sdEq (mem (bz + y / 3)) sv) (sdEq (mem (bz + mem (bA + y) / 3)) sv)

/-- The flag of the triangles in `Z`. -/
def sdMk (mem : ℕ → ℕ) (bz sv x : ℕ) : ℕ := sdEq (mem (bz + x)) sv

/-- The flag of the vertex numbers used by a flagged code below `n` (vertex numbers at `bV`). -/
def sdUse (mem : ℕ → ℕ) (bV : ℕ) (fl : ℕ → ℕ) (n v : ℕ) : ℕ :=
  if ∃ y < n, fl y = 1 ∧ mem (bV + y) = v then 1 else 0

/-- The face flags extended by the outer face (number `m`). -/
def sdFl (mem : ℕ → ℕ) (bz sv m y : ℕ) : ℕ := if y < m then sdMk mem bz sv y else 1

lemma sdInf_le (mem : ℕ → ℕ) (bz bA sv y : ℕ) : sdInf mem bz bA sv y ≤ 1 := by
  unfold sdInf sdOr
  have := sdEq_le (mem (bz + y / 3)) sv
  have := sdEq_le (mem (bz + mem (bA + y) / 3)) sv
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (sdEq_le (mem (bz + y / 3)) sv) with h | h <;>
    rw [h] <;> omega

lemma sdUse_le (mem : ℕ → ℕ) (bV : ℕ) (fl : ℕ → ℕ) (n v : ℕ) : sdUse mem bV fl n v ≤ 1 := by
  unfold sdUse; split_ifs <;> omega

lemma sdFl_le (mem : ℕ → ℕ) (bz sv m y : ℕ) : sdFl mem bz sv m y ≤ 1 := by
  unfold sdFl sdMk; split_ifs
  · exact sdEq_le _ _
  · exact le_rfl

lemma sdCnt_fl (mem : ℕ → ℕ) (bz sv m : ℕ) {y : ℕ} (hy : y ≤ m) :
    sdCnt (sdFl mem bz sv m) y = sdCnt (sdMk mem bz sv) y :=
  sdCnt_congr fun y' hy' => by unfold sdFl; rw [sd_ifP (by omega)]

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}

/-- **The darts of the side in the disc, by code**: a dart `d` of the disc is the image of a
dart of `side N K Z` iff its code is divisible by three (an old dart), its triangle is in `Z`,
and the dart `x` of the piece map numbered by its code divided by three is in `K`. -/
lemma sd_img
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {m : ℕ} (c : SDart (rcl N K) ≃ Fin m) (d : SDart (discDarts (kst N K) Z))
    (x : SDart (rcl N K)) (hx : (c x : ℕ) = ((kmap N K).stCode c d.1 : ℕ) / 3) :
    d ∈ (side N K Z).image (sideE hbd) ↔
      ((kmap N K).stCode c d.1 : ℕ) % 3 = 0 ∧ (kst N K).face d.1 ∈ Z ∧ x.1 ∈ K := by
  constructor
  · intro h
    obtain ⟨y, hy, hyd⟩ := mem_image.1 h
    obtain ⟨hyK, h', hf⟩ := mem_side.1 hy
    have e : d.1 = old ⟨y, h'⟩ := by rw [← hyd]; exact sideE_val hbd hy
    have hc : ((kmap N K).stCode c d.1 : ℕ) = 3 * c ⟨y, h'⟩ := by rw [e]; rfl
    have hxy : x = ⟨y, h'⟩ := c.injective (Fin.ext (by rw [hx, hc]; omega))
    refine ⟨by rw [hc]; omega, by rw [e]; exact hf, by rw [hxy]; exact hyK⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨dd, hdd⟩ := (sd_old_iff c d.1).1 h1
    have hc : ((kmap N K).stCode c d.1 : ℕ) = 3 * c dd := by rw [hdd]; rfl
    have hxd : x = dd := c.injective (Fin.ext (by rw [hx, hc]; omega))
    subst hxd
    have hf : (kst N K).face (old ⟨x.1, x.2⟩) ∈ Z := by rw [← hdd]; exact h2
    have hs : x.1 ∈ side N K Z := mem_side.2 ⟨h3, x.2, hf⟩
    refine mem_image.2 ⟨x.1, hs, Subtype.ext ?_⟩
    rw [sideE_val hbd hs, hdd]

/-- The dart of `side N K Z` embedded as `d` is the dart numbered by the code of `d` divided by
three. -/
lemma sd_img_eq
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {m : ℕ} (c : SDart (rcl N K) ≃ Fin m) (d : SDart (discDarts (kst N K) Z))
    (x : SDart (rcl N K)) (hx : (c x : ℕ) = ((kmap N K).stCode c d.1 : ℕ) / 3) {y : D}
    (hy : y ∈ side N K Z) (hyd : sideE hbd y = d) : y = x.1 := by
  obtain ⟨-, h', -⟩ := mem_side.1 hy
  have e : d.1 = old ⟨y, h'⟩ := by rw [← hyd]; exact sideE_val hbd hy
  have hc : ((kmap N K).stCode c d.1 : ℕ) = 3 * c ⟨y, h'⟩ := by rw [e]; rfl
  have hxy : x = ⟨y, h'⟩ := c.injective (Fin.ext (by rw [hx, hc]; omega))
  rw [hxy]

set_option maxHeartbeats 2000000 in
/-- **The six arrays of the one-face instance of a side** (`sideFD … i₀`: the disc
`discMap (kst N K) Z`, face `discFace hbd i₀`, darts `side N K Z` embedded by `sideE hbd`), in the
format of `fencNatNL_Dk_exec`, from flags and prefix counts over the codes `stCode c` of the
stellar subdivision: the reverses at `bA`, the vertex numbers `stVi vn fn` at `bV`, the marks of
`Z` (`sv`) at `bz`, the flags of `K` at `bK`, the lengths `(ℓ x).toNat` at `bL` and the codes of
the darts of the face `discCyc C Z` from `i₀` on at `bW`. With `inf = sdInf mem bz bA sv`,
`nD = sdCnt inf (3 m)`, the output memory `o` holding at `I0 + j nD + sdCnt inf y` (`y` the code
of a dart of the disc) the values of the six arrays computed by counts, there are numberings
`σ₀ νv₀ τ₀` (with `#DQ = nD`, `#VQ` the count of the used vertex numbers, `#FQ` one more than the
count of the triangles in `Z`) for which `o` holds the arrays `hQRV … hQG`. -/
theorem sd_arrays (hrot : N.RotTrans) (hKr : K ⊆ reps N)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (i₀ : ℕ) (ℓ : D → ℤ) {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m)
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (fn : (kmap N K).Face ≃ Fin nF)
    (mem o : ℕ → ℕ) {bz sv bA bV bK bL bW I0 : ℕ}
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ mem (bz + c x) = sv))
    (hA : ∀ x, mem (bA + (kmap N K).stCode c x) = (kmap N K).stCode c ((kst N K).α x))
    (hV : ∀ x, mem (bV + (kmap N K).stCode c x) = (kmap N K).stVi vn fn ((kst N K).vert x))
    (hKB : ∀ x, mem (bK + c x) = if x.1 ∈ K then 1 else 0)
    (hLP : ∀ x : SDart (rcl N K), x.1 ∈ K → mem (bL + c x) = (ℓ x.1).toNat)
    (hW : ∀ t < C.k, mem (bW + t) = (kmap N K).stCode c ((discCyc C Z).d ((i₀ + t) % C.k)))
    (oRV : ∀ y < 3 * m, sdInf mem bz bA sv y = 1 →
      o (I0 + sdCnt (sdInf mem bz bA sv) y) = sdCnt (sdInf mem bz bA sv) (mem (bA + y)))
    (oNT : ∀ y < 3 * m, sdInf mem bz bA sv y = 1 →
      o (I0 + sdCnt (sdInf mem bz bA sv) (3 * m) + sdCnt (sdInf mem bz bA sv) y) =
        sdCnt (sdUse mem bV (sdInf mem bz bA sv) (3 * m)) (mem (bV + y)))
    (oNF : ∀ y < 3 * m, sdInf mem bz bA sv y = 1 →
      o (I0 + 2 * sdCnt (sdInf mem bz bA sv) (3 * m) + sdCnt (sdInf mem bz bA sv) y) =
        if sdMk mem bz sv (y / 3) = 1 then sdCnt (sdMk mem bz sv) (y / 3)
        else sdCnt (sdMk mem bz sv) m)
    (oIS : ∀ y < 3 * m, sdInf mem bz bA sv y = 1 →
      o (I0 + 3 * sdCnt (sdInf mem bz bA sv) (3 * m) + sdCnt (sdInf mem bz bA sv) y) =
        sdEq (y % 3) 0 * sdMk mem bz sv (y / 3) * mem (bK + y / 3))
    (oLN : ∀ y < 3 * m, sdInf mem bz bA sv y = 1 →
      o (I0 + 4 * sdCnt (sdInf mem bz bA sv) (3 * m) + sdCnt (sdInf mem bz bA sv) y) =
        sdEq (y % 3) 0 * sdMk mem bz sv (y / 3) * mem (bK + y / 3) * mem (bL + y / 3))
    (oG : ∀ t < C.k, o (I0 + 5 * sdCnt (sdInf mem bz bA sv) (3 * m) + t) =
      sdCnt (sdInf mem bz bA sv) (mem (bW + t))) :
    ∃ (σ₀ : SDart (discDarts (kst N K) Z) ≃ Fin (Fintype.card (SDart (discDarts (kst N K) Z))))
      (νv₀ : SVert (dσ (kst N K) Z) (discDarts (kst N K) Z) ≃
        Fin (Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z))))
      (τ₀ : SFace (dσ (kst N K) Z) (discDarts (kst N K) Z) (revPerm (combOfSep (kst N K))) ≃
        Fin (Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
          (revPerm (combOfSep (kst N K)))))),
      Fintype.card (SDart (discDarts (kst N K) Z)) = sdCnt (sdInf mem bz bA sv) (3 * m) ∧
      Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z)) =
        sdCnt (sdUse mem bV (sdInf mem bz bA sv) (3 * m)) (nV + nF) ∧
      Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
        (revPerm (combOfSep (kst N K)))) = sdCnt (sdMk mem bz sv) m + 1 ∧
      (∀ d, o (I0 + σ₀ d) = σ₀ ((discMap (kst N K) Z).rev d)) ∧
      (∀ d, o (I0 + Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        νv₀ ((discMap (kst N K) Z).tail d)) ∧
      (∀ d, o (I0 + 2 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        τ₀ ((discMap (kst N K) Z).face d)) ∧
      (∀ d, o (I0 + 3 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        if d ∈ (side N K Z).image (sideE hbd) then 1 else 0) ∧
      (∀ d, o (I0 + 4 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        (faceLen (side N K Z) (sideE hbd) ℓ d).toNat) ∧
      (∀ i < C.k, o (I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + i) =
        σ₀ (discFace hbd i₀ i)) := by
  classical
  have hl' := stellar_loopless (kmap_loopless hrot hKr)
  set cd := (kmap N K).stCode c with hcd
  set inf := sdInf mem bz bA sv with hinf
  -- the marks by code
  have zmem : ∀ x, ((kst N K).face x ∈ Z ↔ mem (bz + (cd x : ℕ) / 3) = sv) := fun x => by
    rw [sd_face_old c x, hz, Equiv.apply_symm_apply]
  have hcd3 : ∀ x, (cd x : ℕ) / 3 < m := fun x => by have := (cd x).2; omega
  have inf_code : ∀ x, inf (cd x) = if x ∈ discDarts (kst N K) Z then 1 else 0 := fun x => by
    rw [hinf, sdInf, hA x, sdEq_eq, sdEq_eq, sdOr_eq]
    by_cases h : x ∈ discDarts (kst N K) Z
    · rw [sd_ifP h]; rw [mem_discDarts] at h; rw [sd_ifP (by rwa [← zmem, ← zmem])]
    · rw [sd_ifN h]; rw [mem_discDarts] at h; rw [sd_ifN (by rwa [← zmem, ← zmem])]
  have inf_le : ∀ y, inf y ≤ 1 := fun y => sdInf_le _ _ _ _ _
  have hdisc : ∀ d : SDart (discDarts (kst N K) Z), inf (cd d.1) = 1 := fun d => by
    rw [inf_code, sd_ifP d.2]
  -- the darts
  obtain ⟨σ₀, hcD, hσ⟩ := sd_equiv (α := SDart (discDarts (kst N K) Z)) id surjective_id
    (fun d => (cd d.1 : ℕ)) (n := 3 * m) (fl := inf)
    (fun a b => ⟨fun h => by rw [show a = b from h], fun h =>
      Subtype.ext (cd.injective (Fin.ext h))⟩)
    (fun d => (cd d.1).2) (fun y _ => inf_le y) (fun y hy => by
      constructor
      · intro h
        obtain ⟨x, rfl⟩ : ∃ x, (cd x : ℕ) = y := ⟨cd.symm ⟨y, hy⟩, by simp⟩
        rw [inf_code] at h
        refine ⟨⟨x, ?_⟩, rfl⟩
        by_contra hn; rw [sd_ifN hn] at h; exact absurd h (by omega)
      · rintro ⟨a, rfl⟩
        exact hdisc a)
  have hσ' : ∀ d, (σ₀ d : ℕ) = sdCnt inf (cd d.1) := fun d => hσ d
  -- the vertices
  set use := sdUse mem bV inf (3 * m) with huse
  obtain ⟨νv₀, hcV, hν⟩ := sd_equiv (discMap (kst N K) Z).tail
    (fun v => Quotient.inductionOn v fun x => ⟨x, rfl⟩)
    (fun d => ((kmap N K).stVi vn fn ((kst N K).vert d.1) : ℕ)) (n := nV + nF) (fl := use)
    (fun a b => by
      rw [discMap_tail_eq_iff]
      exact ⟨fun h => by rw [h], fun h => ((kmap N K).stVi vn fn).injective (Fin.ext h)⟩)
    (fun d => ((kmap N K).stVi vn fn _).2) (fun y _ => sdUse_le _ _ _ _ _) (fun v hv => by
      rw [huse, sdUse]
      constructor
      · intro h
        have h' : ∃ y < 3 * m, inf y = 1 ∧ mem (bV + y) = v := by
          by_contra hn; rw [sd_ifN hn] at h; exact absurd h (by omega)
        obtain ⟨y, hy, h1, h2⟩ := h'
        obtain ⟨x, rfl⟩ : ∃ x, (cd x : ℕ) = y := ⟨cd.symm ⟨y, hy⟩, by simp⟩
        have hm : x ∈ discDarts (kst N K) Z := by
          rw [inf_code] at h1
          by_contra hn; rw [sd_ifN hn] at h1; exact absurd h1 (by omega)
        exact ⟨⟨x, hm⟩, by rw [← h2, hV]⟩
      · rintro ⟨a, rfl⟩
        rw [sd_ifP ⟨cd a.1, (cd a.1).2, hdisc a, hV a.1⟩])
  have hν' : ∀ d, (νv₀ ((discMap (kst N K) Z).tail d) : ℕ) =
      sdCnt use (mem (bV + cd d.1)) := fun d => by rw [hV]; exact hν d
  -- the faces
  set fl := sdFl mem bz sv m with hfl
  have mk_iff : ∀ x, sdMk mem bz sv ((cd x : ℕ) / 3) = 1 ↔ (kst N K).face x ∈ Z := fun x => by
    rw [sdMk, sdEq_eq, zmem]; split_ifs with h <;> simp [h]
  have fcode : ∀ x, ((kmap N K).stFn c ((kst N K).face x) : ℕ) = (cd x : ℕ) / 3 :=
    fun x => (kmap N K).stFn_face c x
  obtain ⟨τ₀, hcF, hτ⟩ := sd_equiv (discMap (kst N K) Z).face
    (fun v => Quotient.inductionOn v fun x => ⟨x, rfl⟩)
    (fun d => if (kst N K).face d.1 ∈ Z then (cd d.1 : ℕ) / 3 else m) (n := m + 1) (fl := fl)
    (fun a b => by
      rw [sd_face_iff hl' hbd]
      have h1 := hcd3 a.1
      have h2 := hcd3 b.1
      by_cases ha : (kst N K).face a.1 ∈ Z <;> by_cases hb : (kst N K).face b.1 ∈ Z
      · rw [sd_ifP ha, sd_ifP hb, ← fcode, ← fcode]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · rw [h]
          · exact absurd ha h
        · intro h
          exact Or.inl ⟨ha, ((kmap N K).stFn c).injective (Fin.ext h)⟩
      · rw [sd_ifP ha, sd_ifN hb]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd (h ▸ ha) hb
          · exact absurd ha h
        · intro h; omega
      · rw [sd_ifN ha, sd_ifP hb]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h ha
          · exact absurd hb h
        · intro h; omega
      · rw [sd_ifN ha, sd_ifN hb]
        exact ⟨fun _ => rfl, fun _ => Or.inr ⟨ha, hb⟩⟩)
    (fun d => by
      split_ifs
      · have := hcd3 d.1; omega
      · omega)
    (fun y _ => sdFl_le _ _ _ _ _) (fun y hy => by
      rw [hfl, sdFl]
      by_cases hym : y < m
      · rw [sd_ifP hym]
        obtain ⟨x, hxy⟩ : ∃ x : SDart (rcl N K), (c x : ℕ) = y :=
          ⟨c.symm ⟨y, hym⟩, by simp⟩
        have hx : (cd (old x) : ℕ) / 3 = y := by rw [hcd, sd_code_old, hxy]; omega
        constructor
        · intro h
          have hf : (kst N K).face (old x) ∈ Z := (mk_iff (old x)).1 (by rw [hx]; exact h)
          exact ⟨⟨old x, mem_discDarts.2 (Or.inl hf)⟩, by
            show (if (kst N K).face (old x) ∈ Z then (cd (old x) : ℕ) / 3 else m) = y
            rw [sd_ifP hf, hx]⟩
        · rintro ⟨a, ha⟩
          by_cases hf : (kst N K).face a.1 ∈ Z
          · rw [sd_ifP hf] at ha
            rw [← ha]; exact (mk_iff a.1).2 hf
          · rw [sd_ifN hf] at ha; omega
      · rw [sd_ifN hym]
        have hym' : y = m := by omega
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨hout, -⟩ := discCyc_spec hl' hbd
        have h0 := hout 0 C.pos
        refine ⟨⟨(discCyc C Z).d 0, mem_discDarts.2 (Or.inr h0.2)⟩, ?_⟩
        show (if (kst N K).face ((discCyc C Z).d 0) ∈ Z then _ else m) = y
        rw [sd_ifN h0.1, hym'])
  have hτ' : ∀ d, (τ₀ ((discMap (kst N K) Z).face d) : ℕ) =
      sdCnt fl (if (kst N K).face d.1 ∈ Z then (cd d.1 : ℕ) / 3 else m) := fun d => hτ d
  -- the source flags
  have himg : ∀ (d : SDart (discDarts (kst N K) Z)) (x : SDart (rcl N K)),
      (c x : ℕ) = (cd d.1 : ℕ) / 3 →
      (d ∈ (side N K Z).image (sideE hbd) ↔
        (cd d.1 : ℕ) % 3 = 0 ∧ (kst N K).face d.1 ∈ Z ∧ x.1 ∈ K) :=
    fun d x hx => sd_img hbd c d x hx
  rw [← hcD] at oNT oNF oIS oLN oG
  refine ⟨σ₀, νv₀, τ₀, hcD, hcV, ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun i hi => ?_⟩
  · rw [hcF, sdCnt_succ, hfl, sdCnt_fl mem bz sv m le_rfl]
    simp [sdFl]
  · rw [hσ', hσ', oRV _ (cd d.1).2 (hdisc d), hA]
    rfl
  · rw [hσ', hν', oNT _ (cd d.1).2 (hdisc d)]
  · rw [hσ', hτ', oNF _ (cd d.1).2 (hdisc d)]
    by_cases hf : (kst N K).face d.1 ∈ Z
    · rw [sd_ifP ((mk_iff _).2 hf), sd_ifP hf, hfl, sdCnt_fl mem bz sv m (le_of_lt (hcd3 _))]
    · rw [sd_ifN (mt (mk_iff _).1 hf), sd_ifN hf, hfl, sdCnt_fl mem bz sv m le_rfl]
  · obtain ⟨x, hx⟩ : ∃ x : SDart (rcl N K), (c x : ℕ) = (cd d.1 : ℕ) / 3 :=
      ⟨c.symm ⟨_, hcd3 d.1⟩, by simp⟩
    rw [hσ', oIS _ (cd d.1).2 (hdisc d), ← hx, hKB, hx, sdEq_eq]
    have hmk : sdMk mem bz sv ((cd d.1 : ℕ) / 3) = if (kst N K).face d.1 ∈ Z then 1 else 0 := by
      by_cases hf : (kst N K).face d.1 ∈ Z
      · rw [sd_ifP hf]; exact (mk_iff _).2 hf
      · rw [sd_ifN hf]
        have := sdEq_le (mem (bz + (cd d.1 : ℕ) / 3)) sv
        have := mt (mk_iff d.1).1 hf
        unfold sdMk at this ⊢; omega
    rw [hmk]
    by_cases h : d ∈ (side N K Z).image (sideE hbd)
    · obtain ⟨h1, h2, h3⟩ := (himg d x hx).1 h
      rw [sd_ifP h, sd_ifP h1, sd_ifP h2, sd_ifP h3]
    · rw [sd_ifN h]
      by_cases h1 : (cd d.1 : ℕ) % 3 = 0 <;> by_cases h2 : (kst N K).face d.1 ∈ Z <;>
        by_cases h3 : x.1 ∈ K <;> simp only [h1, h2, h3, ite_true, ite_false, mul_zero, zero_mul]
      exact absurd ((himg d x hx).2 ⟨h1, h2, h3⟩) h
  · obtain ⟨x, hx⟩ : ∃ x : SDart (rcl N K), (c x : ℕ) = (cd d.1 : ℕ) / 3 :=
      ⟨c.symm ⟨_, hcd3 d.1⟩, by simp⟩
    rw [hσ', oLN _ (cd d.1).2 (hdisc d), ← hx, hKB, sdEq_eq, faceLen]
    by_cases h : d ∈ (side N K Z).image (sideE hbd)
    · obtain ⟨h1, h2, h3⟩ := (himg d x hx).1 h
      have h' : ∃ y ∈ side N K Z, sideE hbd y = d := mem_image.1 h
      rw [dite_eq_left_of_eq_true (eq_true h'), sd_ifP h1, sd_ifP h3, hx, show sdMk mem bz sv ((cd d.1 : ℕ) / 3) = 1 from
        (mk_iff _).2 h2, ← hx, hLP x h3]
      have hy := h'.choose_spec
      rw [sd_img_eq hbd c d x hx hy.1 hy.2]
      rcases le_total 0 (ℓ x.1) with hl | hl
      · rw [max_eq_right hl]; simp
      · rw [max_eq_left hl, Int.toNat_of_nonpos hl]; simp
    · have h' : ¬ ∃ y ∈ side N K Z, sideE hbd y = d := fun h' => h (mem_image.2 h')
      rw [dite_eq_right_of_eq_false (eq_false h')]
      by_cases h1 : (cd d.1 : ℕ) % 3 = 0 <;> by_cases h3 : x.1 ∈ K <;>
        simp only [h1, h3, ite_true, ite_false, mul_zero, zero_mul, one_mul, mul_one, Int.toNat_zero]
      have h2 : (kst N K).face d.1 ∉ Z := fun h2 => h ((himg d x hx).2 ⟨h1, h2, h3⟩)
      have e2 : sdMk mem bz sv ((cd d.1 : ℕ) / 3) = 0 := by
        have := sdEq_le (mem (bz + (cd d.1 : ℕ) / 3)) sv
        have := mt (mk_iff d.1).1 h2
        unfold sdMk at this ⊢; omega
      rw [hx, e2, zero_mul]
  · rw [oG i hi, hW i hi, hσ', discFace_val]

end Side

end NegSSSP

end PlanarFlow
