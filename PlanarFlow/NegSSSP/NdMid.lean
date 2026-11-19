module

public import PlanarFlow.NegSSSP.NdFront

/-!
# The node step: the numbering, the children's values, the combination

After the front (`NdFront.lean`), when both children have an outcome:

* `ndB1` and **`ndNum_exec`**: the numbering of the vertices of the piece (`nmProg` on the
  frame's `2k` identifier columns, as in the leaf): `O` at the heap top `h`, `I` at `h + 2k`.
* **`nd_gather`**: `cgProg` on a child's outcome region (`Res … (some f)`) in the node's
  numbering: `0` off the child's vertices, `(f x + L).toNat + 1` on them.
* `ndB2`, `ndB3`, `ndB4` (the registers of the two gathers and of the combination).
* **`ndB_exec`**: `ndB = ndB1 ; nmProg ; ndB2 ; cgProg ; ndB3 ; cgProg ; ndB4 ; ndCmb` writes
  `F[v] = (ndComb N P₀ f₀ f₁ (ι v) + L).toNat` at `h + 8k + v` and `r2496 = #bdry N P₀ P₁`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

/-- The registers of `nmProg`: `n = 2k`, `A = d + 3k + 4`, the table `Gt`, `O = h`,
`I = h + 2k`. -/
def ndB1 (Gt : ℕ) : Stmt := block [.addN 2875 2475 2475, .constN 2483 3, .mulN 2484 2483 2475,
  .addN 2484 2484 3004, .constN 2483 4, .addN 2876 2484 2483, .constN 2877 Gt,
  .copyN 2878 3003, .addN 2879 3003 2875]

theorem ndB1_exec (Gt : ℕ) (c : Config) (hc : WordsBounded W c) {d h k : ℕ}
    (r75 : c.nreg 2475 = k) (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h)
    (w1 : d + 3 * k + 4 ≤ W) (w2 : h + 2 * k ≤ W) (w3 : Gt ≤ W) (w4 : 4 ≤ W) :
    ∃ c' t, Exec I W (ndB1 Gt) c c' t ∧ t = 9 ∧ c'.nreg 2875 = 2 * k ∧
      c'.nreg 2876 = d + 3 * k + 4 ∧ c'.nreg 2877 = Gt ∧ c'.nreg 2878 = h ∧
      c'.nreg 2879 = h + 2 * k ∧
      (∀ r, (r < 2483 ∨ (2484 < r ∧ r < 2875) ∨ 2879 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndB1
  exec_block
  all_goals try ((try config_simp); (try simp only [r75, r04, r03]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r75, r04, r03])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

set_option maxHeartbeats 2000000 in
/-- **The numbering of the vertices of the node's piece** (as in the leaf). -/
theorem ndNum_exec (Gt : ℕ) {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c) (r75 : c.nreg 2475 = ck N P)
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (hT0 : ∀ a < g.G, c.nmem (Gt + a) = 0)
    (hGd : Gt + g.G ≤ d) (heh : e ≤ h) (hW : h + 4 * ck N P ≤ W) (w4 : 4 ≤ W) :
    ∃ (c' : Config) (t w : ℕ) (ν : ℕ → ℕ), Exec I W (.seq (ndB1 Gt) nmProg) c c' t ∧
      t ≤ 9 + (25 * (2 * ck N P) + 9) ∧
      c'.nreg 2882 = w ∧ c'.nreg 2875 = 2 * ck N P ∧ c'.nreg 2879 = h + 2 * ck N P ∧
      (∀ x ∈ verts N P, ν (g.gv x) < w ∧
        gInv g N (c'.nmem (h + 2 * ck N P + ν (g.gv x))) = x) ∧
      (∀ v < w, gInv g N (c'.nmem (h + 2 * ck N P + v)) ∈ verts N P ∧
        ν (g.gv (gInv g N (c'.nmem (h + 2 * ck N P + v)))) = v ∧
        c'.nmem (h + 2 * ck N P + v) = g.gv (gInv g N (c'.nmem (h + 2 * ck N P + v)))) ∧
      w = (verts N P).card ∧
      (∀ a < P.card, c'.nmem (h + a) = ν (g.gv (N.tail (cδ g N P a)))) ∧
      (∀ a < P.card, c'.nmem (h + ck N P + a) = ν (g.gv (N.head (cδ g N P a)))) ∧
      (∀ a, (a < h ∨ h + 4 * ck N P ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2483 ∨ (2484 < r ∧ r < 2875) ∨ 2886 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have he := hin.en
  unfold fsz at he
  have hmk := ck_ge (N := N) P
  obtain ⟨c₁, t₁, e₁, ht₁, s75, s76, s77, s78, s79, sn₁, sm₁, sr₁, srm₁, so₁⟩ :=
    ndB1_exec (I := I) Gt c hc r75 r04 r03 (by omega) (by omega) (by omega) w4
  have hAv : ∀ i < 2 * ck N P, c₁.nmem (d + 3 * ck N P + 4 + i) < g.G := fun i hi => by
    rw [sm₁]
    by_cases hik : i < ck N P
    · rw [show d + 3 * ck N P + 4 + i = d + 4 + 3 * ck N P + i by omega, hin.gt i hik]
      exact g.gv_lt _
    · rw [show d + 3 * ck N P + 4 + i = d + 4 + 4 * ck N P + (i - ck N P) by omega,
        hin.gh _ (by omega)]
      exact g.gv_lt _
  obtain ⟨c₂, t₂, e₂, ht₂, w, ν, hwn, n82, hO, hlt, hI, hsurj, nm₂, nn₂, nr₂, nrm₂, no₂⟩ :=
    nmProg_exec (P := I) (nG := g.G) c₁ e₁.wb_right s75 s76 s77 s78 s79 (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hAv (fun a ha => by rw [sm₁]; exact hT0 a ha)
  obtain ⟨P1, P2, hwv⟩ := leaf_num (g := g) (N := N) (P := P)
    (A := fun i => c₁.nmem (d + 3 * ck N P + 4 + i))
    (Imem := fun v => c₂.nmem (h + 2 * ck N P + v)) (w := w) (ν := ν)
    (fun j hj => by
      simp only [sm₁]
      rw [show d + 3 * ck N P + 4 + j = d + 4 + 3 * ck N P + j by omega]; exact hin.gt j hj)
    (fun j hj => by
      simp only [sm₁]
      rw [show d + 3 * ck N P + 4 + (ck N P + j) = d + 4 + 4 * ck N P + j by omega]
      exact hin.gh j hj)
    hlt hI hsurj
  refine ⟨c₂, t₁ + t₂, w, ν, .seq e₁ e₂, by omega, n82,
    by rw [nn₂ _ (by omega)]; exact s75, by rw [nn₂ _ (by omega)]; exact s79, P1, P2, hwv,
    fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun r hr => ?_, by rw [nr₂, sr₁],
    by rw [nrm₂, srm₁], by rw [no₂, so₁]⟩
  · rw [hO a (by omega), sm₁, show d + 3 * ck N P + 4 + a = d + 4 + 3 * ck N P + a by omega,
      hin.gt a (by omega)]
  · rw [Nat.add_assoc, hO _ (by omega), sm₁,
      show d + 3 * ck N P + 4 + (ck N P + a) = d + 4 + 4 * ck N P + a by omega,
      hin.gh a (by omega)]
  · rw [nm₂ a (by omega) (by omega), sm₁]
  · rw [nn₂ r (by omega), sn₁ r (by omega)]

/-- **`cgProg` on a child's outcome region, in the node's numbering.** -/
theorem nd_gather {Pc : Finset D} {f : V → ℤ} {ι₀ : ℕ → V} {ιn : ℕ → V}
    {L R mc w Ib Ob Gt : ℕ} (c : Config) (hc : WordsBounded W c)
    (hI : CgIn (c.nmem (R + 1)) (R + 2) (R + 2 + 2 * mc) Gt w Ib Ob c)
    (hw0 : c.nmem (R + 1) ≤ 2 * mc)
    (hres : ∀ u < c.nmem (R + 1), ι₀ u ∈ verts N Pc ∧ c.nmem (R + 2 + u) = g.gv (ι₀ u) ∧
      c.nmem (R + 2 + 2 * mc + u) = (f (ι₀ u) + L).toNat ∧ |f (ι₀ u)| ≤ L)
    (hcov : ∀ x ∈ verts N Pc, ∃ u < c.nmem (R + 1), ι₀ u = x)
    (hT0 : ∀ a < g.G, c.nmem (Gt + a) = 0) (hIv : ∀ v < w, c.nmem (Ib + v) = g.gv (ιn v))
    (l1 : Gt + g.G ≤ R) (l2 : R + 2 + 4 * mc ≤ Ib) (l3 : Ib + w ≤ Ob) (wO : Ob + w ≤ W)
    (wL : 2 * L + 1 ≤ W) :
    ∃ c' t, Exec I W cgProg c c' t ∧ t ≤ 17 * (2 * mc) + 9 * w + 11 ∧
      (∀ v < w, (c'.nmem (Ob + v) = 0 ↔ ιn v ∉ verts N Pc) ∧
        (ιn v ∈ verts N Pc → c'.nmem (Ob + v) = (f (ιn v) + L).toNat + 1)) ∧
      (∀ a, (a < Ob ∨ Ob + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2467 ∨ 2471 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hres' : ∀ u < c.nmem (R + 1), ι₀ u ∈ verts N Pc ∧ c.nmem (R + 2 + u) = g.gv (ι₀ u) ∧
      c.nmem (R + 2 + 2 * mc + u) = (f (ι₀ u) + L).toNat := fun u hu =>
    ⟨(hres u hu).1, (hres u hu).2.1, (hres u hu).2.2.1⟩
  obtain ⟨c', t, ex, ht, hout, hm, hn, hr, hrm, ho⟩ := cgProg_exec (P := I) (G := g.G) c hc hI
    (fun u hu => by rw [(hres u hu).2.1]; exact g.gv_lt _)
    (cg_cons (ID := fun u => c.nmem (R + 2 + u)) (VL := fun u => c.nmem (R + 2 + 2 * mc + u))
      hres')
    hT0 (fun v hv => by rw [hIv v hv]; exact g.gv_lt _) (by omega) (by omega) (by omega)
    wO (by omega)
    (fun u hu => by
      rw [(hres u hu).2.2.1]
      have := abs_le.1 (hres u hu).2.2.2
      have : ((f (ι₀ u) + L).toNat : ℤ) = f (ι₀ u) + L := Int.toNat_of_nonneg (by omega)
      omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c', t, ex, by omega, fun v hv => ?_, hm, hn, hr, hrm, ho⟩
  have := cg_child (g := g) (N := N) (L := L) (ID := fun u => c.nmem (R + 2 + u))
    (VL := fun u => c.nmem (R + 2 + 2 * mc + u)) (o := c'.nmem (Ob + v)) (x := ιn v) hres' hcov
    (by rw [← hIv v hv]; exact hout v hv)
  exact this

/-! ### The semantics of the combination -/

/-- **The count of the combination is the number of shared vertices.** -/
theorem nd_cnt_bdry {P₀ P₁ : Finset D} {w : ℕ} {ιn : ℕ → V} {ν : V → ℕ} {G₀ G₁ : ℕ → ℕ}
    (hι : ∀ v < w, ιn v ∈ verts N (P₀ ∪ P₁) ∧ ν (ιn v) = v)
    (hν : ∀ x ∈ verts N (P₀ ∪ P₁), ν x < w ∧ ιn (ν x) = x)
    (h₀ : ∀ v < w, G₀ v = 0 ↔ ιn v ∉ verts N P₀) (h₁ : ∀ v < w, G₁ v = 0 ↔ ιn v ∉ verts N P₁) :
    ((range w).filter fun v => G₀ v ≠ 0 ∧ G₁ v ≠ 0).card = (bdry N P₀ P₁).card := by
  have hinj : Set.InjOn ιn ((range w).filter fun v => G₀ v ≠ 0 ∧ G₁ v ≠ 0 : Set ℕ) := by
    intro a ha b hb e
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    rw [← (hι a ha.1).2, ← (hι b hb.1).2, e]
  rw [← card_image_of_injOn hinj]
  congr 1
  ext x
  simp only [mem_image, mem_filter, mem_range, bdry, mem_inter]
  constructor
  · rintro ⟨v, ⟨hv, a0, a1⟩, rfl⟩
    exact ⟨by_contra fun h => a0 ((h₀ v hv).2 h), by_contra fun h => a1 ((h₁ v hv).2 h)⟩
  · rintro ⟨x0, x1⟩
    have hx : x ∈ verts N (P₀ ∪ P₁) := by
      rw [verts_union]; exact mem_union_left _ x0
    obtain ⟨h1, h2⟩ := hν x hx
    refine ⟨ν x, ⟨h1, fun h => ?_, fun h => ?_⟩, h2⟩
    · exact (h₀ _ h1).1 h (by rw [h2]; exact x0)
    · exact (h₁ _ h1).1 h (by rw [h2]; exact x1)

/-- **The value of the combination at a vertex.** -/
theorem nd_cmb_val {P₀ P₁ : Finset D} {f₀ f₁ : V → ℤ} {L : ℕ} {x : V} {a b : ℕ}
    (hx : x ∈ verts N (P₀ ∪ P₁))
    (h₀ : (a = 0 ↔ x ∉ verts N P₀) ∧ (x ∈ verts N P₀ → a = (f₀ x + L).toNat + 1))
    (h₁ : (b = 0 ↔ x ∉ verts N P₁) ∧ (x ∈ verts N P₁ → b = (f₁ x + L).toNat + 1)) :
    cmbV a b = (ndComb N P₀ f₀ f₁ x + L).toNat := by
  unfold cmbV ndComb
  by_cases hx0 : x ∈ verts N P₀
  · have ha : a ≠ 0 := fun h => (h₀.1.1 h) hx0
    rw [if_pos ha, if_pos hx0, h₀.2 hx0]; rfl
  · have ha : a = 0 := h₀.1.2 hx0
    have hx1 : x ∈ verts N P₁ := by
      rw [verts_union] at hx
      rcases mem_union.1 hx with h | h
      · exact absurd h hx0
      · exact h
    rw [if_neg (by omega), if_neg hx0, h₁.2 hx1]; rfl

/-! ### The registers of the gathers and of the combination -/

/-- The registers of `cgProg` for the first child. -/
def ndB2 (Gt : ℕ) : Stmt := block [.addN 2480 2482 2472, .loadN 2460 2480,
  .addN 2461 2480 2472, .addN 2484 2479 2479, .addN 2462 2461 2484, .constN 2463 Gt,
  .copyN 2464 2882, .copyN 2465 2879, .addN 2484 2875 2875, .addN 2466 3003 2484]

/-- The registers of `cgProg` for the second child. -/
def ndB3 : Stmt := block [.addN 2480 2485 2472, .loadN 2460 2480, .addN 2461 2480 2472,
  .addN 2484 2481 2481, .addN 2462 2461 2484, .addN 2484 2875 2875, .addN 2484 2484 2875,
  .addN 2466 3003 2484]

/-- The registers of the combination. -/
def ndB4 : Stmt := block [.copyN 2490 2464, .addN 2484 2875 2875, .addN 2491 3003 2484,
  .addN 2484 2484 2875, .addN 2492 3003 2484, .addN 2484 2484 2875, .addN 2493 3003 2484]

theorem ndB2_exec (Gt : ℕ) (c : Config) (hc : WordsBounded W c) {R m₀ w h k : ℕ}
    (r72 : c.nreg 2472 = 1) (r82 : c.nreg 2482 = R) (r79 : c.nreg 2479 = m₀)
    (r882 : c.nreg 2882 = w) (r879 : c.nreg 2879 = h + 2 * k) (r875 : c.nreg 2875 = 2 * k)
    (r03 : c.nreg 3003 = h) (w1 : R + 2 + 2 * m₀ ≤ W) (w2 : h + 4 * k ≤ W) (w3 : Gt ≤ W) :
    ∃ c' t, Exec I W (ndB2 Gt) c c' t ∧ t = 10 ∧
      CgIn (c.nmem (R + 1)) (R + 2) (R + 2 + 2 * m₀) Gt w (h + 2 * k) (h + 4 * k) c' ∧
      (∀ r, (r < 2460 ∨ (2466 < r ∧ r < 2480) ∨ (2480 < r ∧ r < 2484) ∨ 2484 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndB2
  exec_block
  all_goals try ((try config_simp); (try simp only [r72, r82, r79, r882, r879, r875, r03]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r72, r82, r79, r882, r879, r875, r03])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

theorem ndB3_exec (c : Config) (hc : WordsBounded W c) {R m₁ w h k Gt : ℕ}
    (r72 : c.nreg 2472 = 1) (r85 : c.nreg 2485 = R) (r81 : c.nreg 2481 = m₁)
    (r63 : c.nreg 2463 = Gt) (r64 : c.nreg 2464 = w) (r65 : c.nreg 2465 = h + 2 * k)
    (r875 : c.nreg 2875 = 2 * k)
    (r03 : c.nreg 3003 = h) (w1 : R + 2 + 2 * m₁ ≤ W) (w2 : h + 6 * k ≤ W) :
    ∃ c' t, Exec I W ndB3 c c' t ∧ t = 8 ∧
      CgIn (c.nmem (R + 1)) (R + 2) (R + 2 + 2 * m₁) Gt w (h + 2 * k) (h + 6 * k) c' ∧
      (∀ r, (r < 2460 ∨ (2466 < r ∧ r < 2480) ∨ (2480 < r ∧ r < 2484) ∨ 2484 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndB3
  exec_block
  all_goals try ((try config_simp); (try simp only [r72, r85, r81, r875, r03]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r72, r85, r81, r63, r64, r65, r875, r03])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

theorem ndB4_exec (c : Config) (hc : WordsBounded W c) {w h k : ℕ}
    (r64 : c.nreg 2464 = w) (r875 : c.nreg 2875 = 2 * k) (r03 : c.nreg 3003 = h)
    (w2 : h + 8 * k ≤ W) :
    ∃ c' t, Exec I W ndB4 c c' t ∧ t = 7 ∧ c'.nreg 2490 = w ∧ c'.nreg 2491 = h + 4 * k ∧
      c'.nreg 2492 = h + 6 * k ∧ c'.nreg 2493 = h + 8 * k ∧
      (∀ r, (r < 2484 ∨ (2484 < r ∧ r < 2490) ∨ 2493 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ndB4
  exec_block
  all_goals try ((try config_simp); (try simp only [r64, r875, r03]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r64, r875, r03])
  all_goals first | omega | (simp (disch := omega) only [upd_other])

/-! ### The middle of the node step -/

/-- **The numbering, the two gathers and the combination.** -/
def ndB (Gt : ℕ) : Stmt :=
  .seq (.seq (ndB1 Gt) nmProg) <| .seq (ndB2 Gt) <| .seq cgProg <| .seq ndB3 <| .seq cgProg <|
    .seq ndB4 ndCmb

theorem ndB1_natOnly (Gt : ℕ) : Klein.natOnly (ndB1 Gt) = true := rfl
theorem ndB2_natOnly (Gt : ℕ) : Klein.natOnly (ndB2 Gt) = true := rfl
theorem ndB3_natOnly : Klein.natOnly ndB3 = true := rfl
theorem ndB4_natOnly : Klein.natOnly ndB4 = true := rfl

theorem ndB_natOnly (Gt : ℕ) : Klein.natOnly (ndB Gt) = true := by
  simp only [ndB, Klein.natOnly, ndB1_natOnly, ndB2_natOnly, ndB3_natOnly, ndB4_natOnly,
    nmProg_natOnly, cgProg_natOnly, ndCmb_natOnly, Bool.and_self]

/-- The cost of `ndB`. -/
def ndBCost (m k : ℕ) : ℕ := 50 * k + 108 * m + 80

set_option maxHeartbeats 8000000 in
/-- **The middle of the node step**: when both children have an outcome (`some f₀`, `some f₁`),
the numbering of the piece's vertices (`I` at `h + 2k`), and `F[v] = (ndComb … (ι v) + L).toNat`
at `h + 8k + v`, the number of shared vertices in `r2496`. -/
theorem ndB_exec (Gt : ℕ) {ℓ : D → ℤ} {L n : ℕ} {P : Finset D} {d e bl el er h : ℕ}
    {f₀ f₁ : V → ℤ} (c : Config) (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c)
    (hr0 : Res g N L (msplit g N P).1 (some f₀) (bl + 5) el c)
    (hr1 : Res g N L (msplit g N P).2 (some f₁) (el + 5) er c)
    (r72 : c.nreg 2472 = 1) (r75 : c.nreg 2475 = ck N P)
    (r79 : c.nreg 2479 = (msplit g N P).1.card) (r81 : c.nreg 2481 = (msplit g N P).2.card)
    (r82 : c.nreg 2482 = bl + 5 + fin (msplit g N P).1.card (ck N (msplit g N P).1))
    (r85 : c.nreg 2485 = el + 5 + fin (msplit g N P).2.card (ck N (msplit g N P).2))
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (hT0 : ∀ a < g.G, c.nmem (Gt + a) = 0)
    (hGd : Gt + g.G ≤ d) (l1 : e ≤ bl) (l2 : bl + 5 ≤ el) (l3 : el + 5 ≤ er) (l4 : er ≤ h)
    (hW : h + 10 * ck N P ≤ W) (wL : 2 * L + 1 ≤ W) (w4 : 4 ≤ W) :
    ∃ (c' : Config) (t w : ℕ) (ν : ℕ → ℕ), Exec I W (ndB Gt) c c' t ∧
      t ≤ ndBCost P.card (ck N P) ∧ c'.nreg 2464 = w ∧ w = (verts N P).card ∧
      (∀ x ∈ verts N P, ν (g.gv x) < w ∧
        gInv g N (c'.nmem (h + 2 * ck N P + ν (g.gv x))) = x) ∧
      (∀ v < w, gInv g N (c'.nmem (h + 2 * ck N P + v)) ∈ verts N P ∧
        ν (g.gv (gInv g N (c'.nmem (h + 2 * ck N P + v)))) = v ∧
        c'.nmem (h + 2 * ck N P + v) = g.gv (gInv g N (c'.nmem (h + 2 * ck N P + v)))) ∧
      (∀ a < P.card, c'.nmem (h + a) = ν (g.gv (N.tail (cδ g N P a)))) ∧
      (∀ a < P.card, c'.nmem (h + ck N P + a) = ν (g.gv (N.head (cδ g N P a)))) ∧
      (∀ v < w, c'.nmem (h + 8 * ck N P + v) = (ndComb N (msplit g N P).1 f₀ f₁
          (gInv g N (c'.nmem (h + 2 * ck N P + v))) + L).toNat ∧
        |ndComb N (msplit g N P).1 f₀ f₁ (gInv g N (c'.nmem (h + 2 * ck N P + v)))| ≤ L) ∧
      c'.nreg 2496 = (bdry N (msplit g N P).1 (msplit g N P).2).card ∧
      (∀ v < w, (c'.nmem (h + 4 * ck N P + v) = 0 ↔
          gInv g N (c'.nmem (h + 2 * ck N P + v)) ∉ verts N (msplit g N P).1) ∧
        (gInv g N (c'.nmem (h + 2 * ck N P + v)) ∈ verts N (msplit g N P).1 →
          c'.nmem (h + 4 * ck N P + v) =
            (f₀ (gInv g N (c'.nmem (h + 2 * ck N P + v))) + L).toNat + 1)) ∧
      (∀ v < w, (c'.nmem (h + 6 * ck N P + v) = 0 ↔
          gInv g N (c'.nmem (h + 2 * ck N P + v)) ∉ verts N (msplit g N P).2) ∧
        (gInv g N (c'.nmem (h + 2 * ck N P + v)) ∈ verts N (msplit g N P).2 →
          c'.nmem (h + 6 * ck N P + v) =
            (f₁ (gInv g N (c'.nmem (h + 2 * ck N P + v))) + L).toNat + 1)) ∧
      (∀ a, (a < h ∨ h + 10 * ck N P ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2460 ∨ (2471 < r ∧ r < 2480) ∨ r = 2481 ∨ r = 2482 ∨ r = 2485 ∨ r = 2486 ∨
        (2499 < r ∧ r < 2875) ∨ 2886 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set P₀ := (msplit g N P).1 with hP₀
  set P₁ := (msplit g N P).2 with hP₁
  have hu : P₀ ∪ P₁ = P := msplit_union P
  have hcard := msplit_card (g := g) (N := N) P
  rw [← hP₀, ← hP₁] at hcard
  have hmk := ck_ge (N := N) P
  have he := hin.en
  unfold fsz at he
  have hel := hr0.1
  have her := hr1.1
  unfold fsz at hel her
  -- the numbering
  obtain ⟨c₂, t₂, w, ν, e₂, ht₂, n82, n75, n79, P1, P2, hwv, hTn, hHn, nm₂, nn₂, nr₂, nrm₂,
    no₂⟩ := ndNum_exec (I := I) Gt c hc hin r75 r04 r03 hT0 hGd (by omega) (by omega) w4
  have hw2m : w ≤ 2 * P.card := hwv ▸ NTree.card_verts_le (N := N) P
  have M2 : ∀ a, a < h → c₂.nmem a = c.nmem a := fun a ha => nm₂ a (Or.inl ha)
  -- the first child
  obtain ⟨c₃, t₃, e₃, ht₃, hI₃, n₃, m₃, r₃, rm₃, o₃⟩ :=
    ndB2_exec (I := I) Gt c₂ e₂.wb_right (k := ck N P) (h := h) (w := w)
      (R := bl + 5 + fin P₀.card (ck N P₀)) (m₀ := P₀.card)
      (by rw [nn₂ _ (by omega)]; exact r72) (by rw [nn₂ _ (by omega)]; exact r82)
      (by rw [nn₂ _ (by omega)]; exact r79) n82 n79 n75
      (by rw [nn₂ _ (by omega)]; exact r03) (by unfold fin; omega) (by omega) (by omega)
  have hr0₃ : Res g N L P₀ (some f₀) (bl + 5) el c₃ := res_stab hr0 fun a h1 h2 =>
    ⟨by rw [m₃, M2 a (by omega)], by rw [rm₃, nrm₂]⟩
  obtain ⟨-, -, w₀, ι₀, hw₀, hm₀, hl₀, hc₀⟩ := hr0₃
  have hIv₃ : ∀ v < w, c₃.nmem (h + 2 * ck N P + v) =
      g.gv (gInv g N (c₂.nmem (h + 2 * ck N P + v))) := fun v hv => by
    rw [m₃]; exact (P2 v hv).2.2
  obtain ⟨c₄, t₄, e₄, ht₄, G0, m₄, n₄, r₄, rm₄, o₄⟩ :=
    nd_gather (I := I) (g := g) (N := N) (Pc := P₀) (f := f₀) (ι₀ := ι₀)
      (ιn := fun v => gInv g N (c₂.nmem (h + 2 * ck N P + v))) (L := L) c₃ e₃.wb_right
      (by rw [m₃]; exact hI₃)
      (by rw [hm₀]; exact hw₀) (fun u hu => by rw [hm₀] at hu; exact hl₀ u hu)
      (fun x hx => by rw [hm₀]; exact hc₀ x hx)
      (fun a ha => by rw [m₃, M2 _ (by omega)]; exact hT0 a ha)
      hIv₃ (by unfold fin; omega) (by unfold fin; omega) (by omega) (by omega) wL
  have M4 : ∀ a, (a < h + 4 * ck N P ∨ h + 4 * ck N P + w ≤ a) → c₄.nmem a = c₂.nmem a :=
    fun a ha => by rw [m₄ a ha, m₃]
  -- the second child
  obtain ⟨c₅, t₅, e₅, ht₅, hI₅, n₅, m₅, r₅, rm₅, o₅⟩ :=
    ndB3_exec (I := I) c₄ e₄.wb_right (k := ck N P) (h := h) (w := w) (Gt := Gt)
      (R := el + 5 + fin P₁.card (ck N P₁)) (m₁ := P₁.card)
      (by rw [n₄ _ (by omega), n₃ _ (by omega), nn₂ _ (by omega)]; exact r72)
      (by rw [n₄ _ (by omega), n₃ _ (by omega), nn₂ _ (by omega)]; exact r85)
      (by rw [n₄ _ (by omega), n₃ _ (by omega), nn₂ _ (by omega)]; exact r81)
      (by rw [n₄ 2463 (by omega)]; exact hI₃.r63) (by rw [n₄ 2464 (by omega)]; exact hI₃.r64)
      (by rw [n₄ 2465 (by omega)]; exact hI₃.r65)
      (by rw [n₄ _ (by omega), n₃ _ (by omega)]; exact n75)
      (by rw [n₄ _ (by omega), n₃ _ (by omega), nn₂ _ (by omega)]; exact r03)
      (by unfold fin; omega) (by omega)
  have hr1₅ : Res g N L P₁ (some f₁) (el + 5) er c₅ := res_stab hr1 fun a h1 h2 =>
    ⟨by rw [m₅, M4 a (by omega), M2 a (by omega)], by rw [rm₅, rm₄, rm₃, nrm₂]⟩
  obtain ⟨-, -, w₁, ι₁, hw₁, hm₁, hl₁, hc₁⟩ := hr1₅
  have hIv₅ : ∀ v < w, c₅.nmem (h + 2 * ck N P + v) =
      g.gv (gInv g N (c₂.nmem (h + 2 * ck N P + v))) := fun v hv => by
    rw [m₅, M4 _ (by omega)]; exact (P2 v hv).2.2
  obtain ⟨c₆, t₆, e₆, ht₆, G1, m₆, n₆, r₆, rm₆, o₆⟩ :=
    nd_gather (I := I) (g := g) (N := N) (Pc := P₁) (f := f₁) (ι₀ := ι₁)
      (ιn := fun v => gInv g N (c₂.nmem (h + 2 * ck N P + v))) (L := L) c₅ e₅.wb_right
      (by rw [m₅]; exact hI₅)
      (by rw [hm₁]; exact hw₁) (fun u hu => by rw [hm₁] at hu; exact hl₁ u hu)
      (fun x hx => by rw [hm₁]; exact hc₁ x hx)
      (fun a ha => by rw [m₅, M4 _ (by omega), M2 _ (by omega)]; exact hT0 a ha)
      hIv₅ (by unfold fin; omega) (by unfold fin; omega) (by omega) (by omega) wL
  -- the combination
  obtain ⟨c₇, t₇, e₇, ht₇, q90, q91, q92, q93, qn₇, qm₇, qr₇, qrm₇, qo₇⟩ :=
    ndB4_exec (I := I) c₆ e₆.wb_right (w := w) (h := h) (k := ck N P)
      (by rw [n₆ 2464 (by omega)]; exact hI₅.r64)
      (by rw [n₆ _ (by omega), n₅ _ (by omega), n₄ _ (by omega), n₃ _ (by omega)]; exact n75)
      (by rw [n₆ _ (by omega), n₅ _ (by omega), n₄ _ (by omega), n₃ _ (by omega),
        nn₂ _ (by omega)]; exact r03) (by omega)
  obtain ⟨c₈, t₈, e₈, ht₈, F8, cnt8, m₈, n₈, r₈, rm₈, o₈⟩ :=
    ndCmb_exec (I := I) c₇ e₇.wb_right q90 q91 q92 q93 (by omega) (by omega) (by omega)
      (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  -- the memory of `c₈`
  have K8 : ∀ a, (a < h + 4 * ck N P ∨ h + 8 * ck N P + w ≤ a) →
      (a < h + 6 * ck N P ∨ h + 6 * ck N P + w ≤ a) → c₈.nmem a = c₂.nmem a := fun a h1 h2 => by
    rw [m₈ a (by omega), qm₇, m₆ a (by omega), m₅]
    exact M4 a (by omega)
  have G48 : ∀ v < w, c₇.nmem (h + 4 * ck N P + v) = c₄.nmem (h + 4 * ck N P + v) :=
    fun v hv => by rw [qm₇, m₆ _ (by omega), m₅]
  have G68 : ∀ v < w, c₇.nmem (h + 6 * ck N P + v) = c₆.nmem (h + 6 * ck N P + v) :=
    fun v hv => by rw [qm₇]
  have hI8 : ∀ v < w, c₈.nmem (h + 2 * ck N P + v) = c₂.nmem (h + 2 * ck N P + v) :=
    fun v hv => K8 _ (by omega) (by omega)
  have hvP : ∀ v < w, gInv g N (c₂.nmem (h + 2 * ck N P + v)) ∈ verts N (P₀ ∪ P₁) :=
    fun v hv => by rw [hu]; exact (P2 v hv).1
  have h₀ : ∀ v < w, (c₇.nmem (h + 4 * ck N P + v) = 0 ↔
      gInv g N (c₂.nmem (h + 2 * ck N P + v)) ∉ verts N P₀) := fun v hv => by
    rw [G48 v hv]; exact (G0 v hv).1
  have h₁ : ∀ v < w, (c₇.nmem (h + 6 * ck N P + v) = 0 ↔
      gInv g N (c₂.nmem (h + 2 * ck N P + v)) ∉ verts N P₁) := fun v hv => by
    rw [G68 v hv]; exact (G1 v hv).1
  have hcnt := nd_cnt_bdry (N := N) (P₀ := P₀) (P₁ := P₁) (w := w)
    (ιn := fun v => gInv g N (c₂.nmem (h + 2 * ck N P + v))) (ν := fun x => ν (g.gv x))
    (G₀ := fun v => c₇.nmem (h + 4 * ck N P + v)) (G₁ := fun v => c₇.nmem (h + 6 * ck N P + v))
    (fun v hv => ⟨hvP v hv, (P2 v hv).2.1⟩)
    (fun x hx => by rw [hu] at hx; exact P1 x hx) h₀ h₁
  refine ⟨c₈, t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈))))), w, ν,
    .seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))), ?_, ?_, hwv,
    fun x hx => ?_, fun v hv => ?_, fun a ha => ?_, fun a ha => ?_, fun v hv => ?_,
    by rw [cnt8]; exact hcnt, fun v hv => ?_, fun v hv => ?_, fun a ha => ?_, fun r hr => ?_,
    ?_, ?_, ?_⟩
  · unfold ndBCost; omega
  · rw [n₈ 2464 (by omega), qn₇ 2464 (by omega), n₆ 2464 (by omega)]; exact hI₅.r64
  · rw [hI8 _ (P1 x hx).1]; exact P1 x hx
  · rw [hI8 v hv]; exact P2 v hv
  · rw [K8 _ (by omega) (by omega)]; exact hTn a ha
  · rw [K8 _ (by omega) (by omega)]; exact hHn a ha
  · rw [hI8 v hv, F8 v hv]
    have hx := hvP v hv
    refine ⟨nd_cmb_val hx ⟨h₀ v hv, fun h' => ?_⟩ ⟨h₁ v hv, fun h' => ?_⟩, ?_⟩
    · rw [G48 v hv]; exact (G0 v hv).2 h'
    · rw [G68 v hv]; exact (G1 v hv).2 h'
    · unfold ndComb
      split_ifs with h'
      · obtain ⟨u, hu', e'⟩ := hc₀ _ h'
        rw [← e']; exact (hl₀ u hu').2.2.2
      · have h1' : gInv g N (c₂.nmem (h + 2 * ck N P + v)) ∈ verts N P₁ := by
          rw [verts_union] at hx
          rcases mem_union.1 hx with h2 | h2
          · exact absurd h2 h'
          · exact h2
        obtain ⟨u, hu', e'⟩ := hc₁ _ h1'
        rw [← e']; exact (hl₁ u hu').2.2.2
  · have e4 : c₈.nmem (h + 4 * ck N P + v) = c₇.nmem (h + 4 * ck N P + v) :=
      m₈ _ (by omega)
    rw [e4, G48 v hv, hI8 v hv]; exact G0 v hv
  · have e6 : c₈.nmem (h + 6 * ck N P + v) = c₇.nmem (h + 6 * ck N P + v) :=
      m₈ _ (by omega)
    rw [e6, G68 v hv, hI8 v hv]; exact G1 v hv
  · rw [m₈ a (by omega), qm₇, m₆ a (by omega), m₅, m₄ a (by omega), m₃, nm₂ a (by omega)]
  · rw [n₈ r (by omega), qn₇ r (by omega), n₆ r (by omega), n₅ r (by omega), n₄ r (by omega),
      n₃ r (by omega), nn₂ r (by omega)]
  · rw [r₈, qr₇, r₆, r₅, r₄, r₃, nr₂]
  · rw [rm₈, qrm₇, rm₆, rm₅, rm₄, rm₃, nrm₂]
  · rw [o₈, qo₇, o₆, o₅, o₄, o₃, no₂]

end Frame

end NegSSSP

end PlanarFlow
