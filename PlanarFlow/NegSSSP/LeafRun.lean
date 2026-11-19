module

public import PlanarFlow.NegSSSP.LeafProg
public import PlanarFlow.NegSSSP.NSpecInst
public import PlanarFlow.NegSSSP.Enc.RnRes
public import PlanarFlow.NegSSSP.Enc.NumFirst

/-!
# The leaf of the driver on the frame

`leafS`: the numbering of the vertices of the piece (`nmProg` on the frame's columns of tail and
head identifiers, `2k` entries, with the scratch table `[Gt, Gt + G)` zero before and after),
Bellman–Ford for the leaves (`lbProg`, `R = w` rounds, `K = w m L`) on the offset lengths of the
frame, then either the renormalized outcome (`resProg`: `Res … (some g)`) when no arc is
relaxable, or the flag `1` in the outcome region (`Res … none`, no feasible potential).

* `leaf_num`: the numbering of `nmProg` on the frame's columns is a numbering of `verts N P`
  (`ν' = ν ∘ gv`, `ι = invFun gv ∘ I`), with `w = #verts N P ≤ 2m`.
* **`leafS_exec`**: the field `leaf` of `NSpecR` for `leafS`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- A left inverse of the vertex identifiers (`V` is inhabited by `N.tail g.d₀`). -/
noncomputable def gInv (g : GIds D V) (N : CombMap D V F) (n : ℕ) : V :=
  @Function.invFun V ℕ ⟨N.tail g.d₀⟩ g.gv n

theorem gInv_gv (y : V) : gInv g N (g.gv y) = y :=
  @Function.leftInverse_invFun V ℕ ⟨N.tail g.d₀⟩ g.gv g.gv_inj y

theorem verts_of_rcl {P : Finset D} {x : D} (hx : x ∈ rcl N P) :
    N.tail x ∈ verts N P ∧ N.head x ∈ verts N P := by
  rw [mem_rcl] at hx
  rcases hx with hx | hx
  · exact ⟨mem_verts.2 ⟨x, hx, Or.inl rfl⟩, mem_verts.2 ⟨x, hx, Or.inr rfl⟩⟩
  · refine ⟨mem_verts.2 ⟨N.rev x, hx, Or.inr ?_⟩, mem_verts.2 ⟨N.rev x, hx, Or.inl ?_⟩⟩
    · rw [CombMap.head_rev]
    · rw [CombMap.tail_rev]

/-- **The numbering of `nmProg` on the frame's columns** is a numbering of the vertices of the
piece. -/
theorem leaf_num {P : Finset D} {A : ℕ → ℕ} {Imem : ℕ → ℕ} {w : ℕ} {ν : ℕ → ℕ}
    (hAT : ∀ h < ck N P, A h = g.gv (N.tail (cδ g N P h)))
    (hAH : ∀ h < ck N P, A (ck N P + h) = g.gv (N.head (cδ g N P h)))
    (hlt : ∀ i < 2 * ck N P, ν (A i) < w)
    (hI : ∀ i < 2 * ck N P, Imem (ν (A i)) = A i)
    (hsurj : ∀ v < w, ∃ i < 2 * ck N P, ν (A i) = v) :
    (∀ x ∈ verts N P, ν (g.gv x) < w ∧ gInv g N (Imem (ν (g.gv x))) = x) ∧
    (∀ v < w, gInv g N (Imem v) ∈ verts N P ∧
      ν (g.gv (gInv g N (Imem v))) = v ∧
      Imem v = g.gv (gInv g N (Imem v))) ∧
    w = (verts N P).card := by
  have hinv : ∀ y, gInv g N (g.gv y) = y := gInv_gv
  have hmk := ck_ge (N := N) P
  -- every vertex is an entry
  have key : ∀ x ∈ verts N P, ∃ i < 2 * ck N P, A i = g.gv x := fun x hx => by
    obtain ⟨d, hd, h⟩ := mem_verts.1 hx
    obtain ⟨h1, h2⟩ := cδ_idxOf (g := g) (N := N) hd
    rcases h with h | h
    · exact ⟨(cL g P).idxOf d, by omega, by rw [hAT _ (by omega), h2, h]⟩
    · exact ⟨ck N P + (cL g P).idxOf d, by omega, by rw [hAH _ (by omega), h2, h]⟩
  -- every entry is a vertex
  have key2 : ∀ i < 2 * ck N P, ∃ y ∈ verts N P, A i = g.gv y := fun i hi => by
    by_cases hik : i < ck N P
    · exact ⟨_, (verts_of_rcl (cδ_mem (g := g) hik)).1, hAT i hik⟩
    · have hj : i - ck N P < ck N P := by omega
      refine ⟨_, (verts_of_rcl (cδ_mem (g := g) hj)).2, ?_⟩
      rw [← hAH _ hj]; congr 1; omega
  have P1 : ∀ x ∈ verts N P, ν (g.gv x) < w ∧ gInv g N (Imem (ν (g.gv x))) = x :=
    fun x hx => by
      obtain ⟨i, hi, e⟩ := key x hx
      refine ⟨by rw [← e]; exact hlt i hi, ?_⟩
      rw [← e, hI i hi, e, hinv]
  have P2 : ∀ v < w, gInv g N (Imem v) ∈ verts N P ∧
      ν (g.gv (gInv g N (Imem v))) = v ∧
      Imem v = g.gv (gInv g N (Imem v)) := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := hsurj v hv
    obtain ⟨y, hy, e⟩ := key2 i hi
    rw [hI i hi, e, hinv]
    exact ⟨hy, rfl, rfl⟩
  refine ⟨P1, P2, le_antisymm ?_ ?_⟩
  · -- `v ↦ ι v` is injective from `[0, w)` into the vertices
    have : (range w).image (fun v => gInv g N (Imem v)) ⊆ verts N P := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
      exact (P2 v (mem_range.1 hv)).1
    have hinj : Set.InjOn (fun v => gInv g N (Imem v)) (range w : Set ℕ) := by
      intro a ha b hb hab
      have e1 := (P2 a (mem_range.1 ha)).2.1
      have e2 := (P2 b (mem_range.1 hb)).2.1
      simp only at hab
      rw [← e1, ← e2, hab]
    have := card_le_card this
    rwa [card_image_of_injOn hinj, card_range] at this
  · have : (verts N P).image (fun x => ν (g.gv x)) ⊆ range w := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
      exact mem_range.2 (P1 x hx).1
    have hinj : Set.InjOn (fun x => ν (g.gv x)) (verts N P : Set V) := by
      intro a ha b hb hab
      have e1 := (P1 a ha).2
      have e2 := (P1 b hb).2
      simp only at hab
      rw [← e1, ← e2, hab]
    have := card_le_card this
    rwa [card_image_of_injOn hinj, card_range] at this

/-! ### The blocks of the leaf -/

/-- The registers of the leaf: `r2425 = 1`, `r2426 = 0`, `r2430 = m`, `r2431 = k`, `r2432 = L`
(read from the frame at `r3004 = d`), and those of `nmProg`: `n = 2k`, `A = d + 3k + 4` (the
columns of tail and head identifiers), the table `Gt`, `O = h`, `I = h + 2k` (`h = r3003`). -/
def lfSet (Gt : ℕ) : Stmt := block [.constN 2425 1, .constN 2426 0, .constN 2433 1,
  .addN 2427 3004 2433, .loadN 2430 2427, .constN 2433 2, .addN 2427 3004 2433,
  .loadN 2431 2427, .constN 2433 3, .addN 2427 3004 2433, .loadN 2432 2427,
  .addN 2875 2431 2431, .constN 2433 3, .mulN 2434 2433 2431,
  .addN 2434 2434 3004, .constN 2433 4, .addN 2876 2434 2433, .constN 2877 Gt,
  .copyN 2878 3003, .addN 2879 3003 2875]

/-- The registers of `lbProg`: `m`, `T = h`, `H = h + k`, `LL = d + 5k + 4`, `L`, `D = h + 4k`,
`w`, `R = w`, `K = w m L` (`w = r2882` from `nmProg`). -/
def lbSet : Stmt := block [.copyN 2400 2430, .copyN 2401 3003, .addN 2402 3003 2431,
  .constN 2433 5, .mulN 2434 2433 2431, .addN 2434 2434 3004, .constN 2433 4,
  .addN 2403 2434 2433, .copyN 2404 2432, .addN 2434 2875 2875, .addN 2405 3003 2434,
  .copyN 2406 2882, .copyN 2407 2882, .mulN 2434 2882 2430, .mulN 2408 2434 2432]

/-- The flag `1` at the start of the outcome region `d + 5k + m + 4`. -/
def lfNone : Stmt := block [.constN 2433 5, .mulN 2434 2433 2431, .addN 2434 2434 3004,
  .addN 2434 2434 2430, .constN 2433 4, .addN 2434 2434 2433, .storeN 2434 2425]

/-- The registers of `resProg`: `w`, `T = h`, `H = h + k`, `F = h + 4k` (the values of
Bellman–Ford), the scratch `h + 6k`, `I = h + 2k`. -/
def lfRes : Stmt := block [.copyN 2950 2882, .copyN 2951 3003, .addN 2952 3003 2431,
  .addN 2434 2875 2875, .addN 2953 3003 2434, .addN 2434 2434 2875, .addN 2954 3003 2434,
  .addN 2955 3003 2875]

/-- **The leaf of the driver.** -/
def leafS (Gt : ℕ) : Stmt :=
  .seq (lfSet Gt) (.seq nmProg (.seq lbSet (.seq lbProg (.ifLtN 2426 2424 lfNone
    (.seq lfRes resProg)))))

theorem lfSet_exec (Gt : ℕ) (c : Config) (hc : WordsBounded W c) {d h m k L : ℕ}
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (m1 : c.nmem (d + 1) = m)
    (m2 : c.nmem (d + 2) = k) (m3 : c.nmem (d + 3) = L) (hW : d + 3 * k + 4 ≤ W)
    (hW2 : h + 2 * k ≤ W) (hG : Gt ≤ W) :
    ∃ c' t, Exec I W (lfSet Gt) c c' t ∧ t = 20 ∧ c'.nreg 2425 = 1 ∧ c'.nreg 2426 = 0 ∧
      c'.nreg 2430 = m ∧ c'.nreg 2431 = k ∧ c'.nreg 2432 = L ∧ c'.nreg 2875 = 2 * k ∧
      c'.nreg 2876 = d + 3 * k + 4 ∧ c'.nreg 2877 = Gt ∧ c'.nreg 2878 = h ∧
      c'.nreg 2879 = h + 2 * k ∧
      (∀ r, (r < 2425 ∨ (2434 < r ∧ r < 2875) ∨ 2879 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lfSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r03, m1, m2, m3]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r04, r03, m1, m2, m3]
  all_goals try omega
  simp (disch := omega) only [upd_other]

theorem lbSet_exec (c : Config) (hc : WordsBounded W c) {d h m k L w : ℕ}
    (r04 : c.nreg 3004 = d) (r03 : c.nreg 3003 = h) (r30 : c.nreg 2430 = m)
    (r31 : c.nreg 2431 = k) (r32 : c.nreg 2432 = L) (r75 : c.nreg 2875 = 2 * k)
    (r82 : c.nreg 2882 = w) (hW : d + 5 * k + 4 ≤ W) (hW2 : h + 4 * k ≤ W)
    (hW3 : w * m * L ≤ W) (hW4 : w * m ≤ W) (h5 : 5 ≤ W) :
    ∃ c' t, Exec I W lbSet c c' t ∧ t = 15 ∧ c'.nreg 2400 = m ∧ c'.nreg 2401 = h ∧
      c'.nreg 2402 = h + k ∧ c'.nreg 2403 = d + 5 * k + 4 ∧ c'.nreg 2404 = L ∧
      c'.nreg 2405 = h + 4 * k ∧ c'.nreg 2406 = w ∧ c'.nreg 2407 = w ∧
      c'.nreg 2408 = w * m * L ∧
      (∀ r, (r < 2400 ∨ (2408 < r ∧ r < 2433) ∨ 2434 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lbSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r03, r30, r31, r32, r75, r82]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r04, r03, r30, r31, r32, r75, r82]
  all_goals try omega
  simp (disch := omega) only [upd_other]

theorem lfNone_exec (c : Config) (hc : WordsBounded W c) {d m k : ℕ}
    (r04 : c.nreg 3004 = d) (r30 : c.nreg 2430 = m) (r31 : c.nreg 2431 = k)
    (r25 : c.nreg 2425 = 1) (hW : d + 5 * k + m + 4 ≤ W) (h5 : 5 ≤ W) :
    ∃ c' t, Exec I W lfNone c c' t ∧ t = 7 ∧ c'.nmem = upd c.nmem (d + 5 * k + m + 4) 1 ∧
      (∀ r, (r < 2433 ∨ 2434 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lfNone
  exec_block
  all_goals try ((try config_simp); (try simp only [r04, r30, r31]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r04, r30, r31, r25]
  · congr 1; omega
  · simp (disch := omega) only [upd_other]

theorem lfRes_exec (c : Config) (hc : WordsBounded W c) {h k w : ℕ}
    (r03 : c.nreg 3003 = h) (r31 : c.nreg 2431 = k) (r75 : c.nreg 2875 = 2 * k)
    (r82 : c.nreg 2882 = w) (hW : h + 6 * k ≤ W) :
    ∃ c' t, Exec I W lfRes c c' t ∧ t = 8 ∧ c'.nreg 2950 = w ∧ c'.nreg 2951 = h ∧
      c'.nreg 2952 = h + k ∧ c'.nreg 2953 = h + 4 * k ∧ c'.nreg 2954 = h + 6 * k ∧
      c'.nreg 2955 = h + 2 * k ∧
      (∀ r, (r < 2434 ∨ (2434 < r ∧ r < 2950) ∨ 2955 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lfRes
  exec_block
  all_goals try ((try config_simp); (try simp only [r03, r31, r75, r82]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r03, r31, r75, r82]
  all_goals try omega
  simp (disch := omega) only [upd_other]

end Frame

end NegSSSP

end PlanarFlow
