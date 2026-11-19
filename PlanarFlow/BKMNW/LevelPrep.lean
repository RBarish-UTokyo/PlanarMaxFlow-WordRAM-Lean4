module

public import PlanarFlow.BKMNW.HoleProg

/-!
# The labels of the chosen hole and the arrays of the heavy and anchor scans

At a prune level of `scertD`, once the cut-vertex hole `g = Hs[J]` is known (`hlProg`):

* **`phCC := phProg ; ccProg`**, **`phCC_comp`**: the labels of the components off `g`
  (`LAB[i] = LAB[j] ↔ e j ∈ comp M N Hs g (e i)` for `e i ∈ N`, `0 < LAB ≤ n`), from the
  per-index arrays of the piece (`ccProg_comp_sub` on the arrays of `phProg`);
* **`lpProg`** (registers `4880 = n`, `4881 = NFb`, `4882 = THb`, `4883 = EXb`, `4884 = J1`,
  `4885 = TGb`, `4886 = TG2b`, `4887 = VALb`, `4888 = SUMb`; written `4889 … 4896`, the total
  in `4891`): one scan writing `TG[i] = [tail ∈ g]` (anchor scan), `TG2[i] = [tail ∈ g ∧ e i ∈ N]`
  (anchor of the cut), `VAL[i] = [e i ∈ N] (1 + EX[i])` (weights for `saProg`), `SUM[k] = 0`
  (`k ≤ n`), the total `Σ VAL`; **`lpProg_exec`** (`27 n + 8` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The labels of the chosen hole -/

section CC

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The components off a hole**: the preparation, then `ccProg`. -/
def phCC : Stmt := .seq phProg ccProg

/-- **The labels of the components off `g` from the per-index arrays of the piece** (the inputs
of `phCut_cutH`). -/
theorem phCC_comp {B N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hg : g ∈ Hs) {e : ℕ → D}
    {n NFb THb RV0b J1 GNb RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hmem : ∀ i < n, e i ∈ B)
    (hsurj : ∀ d ∈ B, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsub : N ⊆ B) (c : Config) (hc : WordsBounded W c)
    (hL : CgLay n n RVb TKb YFb LSb OFFb ADJb) (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W)
    (hGN : GNb + n ≤ RVb) (hin : NFb + n ≤ GNb ∧ THb + n ≤ GNb ∧ RV0b + n ≤ GNb)
    (hW : 2 * n + 2 ≤ W)
    (hrv0 : ∀ i < n, c.nmem (RV0b + i) < n ∧ e (c.nmem (RV0b + i)) = M.rev (e i))
    (hnf : ∀ i < n, (c.nmem (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hth : ∀ i < n, (c.nmem (THb + i) = J1 ↔ M.tail (e i) ∈ g))
    (hTK : ∀ i < n, c.nmem (TKb + i) < n)
    (hkey : ∀ i < n, ∀ j < n, (c.nmem (TKb + i) = c.nmem (TKb + j) ↔
      HRel Hs (M.tail (e i)) (M.tail (e j))))
    (p0 : c.nreg 4840 = n) (p1 : c.nreg 4841 = NFb) (p2 : c.nreg 4842 = THb)
    (p3 : c.nreg 4843 = RV0b) (p5 : c.nreg 4845 = J1) (p6 : c.nreg 4846 = YFb)
    (p7 : c.nreg 4847 = GNb) (p8 : c.nreg 4848 = RVb) (p9 : c.nreg 4849 = LABb)
    (p10 : c.nreg 4866 = LSb)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb) :
    ∃ c' k, Exec P W phCC c c' k ∧ k ≤ 140 * n + 21 ∧
      (∀ i < n, ∀ j < n, e i ∈ N → (c'.nmem (LABb + i) = c'.nmem (LABb + j) ↔
        e j ∈ comp M N Hs g (e i))) ∧
      (∀ u < n, 0 < c'.nmem (LABb + u) ∧ c'.nmem (LABb + u) ≤ n) ∧
      (∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4853) ∨ 4865 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLc := hL
  have hBc := hB
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨h1, h2, h3⟩ := hin
  obtain ⟨c₁, k₁, e₁, hk₁, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩ := phProg_exec (P := P) c hc
    p0 p1 p2 p3 p5 p6 p7 p8 p9 p10 (fun i hi => (hrv0 i hi).1)
    ⟨by omega, by omega, by omega, hGN, by omega, by omega, by omega, by omega, hW⟩
  have hw₁ := e₁.wb_right
  have fr : ∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c₁.nmem a = c.nmem a :=
    fun a ha => H6 a (by omega) (by omega) (by omega) (by omega) (by omega)
  have q : ∀ x, (x < 4853 ∨ 4865 < x) → c₁.nreg x = c.nreg x := H7
  obtain ⟨hE, -⟩ := ph_cg (M := M) (Hs := Hs) (g := g) hmem hsurj hinj hsub hrv0 hnf hth hkey
  obtain ⟨c₂, k₂, e₂, hk₂, G1, G2, G3, G4, G5, G6, G7⟩ := ccProg_comp_sub (P := P) (M := M)
    (B := B) (N := N) (hClosed_of_mem hd hg) c₁ hw₁ hLc hBc
    (fun i hi => by rw [fr _ (by omega)]; exact hTK i hi)
    (CgEnumSub.congr hE (fun i hi => by rw [H3 i hi])
      (fun i hi => by simp only [cgKey]; rw [fr _ (by omega)])
      (fun i hi => by simp only [cgYf]; rw [H1 i hi]))
    (fun k hk => H5 k hk) H4
    (by rw [q _ (by omega), r0]) (by rw [q _ (by omega), r1]) (by rw [q _ (by omega), r2])
    (by rw [q _ (by omega), r3]) (by rw [q _ (by omega), r4]) (by rw [q _ (by omega), r5])
    (by rw [q _ (by omega), r6]) (by rw [q _ (by omega), s0]) (by rw [q _ (by omega), s1])
    (by rw [q _ (by omega), s2]) (by rw [q _ (by omega), s3]) (by rw [q _ (by omega), s4])
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, G1, G2, fun a ha => ?_, fun x hx => ?_,
    by rw [G5, H8], by rw [G6, H9], by rw [G7, H10]⟩
  · rw [G3 a (by omega) (by omega) (by omega), fr a ha]
  · rw [G4 x (by omega), q x (by omega)]

end CC

/-! ### The arrays of the heavy and anchor scans -/

/-- The value `[nf ≠ 0] (1 + ex)`. -/
def lpV (nf ex : ℕ) : ℕ := (ex + 1) * (nf / nf)

lemma lpV_eq (nf ex : ℕ) : lpV nf ex = if nf ≠ 0 then 1 + ex else 0 := by
  unfold lpV; rw [sgn_eq]; split_ifs <;> simp_all; omega

lemma lpV_le (nf ex : ℕ) : lpV nf ex ≤ 1 + ex := by rw [lpV_eq]; split_ifs <;> omega

/-- One index (`4889 = 1`, `4890 = i`, `4891 = tot`, `4892 = 0`). -/
def lpBody : Stmt :=
  block [.addN 4893 4881 4890, .loadN 4893 4893, .divN 4893 4893 4893,
    .addN 4894 4882 4890, .loadN 4894 4894, .subN 4895 4894 4884, .subN 4896 4884 4894,
    .addN 4895 4895 4896, .divN 4895 4895 4895, .subN 4895 4889 4895,
    .addN 4894 4883 4890, .loadN 4894 4894, .addN 4894 4894 4889, .mulN 4894 4894 4893,
    .addN 4891 4891 4894,
    .addN 4896 4885 4890, .storeN 4896 4895,
    .addN 4896 4887 4890, .storeN 4896 4894,
    .mulN 4894 4895 4893, .addN 4896 4886 4890, .storeN 4896 4894,
    .addN 4896 4888 4890, .storeN 4896 4892,
    .addN 4890 4890 4889]

/-- **The arrays of the heavy and anchor scans.** -/
def lpProg : Stmt :=
  .seq (block [.constN 4889 1, .constN 4890 0, .constN 4891 0, .constN 4892 0,
    .addN 4896 4888 4880, .storeN 4896 4892]) (.whileLtN 4890 4880 lpBody)

section Exec

variable {P : Input} {W : ℕ}

theorem lpBody_exec (c : Config) (hc : WordsBounded W c)
    {NFb THb EXb J1 TGb TG2b VALb SUMb i tot : ℕ}
    (r1 : c.nreg 4881 = NFb) (r2 : c.nreg 4882 = THb) (r3 : c.nreg 4883 = EXb)
    (r4 : c.nreg 4884 = J1) (r5 : c.nreg 4885 = TGb) (r6 : c.nreg 4886 = TG2b)
    (r7 : c.nreg 4887 = VALb) (r8 : c.nreg 4888 = SUMb) (r9 : c.nreg 4889 = 1)
    (r10 : c.nreg 4890 = i) (r11 : c.nreg 4891 = tot) (r12 : c.nreg 4892 = 0)
    (w1 : NFb + i ≤ W) (w2 : THb + i ≤ W) (w3 : EXb + i ≤ W) (w4 : TGb + i ≤ W)
    (w5 : TG2b + i ≤ W) (w6 : VALb + i ≤ W) (w7 : SUMb + i ≤ W) (w8 : i + 1 ≤ W)
    (w9 : tot + c.nmem (EXb + i) + 1 ≤ W) :
    ∃ c' t, Exec P W lpBody c c' t ∧ t = 25 ∧ c'.nreg 4890 = i + 1 ∧
      c'.nreg 4891 = tot + lpV (c.nmem (NFb + i)) (c.nmem (EXb + i)) ∧
      c'.nmem = upd (upd (upd (upd c.nmem (TGb + i) (1 - phNe (c.nmem (THb + i)) J1))
        (VALb + i) (lpV (c.nmem (NFb + i)) (c.nmem (EXb + i))))
        (TG2b + i) ((1 - phNe (c.nmem (THb + i)) J1) * (c.nmem (NFb + i) / c.nmem (NFb + i))))
        (SUMb + i) 0 ∧
      (∀ x, (x < 4890 ∨ x = 4892 ∨ 4896 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hth := hc.2 (THb + i)
  have hJ := hc.1 4884
  rw [r4] at hJ
  have hne : (c.nmem (THb + i) - J1 + (J1 - c.nmem (THb + i))) /
      (c.nmem (THb + i) - J1 + (J1 - c.nmem (THb + i))) = phNe (c.nmem (THb + i)) J1 := rfl
  have hv : (c.nmem (EXb + i) + 1) * (c.nmem (NFb + i) / c.nmem (NFb + i)) =
      lpV (c.nmem (NFb + i)) (c.nmem (EXb + i)) := rfl
  have hv1 := lpV_le (c.nmem (NFb + i)) (c.nmem (EXb + i))
  have hne1 : phNe (c.nmem (THb + i)) J1 ≤ 1 := by rw [phNe_eq]; split_ifs <;> omega
  have ha1 : c.nmem (NFb + i) / c.nmem (NFb + i) ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
  have hm1 : (1 - phNe (c.nmem (THb + i)) J1) * (c.nmem (NFb + i) / c.nmem (NFb + i)) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha1 with h | h <;> rw [h] <;> omega
  have hW1 : 1 ≤ W := by omega
  unfold lpBody
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hne, hv]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r9, r10]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hne, hv]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hne, hv]
  · obtain ⟨a1, a2, a4, a5, a6, a7⟩ : x ≠ 4890 ∧ x ≠ 4891 ∧ x ≠ 4893 ∧
        x ≠ 4894 ∧ x ≠ 4895 ∧ x ≠ 4896 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7]

/-- **The arrays of the heavy and anchor scans on the machine**: within `27 n + 8` steps
`TG[i] = 1 - phNe TH[i] J1`, `TG2[i] = (1 - phNe TH[i] J1) [NF[i] ≠ 0]`, `VAL[i] = lpV NF[i]
EX[i]`, `SUM[k] = 0` (`k ≤ n`), `r4891 = Σ_{i < n} VAL[i]`; memory outside the four arrays,
registers outside `4889 … 4896`, reals and output kept. -/
theorem lpProg_exec (c : Config) (hc : WordsBounded W c)
    {n NFb THb EXb J1 TGb TG2b VALb SUMb : ℕ}
    (r0 : c.nreg 4880 = n) (r1 : c.nreg 4881 = NFb) (r2 : c.nreg 4882 = THb)
    (r3 : c.nreg 4883 = EXb) (r4 : c.nreg 4884 = J1) (r5 : c.nreg 4885 = TGb)
    (r6 : c.nreg 4886 = TG2b) (r7 : c.nreg 4887 = VALb) (r8 : c.nreg 4888 = SUMb)
    (lay : NFb + n ≤ TGb ∧ THb + n ≤ TGb ∧ EXb + n ≤ TGb ∧ TGb + n ≤ TG2b ∧ TG2b + n ≤ VALb ∧
      VALb + n ≤ SUMb ∧ SUMb + n + 1 ≤ W)
    (hsum : ∑ j ∈ range n, (1 + c.nmem (EXb + j)) ≤ W) :
    ∃ c' t, Exec P W lpProg c c' t ∧ t ≤ 27 * n + 8 ∧
      (∀ i < n, c'.nmem (TGb + i) = 1 - phNe (c.nmem (THb + i)) J1) ∧
      (∀ i < n, c'.nmem (TG2b + i) =
        (1 - phNe (c.nmem (THb + i)) J1) * (c.nmem (NFb + i) / c.nmem (NFb + i))) ∧
      (∀ i < n, c'.nmem (VALb + i) = lpV (c.nmem (NFb + i)) (c.nmem (EXb + i))) ∧
      (∀ k ≤ n, c'.nmem (SUMb + k) = 0) ∧
      c'.nreg 4891 = ∑ j ∈ range n, lpV (c.nmem (NFb + j)) (c.nmem (EXb + j)) ∧
      (∀ a, (a < TGb ∨ SUMb + n + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4889 ∨ 4896 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := lay
  unfold lpProg
  obtain ⟨c₁, k₁, e₁, hk₁, g89, g90, g91, g92, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4889 1, .constN 4890 0, .constN 4891 0, .constN 4892 0,
        .addN 4896 4888 4880, .storeN 4896 4892]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 4889 = 1 ∧ c₁.nreg 4890 = 0 ∧ c₁.nreg 4891 = 0 ∧ c₁.nreg 4892 = 0 ∧
      (∀ x, (x < 4889 ∨ 4896 < x) → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = upd c.nmem (SUMb + n) 0 ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [r0, r8]); omega)
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp,
      fun x hx => ?_, by config_simp; simp only [r0, r8], rfl, rfl, rfl⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4889 ∧ x ≠ 4890 ∧ x ≠ 4891 ∧ x ≠ 4892 ∧ x ≠ 4896 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4889 ∨ 4896 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  have hex : ∀ j < n, 1 + m₀ (EXb + j) ≤ W := fun j hj =>
    (single_le_sum (f := fun j => 1 + m₀ (EXb + j)) (fun _ _ => Nat.zero_le _)
      (mem_range.2 hj)).trans hsum
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4890 ∨ x = 4892 ∨ 4896 < x) → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 4891 = ∑ j ∈ range i, lpV (m₀ (NFb + j)) (m₀ (EXb + j)) ∧
    (∀ j < i, c'.nmem (TGb + j) = 1 - phNe (m₀ (THb + j)) J1) ∧
    (∀ j < i, c'.nmem (TG2b + j) = (1 - phNe (m₀ (THb + j)) J1) * (m₀ (NFb + j) / m₀ (NFb + j))) ∧
    (∀ j < i, c'.nmem (VALb + j) = lpV (m₀ (NFb + j)) (m₀ (EXb + j))) ∧
    (∀ k ≤ n, k < i ∨ k = n → c'.nmem (SUMb + k) = 0) ∧
    (∀ a, ¬ (TGb ≤ a ∧ a < TGb + i) → ¬ (TG2b ≤ a ∧ a < TG2b + i) →
      ¬ (VALb ≤ a ∧ a < VALb + i) → ¬ (SUMb ≤ a ∧ a < SUMb + i) → a ≠ SUMb + n →
      c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h90, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ := tgRange (P := P)
    (a := 4890) (b := 4880) (body := lpBody) J (B := 25) c₁ hw₁ g90
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [g91]; rfl, fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun k hk h => by
        rcases h with h | rfl
        · omega
        · rw [gm₁, upd_same],
      fun a _ _ _ _ ha => by rw [gm₁, upd_other _ _ _ ha], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h90 h80 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ => by
      have f : ∀ x, (x < 4890 ∨ x = 4892 ∨ 4896 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (NFb + i) = m₀ (NFb + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have e2 : c'.nmem (THb + i) = m₀ (THb + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have e3 : c'.nmem (EXb + i) = m₀ (EXb + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have htot : ∑ j ∈ range i, lpV (m₀ (NFb + j)) (m₀ (EXb + j)) + (1 + m₀ (EXb + i)) ≤ W := by
        have h1 : ∑ j ∈ range i, lpV (m₀ (NFb + j)) (m₀ (EXb + j)) ≤
            ∑ j ∈ range i, (1 + m₀ (EXb + j)) := sum_le_sum fun j _ => lpV_le _ _
        have h2 : ∑ j ∈ range (i + 1), (1 + m₀ (EXb + j)) ≤ W :=
          (sum_le_sum_of_subset_of_nonneg (fun x hx => by simp only [mem_range] at hx ⊢; omega)
            (fun _ _ _ => Nat.zero_le _)).trans hsum
        rw [sum_range_succ] at h2
        omega
      obtain ⟨c'', t, ex, ht, h90', h91', hm', hn', hr', hrm', ho'⟩ :=
        lpBody_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4]) (by rw [f _ (by omega), q _ (by omega), r5])
        (by rw [f _ (by omega), q _ (by omega), r6]) (by rw [f _ (by omega), q _ (by omega), r7])
        (by rw [f _ (by omega), q _ (by omega), r8]) (by rw [f _ (by omega), g89]) h90 j2
        (by rw [f _ (by omega), g92]) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by rw [e3]; omega)
      rw [e1, e2, e3] at hm'
      rw [e1, e3] at h91'
      refine ⟨c'', t, ex, ht.le, h90', by rw [hn' _ (by omega)]; exact h80,
        fun x hx => by rw [hn' x hx, f x hx], by rw [h91', sum_range_succ],
        fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun k hk hk' => ?_,
        fun a h1 h2 h3 h4 h5 => ?_, by rw [hr', j8], by rw [hrm', j9], by rw [ho', j10]⟩
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j4 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j5 j hj
        · rw [upd_same]
      · rw [hm']
        by_cases hki : k = i
        · subst hki; rw [upd_same]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact j6 k hk (by omega)
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j7 a (by omega) (by omega) (by omega) (by omega) h5)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j3, j4, j5, fun k hk => j6 k hk (by omega), j2,
    fun a ha => j7 a (by omega) (by omega) (by omega) (by omega) (by omega),
    fun x hx => by rw [j1 x (by omega), q x hx], by rw [j8, gr₁], by rw [j9, grm₁],
    by rw [j10, go₁]⟩

end Exec

end BKMNW

end PlanarFlow
