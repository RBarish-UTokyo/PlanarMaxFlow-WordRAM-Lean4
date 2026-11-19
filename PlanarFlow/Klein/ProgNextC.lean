module

public import PlanarFlow.Klein.ProgNext
public import PlanarFlow.Klein.ProgQueryC
public import PlanarFlow.Klein.ProgPivotC

/-!
# From one move to the next on the machine (the trees), with bounded comparisons

`nxPiv_orunC`, `nxA_orunC`: the proofs of `PlanarFlow/Klein/ProgNext.lean` replayed as runs whose
real comparisons are bounded (`DynTree.ORunC`). With the bound `A - Lo` of the values of the
forest at the end of the move (`Lo` the bound of `Stored` at the nodes of the faces), `|wt| ≤ Wt`
for the weights of the move, `Wt + tripW ≤ A - Lo` and
`2 (5 (A - Lo) + 6 tripK + 4 (Wt + tripW)) ≤ H`: the pivot of the next target on the next
boundary dart has an amount `c` with `|c| ≤ tripK` (as in `next_stored`), new values at most
`Wt + tripW + tripK`, so the values after the part are at most `A - (Lo - tripK)`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ}
  {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

section
variable {P : Input} {W B Hc : ℕ}

theorem nxPiv_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 8 * nD + n ≤ W) (hB : n + 2 * nD ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {φ wt : D → ℤ} {fe : F} {Lo : ℝ} {T : DTree M.dual}
    {val : D → ℤ} (hSt : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val)
    (hKM : KMem M σ ιv T wt φ c) (h101 : c.nreg 101 = ιf fe) {b : D}
    (h110 : c.nreg 110 = σ b) (h111 : c.nreg 111 = ιv (M.tail b))
    (h115 : c.nreg 115 = ιv (M.head b))
    (hy : M.head b ≠ T.root) (hna : ¬ T.Anc (M.head b) (M.dual.face b)) (hbT : ¬ T.InT b)
    {U Tb : ℝ} (hU : VBnd U n Fo)
    (ht₁ : |((wt (T.par (M.head b)) - φ (T.par (M.head b)) -
      (T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b) : ℤ) : ℝ)| ≤ Tb)
    (ht₂ : |((wt (M.rev (T.par (M.head b))) + φ (T.par (M.head b)) +
      (T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b) : ℤ) : ℝ)| ≤ Tb)
    (ht₃ : |(φ b : ℝ)| ≤ Tb) (ht₄ : |(φ (M.rev b) : ℝ)| ≤ Tb)
    (hH : 2 * (5 * U + 2 * |((T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b : ℤ) : ℝ)| +
      4 * Tb) ≤ Hc) :
    ∃ c' G' os, ORunC P W Hc B n (nxPivS B nD) c Fo G c' os G' 27 84 ∧ os.length = 16 ∧
      (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe
        (Lo - |((T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b : ℤ) : ℝ)|) (runOpsE n Fo os).1
        (T.reparent (M.head b) b hy (dual_face_rev b) hna)
        (pivotVal T φ wt val (M.head b) (T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b)) ∧
      VBnd (max (U + |((T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b : ℤ) : ℝ)|) Tb) n
        (runOpsE n Fo os).1 ∧
      KMem M σ ιv (T.reparent (M.head b) b hy (dual_face_rev b) hna) wt φ c' ∧ LoFr c c' ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aTP + ιv (M.head b) →
        c'.nmem a = c.nmem a) := by
  have hlab := fun x => lct_label hSt.tree hL.prim.f_lt hL.prim.e_lt hL.hv x
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU _ (hL.dual.e_lt b)).1
  have hTb : 0 ≤ Tb := (abs_nonneg _).trans ht₃
  have hH0 : 2 * U ≤ Hc := by
    have := abs_nonneg ((T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b : ℤ) : ℝ); linarith
  obtain ⟨c₁, G₁, o₁, -, -, -, s₁, -, m₁, f₁⟩ := regQuery_orunC (P := P) hW hc hS hU hH0 h111
    (hL.prim.f_lt _)
  have e₂ := Exec.copyR (P := P) o₁.1.2.wb 125 196
  have g₂ : GFr 125 126 c₁ { c₁ with rreg := upd c₁.rreg 125 (c₁.rreg 196) } := by gfr_tac
  have o₂ := ORunC.ofGFr (H := Hc) e₂ o₁.1.2.lcte g₂ (by omega) (by rfl)
  obtain ⟨c₃, G₃, o₃, -, -, -, s₃, -, m₃, f₃⟩ := regQuery_orunC (P := P) hW e₂.wb_right
    o₂.1.2.lcte hU hH0 (v := ιv (M.head b))
    (by rw [(g₂.1 115 (by omega)).1, f₁.1 115 (by omega), h115]) (hL.prim.f_lt _)
  have e₄ := Exec.copyR (P := P) o₃.1.2.wb 126 196
  have g₄ : GFr 126 127 c₃ { c₃ with rreg := upd c₃.rreg 126 (c₃.rreg 196) } := by gfr_tac
  have o₄ := ORunC.ofGFr (H := Hc) e₄ o₃.1.2.lcte g₄ (by omega) (by rfl)
  set c₄ := { c₃ with rreg := upd c₃.rreg 126 (c₃.rreg 196) } with hc₄
  have q110 : c₄.nreg 110 = σ b := by
    rw [hc₄]; config_simp
    rw [f₃.1 110 (by omega), (g₂.1 110 (by omega)).1, f₁.1 110 (by omega), h110]
  have q125 : c₄.rreg 125 = T.psum φ (M.tail b) := by
    rw [hc₄]; config_simp; rw [f₃.2.1 125 (by omega)]; config_simp; rw [s₁]; exact hlab _
  have q126 : c₄.rreg 126 = T.psum φ (M.head b) := by
    rw [hc₄]; config_simp; rw [s₃]; exact hlab _
  have hm₄ : MemFrame B n (mem c) (mem c₄) :=
    ((m₁.trans B n g₂.memFrame).trans B n m₃).trans B n g₄.memFrame
  have hKM₄ := hKM.congr hm₄ hB hL
  have hσb := (σ b).2
  have hc₄w : WordsBounded W c₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, r110, r114, g₅⟩ : ∃ c' k', Exec P W (block [.constN 117 (aPH nD),
      .addN 117 117 110, .loadR 127 117, .subR 110 125 126, .addR 110 110 127, .copyN 114 110])
      c₄ c' k' ∧ k' = 6 ∧
      c'.rreg 110 = ((T.psum φ (M.tail b) - T.psum φ (M.head b) + φ b : ℤ) : ℝ) ∧
      c'.nreg 114 = σ b ∧ GFr 110 128 c₄ c' := by
    exec_block
    · unfold aPH; omega
    · config_simp; rw [q110]; unfold aPH; omega
    · refine ⟨rfl, ?_, by config_simp; exact q110, by gfr_tac⟩
      config_simp; rw [q125, q126, q110, hKM₄.ph]; push_cast; ring
  have o₅ := ORunC.ofGFr (H := Hc) e₅ o₄.1.2.lcte g₅ (by omega) (by rfl)
  obtain ⟨c₆, G₆, os, o₆, -, hlen, hout, hSt', hVB, hKM₆, lf₆, rm₆, nm₆⟩ := pivCore_orunC hW hWa hB
    hP hM hL hK e₅.wb_right o₅.1.2.lcte hSt (hKM₄.congr g₅.memFrame hB hL)
    (by rw [(g₅.1 101 (by omega)).1, (g₄.1 101 (by omega)).1, f₃.1 101 (by omega),
      (g₂.1 101 (by omega)).1, f₁.1 101 (by omega), h101]) r114 r110 hy hna hbT hU ht₁ ht₂ ht₃
    ht₄ hH
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  have hm₅ : MemFrame B n (mem c) (mem c₅) := hm₄.trans B n g₅.memFrame
  refine ⟨c₆, G₆, os, o.mono (by omega) (by omega), hlen, hout, hSt', hVB, hKM₆, ?_,
    fun a ha => (rm₆ a ha).trans (hm₅ a ha).2,
    fun a ha hne => (nm₆ a ha hne).trans (hm₅ a ha).1⟩
  exact ((((((RegFr.loFr f₁).trans (g₂.loFr (by omega))).trans (RegFr.loFr f₃)).trans
    (g₄.loFr (by omega))).trans (g₅.loFr le_rfl)).trans lf₆)

theorem nxA_orunC (hW : B + 16 * (n + 1) ≤ W) {k : ℕ} (hWa : 8 * nD + n + k ≤ W)
    (hB : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) {g : ℕ → D}
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hLay : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) {j : ℕ} {R : MoveData M S}
    (h : MoveSpec M k g S ℓ j R) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {Lo : ℝ}
    (hSt : Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) Lo Fo (R.T R.m) (R.val R.m))
    (hKM : KMem M σ ιv (R.T R.m) (tripWt M k g S ℓ j) (tripφ S ℓ) c)
    (h90 : c.nreg 90 = j % k) (h91 : c.nreg 91 = (j + 1) % k)
    (h101 : c.nreg 101 = ιf (M.face (g (j % k)))) {A Wt : ℝ}
    (hwtb : ∀ d, |(tripWt M k g S ℓ j d : ℝ)| ≤ Wt) (hTA : Wt + tripW S ℓ ≤ A - Lo)
    (hHn : 2 * (5 * (A - Lo) + 6 * tripK V S ℓ + 4 * (Wt + tripW S ℓ)) ≤ Hc)
    (hVo : VBnd (A - Lo) n Fo) :
    ∃ (c' : Config) (G' : List VT) (os : List EOp) (T' : DTree M.dual) (val' : D → ℤ),
      ORunC P W Hc B n (nxAS B nD n) c Fo G c' os G' 29 125 ∧ os.length ≤ 18 ∧
      (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g ((j + 1) % k))) (Lo - tripK V S ℓ)
        (runOpsE n Fo os).1 T' val' ∧
      VInv T' (tripφ S ℓ) (tripWt M k g S ℓ j) val' ∧ T'.root = tripDst M k g j ∧
      T'.par (tripDst M k g (j + 1)) = g ((j + 1) % k) ∧
      (tripDst M k g (j + 1) ≠ tripSrc M k g j →
        T'.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      (∀ x, x ≠ tripSrc M k g j → x ≠ tripDst M k g (j + 1) → T'.par x = (R.T R.m).par x) ∧
      KMem M σ ιv T' (tripWt M k g S ℓ j) (tripφ S ℓ) c' ∧
      c'.nreg 100 = ιf (M.face (M.rev (g ((j + 1) % k)))) ∧
      c'.nreg 101 = ιf (M.face (g ((j + 1) % k))) ∧
      (∀ r, r < 100 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c'.nmem a = c.nmem a) ∧
      VBnd (A - (Lo - tripK V S ℓ)) n (runOpsE n Fo os).1 := by
  classical
  have hU0 : 0 ≤ A - Lo := (abs_nonneg _).trans (hVo _ (hLay.dual.e_lt (g 0))).1
  have hW0 : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hWt0 : 0 ≤ Wt := (abs_nonneg _).trans (hwtb (g 0))
  have hK0' : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have hH0 : 2 * (A - Lo) ≤ Hc := by linarith
  have hH1 : 2 * (A - (Lo - tripK V S ℓ)) ≤ Hc := by linarith
  -- the data (as in `next_stored`)
  have hC := h.1.compat R.m le_rfl
  rw [end_tpar H hR h] at hC
  have hV := h.1.vinv R.m le_rfl
  have hk := H.two_le_k
  have hK0 : (0 : ℝ) ≤ tripK V S ℓ := by exact_mod_cast tripK_nonneg
  have e1 : (j + 1 + 1) % k = ((j + 1) % k + 1) % k := (Nat.mod_add_mod _ _ _).symm
  have hwv : tripDst M k g (j + 1) ≠ tripDst M k g j := by
    intro h'
    exact H.mod_ne (j + 1) (H.face.inj _ (H.mod_lt (j + 1 + 1)) _ (H.mod_lt (j + 1)) h').symm
  have hvu : tripDst M k g j ≠ tripSrc M k g j := fun h' =>
    H.mod_ne j (H.face.inj _ (H.mod_lt j) _ (H.mod_lt (j + 1)) h'.symm)
  have he'w : M.head (g ((j + 1) % k)) = tripDst M k g (j + 1) := by
    rw [H.head_g _ (H.mod_lt _)]; unfold tripDst; rw [e1]
  have hv : tripDst M k g j ≠ (R.T R.m).root := by rw [hC.root]; exact hvu
  have hup : M.tail ((R.T R.m).par (tripDst M k g j)) = (R.T R.m).root := by
    rw [hC.par_v, hC.tail, hC.root]
  obtain ⟨hv1, ho1, hS1⟩ := rerootChild_stored hLay hSt hv hup
  set T₁ := rerootChild (R.T R.m) _ hv hup with hT₁
  have hV₁ : VInv T₁ (tripφ S ℓ) (tripWt M k g S ℓ j) (R.val R.m) :=
    rerootChild_vinv _ hv hup (by rw [hC.par_v]; exact H.tripφ_g j)
      (by rw [hC.par_v]; exact H.tripφ_rev_g j) hV
  have hr₁ : T₁.root = tripDst M k g j := rfl
  have hpu : T₁.par (tripSrc M k g j) = M.rev (g (j % k)) := by
    rw [← hC.root, hT₁, rerootChild_par_root, hC.par_v]
  have hpx : ∀ x, x ≠ tripSrc M k g j → T₁.par x = (R.T R.m).par x := fun x hx =>
    rerootChild_par _ hv hup x (by rw [hC.root]; exact hx)
  set b := g ((j + 1) % k) with hb
  set w := tripDst M k g (j + 1) with hw
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hgb := hG _ (H.mod_lt (j + 1))
  have hga := hG _ (H.mod_lt j)
  have hm1 := H.mod_lt (j + 1)
  have hm0 := H.mod_lt j
  have hvn := hLay.prim.f_lt
  -- the node of the next source, and `evert` there
  obtain ⟨c₁, k₁, e₁, hk₁, p110, p111, g₁⟩ : ∃ c' k', Exec P W (block [.constN 110 (iGB nD n),
      .addN 110 110 91, .readIn 110 110, .constN 111 (iNT nD), .addN 111 111 110,
      .readIn 111 111]) c c' k' ∧ k' = 6 ∧ c'.nreg 110 = σ b ∧
      c'.nreg 111 = ιv (tripDst M k g j) ∧ GFr 110 112 c c' := by
    have := hσ b
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iGB, iNT]; omega)
      | (config_simp; simp only [h91, hgb]; simp only [iGB, iNT]; omega))
    refine ⟨rfl, by config_simp; simp only [h91, hgb, hb], ?_, by gfr_tac⟩
    config_simp; simp only [h91, hgb, hK.nt]; rfl
  have o₁ := ORunC.ofGFr (H := Hc) e₁ hS g₁ (by omega) (by rfl)
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := regEvert_orunC (P := P) hW e₁.wb_right o₁.1.2.lcte hVo hH0 p111
    (hvn _)
  -- the parent dart of the old source, and the parent dart of the next target
  have hc₂ := o₂.1.2.wb
  have q110 : c₂.nreg 110 = σ b := by rw [f₂.1 110 (by omega), p110]
  have q90 : c₂.nreg 90 = j % k := by rw [f₂.1 90 (by omega), (g₁.1 90 (by omega)).1, h90]
  obtain ⟨c₃, k₃, e₃, hk₃, t115, t116, tnm, tregs, trr, trm, tout⟩ : ∃ c' k', Exec P W
      (block [.constN 112 (iGB nD n), .addN 112 112 90, .readIn 112 112,
        .constN 113 (iRV nD), .addN 113 113 112, .readIn 113 113,
        .constN 114 (iNT nD), .addN 114 114 112, .readIn 114 114,
        .constN 115 aTP, .addN 115 115 114, .storeN 115 113,
        .constN 115 (iNH nD), .addN 115 115 110, .readIn 115 115,
        .constN 116 aTP, .addN 116 116 115, .loadN 116 116]) c₂ c' k' ∧ k' = 18 ∧
      c'.nreg 115 = ιv w ∧ c'.nreg 116 = c'.nmem (aTP + ιv w) ∧
      c'.nmem = upd c₂.nmem (aTP + ιv (tripSrc M k g j)) (σ (M.rev (g (j % k)))) ∧
      (∀ r, (r < 112 ∨ 117 ≤ r) → c'.nreg r = c₂.nreg r) ∧ c'.rreg = c₂.rreg ∧
      c'.rmem = c₂.rmem ∧ c'.output = c₂.output := by
    have := hσ (g (j % k))
    have := hσ (M.rev (g (j % k)))
    have := hσ b
    have := hvn (M.tail (g (j % k)))
    have := hvn (M.head b)
    have := hvn w
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iGB, iNT, iRV, iNH, aTP]; omega)
      | (config_simp; simp only [q90, q110, hga, hK.rv, hK.nt, hK.nh, he'w]; simp only [iGB, iNT,
          iRV, iNH, aTP]; omega))
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals try (config_simp; simp only [q110, q90, hga, hK.rv, hK.nt, hK.nh, he'w]; done)
    · config_simp; simp only [q90, hga, hK.rv, hK.nt]; rfl
    · simp only [upd_out (lo := 112) (hi := 117) hr, Nat.reduceLeDiff, Nat.reduceLT, le_refl]
  have hsrc := hvn (tripSrc M k g j)
  have o₃ : ORunC P W Hc B n _ c₂ _ G₂ c₃ [] G₂ 0 k₃ := ORunC.glue (H := Hc) e₃ o₂.1.2.lcte
    (fun a ha _ => ⟨by rw [tnm, upd_other _ _ _ (by unfold aTP; omega)], by rw [trm]⟩)
    (tregs 151 (by omega)) (by rfl)
  -- the mutable arrays hold the re-rooted tree
  have hKM₃ : KMem M σ ιv T₁ (tripWt M k g S ℓ j) (tripφ S ℓ) c₃ := by
    have hm := m₂
    refine ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩
    · rw [tnm]
      by_cases hxs : x = tripSrc M k g j
      · rw [hxs, upd_same, hpu]
      · rw [upd_other _ _ _ (fun h => hxs (hLay.prim.f_inj (by unfold aTP at h; omega))),
          hpx x hxs]
        have h1 := (hm (aTP + ιv x) (Or.inl (by have := hvn x; unfold aTP; omega))).1
        simp only [DynTree.mem] at h1
        rw [h1, g₁.2.1]
        exact hKM.tp x (by rw [hC.root]; exact hxs)
    · rw [trm]
      have h1 := (hm (aWT + σ d) (Or.inl (by have := hσ d; unfold aWT; omega))).2
      simp only [DynTree.mem] at h1
      rw [h1, g₁.2.2.1]; exact hKM.wt d
    · rw [trm]
      have h1 := (hm (aPH nD + σ d) (Or.inl (by have := hσ d; unfold aPH; omega))).2
      simp only [DynTree.mem] at h1
      rw [h1, g₁.2.2.1]; exact hKM.ph d
  have t116' : c₃.nreg 116 = σ (T₁.par w) := by
    rw [t116]; exact hKM₃.tp w hwv
  have t110 : c₃.nreg 110 = σ b := by rw [tregs 110 (by omega), q110]
  have t111 : c₃.nreg 111 = ιv (M.tail b) := by
    rw [tregs 111 (by omega), f₂.1 111 (by omega), p111]; rfl
  have t101 : c₃.nreg 101 = ιf (M.face (g (j % k))) := by
    rw [tregs 101 (by omega), f₂.1 101 (by omega), (g₁.1 101 (by omega)).1, h101]
  -- the pivot of the next target, when needed
  have hmid : ∃ (c₄ : Config) (G₄ : List VT) (os₂ : List EOp) (T₂ : DTree M.dual)
      (val₂ : D → ℤ), ORunC P W Hc B n (.ifLtN 116 110 (nxPivS B nD)
        (.ifLtN 110 116 (nxPivS B nD) .skip)) c₃ (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1
        G₂ c₄ os₂ G₄ 27 87 ∧ os₂.length ≤ 16 ∧
      (runOpsE n (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 os₂).2 = [] ∧
      Stored M n ιv ιg ιf ιe (tripφ S ℓ) (M.face (g (j % k))) (Lo - tripK V S ℓ)
        (runOpsE n (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 os₂).1 T₂ val₂ ∧
      VInv T₂ (tripφ S ℓ) (tripWt M k g S ℓ j) val₂ ∧ T₂.root = tripDst M k g j ∧
      T₂.par w = b ∧ (w ≠ tripSrc M k g j → T₂.par (tripSrc M k g j) = M.rev (g (j % k))) ∧
      (∀ x, x ≠ tripSrc M k g j → x ≠ w → T₂.par x = (R.T R.m).par x) ∧
      KMem M σ ιv T₂ (tripWt M k g S ℓ j) (tripφ S ℓ) c₄ ∧ LoFr c₃ c₄ ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₄.rmem a = c₃.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → n ≤ a → c₄.nmem a = c₃.nmem a) ∧
      VBnd (A - (Lo - tripK V S ℓ)) n
        (runOpsE n (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 os₂).1 := by
    have hV1 : VBnd (A - Lo) n (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 :=
      vbnd_evertOp hVo _
    by_cases hin : T₁.par w = b
    · have hge : ¬ c₃.nreg 116 < c₃.nreg 110 := by rw [t116', t110, hin]; omega
      have hge' : ¬ c₃.nreg 110 < c₃.nreg 116 := by rw [t116', t110, hin]; omega
      have o : ORunC P W Hc B n .skip c₃ (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 G₂ c₃ []
          G₂ 0 0 := ORunC.skip e₃.wb_right o₃.1.2.lcte
      refine ⟨c₃, G₂, [], T₁, R.val R.m, ((o.ifLtN_false (t := nxPivS B nD) hge').ifLtN_false
        (t := nxPivS B nD) hge).mono (by omega) (by omega), by simp, rfl,
        hS1.mono (by linarith), hV₁, hr₁, hin, fun _ => hpu, fun x hx _ => hpx x hx, hKM₃,
        LoFr.refl _, fun _ _ => rfl, fun _ _ _ => rfl, hV1.mono (by linarith)⟩
    have hw₁ : M.head b ≠ T₁.root := by rw [he'w]; exact hwv
    have hna : ¬ T₁.Anc (M.head b) (M.dual.face b) := by
      change ¬ T₁.Anc (M.head b) T₁.root
      rw [T₁.anc_root_iff, he'w]; exact hwv
    have hbT : ¬ T₁.InT b := by
      rintro ⟨x, hx, hd | hd⟩
      · have : x = w := by rw [← tpar_head T₁ hx, ← hd, he'w]
        subst this; exact hin hd.symm
      · have hd' : b = M.rev (T₁.par x) := hd
        have : M.head (T₁.par x) = tripDst M k g j := by
          rw [← M.tail_rev, ← hd']; rfl
        rw [tpar_head T₁ hx] at this
        exact hx this
    have hne : c₃.nreg 116 ≠ c₃.nreg 110 := by
      rw [t116', t110]; intro h'
      exact hin (σ.injective (Fin.ext h'))
    have tb1 : ∀ p q r : ℝ, |p| ≤ Wt → |q| ≤ tripW S ℓ → |p - q - r| ≤ Wt + tripW S ℓ + |r| :=
      fun p q r hp hq => by
        have h1 := abs_sub p q; have h2 := abs_sub (p - q) r; linarith
    have tb2 : ∀ p q r : ℝ, |p| ≤ Wt → |q| ≤ tripW S ℓ → |p + q + r| ≤ Wt + tripW S ℓ + |r| :=
      fun p q r hp hq => by
        have h1 := abs_add_le p q; have h2 := abs_add_le (p + q) r; linarith
    have hφb : ∀ d, |(tripφ S ℓ d : ℝ)| ≤ tripW S ℓ := fun d => by
      exact_mod_cast abs_tripφ_le (S := S) (ℓ := ℓ) d
    have hcK' : |((T₁.psum (tripφ S ℓ) (M.tail b) - T₁.psum (tripφ S ℓ) (M.head b) +
        tripφ S ℓ b : ℤ) : ℝ)| ≤ tripK V S ℓ := by
      have hc' : |T₁.psum (tripφ S ℓ) (M.tail b) - T₁.psum (tripφ S ℓ) (M.head b) +
          tripφ S ℓ b| ≤ tripK V S ℓ := by
        have hB3 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.tail b))
        have hB4 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.head b))
        have hWd := abs_le.1 (abs_tripφ_le (S := S) (ℓ := ℓ) b)
        have l1 := abs_nonneg (tripL V S ℓ)
        have l3 := le_abs_self (tripW S ℓ)
        have l5 := le_abs_self ((Fintype.card V : ℤ) * tripW S ℓ)
        unfold tripK driftK
        exact abs_le.2 ⟨by linarith, by linarith⟩
      rw [← Int.cast_abs]; exact_mod_cast hc'
    have hcK'' := hcK'
    push_cast at hcK''
    obtain ⟨c₄, G₄, os, o, hlen, hout, hS₂, hVB₂, hKM₄, lf₄, rm₄, nm₄⟩ := nxPiv_orunC hW
      (by omega) hB hP H.plane hLay hK e₃.wb_right o₃.1.2.lcte hS1 hKM₃ t101 t110 t111
      (by rw [t115, he'w]) hw₁ hna hbT (Tb := Wt + tripW S ℓ + tripK V S ℓ) hV1
      (by push_cast; exact (tb1 _ _ _ (hwtb _) (hφb _)).trans (by linarith))
      (by push_cast; exact (tb2 _ _ _ (hwtb _) (hφb _)).trans (by linarith))
      ((hφb b).trans (by linarith)) ((hφb (M.rev b)).trans (by linarith)) (by linarith)
    have hcv : R.val R.m b - tripWt M k g S ℓ j b + tripφ S ℓ b =
        T₁.psum (tripφ S ℓ) (M.tail b) - T₁.psum (tripφ S ℓ) (M.head b) + tripφ S ℓ b := by
      rw [hV₁ b hbT]; ring
    have hcK : |((T₁.psum (tripφ S ℓ) (M.tail b) - T₁.psum (tripφ S ℓ) (M.head b) +
        tripφ S ℓ b : ℤ) : ℝ)| ≤ tripK V S ℓ := by
      have hc' : |T₁.psum (tripφ S ℓ) (M.tail b) - T₁.psum (tripφ S ℓ) (M.head b) +
          tripφ S ℓ b| ≤ tripK V S ℓ := by
        have hB3 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.tail b))
        have hB4 := abs_le.1 (abs_psum_le_mul T₁ (abs_tripφ_le (S := S) (ℓ := ℓ)) (M.head b))
        have hWd := abs_le.1 (abs_tripφ_le (S := S) (ℓ := ℓ) b)
        have l1 := abs_nonneg (tripL V S ℓ)
        have l3 := le_abs_self (tripW S ℓ)
        have l5 := le_abs_self ((Fintype.card V : ℤ) * tripW S ℓ)
        unfold tripK driftK
        exact abs_le.2 ⟨by linarith, by linarith⟩
      rw [← Int.cast_abs]; exact_mod_cast hc'
    have hV₂ := reparent_vinv H.plane T₁ hw₁ (dual_face_rev b) hna hbT hV₁
    rw [hcv] at hV₂
    have hT2 : ∀ x, (T₁.reparent (M.head b) b hw₁ (dual_face_rev b) hna).par x =
        if x = w then b else T₁.par x := fun x => by rw [DTree.reparent_par, he'w]
    have hO : ORunC P W Hc B n (.ifLtN 116 110 (nxPivS B nD) (.ifLtN 110 116 (nxPivS B nD) .skip)) c₃
        (runOpsE n Fo [.evert (ιv (tripDst M k g j))]).1 G₂ c₄ os G₄ 27 87 := by
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · exact (o.ifLtN_true (e := .ifLtN 110 116 (nxPivS B nD) .skip) hl).mono le_rfl (by omega)
      · exact ((o.ifLtN_true (e := .skip) hl).ifLtN_false (t := nxPivS B nD)
          (by omega)).mono le_rfl (by omega)
    refine ⟨c₄, G₄, os, _, _, hO, by omega, hout, hS₂.mono (by linarith), hV₂, rfl, ?_,
      fun hws => ?_, fun x hx hxw => ?_, hKM₄, lf₄, rm₄, fun a ha han => ?_,
      hVB₂.mono (max_le (by linarith) (by linarith))⟩
    · rw [hT2, ite_eq_left rfl]
    · rw [hT2, ite_eq_right (Ne.symm hws)]; exact hpu
    · rw [hT2, ite_eq_right hxw]; exact hpx x hx
    · exact nm₄ a ha (by have := hvn (M.head b); unfold aTP; omega)
  obtain ⟨c₄, G₄, os₂, T₂, val₂, o₄, hl₂, ho₂, hS₂, hV₂, hr₂, hpw₂, hpu₂, hpx₂, hKM₄, lf₄, rm₄,
    nm₄, hVm⟩ := hmid
  -- the face of `b`, and `evert` there
  have hc₄ := o₄.1.2.wb
  have u91 : c₄.nreg 91 = (j + 1) % k := by
    rw [(lf₄.1 91 (by omega)).1, tregs 91 (by omega), f₂.1 91 (by omega),
      (g₁.1 91 (by omega)).1, h91]
  obtain ⟨c₅, k₅, e₅, hk₅, v110, v117, g₅⟩ : ∃ c' k', Exec P W (block [.constN 110 (iGB nD n),
      .addN 110 110 91, .readIn 110 110, .constN 117 (iNF nD), .addN 117 117 110,
      .readIn 117 117]) c₄ c' k' ∧ k' = 6 ∧ c'.nreg 110 = σ b ∧
      c'.nreg 117 = ιf (M.face b) ∧ GFr 110 118 c₄ c' := by
    have := hσ b
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iGB, iNF]; omega)
      | (config_simp; simp only [u91, hgb]; simp only [iGB, iNF]; omega))
    refine ⟨rfl, by config_simp; simp only [u91, hgb, hb], ?_, by gfr_tac⟩
    config_simp; simp only [u91, hgb, hK.nf, hb]
  have o₅ := ORunC.ofGFr (H := Hc) e₅ o₄.1.2.lcte g₅ (by omega) (by rfl)
  obtain ⟨c₆, G₆, o₆, m₆, f₆⟩ := regEvert_orunC (P := P) hW e₅.wb_right o₅.1.2.lcte hVm hH1 v117
    (hLay.dual.f_lt _)
  obtain ⟨hv3, ho3, hS3⟩ := recot_stored hLay hS₂ (M.face b)
  -- the query nodes of the next move
  have hc₆ := o₆.1.2.wb
  have w110 : c₆.nreg 110 = σ b := by rw [f₆.1 110 (by omega), v110]
  have w117 : c₆.nreg 117 = ιf (M.face b) := by rw [f₆.1 117 (by omega), v117]
  obtain ⟨c₇, k₇, e₇, hk₇, x100, x101, g₇⟩ : ∃ c' k', Exec P W (block [.copyN 101 117,
      .constN 118 (iRV nD), .addN 118 118 110, .readIn 118 118, .constN 100 (iNF nD),
      .addN 100 100 118, .readIn 100 100]) c₆ c' k' ∧ k' = 7 ∧
      c'.nreg 100 = ιf (M.face (M.rev b)) ∧ c'.nreg 101 = ιf (M.face b) ∧
      (∀ r, r < 100 → c'.nreg r = c₆.nreg r ∧ c'.rreg r = c₆.rreg r) ∧ c'.nmem = c₆.nmem ∧
      c'.rmem = c₆.rmem ∧ c'.output = c₆.output ∧ c'.nreg 151 = c₆.nreg 151 := by
    have := hσ b
    have := hσ (M.rev b)
    exec_block
    all_goals try (first
      | exact hP _
      | (simp only [iRV, iNF]; omega)
      | (config_simp; simp only [w110, hK.rv]; simp only [iRV, iNF]; omega))
    refine ⟨rfl, ?_, by config_simp; exact w117, fun r hr => ⟨?_, rfl⟩, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [w110, hK.rv, hK.nf]
    · simp only [upd_out (lo := 100) (hi := 119) (Or.inl hr), Nat.reduceLeDiff, Nat.reduceLT,
        le_refl]
  have o₇ : ORunC P W Hc B n _ c₆ _ G₆ c₇ [] G₆ 0 k₇ := ORunC.glue (H := Hc) e₇ o₆.1.2.lcte
    (fun a _ _ => by rw [g₇.2.1, g₇.2.2.1]; exact ⟨rfl, rfl⟩) g₇.2.2.2.2 (by rfl)
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq o₇)))))
  simp only [List.nil_append, List.append_nil] at o
  have hmem : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₇.rmem a = c₄.rmem a ∧
      c₇.nmem a = c₄.nmem a := fun a ha => by
    have h6 := m₆ a ha
    simp only [DynTree.mem] at h6
    rw [g₇.2.1, g₇.2.2.1, h6.1, h6.2, g₅.2.1, g₅.2.2.1]; exact ⟨rfl, rfl⟩
  have hmem₃ : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₃.rmem a = c.rmem a ∧
      (n ≤ a → c₃.nmem a = c.nmem a) := fun a ha => by
    have h2 := m₂ a ha
    simp only [DynTree.mem] at h2
    refine ⟨by rw [trm, h2.2, g₁.2.2.1], fun han => ?_⟩
    rw [tnm, upd_other _ _ _ (by unfold aTP; omega), h2.1, g₁.2.1]
  refine ⟨c₇, G₆, _, T₂, val₂, o.mono (by omega) (by omega), ?_, ?_, ?_, hV₂, hr₂, hpw₂, hpu₂,
    hpx₂, ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩, x100, x101, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha han => ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · rw [runOpsE_append, runOpsE_append, ho1, ho₂, ho3]; rfl
  · rw [runOpsE_fst_append, runOpsE_fst_append]; exact hS3
  · rw [(hmem _ (Or.inl (by have := hvn x; unfold aTP; omega))).2]; exact hKM₄.tp x hx
  · rw [(hmem _ (Or.inl (by have := hσ d; unfold aWT; omega))).1]; exact hKM₄.wt d
  · rw [(hmem _ (Or.inl (by have := hσ d; unfold aPH; omega))).1]; exact hKM₄.ph d
  · rw [(g₇.1 r hr).1, (g₇.1 r hr).2, f₆.1 r (by omega), f₆.2.1 r (by omega),
      (g₅.1 r (by omega)).1, (g₅.1 r (by omega)).2, (lf₄.1 r (by omega)).1,
      (lf₄.1 r (by omega)).2, tregs r (by omega), trr, f₂.1 r (by omega), f₂.2.1 r (by omega),
      (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [g₇.2.2.2.1, f₆.2.2, g₅.2.2.2, lf₄.2, tout, f₂.2.2, g₁.2.2.2]
  · rw [(hmem a ha).1, rm₄ a ha, (hmem₃ a ha).1]
  · rw [(hmem a ha).2, nm₄ a ha han, (hmem₃ a ha).2 han]
  · rw [runOpsE_fst_append, runOpsE_fst_append]; exact vbnd_evertOp hVm _

end

end Klein

end PlanarFlow
