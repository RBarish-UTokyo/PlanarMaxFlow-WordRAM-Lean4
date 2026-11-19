module

public import PlanarFlow.STFlow.InitC
public import PlanarFlow.STFlow.ProgMain

/-!
# The flow into `OUT` with bounded comparisons

The compare-bounded versions (`ORunC`) of the realization lemmas of the output phase
(`PlanarFlow/STFlow/ProgOut.lean`), replayed with the same proofs: `stCv_orunC` (`cv_orun`, the
operations with values at most `Vb` before each, `AllV`), `stLam_orunC`, `stRd_orunC`,
`stWr_orunC` (no operation, the forest with values at most `Vb`), with `2 Vb ≤ H`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

section
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {W B : ℕ}

theorem stCvBody_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + 6 ≤ W)
    (hB : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {T₀ T : DTree M} {ts : List F}
    (hts : ∀ i (h : i < ts.length), P.data.getD (iIT nD n 2 + i) 0 = σ (T₀.par ts[i]))
    (htl : iIT nD n 2 + ts.length ≤ W) (hroot : ∀ y ∈ ts, y ≠ T₀.root ∧ y ≠ T.root)
    {cap w : D → ℤ} {i : ℕ} (hi : i < ts.length) {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) (h120 : c.nreg 120 = i)
    (htp : ∀ y, y ≠ T.root → c.nmem (aTP + ιF y) = σ (T.par y))
    (hcp : ∀ d, c.rmem (aCP nD + σ d) = cap d) (hwt : ∀ d, c.rmem (aWT + σ d) = w d)
    (hv : ValidOpsE n Fo (pointOps ιF ιG (toDD T) ts[i]
      (cap (T.par ts[i]) - w (T.par ts[i]))
      (cap (M.rev (T.par ts[i])) - w (M.rev (T.par ts[i]))))) {H : ℕ} {Vb : ℝ}
    (hAV : AllV Vb n Fo (pointOps ιF ιG (toDD T) ts[i]
      (cap (T.par ts[i]) - w (T.par ts[i]))
      (cap (M.rev (T.par ts[i])) - w (M.rev (T.par ts[i]))))) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (cvBodyS B nD n) c Fo G c' (pointOps ιF ιG (toDD T) ts[i]
        (cap (T.par ts[i]) - w (T.par ts[i])) (cap (M.rev (T.par ts[i])) - w (M.rev (T.par ts[i]))))
        G' 4 40 ∧ c'.nreg 120 = i + 1 ∧ IFr B n c c' := by
  set y := ts[i] with hy
  have hy0 : y ≠ T₀.root := (hroot y (List.getElem_mem hi)).1
  have hyr : y ≠ T.root := (hroot y (List.getElem_mem hi)).2
  set a := T.par y with ha
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have h1 := hσ (T₀.par y)
  have h2 := hσ a
  have h3 := hσ (M.rev a)
  have hny : P.data.getD (iNH nD + σ (T₀.par y)) 0 = ιF y := by
    rw [hK.nh]; exact congrArg ιF (T₀.head_par y hy0)
  have hyn := hL.prim.f_lt y
  obtain ⟨c₁, k₁, e₁, hk₁, p134, p135, p140, p141, p142, p143, g₁⟩ : ∃ c' k',
      Exec P W (block (cvRd nD n)) c c' k' ∧ k' = 36 ∧ c'.nreg 134 = ιG a ∧
      c'.nreg 135 = ιF (M.face a) ∧ c'.rreg 140 = ((cap a - w a : ℤ) : ℝ) ∧
      c'.rreg 141 = ((-(cap a - w a) : ℤ) : ℝ) ∧
      c'.rreg 142 = ((cap (M.rev a) - w (M.rev a) : ℤ) : ℝ) ∧
      c'.rreg 143 = ((-(cap (M.rev a) - w (M.rev a)) : ℤ) : ℝ) ∧ GFr 130 144 c c' := by
    unfold cvRd
    exec_block
    all_goals try (first
      | exact hP _
      | omega
      | (offs_simp'; omega)
      | (config_simp; rw [h120]; omega)
      | (config_simp; rw [h120, hts i hi]; offs_simp'; omega)
      | (config_simp; rw [h120, hts i hi, hny]; offs_simp'; omega)
      | (config_simp; rw [h120, hts i hi, hny, htp y hyr]; offs_simp'; omega)
      | (config_simp; rw [h120, hts i hi, hny, htp y hyr, hK.rv]; offs_simp'; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hK.ng]
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hK.nt]; rfl
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hcp, hwt]; push_cast; ring
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hcp, hwt]; push_cast; ring
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hK.rv, hcp, hwt]; push_cast; rfl
    · config_simp; rw [h120, hts i hi, hny, htp y hyr, hK.rv, hcp, hwt]
      show ((0 : ℤ) : ℝ) - ((cap (M.rev a) : ℝ) - (w (M.rev a) : ℝ)) = _
      push_cast; ring
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  set zr : ℕ → ℤ := fun r => if r = 140 then cap a - w a else if r = 141 then -(cap a - w a)
    else if r = 142 then cap (M.rev a) - w (M.rev a) else -(cap (M.rev a) - w (M.rev a))
    with hzr
  have hops : [ROp.add 134 140, ROp.add 135 141, ROp.add2 134 142, ROp.add2 135 143].map
      (ROp.eop c₁ zr) = pointOps ιF ιG (toDD T) y (cap a - w a)
        (cap (M.rev a) - w (M.rev a)) := by
    simp [ROp.eop, p134, p135, hzr, pointOps]; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨c₂, G₂, o₂, m₂, f₂⟩ := ropsS_orunC (P := P) hW zr hH
    [ROp.add 134 140, ROp.add 135 141, ROp.add2 134 142, ROp.add2 135 143] e₁.wb_right
    o₁.1.2.lcte (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact ⟨by norm_num, by norm_num, by rw [p140]; simp [hzr]⟩
      · exact ⟨by norm_num, by norm_num, by rw [p141]; simp [hzr]⟩
      · exact ⟨by norm_num, by norm_num, by rw [p142]; simp [hzr]⟩
      · exact ⟨by norm_num, by norm_num, by rw [p143]; simp [hzr]⟩) (by rw [hops]; exact hv)
    (by rw [hops]; exact hAV)
  rw [hops] at o₂
  have hc₂ := o₂.1.2.wb
  obtain ⟨c₃, k₃, e₃, hk₃, q120, g₃, n₃⟩ := incI_exec (P := P) hc₂ (i := i)
    (by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]) (by omega)
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append, List.append_nil] at o
  refine ⟨c₃, G₂, o.mono (by simp) (by omega), q120, ?_⟩
  refine ((IFr.refl B n c).trans ⟨fun r hr => (g₁.1 r (by omega)).1, fun r hr =>
    (g₁.1 r (by omega)).2, g₁.2.2.2, fun a _ => by rw [g₁.2.1, g₁.2.2.1]; exact ⟨rfl, rfl⟩⟩).trans
    (IFr.trans ⟨fun r hr => f₂.1 r (by omega), fun r hr => f₂.2.1 r (by omega), f₂.2.2,
      fun a ha => m₂ a ha⟩ ⟨fun r hr => n₃ r (by omega) (by omega), fun r hr =>
      (g₃.1 r (by omega)).2, g₃.2.2.2, fun a _ => by rw [g₃.2.1, g₃.2.2.1]; exact ⟨rfl, rfl⟩⟩)


theorem stCv_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 9 * nD + 7 * n + 6 ≤ W)
    (hB : 7 * nD + 3 ≤ B) (hBn : n + 2 * nD ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W)
    (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {T₀ : DTree M} {C₀ : DTree M.dual} {vs ts : List F}
    {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P) {T : DTree M}
    (hroot : T.root = T₀.root) {cap w : D → ℤ} {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c)
    (htp : ∀ y, y ≠ T.root → c.nmem (aTP + ιF y) = σ (T.par y))
    (hcp : ∀ d, c.rmem (aCP nD + σ d) = cap d) (hwt : ∀ d, c.rmem (aWT + σ d) = w d)
    (hv : ValidOpsE n Fo (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y))))) {H : ℕ}
    {Vb : ℝ} (hAV : AllV Vb n Fo (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))))
    (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (cvS B nD n) c Fo G c' (ts.flatMap fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))) G'
        (4 * ts.length) (42 * ts.length + 5) ∧ IFr0 B n c c' := by
  have htl := hI.oT.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hv
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ := ldI_exec (P := P) hc hP
    (off := iHD nD n 2 + 1) (by unfold iHD iIV; omega)
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hroot' : ∀ y ∈ ts, y ≠ T₀.root ∧ y ≠ T.root := fun y hy => by
    have := (hI.oT.ymem y).1 hy
    exact ⟨this, hroot ▸ this⟩
  obtain ⟨c₂, G₂, o₂, q₂⟩ := stListLoop_orunC (P := P) (W := W) (B := B) (n := n) (ra := 120)
    (rb := 121) ts (fun y => pointOps ιF ιG (toDD T) y
      (cap (T.par y) - w (T.par y)) (cap (M.rev (T.par y)) - w (M.rev (T.par y)))) hv hAV
    (fun _ c' => IFr B n c₁ c') (body := cvBodyS B nD n) (mb := 4) (hb := 40)
    (fun i hi c' G' hQ hc' hS' h120 _ hvi hAi => by
      obtain ⟨c₂, G₂, o, q120, fr⟩ := stCvBody_orunC hW hWa hB hP hL hK (T₀ := T₀) (T := T)
        hI.it (by simp only [iIT, iIV]; omega) hroot' hi hc' hS' h120
        (fun y hy => by
          rw [(hQ.2.2.2 _ (Or.inl (by have := hL.prim.f_lt y; unfold aTP; omega))).1,
            g₁.2.1]; exact htp y hy)
        (fun d => by
          have := (σ d).2
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aCP; omega))).2, g₁.2.2.1]; exact hcp d)
        (fun d => by
          have := (σ d).2
          rw [(hQ.2.2.2 _ (Or.inl (by unfold aWT; omega))).2, g₁.2.2.1]; exact hwt d) hvi hAi hH
      exact ⟨c₂, G₂, o, hQ.trans fr, q120, by rw [fr.1 121 (by omega), hQ.1 121 (by omega),
        p121, hI.l1]⟩)
    e₁.wb_right o₁.1.2.lcte (IFr.refl _ _ _) p120 (by rw [p121, hI.l1])
  have o := o₁.seq o₂
  simp only [List.nil_append] at o
  refine ⟨c₂, G₂, o.mono (by omega) (by omega), (g₁.to0 (by omega)).trans q₂.to0⟩


end

section
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {W B : ℕ}

theorem stLam_orunC (hW : B + 16 * (n + 1) ≤ W)
    (hB : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H) {e : D} (h104 : c.nreg 104 = σ e)
    {cap : D → ℤ} (hcp : ∀ d, c.rmem (aCP nD + σ d) = cap d) :
    ∃ c' G', ORunC P W H B n (lamS B nD) c Fo G c' [] G' 2 13 ∧
      c'.rreg 111 = cap e - pathSum Fo n (ιF (M.face (M.rev e))) +
        pathSum Fo n (ιF (M.face e)) ∧ IFr0 B n c c' ∧ c'.nreg 104 = c.nreg 104 := by
  have he := (σ e).2
  obtain ⟨c₁, k₁, e₁, hk₁, p130, p131, g₁⟩ : ∃ c' k', Exec P W (block [.constN 130 (iNT nD),
      .addN 130 130 104, .readIn 130 130, .constN 131 (iNH nD), .addN 131 131 104,
      .readIn 131 131]) c c' k' ∧ k' = 6 ∧ c'.nreg 130 = ιF (M.face e) ∧
      c'.nreg 131 = ιF (M.face (M.rev e)) ∧ GFr 130 132 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | (offs_simp'; omega)
      | (config_simp; rw [h104]; offs_simp'; omega))
    refine ⟨rfl, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h104, hK.nt]; rfl
    · config_simp; rw [h104, hK.nh]; rfl
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, -, -, -, s₂, -, m₂, f₂⟩ := regQuery_orunC (P := P) hW e₁.wb_right
    o₁.1.2.lcte hV hH p130 (hL.prim.f_lt _)
  have e₃ := Exec.copyR (P := P) o₂.1.2.wb 112 196
  have g₃ : GFr 112 113 c₂ { c₂ with rreg := upd c₂.rreg 112 (c₂.rreg 196) } := by gfr_tac
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  obtain ⟨c₄, G₄, o₄, -, -, -, s₄, -, m₄, f₄⟩ := regQuery_orunC (P := P) hW e₃.wb_right
    o₃.1.2.lcte hV hH (v := ιF (M.face (M.rev e)))
    (by rw [(g₃.1 131 (by omega)).1, f₂.1 131 (by omega), p131]) (hL.prim.f_lt _)
  have e₅ := Exec.copyR (P := P) o₄.1.2.wb 113 196
  set c₅ := { c₄ with rreg := upd c₄.rreg 113 (c₄.rreg 196) } with hc₅
  have g₅ : GFr 113 114 c₄ c₅ := by rw [hc₅]; gfr_tac
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) rfl
  have q104 : c₅.nreg 104 = c.nreg 104 := by
    rw [(g₅.1 104 (by omega)).1, f₄.1 104 (by omega), (g₃.1 104 (by omega)).1,
      f₂.1 104 (by omega), (g₁.1 104 (by omega)).1]
  have q112 : c₅.rreg 112 = pathSum Fo n (ιF (M.face e)) := by
    rw [(g₅.1 112 (by omega)).2, f₄.2.1 112 (by omega)]; config_simp; exact s₂
  have q113 : c₅.rreg 113 = pathSum Fo n (ιF (M.face (M.rev e))) := by
    rw [hc₅]; config_simp; exact s₄
  have mf₅ : MemFrame B n (DynTree.mem c) (DynTree.mem c₅) :=
    (g₁.memFrame.trans B n m₂).trans B n (g₃.memFrame.trans B n (m₄.trans B n g₅.memFrame))
  have hcp₅ : c₅.rmem (aCP nD + σ e) = cap e := by
    have := (mf₅ (aCP nD + σ e) (Or.inl (by unfold aCP; omega))).2
    simp only [DynTree.mem] at this
    rw [this]; exact hcp e
  obtain ⟨c₆, k₆, e₆, hk₆, t111, g₆⟩ : ∃ c' k', Exec P W (block [.constN 132 (aCP nD),
      .addN 132 132 104, .loadR 111 132, .subR 111 111 113, .addR 111 111 112]) c₅ c' k' ∧
      k' = 5 ∧ c'.rreg 111 = cap e - pathSum Fo n (ιF (M.face (M.rev e))) +
        pathSum Fo n (ιF (M.face e)) ∧ GFr 111 133 c₅ c' := by
    have hc₅w : WordsBounded W c₅ := e₅.wb_right
    exec_block
    all_goals try (first
      | (offs_simp'; omega)
      | (config_simp; rw [q104, h104]; offs_simp'; omega))
    refine ⟨rfl, ?_, by gfr_tac⟩
    config_simp; rw [q104, h104, hcp₅, q112, q113]
  have o₆ := ORunC.ofGFr (H := H) e₆ o₅.1.2.lcte g₆ (by omega) rfl
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq o₆))))
  simp only [List.nil_append] at o
  refine ⟨c₆, G₄, o.mono (by omega) (by omega), t111, ?_, ?_⟩
  · exact (g₁.to0 (by omega)).trans ((RegFr.to0 f₂ m₂).trans ((g₃.to0 (by omega)).trans
      ((RegFr.to0 f₄ m₄).trans ((g₅.to0 (by omega)).trans (g₆.to0 (by omega))))))
  · rw [(g₆.1 104 (by omega)).1, q104]


end

section
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {W B : ℕ}

theorem stRdBody_orunC (hW : B + 16 * (n + 1) ≤ W) (hB : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {d : D} {i : ℕ} (hd : (σ d : ℕ) = i)
    {c : Config} (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H)
    (h120 : c.nreg 120 = i) :
    ∃ c' G', ORunC P W H B n (rdBodyS B nD) c Fo G c' [] G' 2 10 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aAK nD + i → c'.rmem a = c.rmem a) ∧
      c'.rmem (aAK nD + i) = Fo.val2 (ιE d) := by
  have hσd := (σ d).2
  obtain ⟨c₁, k₁, e₁, hk₁, p130, g₁⟩ : ∃ c' k', Exec P W (block [.constN 130 (iNE nD),
      .addN 130 130 120, .readIn 130 130]) c c' k' ∧ k' = 3 ∧ c'.nreg 130 = ιE d ∧
      GFr 130 131 c c' := by
    exec_block
    all_goals try (first
      | exact hP _
      | (offs_simp'; omega)
      | (config_simp; rw [h120]; offs_simp'; omega))
    refine ⟨rfl, ?_, by gfr_tac⟩
    config_simp; rw [h120, ← hd, hK.ne]
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, v₂, m₂, f₂⟩ := regVal_orunC (P := P) hW e₁.wb_right o₁.1.2.lcte hV hH true
    p130 (hL.dual.e_lt d)
  have q120 : c₂.nreg 120 = i := by rw [f₂.1 120 (by omega), (g₁.1 120 (by omega)).1, h120]
  obtain ⟨c₃, k₃, e₃, hk₃, t120, tn, tr, tm, tnm, tout⟩ : ∃ c' k', Exec P W
      (block ([.constN 131 (aAK nD), .addN 131 131 120, .storeR 131 195] ++ incI)) c₂ c' k' ∧
      k' = 5 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, r ≠ 120 → r ≠ 131 → r ≠ 127 → c'.nreg r = c₂.nreg r) ∧ c'.rreg = c₂.rreg ∧
      c'.rmem = upd c₂.rmem (aAK nD + i) (Fo.val2 (ιE d)) ∧ c'.nmem = c₂.nmem ∧
      c'.output = c₂.output := by
    have hc₂ := o₂.1.2.wb
    unfold incI
    exec_block
    all_goals try (first
      | omega
      | (offs_simp'; omega)
      | (config_simp; rw [q120]; offs_simp'; omega))
    refine ⟨rfl, by config_simp; rw [q120], fun r h1 h2 h3 => ?_, rfl, ?_, rfl, rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
    · config_simp; rw [q120, v₂]; rfl
  have o₃ : ORunC P W H B n _ c₂ Fo G₂ c₃ [] G₂ 0 k₃ := ORunC.glue e₃ o₂.1.2.lcte
    (fun a ha _ => ⟨by rw [tnm], by rw [tm, upd_other _ _ _ (by unfold aAK; omega)]⟩)
    (tn 151 (by omega) (by omega) (by omega)) rfl
  have o := o₁.seq (o₂.seq o₃)
  simp only [List.nil_append] at o
  refine ⟨c₃, G₂, o.mono (by omega) (by omega), t120, fun r hr => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha hne => ?_, ?_⟩
  · rw [tn r (by omega) (by omega) (by omega), f₂.1 r (by omega), (g₁.1 r (by omega)).1]
  · rw [tr, f₂.2.1 r (by omega), (g₁.1 r (by omega)).2]
  · rw [tout, f₂.2.2, g₁.2.2.2]
  · have := (m₂ a ha).1
    simp only [DynTree.mem] at this
    rw [tnm, this, g₁.2.1]
  · have := (m₂ a ha).2
    simp only [DynTree.mem] at this
    rw [tm, upd_other _ _ _ hne, this, g₁.2.2.1]
  · rw [tm, upd_same]


theorem stRd_orunC (hW : B + 16 * (n + 1) ≤ W) (hB : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (rdS B nD) c Fo G c' [] G' (2 * nD) (12 * nD + 4) ∧
      (∀ d, c'.rmem (aAK nD + σ d) = Fo.val2 (ιE d)) ∧
      (∀ r, r < 120 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aAK nD ∨ aAK nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ : ∃ c' k', Exec P W (block [.constN 120 0,
      .constN 121 nD]) c c' k' ∧ k' = 2 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = nD ∧
      GFr 120 122 c c' := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hlen : (List.range nD).length = nD := List.length_range
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := stListLoop_orunC (P := P) (W := W) (B := B)
    (n := n) (ra := 120) (rb := 121) (List.range nD) (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial) (by rw [flatMap_nil']; exact hV)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c₁.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c₁.rreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aAK nD ∨ aAK nD + i ≤ a) →
        c'.rmem a = c₁.rmem a) ∧
      ∀ d : D, (σ d : ℕ) < i → c'.rmem (aAK nD + σ d) = Fo.val2 (ιE d))
    (body := rdBodyS B nD) (mb := 2) (hb := 10)
    (fun i hi c' G' hQ hc' hS' h120 h121 _ _ => by
      rw [flatMap_nil'] at hS' ⊢
      have hi' : i < nD := by rw [hlen] at hi; exact hi
      set d := σ.symm ⟨i, hi'⟩ with hd
      have hσd : (σ d : ℕ) = i := by rw [hd, Equiv.apply_symm_apply]
      obtain ⟨c₃, G₃, o, q120, qn, qr, qout, qnm, qrm, qv⟩ := stRdBody_orunC hW hB hP hL hK hσd
        hc' hS' hV hH h120
      refine ⟨c₃, G₃, o, ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr,
        fun r hr => by rw [qr r hr]; exact hQ.2.1 r hr, by rw [qout]; exact hQ.2.2.1,
        fun a ha => by rw [qnm a ha]; exact hQ.2.2.2.1 a ha, fun a ha ha' => ?_,
        fun d' hd' => ?_⟩, q120, by rw [qn 121 (by omega), h121]⟩
      · rw [qrm a ha (by omega)]; exact hQ.2.2.2.2.1 a ha (by omega)
      · rcases Nat.lt_or_ge (σ d' : ℕ) i with h' | h'
        · rw [qrm _ (Or.inl (by unfold aAK; omega)) (by omega)]
          exact hQ.2.2.2.2.2 d' h'
        · have : d' = d := σ.injective (Fin.ext (by omega))
          subst this
          rw [hσd, qv]; rfl)
    e₁.wb_right o₁.1.2.lcte ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hlen])
  rw [flatMap_nil', hlen] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by omega) (by omega), fun d => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha ha' => ?_⟩
  · exact q₆ d (by rw [hlen]; exact (σ d).2)
  · rw [q₁ r (by omega), q₂ r (by omega), (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [q₃, g₁.2.2.2]
  · rw [q₄ a ha, g₁.2.1]
  · rw [q₅ a ha (by rw [hlen]; exact ha'), g₁.2.2.1]


end

section
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {W B : ℕ}

theorem stWrBody_orunC (hW : B + 16 * (n + 1) ≤ W) (hB : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {d : D} {i : ℕ} (hd : (σ d : ℕ) = i)
    {c : Config} (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H)
    (h120 : c.nreg 120 = i) :
    ∃ c' G', ORunC P W H B n (wrBodyS B nD) c Fo G c' [] G' 5 40 ∧ c'.nreg 120 = i + 1 ∧
      (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aOT nD + i → c'.rmem a = c.rmem a) ∧
      c'.rmem (aOT nD + i) = wrVal Fo n ιF ιV ιE M (c.rreg 111) (c.rmem (aRS nD + i))
        (c.rmem (aAK nD + i)) d := by
  have hσd := (σ d).2
  obtain ⟨c₁, k₁, e₁, hk₁, p130, p131, p132, p133, g₁⟩ : ∃ c' k', Exec P W (block (wrRd nD)) c
      c' k' ∧ k' = 12 ∧ c'.nreg 130 = ιE d ∧ c'.nreg 131 = ιV (M.tail d) ∧
      c'.nreg 132 = ιF (M.face d) ∧ c'.nreg 133 = ιF (M.face (M.rev d)) ∧
      GFr 130 134 c c' := by
    unfold wrRd
    exec_block
    all_goals try (first
      | exact hP _
      | (offs_simp'; omega)
      | (config_simp; rw [h120]; offs_simp'; omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, by gfr_tac⟩
    · config_simp; rw [h120, ← hd, hK.ne]
    · config_simp; rw [h120, ← hd, hK.nf]; rfl
    · config_simp; rw [h120, ← hd, hK.nt]; rfl
    · config_simp; rw [h120, ← hd, hK.nh]; rfl
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  obtain ⟨c₂, G₂, o₂, v₂, m₂, f₂⟩ := regVal_orunC (P := P) hW e₁.wb_right o₁.1.2.lcte hV hH true
    p130 (hL.dual.e_lt d)
  have e₃ := Exec.copyR (P := P) o₂.1.2.wb 130 195
  set c₃ := { c₂ with rreg := upd c₂.rreg 130 (c₂.rreg 195) } with hc₃
  have g₃ : GFr 130 131 c₂ c₃ := by rw [hc₃]; gfr_tac
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) rfl
  obtain ⟨c₄, G₄, o₄, -, -, -, s₄, -, m₄, f₄⟩ := regQuery_orunC (P := P) hW e₃.wb_right
    o₃.1.2.lcte hV hH (v := ιF (M.face d)) (by rw [show c₃.nreg 132 = c₂.nreg 132 from rfl,
      f₂.1 132 (by omega), p132]) (hL.prim.f_lt _)
  have e₅ := Exec.copyR (P := P) o₄.1.2.wb 131 196
  set c₅ := { c₄ with rreg := upd c₄.rreg 131 (c₄.rreg 196) } with hc₅
  have g₅ : GFr 131 132 c₄ c₅ := by rw [hc₅]; gfr_tac
  have o₅ := ORunC.ofGFr (H := H) e₅ o₄.1.2.lcte g₅ (by omega) rfl
  obtain ⟨c₆, G₆, o₆, -, -, -, s₆, -, m₆, f₆⟩ := regQuery_orunC (P := P) hW e₅.wb_right
    o₅.1.2.lcte hV hH (v := ιF (M.face (M.rev d))) (by rw [show c₅.nreg 133 = c₄.nreg 133 from rfl,
      f₄.1 133 (by omega), show c₃.nreg 133 = c₂.nreg 133 from rfl, f₂.1 133 (by omega),
      p133]) (hL.prim.f_lt _)
  have e₇ := Exec.copyR (P := P) o₆.1.2.wb 132 196
  set c₇ := { c₆ with rreg := upd c₆.rreg 132 (c₆.rreg 196) } with hc₇
  have g₇ : GFr 132 133 c₆ c₇ := by rw [hc₇]; gfr_tac
  have o₇ := ORunC.ofGFr (H := H) e₇ o₆.1.2.lcte g₇ (by omega) rfl
  have n130 : c₇.nreg 130 = ιE d := by
    rw [show c₇.nreg 130 = c₆.nreg 130 from rfl, f₆.1 130 (by omega),
      show c₅.nreg 130 = c₄.nreg 130 from rfl, f₄.1 130 (by omega),
      show c₃.nreg 130 = c₂.nreg 130 from rfl, f₂.1 130 (by omega), p130]
  obtain ⟨c₈, G₈, o₈, a195, -, m₈, f₈⟩ := regParent_orunC (P := P) hW e₇.wb_right o₇.1.2.lcte hV hH
    n130 (hL.dual.e_lt d)
  -- the registers so far
  have hreg : ∀ r, r < 130 → c₈.nreg r = c.nreg r ∧ c₈.rreg r = c.rreg r := fun r hr =>
    ⟨by rw [f₈.1 r (by omega), show c₇.nreg r = c₆.nreg r from rfl, f₆.1 r (by omega),
        show c₅.nreg r = c₄.nreg r from rfl, f₄.1 r (by omega),
        show c₃.nreg r = c₂.nreg r from rfl, f₂.1 r (by omega), (g₁.1 r (by omega)).1],
      by rw [f₈.2.1 r (by omega), (g₇.1 r (by omega)).2, f₆.2.1 r (by omega),
        (g₅.1 r (by omega)).2, f₄.2.1 r (by omega), (g₃.1 r (by omega)).2, f₂.2.1 r (by omega),
        (g₁.1 r (by omega)).2]⟩
  have r130 : c₈.rreg 130 = Fo.val2 (ιE d) := by
    rw [f₈.2.1 130 (by omega), (g₇.1 130 (by omega)).2, f₆.2.1 130 (by omega),
      (g₅.1 130 (by omega)).2, f₄.2.1 130 (by omega), hc₃]
    config_simp; rw [v₂]; rfl
  have r131 : c₈.rreg 131 = pathSum Fo n (ιF (M.face d)) := by
    rw [f₈.2.1 131 (by omega), (g₇.1 131 (by omega)).2, f₆.2.1 131 (by omega), hc₅]
    config_simp; exact s₄
  have r132 : c₈.rreg 132 = pathSum Fo n (ιF (M.face (M.rev d))) := by
    rw [f₈.2.1 132 (by omega), hc₇]; config_simp; exact s₆
  have n131 : c₈.nreg 131 = ιV (M.tail d) := by
    rw [f₈.1 131 (by omega), show c₇.nreg 131 = c₆.nreg 131 from rfl, f₆.1 131 (by omega),
      show c₅.nreg 131 = c₄.nreg 131 from rfl, f₄.1 131 (by omega),
      show c₃.nreg 131 = c₂.nreg 131 from rfl, f₂.1 131 (by omega), p131]
  have mf₈ : MemFrame B n (DynTree.mem c) (DynTree.mem c₈) :=
    (g₁.memFrame.trans B n m₂).trans B n (g₃.memFrame.trans B n (m₄.trans B n
      (g₅.memFrame.trans B n (m₆.trans B n (g₇.memFrame.trans B n m₈)))))
  have hmem : ∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c₈.nmem a = c.nmem a ∧
      c₈.rmem a = c.rmem a := fun a ha => by
    have := mf₈ a ha; simp only [DynTree.mem] at this; exact this
  have hc₈ := o₈.1.2.wb
  have q120 : c₈.nreg 120 = i := by rw [(hreg 120 (by omega)).1, h120]
  -- the change of the second value, times `λ`
  obtain ⟨c₉, k₉, e₉, hk₉, t133, t136, tn9, tr9, tm9, tnm9, tout9⟩ : ∃ c' k', Exec P W
      (block [.constN 134 (aAK nD), .addN 134 134 120, .loadR 133 134, .subR 133 130 133,
        .mulR 133 133 111, .constR 136 0]) c₈ c' k' ∧ k' = 6 ∧
      c'.rreg 133 = (Fo.val2 (ιE d) - c.rmem (aAK nD + i)) * c.rreg 111 ∧
      c'.rreg 136 = 0 ∧ (∀ r, r ≠ 134 → c'.nreg r = c₈.nreg r) ∧
      (∀ r, r ≠ 133 → r ≠ 136 → c'.rreg r = c₈.rreg r) ∧ c'.rmem = c₈.rmem ∧
      c'.nmem = c₈.nmem ∧ c'.output = c₈.output := by
    exec_block
    all_goals try (first
      | (offs_simp'; omega)
      | (config_simp; rw [q120]; offs_simp'; omega))
    refine ⟨rfl, ?_, ?_, fun r h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · config_simp
      rw [q120, r130, (hmem _ (Or.inl (by unfold aAK; omega))).2, (hreg 111 (by omega)).2]
    · config_simp; push_cast; rfl
    · config_simp; simp only [upd_other _ _ _ h1]
    · config_simp; simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]
  have o₉ : ORunC P W H B n _ c₈ Fo G₈ c₉ [] G₈ 0 k₉ := ORunC.glue e₉ o₈.1.2.lcte
    (fun a _ _ => by rw [tnm9, tm9]; exact ⟨rfl, rfl⟩) (tn9 151 (by omega)) rfl
  -- the sign
  have hsg : ∃ c₁₀ k₁₀, Exec P W (.ifLtN 195 131 (.instr (.subR 133 136 133))
      (.ifLtN 131 195 (.instr (.subR 133 136 133)) .skip)) c₉ c₁₀ k₁₀ ∧ k₁₀ ≤ 4 ∧
      c₁₀.rreg 133 = (if Fo.par (ιE d) = ιV (M.tail d) then 1 else -1) *
        ((Fo.val2 (ιE d) - c.rmem (aAK nD + i)) * c.rreg 111) ∧
      c₁₀.nreg = c₉.nreg ∧ (∀ r, r ≠ 133 → c₁₀.rreg r = c₉.rreg r) ∧ c₁₀.rmem = c₉.rmem ∧
      c₁₀.nmem = c₉.nmem ∧ c₁₀.output = c₉.output := by
    have h195 : c₉.nreg 195 = Fo.par (ιE d) := by rw [tn9 195 (by omega), a195]; rfl
    have h131 : c₉.nreg 131 = ιV (M.tail d) := by rw [tn9 131 (by omega), n131]
    by_cases hpar : Fo.par (ιE d) = ιV (M.tail d)
    · refine ⟨c₉, 2 + 2, .ifLtN_false (by omega) (.ifLtN_false (by omega)
        (.skip e₉.wb_right)), by omega, ?_, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [ite_eq_left hpar, one_mul, t133]
    · have hne : c₉.nreg 195 ≠ c₉.nreg 131 := by rw [h195, h131]; exact hpar
      have hv : (0 : ℝ) - c₉.rreg 133 = (if Fo.par (ιE d) = ιV (M.tail d) then 1 else -1) *
          ((Fo.val2 (ιE d) - c.rmem (aAK nD + i)) * c.rreg 111) := by
        rw [ite_eq_right hpar, t133]; ring
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · refine ⟨{ c₉ with rreg := upd c₉.rreg 133 (c₉.rreg 136 - c₉.rreg 133) }, _,
          .ifLtN_true hl (Exec.subR e₉.wb_right 133 136 133), by omega, ?_, rfl,
          fun r hr => by config_simp; simp only [upd_other _ _ _ hr], rfl, rfl, rfl⟩
        config_simp; rw [t136, hv]
      · refine ⟨{ c₉ with rreg := upd c₉.rreg 133 (c₉.rreg 136 - c₉.rreg 133) }, _,
          .ifLtN_false (by omega) (.ifLtN_true hl (Exec.subR e₉.wb_right 133 136 133)),
          by omega, ?_, rfl, fun r hr => by config_simp; simp only [upd_other _ _ _ hr], rfl,
          rfl, rfl⟩
        config_simp; rw [t136, hv]
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, u133, un, ur, urm, unm, uout⟩ := hsg
  have o₁₀ : ORunC P W H B n _ c₉ Fo G₈ c₁₀ [] G₈ 0 k₁₀ := ORunC.glue e₁₀ o₉.1.2.lcte
    (fun a _ _ => by rw [unm, urm]; exact ⟨rfl, rfl⟩) (by rw [un]) rfl
  -- the value and the store
  have v132 : c₁₀.rreg 132 = pathSum Fo n (ιF (M.face (M.rev d))) := by
    rw [ur 132 (by omega), tr9 132 (by omega) (by omega), r132]
  have v131 : c₁₀.rreg 131 = pathSum Fo n (ιF (M.face d)) := by
    rw [ur 131 (by omega), tr9 131 (by omega) (by omega), r131]
  have w120 : c₁₀.nreg 120 = i := by rw [un, tn9 120 (by omega), q120]
  have hc₁₀ := e₁₀.wb_right
  have hrs : c₁₀.rmem (aRS nD + i) = c.rmem (aRS nD + i) := by
    rw [urm, tm9, (hmem _ (Or.inl (by unfold aRS; omega))).2]
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, x120, xn, xr, xm, xnm, xout⟩ : ∃ c' k', Exec P W
      (block ([.addR 133 133 132, .subR 133 133 131, .constN 134 (aRS nD),
        .addN 134 134 120, .loadR 134 134, .mulR 133 133 134, .constN 135 (aOT nD),
        .addN 135 135 120, .storeR 135 133] ++ incI)) c₁₀ c' k' ∧ k' = 11 ∧
      c'.nreg 120 = i + 1 ∧ (∀ r, r ≠ 120 → r ≠ 134 → r ≠ 135 → r ≠ 127 →
        c'.nreg r = c₁₀.nreg r) ∧ (∀ r, r < 130 → c'.rreg r = c₁₀.rreg r) ∧
      c'.rmem = upd c₁₀.rmem (aOT nD + i) (wrVal Fo n ιF ιV ιE M (c.rreg 111)
        (c.rmem (aRS nD + i)) (c.rmem (aAK nD + i)) d) ∧ c'.nmem = c₁₀.nmem ∧
      c'.output = c₁₀.output := by
    unfold incI
    exec_block
    all_goals try (first
      | omega
      | (offs_simp'; omega)
      | (config_simp; rw [w120]; offs_simp'; omega))
    refine ⟨rfl, by config_simp; rw [w120], fun r h1 h2 h3 h4 => ?_, fun r hr => ?_, ?_, rfl,
      rfl⟩
    · config_simp
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
        upd_other _ _ _ h4]
    · config_simp
      simp only [upd_other _ _ _ (show r ≠ 133 by omega), upd_other _ _ _ (show r ≠ 134 by omega)]
    · config_simp
      rw [w120, hrs, u133, v132, v131]
      unfold wrVal; ring_nf
  have o₁₁ : ORunC P W H B n _ c₁₀ Fo G₈ c₁₁ [] G₈ 0 k₁₁ := ORunC.glue e₁₁ o₁₀.1.2.lcte
    (fun a ha _ => ⟨by rw [xnm], by rw [xm, upd_other _ _ _ (by unfold aOT; omega)]⟩)
    (xn 151 (by omega) (by omega) (by omega) (by omega)) rfl
  have o := o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq (o₉.seq
    (o₁₀.seq o₁₁)))))))))
  simp only [List.nil_append] at o
  refine ⟨c₁₁, G₈, o.mono (by omega) (by omega), x120, fun r hr => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha hne => ?_, ?_⟩
  · rw [xn r (by omega) (by omega) (by omega) (by omega), un, tn9 r (by omega)]
    rcases hr with hr | rfl
    · exact (hreg r (by omega)).1
    · exact (hreg 121 (by omega)).1
  · rw [xr r (by omega), ur r (by omega), tr9 r (by omega) (by omega)]
    exact (hreg r (by omega)).2
  · rw [xout, uout, tout9, f₈.2.2, g₇.2.2.2, f₆.2.2, g₅.2.2.2, f₄.2.2, g₃.2.2.2, f₂.2.2,
      g₁.2.2.2]
  · rw [xnm, unm, tnm9]; exact (hmem a ha).1
  · rw [xm, upd_other _ _ _ hne, urm, tm9]; exact (hmem a ha).2
  · rw [xm, upd_same]


theorem stWr_orunC (hW : B + 16 * (n + 1) ≤ W) (hB : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P) {c : Config} (hc : WordsBounded W c)
    {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {H : ℕ} {Vb : ℝ} (hV : VBnd Vb n Fo) (hH : 2 * Vb ≤ H) :
    ∃ c' G', ORunC P W H B n (wrS B nD) c Fo G c' [] G' (5 * nD) (42 * nD + 4) ∧
      (∀ d, c'.rmem (aOT nD + σ d) = wrVal Fo n ιF ιV ιE M (c.rreg 111)
        (c.rmem (aRS nD + σ d)) (c.rmem (aAK nD + σ d)) d) ∧
      (∀ r, r < 110 → c'.nreg r = c.nreg r ∧ c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aOT nD ∨ aOT nD + nD ≤ a) →
        c'.rmem a = c.rmem a) := by
  obtain ⟨c₁, k₁, e₁, hk₁, p120, p121, g₁⟩ : ∃ c' k', Exec P W (block [.constN 120 0,
      .constN 121 nD]) c c' k' ∧ k' = 2 ∧ c'.nreg 120 = 0 ∧ c'.nreg 121 = nD ∧
      GFr 120 122 c c' := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by gfr_tac⟩
  have o₁ := ORunC.ofGFr (H := H) e₁ hS g₁ (by omega) rfl
  have hlen : (List.range nD).length = nD := List.length_range
  obtain ⟨c₂, G₂, o₂, q₁, q₂, q₃, q₄, q₅, q₆⟩ := stListLoop_orunC (P := P) (W := W) (B := B)
    (n := n) (ra := 120) (rb := 121) (List.range nD) (fun _ => ([] : List EOp)) (F₀ := Fo)
    (by rw [flatMap_nil']; trivial) (by rw [flatMap_nil']; exact hV)
    (fun i c' => (∀ r, (r < 120 ∨ r = 121) → c'.nreg r = c₁.nreg r) ∧
      (∀ r, r < 120 → c'.rreg r = c₁.rreg r) ∧ c'.output = c₁.output ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → (a < aOT nD ∨ aOT nD + i ≤ a) →
        c'.rmem a = c₁.rmem a) ∧
      ∀ d : D, (σ d : ℕ) < i → c'.rmem (aOT nD + σ d) = wrVal Fo n ιF ιV ιE M (c₁.rreg 111)
        (c₁.rmem (aRS nD + σ d)) (c₁.rmem (aAK nD + σ d)) d)
    (body := wrBodyS B nD) (mb := 5) (hb := 40)
    (fun i hi c' G' hQ hc' hS' h120 h121 _ _ => by
      rw [flatMap_nil'] at hS' ⊢
      have hi' : i < nD := by rw [hlen] at hi; exact hi
      set d := σ.symm ⟨i, hi'⟩ with hd
      have hσd : (σ d : ℕ) = i := by rw [hd, Equiv.apply_symm_apply]
      obtain ⟨c₃, G₃, o, q120, qn, qr, qout, qnm, qrm, qv⟩ := stWrBody_orunC hW hB hP hL hK hσd
        hc' hS' hV hH h120
      refine ⟨c₃, G₃, o, ⟨fun r hr => by rw [qn r hr]; exact hQ.1 r hr,
        fun r hr => by rw [qr r hr]; exact hQ.2.1 r hr, by rw [qout]; exact hQ.2.2.1,
        fun a ha => by rw [qnm a ha]; exact hQ.2.2.2.1 a ha, fun a ha ha' => ?_,
        fun d' hd' => ?_⟩, q120, by rw [qn 121 (by omega), h121]⟩
      · rw [qrm a ha (by omega)]; exact hQ.2.2.2.2.1 a ha (by omega)
      · rcases Nat.lt_or_ge (σ d' : ℕ) i with h' | h'
        · rw [qrm _ (Or.inl (by unfold aOT; omega)) (by omega)]
          exact hQ.2.2.2.2.2 d' h'
        · have : d' = d := σ.injective (Fin.ext (by omega))
          subst this
          rw [hσd, qv, hQ.2.1 111 (by omega), ← hσd,
            hQ.2.2.2.2.1 _ (Or.inl (by unfold aRS; omega)) (Or.inl (by unfold aRS aOT; omega)),
            hQ.2.2.2.2.1 _ (Or.inl (by unfold aAK; omega)) (Or.inl (by unfold aAK aOT; omega))]
          rfl)
    e₁.wb_right o₁.1.2.lcte ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ p120 (by rw [p121, hlen])
  rw [flatMap_nil', hlen] at o₂
  have o := o₁.seq o₂
  refine ⟨c₂, G₂, o.mono (by omega) (by omega), fun d => ?_, fun r hr => ?_, ?_,
    fun a ha => ?_, fun a ha ha' => ?_⟩
  · rw [q₆ d (by rw [hlen]; exact (σ d).2), (g₁.1 111 (by omega)).2, g₁.2.2.1]
  · rw [q₁ r (by omega), q₂ r (by omega), (g₁.1 r (by omega)).1, (g₁.1 r (by omega)).2]
    exact ⟨rfl, rfl⟩
  · rw [q₃, g₁.2.2.2]
  · rw [q₄ a ha, g₁.2.1]
  · rw [q₅ a ha (by rw [hlen]; exact ha'), g₁.2.2.1]


end

end STFlow

end PlanarFlow
