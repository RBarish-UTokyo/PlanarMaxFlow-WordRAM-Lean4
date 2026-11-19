module

public import PlanarFlow.Monge.FRCmp

/-!
# FR-Dijkstra: bounded comparisons of the activation

`PlanarFlow.Monge.FR.act` and its parts are good (`PlanarFlow.Monge.FR.FG`): every stored real
is an item `d σ + F ρ σ` of a triplet written by `tPut` (`PlanarFlow.Monge.FR.tPut_good`), with
`σ` the activated source `a` or the owner of a triplet, an active source; all the other parts
pass the abstract interpretation. The proofs follow the realization lemmas of
`PlanarFlow/Monge/FRActivate.lean` (their runs are the runs, by `WordRAM.Machine.Exec.det`), up to
the writes of the triplets. The bounds `hEB`, `heA` of the values of the active sources and of
`a` come from the run of Dijkstra's algorithm (`PlanarFlow.Monge.FR.MRun.dist_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap CmpAbs

variable {P : Prm} {I : Input} {L : ℕ}

section walk

variable {B Q T k a : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X : ℕ → Prop} {Act : ℕ → Prop}

local notation "Bt'" => Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a

/-- `tPut` inside an activation is good. -/
theorem tPutA_good (hL : Lay P) (hXB : XB P L) {c₀ : Config} {σ j1 j2 : ℕ} (c : Config)
    (h : AS P B Q T k a e c₀ c) (h200 : c.nreg 200 = σ)
    (hσ : σ < hbNc P.b (2 ^ T) k) (h201 : c.nreg 201 = j1) (h202 : c.nreg 202 = j2)
    (hj : j1 < j2) (hj2 : j2 ≤ hbNr P.b (2 ^ T) k) (heB : |e σ| ≤ (P.N * L : ℝ)) :
    FG I P L tPut c :=
  tPut_good hL hXB c h.wb h.env h.hB h.qr (h.eok σ hσ) heB h200 hσ h201 h202 hj hj2

/-- **One step of the left walk is good.** -/
theorem lwBody_good (hL : Lay P) (hXB : XB P L) {β hy : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (c : Config) (hI : ILW P B Q T k a e own X β hy c₀ c₁ c) (hgo : c.nreg 117 < c.nreg 268) :
    FG I P L lwBody c := by
  have hAS := hI.as
  have g117 := hAS.env.g.r117
  have g110 := hAS.env.g.r110
  have h268 : c.nreg 268 = 1 := by have := hI.fl; rw [g117] at hgo; omega
  have hΦ : wΦ Q T c = LD T * nst Q (2 ^ T) c.nmem + LF T := by unfold wΦ; rw [iteT h268]
  obtain ⟨hcur, hpc, h264, hcβ, hbe⟩ := hI.go h268
  have hM := hI.mem
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  generalize hcv : c.nreg 263 = cur at hcur hpc h264 hcβ hbe
  rw [h264] at hM
  have hst := hM.st cur hcur hpc
  generalize hev : tEnd Q c.nmem cur = ee at hM hbe h264 hst
  generalize huv : tOwn Q c.nmem cur = u
  have hown : ∀ ρ, cur ≤ ρ → ρ ≤ ee → own ρ = u := fun ρ h1 h2 => by
    rw [← huv]; exact hM.own cur hcur hpc ρ h1 (by rw [hev]; exact h2)
  have hu : u < hbNc P.b (2 ^ T) k := by
    rw [← hown cur le_rfl hst.1]; exact hAH.ok.lt _ (hAH.ok.act cur (by omega))
  have ha := hAH.ha
  have hBc : ∀ ρ, cur ≤ ρ → ρ ≤ ee →
      (Bt' ρ ↔ EE P T k e ρ a < EE P T k e ρ u) := fun ρ h1 h2 => by
    unfold Bt; rw [hown ρ h1 h2]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hda := hI.da
  rw [h264] at hda
  have hhb := hI.hb
  rw [h264] at hhb
  have hle := hI.le
  rw [h264] at hle
  unfold lwBody
  -- the owner and the last row of the current start
  refine good_seq_use (ldCurA hL (I := I) c hAS hcv hcur) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f275, f277, hF₂, hN₂, hM₂⟩
  rw [huv] at f275; rw [hev] at f277
  refine good_seq_use (copyA hL (I := I) c₂ hAS₂ 274 263 fr_ne) (fg_abs0 (by decide)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f274, hF₃, hN₃, hM₃⟩
  rw [hF₂.n 263 fr_ne, hcv] at f274
  refine good_seq_use (btA hL (I := I) c₃ hAS₃ f274 hcur (by rw [hF₃.n 275 fr_ne]; exact f275) hu ha) (fg_abs0 (by decide)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f273, hF₄, hN₄, hM₄⟩
  have N4 : c₄.nmem = c.nmem := by rw [hN₄, hN₃, hN₂]
  have R4 : c₄.rmem = c.rmem := by rw [hM₄, hM₃, hM₂]
  have F4 : Fr LWm AcR c c₄ := ((hF₂.trans hF₃ fr_incl fr_incl (fun _ h => False.elim h)
    (fun _ h => False.elim h)).trans hF₄ (fun r h => h) fr_incl (fun _ h => False.elim h)
    fr_incl)
  have k4 : ∀ r, ¬ LWm r → c₄.nreg r = c.nreg r := F4.n
  have k4c : c₄.nreg 263 = cur := by rw [hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, hF₂.n 263 fr_ne, hcv]
  have k4u : c₄.nreg 275 = u := by rw [hF₄.n 275 fr_ne, hF₃.n 275 fr_ne, f275]
  have k4e : c₄.nreg 277 = ee := by rw [hF₄.n 277 fr_ne, hF₃.n 277 fr_ne, f277]
  by_cases hb : EE P T k e cur a < EE P T k e cur u
  · -- delete the current triplet (no write of a real)
    rw [iteT hb] at f273
    refine good_ifLtN_true (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    exact fg_abs0 (by decide)
  · -- cut the current triplet
    rw [iteF hb] at f273
    refine good_ifLtN_false (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hnb : ¬ Bt' cur := fun h => hb ((hBc cur le_rfl hst.1).1 h)
    have hce : cur < ee := by
      rcases Nat.eq_or_lt_of_le hst.1 with h | h
      · exact absurd (h ▸ hbe) hnb
      · exact h
    have hQ := hAS.hQ
    unfold lwCut
    refine good_seq_ex (fg_abs0 (by decide)) ?_
    exec_block
    · config_simp; rw [k4c, k4 110 fr_ne, g110]; omega
    generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
    have hw₅ : WordsBounded P.W c₅ := hc₅ ▸ ‹_›
    have F5 : Fr (fun r => r = 269 ∨ r = 270 ∨ r = 276) (fun _ => False) c₄ c₅ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₅]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₅], by rw [← hc₅]⟩
    have hAS₅ := hAS₄.next hL hw₅ F5 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₅]) (fun x _ => by rw [← hc₅])
    have N5 : c₅.nmem = c.nmem := by rw [← hc₅]; exact N4
    have R5 : c₅.rmem = c.rmem := by rw [← hc₅]; exact R4
    have f269 : c₅.nreg 269 = cur := by rw [← hc₅]; config_simp; rw [k4c]
    have f270 : c₅.nreg 270 = ee := by rw [← hc₅]; config_simp; rw [k4e]
    have f276 : c₅.nreg 276 = cur + 1 := by
      rw [← hc₅]; config_simp; rw [k4c, k4 110 fr_ne, g110]
    have f275 : c₅.nreg 275 = u := by rw [F5.n 275 fr_ne, k4u]
    have f263 : c₅.nreg 263 = cur := by rw [F5.n 263 fr_ne, k4c]
    refine good_seq_use (bsLoop_exec (I := I) (lo₀ := cur) (hi₀ := ee) hL true c₅ hAS₅ hu ha f275
      (by omega) (by rw [f269, f270]; exact hce) (by rw [f276, f269])
      (by rw [f269]; simpa using hb) (by rw [f270]; simpa using (hBc ee hst.1 le_rfl).1 hbe)
      (by rw [f269]) (by rw [f270])) (fg_abs0 (by decide)) ?_
    intro c₆ k₆ hk₆ hw₆ ⟨hI₆, hadj⟩
    have hAS₆ := hI₆.as
    generalize hlov : c₆.nreg 269 = lo at hadj
    generalize hhiv : c₆.nreg 270 = hi at hadj
    have hlo1 := hI₆.lob; have hhi1 := hI₆.hib; have hlq := hI₆.lo; have hhq := hI₆.hi
    rw [hlov] at hlo1 hlq; rw [hhiv] at hhi1 hhq
    simp only [iff_true] at hlq hhq
    have hBhi : Bt' hi := (hBc hi (by omega) hhi1).2 hhq
    have hnBlo : ¬ Bt' lo := fun h => hlq ((hBc lo hlo1 (by omega)).1 h)
    have N6 : c₆.nmem = c.nmem := by rw [hI₆.nm, N5]
    have R6 : c₆.rmem = c.rmem := by rw [hI₆.rm, R5]
    have k6 : ∀ r, ¬ ((130 ≤ r ∧ r < 134) ∨ (269 ≤ r ∧ r < 275) ∨ r = 276) →
        c₆.nreg r = c₅.nreg r := hI₆.keep
    have F6 : Fr LWl AcR c c₆ := ⟨fun r hr => by
      rw [k6 r (by simp only [LWl, TPn] at hr; omega), F5.n r (by simp only [LWl] at hr; omega),
        F4.n r (by simp only [LWl, LWm, TPn] at hr ⊢; omega)],
      fun r hr => by
        rw [hI₆.keepR r (by simp only [AcR, TPr] at hr; omega), F5.r r (fun h => h),
          F4.r r hr], by rw [hI₆.out, F5.o, F4.o]⟩
    refine good_seq_use (copyA hL (I := I) c₆ hAS₆ 230 263 fr_ne) (fg_abs0 (by decide)) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f230, hF₇, hN₇, hM₇⟩
    rw [k6 263 (by omega), f263] at f230
    refine good_seq_use (tDelA hL (I := I) c₇ hAS₇ f230 hcur (by rw [hN₇, hM₇, N6, R6]; exact hM)
      (by rw [hN₇, N6]; exact hpc)) (fg_abs0 (by decide)) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hM₈, hn₈, hF₈⟩
    rw [hN₇, N6, hev] at hM₈
    refine good_seq_ex (fg_abs0 (by decide)) ?_
    exec_block
    generalize hc₉ : (Config.mk _ _ _ _ _ _ : Config) = c₉
    have hw₉ : WordsBounded P.W c₉ := hc₉ ▸ ‹_›
    have F9 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c₈ c₉ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₉]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₉], by rw [← hc₉]⟩
    have hAS₉ := hAS₈.next hL hw₉ F9 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₉]) (fun x _ => by rw [← hc₉])
    have k8 : ∀ r, ¬ (TPn r ∨ r = 230) → c₈.nreg r = c₆.nreg r := fun r hr => by
      rw [hF₈.n r (fun h => hr (Or.inl h)), hF₇.n r (fun h => hr (Or.inr h))]
    have hActu : Act u := by rw [← hown cur le_rfl hst.1]; exact hAH.ok.act cur (by omega)
    refine Good.seq (tPutA_good hL hXB (σ := u) (j1 := cur) (j2 := hi) c₉ hAS₉
      (by rw [← hc₉]; config_simp; rw [k8 275 fr_ne, k6 275 (by omega), f275]) hu
      (by rw [← hc₉]; config_simp; rw [k8 263 fr_ne, k6 263 (by omega), f263])
      (by rw [← hc₉]; config_simp; rw [k8 270 fr_ne, hhiv]) (by omega) (by omega)
      (hEB u hActu)) fun _ _ _ => fg_abs0 (by decide)

/-- **The left walk is good.** -/
theorem lwLoop_good (hL : Lay P) (hXB : XB P L) {β hy : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (hI : ILW P B Q T k a e own X β hy c₀ c₁ c₁) :
    FG I P L (.whileLtN 117 268 lwBody) c₁ :=
  Good.whileLtN (ILW P B Q T k a e own X β hy c₀ c₁) (fun c hI' hlt =>
    ⟨lwBody_good hL hXB hAH hEB c hI' hlt, fun c₂ k₂ e₂ => by
      obtain ⟨c', k', e', hI'', -⟩ := lwBody_exec (I := I) hL hAH hOL c hI' hlt
      obtain ⟨rfl, rfl⟩ := Exec.det e' e₂
      exact hI''⟩) hI

/-- **One step of the right walk is good.** -/
theorem rwBody_good (hL : Lay P) (hXB : XB P L) {β hx : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (c : Config) (hI : IRW P B Q T k a e own X β hx c₀ c₁ c) (hgo : c.nreg 117 < c.nreg 268) :
    FG I P L rwBody c := by
  have hAS := hI.as
  have g117 := hAS.env.g.r117
  have g110 := hAS.env.g.r110
  have hQ := hAS.hQ
  have h268 : c.nreg 268 = 1 := by have := hI.fl; rw [g117] at hgo; omega
  have hΦ : wΦ Q T c = LD T * nst Q (2 ^ T) c.nmem + LF T := by unfold wΦ; rw [iteT h268]
  obtain ⟨hcur, hpc, h265, hcβ, hBcur⟩ := hI.go h268
  have hM := hI.mem
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  generalize hcv : c.nreg 263 = cur at hcur hpc h265 hcβ hBcur
  rw [h265] at hM
  have hst := hM.st cur hcur hpc
  generalize hev : tEnd Q c.nmem cur = ee at hst
  generalize huv : tOwn Q c.nmem cur = u
  have hown : ∀ ρ, cur ≤ ρ → ρ ≤ ee → own ρ = u := fun ρ h1 h2 => by
    rw [← huv]; exact hM.own cur hcur hpc ρ h1 (by rw [hev]; exact h2)
  have hu : u < hbNc P.b (2 ^ T) k := by
    rw [← hown cur le_rfl hst.1]; exact hAH.ok.lt _ (hAH.ok.act cur (by omega))
  have ha := hAH.ha
  have hBc : ∀ ρ, cur ≤ ρ → ρ ≤ ee →
      (Bt' ρ ↔ EE P T k e ρ a < EE P T k e ρ u) := fun ρ h1 h2 => by
    unfold Bt; rw [hown ρ h1 h2]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hda := hI.da
  rw [h265] at hda
  have hhb := hI.hb
  rw [h265] at hhb
  have hle := hI.le
  rw [h265] at hle
  have hrx := hI.rx
  unfold rwBody
  refine good_seq_use (ldCurA hL (I := I) c hAS hcv hcur) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f275, f277, hF₂, hN₂, hM₂⟩
  rw [huv] at f275; rw [hev] at f277
  refine good_seq_use (copyA hL (I := I) c₂ hAS₂ 274 277 fr_ne) (fg_abs0 (by decide)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f274, hF₃, hN₃, hM₃⟩
  rw [f277] at f274
  refine good_seq_use (btA hL (I := I) c₃ hAS₃ f274 (by omega) (by rw [hF₃.n 275 fr_ne]; exact f275)
    hu ha) (fg_abs0 (by decide)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f273, hF₄, hN₄, hM₄⟩
  have N4 : c₄.nmem = c.nmem := by rw [hN₄, hN₃, hN₂]
  have R4 : c₄.rmem = c.rmem := by rw [hM₄, hM₃, hM₂]
  have F4 : Fr LWc AcR c c₄ := ((hF₂.trans hF₃ fr_incl fr_incl (fun _ h => False.elim h)
    (fun _ h => False.elim h)).trans hF₄ (fun r h => h) fr_incl (fun _ h => False.elim h)
    fr_incl)
  have k4 : ∀ r, ¬ LWc r → c₄.nreg r = c.nreg r := F4.n
  have k4c : c₄.nreg 263 = cur := by rw [hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, hF₂.n 263 fr_ne, hcv]
  have k4u : c₄.nreg 275 = u := by rw [hF₄.n 275 fr_ne, hF₃.n 275 fr_ne, f275]
  have k4e : c₄.nreg 277 = ee := by rw [hF₄.n 277 fr_ne, hF₃.n 277 fr_ne, f277]
  have k4x : c₄.nreg 264 = hx := by
    rw [hF₄.n 264 fr_ne, hF₃.n 264 fr_ne, hF₂.n 264 fr_ne, hrx]
  by_cases hb : EE P T k e ee a < EE P T k e ee u
  · -- delete the current triplet (no write of a real)
    rw [iteT hb] at f273
    refine good_ifLtN_true (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    exact fg_abs0 (by decide)
  · -- cut the current triplet
    rw [iteF hb] at f273
    refine good_ifLtN_false (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hnb : ¬ Bt' ee := fun h => hb ((hBc ee hst.1 le_rfl).1 h)
    have hce : cur < ee := by
      rcases Nat.eq_or_lt_of_le hst.1 with h | h
      · exact absurd (h ▸ hBcur) hnb
      · exact h
    unfold rwCut
    refine good_seq_ex (fg_abs0 (by decide)) ?_
    exec_block
    · config_simp; rw [k4c, k4 110 fr_ne, g110]; omega
    generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
    have hw₅ : WordsBounded P.W c₅ := hc₅ ▸ ‹_›
    have F5 : Fr (fun r => r = 269 ∨ r = 270 ∨ r = 276) (fun _ => False) c₄ c₅ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₅]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₅], by rw [← hc₅]⟩
    have hAS₅ := hAS₄.next hL hw₅ F5 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₅]) (fun x _ => by rw [← hc₅])
    have N5 : c₅.nmem = c.nmem := by rw [← hc₅]; exact N4
    have R5 : c₅.rmem = c.rmem := by rw [← hc₅]; exact R4
    have f269 : c₅.nreg 269 = cur := by rw [← hc₅]; config_simp; rw [k4c]
    have f270 : c₅.nreg 270 = ee := by rw [← hc₅]; config_simp; rw [k4e]
    have f276 : c₅.nreg 276 = cur + 1 := by
      rw [← hc₅]; config_simp; rw [k4c, k4 110 fr_ne, g110]
    have f275 : c₅.nreg 275 = u := by rw [F5.n 275 fr_ne, k4u]
    have f263 : c₅.nreg 263 = cur := by rw [F5.n 263 fr_ne, k4c]
    refine good_seq_use (bsLoop_exec (I := I) (lo₀ := cur) (hi₀ := ee) hL false c₅ hAS₅ hu ha f275
      (by omega) (by rw [f269, f270]; exact hce) (by rw [f276, f269])
      (by rw [f269]; simpa using (hBc cur le_rfl hst.1).1 hBcur) (by rw [f270]; simpa using hb)
      (by rw [f269]) (by rw [f270])) (fg_abs0 (by decide)) ?_
    intro c₆ k₆ hk₆ hw₆ ⟨hI₆, hadj⟩
    have hAS₆ := hI₆.as
    generalize hlov : c₆.nreg 269 = lo at hadj
    generalize hhiv : c₆.nreg 270 = hi at hadj
    have hlo1 := hI₆.lob; have hhi1 := hI₆.hib; have hlq := hI₆.lo; have hhq := hI₆.hi
    rw [hlov] at hlo1 hlq; rw [hhiv] at hhi1 hhq
    simp only [Bool.false_eq_true, iff_false, not_not] at hlq hhq
    have hBlo : Bt' lo := (hBc lo hlo1 (by omega)).2 hlq
    have hnBhi : ¬ Bt' hi := fun h => hhq ((hBc hi (by omega) hhi1).1 h)
    have N6 : c₆.nmem = c.nmem := by rw [hI₆.nm, N5]
    have R6 : c₆.rmem = c.rmem := by rw [hI₆.rm, R5]
    have k6 : ∀ r, ¬ ((130 ≤ r ∧ r < 134) ∨ (269 ≤ r ∧ r < 275) ∨ r = 276) →
        c₆.nreg r = c₅.nreg r := hI₆.keep
    have F6 : Fr LWn AcR c c₆ := ⟨fun r hr => by
      rw [k6 r (by simp only [LWn, TPn] at hr; omega), F5.n r (by simp only [LWn] at hr; omega),
        F4.n r (by simp only [LWn, LWc, TPn] at hr ⊢; omega)],
      fun r hr => by
        rw [hI₆.keepR r (by simp only [AcR, TPr] at hr; omega), F5.r r (fun h => h),
          F4.r r hr], by rw [hI₆.out, F5.o, F4.o]⟩
    refine good_seq_use (copyA hL (I := I) c₆ hAS₆ 230 263 fr_ne) (fg_abs0 (by decide)) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f230, hF₇, hN₇, hM₇⟩
    rw [k6 263 (by omega), f263] at f230
    refine good_seq_use (tDelA hL (I := I) c₇ hAS₇ f230 hcur (by rw [hN₇, hM₇, N6, R6]; exact hM)
      (by rw [hN₇, N6]; exact hpc)) (fg_abs0 (by decide)) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hM₈, hn₈, hF₈⟩
    rw [hN₇, N6, hev] at hM₈
    refine good_seq_ex (fg_abs0 (by decide)) ?_
    exec_block
    · config_simp
      rw [hF₈.n 269 fr_ne, hF₇.n 269 fr_ne, hlov, hAS₈.env.g.r110]; omega
    · config_simp
      rw [hF₈.n 277 fr_ne, hF₇.n 277 fr_ne, k6 277 (by omega), F5.n 277 fr_ne, k4e,
        hAS₈.env.g.r110]; omega
    generalize hc₉ : (Config.mk _ _ _ _ _ _ : Config) = c₉
    have hw₉ : WordsBounded P.W c₉ := hc₉ ▸ ‹_›
    have F9 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c₈ c₉ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₉]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₉], by rw [← hc₉]⟩
    have hAS₉ := hAS₈.next hL hw₉ F9 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₉]) (fun x _ => by rw [← hc₉])
    have k8 : ∀ r, ¬ (TPn r ∨ r = 230) → c₈.nreg r = c₆.nreg r := fun r hr => by
      rw [hF₈.n r (fun h => hr (Or.inl h)), hF₇.n r (fun h => hr (Or.inr h))]
    have hActu : Act u := by rw [← hown cur le_rfl hst.1]; exact hAH.ok.act cur (by omega)
    refine Good.seq (tPutA_good hL hXB (σ := u) (j1 := lo + 1) (j2 := ee + 1) c₉ hAS₉
      (by rw [← hc₉]; config_simp; rw [k8 275 fr_ne, k6 275 (by omega), f275]) hu
      (by rw [← hc₉]; config_simp; rw [k8 269 fr_ne, hlov, hAS₈.env.g.r110])
      (by rw [← hc₉]; config_simp; rw [k8 277 fr_ne, k6 277 (by omega), F5.n 277 fr_ne, k4e,
        hAS₈.env.g.r110]) (by omega) (by omega) (hEB u hActu)) fun _ _ _ => fg_abs0 (by decide)
/-- **The right walk is good.** -/
theorem rwLoop_good (hL : Lay P) (hXB : XB P L) {β hx : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (hI : IRW P B Q T k a e own X β hx c₀ c₁ c₁) :
    FG I P L (.whileLtN 117 268 rwBody) c₁ :=
  Good.whileLtN (IRW P B Q T k a e own X β hx c₀ c₁) (fun c hI' hlt =>
    ⟨rwBody_good hL hXB hAH hEB c hI' hlt, fun c₂ k₂ e₂ => by
      obtain ⟨c', k', e', hI'', -⟩ := rwBody_exec (I := I) hL hAH hOL c hI' hlt
      obtain ⟨rfl, rfl⟩ := Exec.det e' e₂
      exact hI''⟩) hI

/-- **The left part of the activation is good.** -/
theorem actL_good (hL : Lay P) (hXB : XB P L) {β : ℕ} {c₀ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (c : Config) (hβs : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c.nmem β = 1))
    (hAS : AS P B Q T k a e c₀ c) (hM : BM P T k e own X (fun _ => False) Q c.nmem c.rmem)
    (h264 : c.nreg 264 = 0) (h265 : c.nreg 265 = 0)
    (hp1 : c.nreg 222 = 2 ^ T ∨ Pv Q (2 ^ T) β c.nmem (c.nreg 222))
    (hp2 : ∀ y, Pv Q (2 ^ T) β c.nmem y → c.nreg 222 ≠ 2 ^ T ∧ y ≤ c.nreg 222) :
    FG I P L actL c := by
  have g117 := hAS.env.g.r117
  have g110 := hAS.env.g.r110
  have hQ := hAS.hQ
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hM0 : BM P T k e own X (fun ρ => c.nreg 264 ≤ ρ ∧ ρ < c.nreg 265) Q c.nmem c.rmem :=
    hM.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => h.elim⟩)
      (fun ρ hρ => absurd hρ (by omega))
  generalize hαv : c.nreg 222 = α at hp1 hp2
  unfold actL
  refine good_seq_use (copyA hL (I := I) c hAS 263 222 fr_ne) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f263, hF₂, hN₂, hM₂⟩
  rw [hαv] at f263
  have k2 : ∀ r, r ≠ 263 → c₂.nreg r = c.nreg r := fun r h => hF₂.n r h
  by_cases hα : α < 2 ^ T
  · obtain ⟨hα0, hαp, hαβ⟩ : Pv Q (2 ^ T) β c.nmem α := hp1.resolve_left (by omega)
    have hst := hM.st α hα0 hαp
    generalize heαv : tEnd Q c.nmem α = eα at hst
    generalize huαv : tOwn Q c.nmem α = uα
    have heβ : eα < β := by
      rcases hβs with h | ⟨h1, h2⟩
      · omega
      · have := hM.disj α β hαβ h1 hαp h2; rw [heαv] at this; exact this
    have hownα : ∀ ρ, α ≤ ρ → ρ ≤ eα → own ρ = uα := fun ρ h1 h2 => by
      rw [← huαv]; exact hM.own α hα0 hαp ρ h1 (by rw [heαv]; exact h2)
    have huα : uα < hbNc P.b (2 ^ T) k := by
      rw [← hownα eα hst.1 le_rfl]; exact hAH.ok.lt _ (hAH.ok.act eα (by omega))
    have hBe : Bt' eα ↔ EE P T k e eα a < EE P T k e eα uα := by
      unfold Bt; rw [hownα eα hst.1 le_rfl]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have hnxe : ¬ X eα := (hM.not_hole hα0 hαp hst.1 (by rw [heαv])).1
    -- the rows between `eα` and `β` are not covered
    have hgap : ∀ ρ, eα < ρ → ρ < β → ¬ Bt' ρ := fun ρ h1 h2 =>
      hAH.uncov hM (fun h => h) (uncov_before hM (Or.inr ⟨hα0, hαp, hαβ⟩) hp2 h2
        (Or.inr (by rw [heαv]; exact h1)))
    refine good_ifLtN_true (by rw [f263, k2 121 (by omega), hAS.env.h.r121]; exact hα) ?_
    refine good_seq_use (ldCurA hL (I := I) c₂ hAS₂ f263 hα0) (fg_abs0 (by decide)) ?_
    intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f275, f277, hF₃, hN₃, hM₃⟩
    rw [hN₂, huαv] at f275; rw [hN₂, heαv] at f277
    refine good_seq_use (copyA hL (I := I) c₃ hAS₃ 274 277 fr_ne) (fg_abs0 (by decide)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f274, hF₄, hN₄, hM₄⟩
    rw [f277] at f274
    refine good_seq_use (btA hL (I := I) c₄ hAS₄ f274 (by omega) (by rw [hF₄.n 275 fr_ne, f275])
      huα hAH.ha) (fg_abs0 (by decide)) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hAS₅, f273, hF₅, hN₅, hM₅⟩
    have N5 : c₅.nmem = c.nmem := by rw [hN₅, hN₄, hN₃, hN₂]
    have R5 : c₅.rmem = c.rmem := by rw [hM₅, hM₄, hM₃, hM₂]
    have F5 : Fr LWl AcR c c₅ := ((hF₂.trans hF₃ fr_incl fr_incl (fun _ h => False.elim h)
      (fun _ h => False.elim h)).trans hF₄ (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)).trans hF₅ (fun r h => h) fr_incl (fun _ h => False.elim h)
      fr_incl
    have k5 : ∀ r, ¬ LWl r → c₅.nreg r = c.nreg r := F5.n
    by_cases hb : EE P T k e eα a < EE P T k e eα uα
    · rw [iteT hb] at f273
      refine good_ifLtN_true (by rw [k5 117 fr_ne, g117, f273]; omega) ?_
      refine good_seq_ex (fg_abs0 (by decide)) ?_
      exec_block
      · config_simp; rw [hF₅.n 277 fr_ne, hF₄.n 277 fr_ne, f277, k5 110 fr_ne, g110]; omega
      · config_simp; rw [hF₅.n 277 fr_ne, hF₄.n 277 fr_ne, f277, k5 110 fr_ne, g110]; omega
      generalize hc₆ : (Config.mk _ _ _ _ _ _ : Config) = c₆
      have hw₆ : WordsBounded P.W c₆ := hc₆ ▸ ‹_›
      have F6 : Fr (fun r => r = 264 ∨ r = 265 ∨ r = 268) (fun _ => False) c₅ c₆ :=
        ⟨fun r hr => by beta_reduce at hr; rw [← hc₆]; config_simp; upd_tac,
          fun _ _ => by rw [← hc₆], by rw [← hc₆]⟩
      have hAS₆ := hAS₅.next hL hw₆ F6 fr_incl (fun _ h => False.elim h)
        (fun x _ => by rw [← hc₆]) (fun x _ => by rw [← hc₆])
      have e277 : c₅.nreg 277 = eα := by rw [hF₅.n 277 fr_ne, hF₄.n 277 fr_ne, f277]
      have f264 : c₆.nreg 264 = eα + 1 := by
        rw [← hc₆]; config_simp; rw [e277, k5 110 fr_ne, g110]
      have f265 : c₆.nreg 265 = eα + 1 := by
        rw [← hc₆]; config_simp; rw [e277, k5 110 fr_ne, g110]
      have f268 : c₆.nreg 268 = 1 := by rw [← hc₆]; config_simp; rw [k5 110 fr_ne, g110]
      have f263' : c₆.nreg 263 = α := by
        rw [F6.n 263 fr_ne, hF₅.n 263 fr_ne, hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, f263]
      have N6 : c₆.nmem = c.nmem := by rw [← hc₆]; exact N5
      have R6 : c₆.rmem = c.rmem := by rw [← hc₆]; exact R5
      have hI₆ : ILW P B Q T k a e own X β (eα + 1) c₀ c₆ c₆ := by
        refine ⟨hAS₆, fun _ _ => rfl, f265, ?_, fun ρ h1 h2 => by omega, by omega, Or.inr f268,
          fun _ => ⟨by rw [f263']; exact hα0, by rw [f263', N6]; exact hαp,
            by rw [f264, f263', N6, heαv], by rw [f263']; exact hαβ,
            by rw [f263', N6, heαv]; exact hBe.2 hb⟩, fun ρ h1 h2 => ?_⟩
        · rw [f264, N6, R6]
          exact hM.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => h.elim⟩)
            (fun ρ hρ => absurd hρ (by omega))
        · rw [f264]
          have := h1 f268
          rw [f264] at this
          exact ⟨fun h => absurd h (hgap ρ (by omega) h2), fun h => by omega⟩
      exact lwLoop_good hL hXB hAH hOL hEB hI₆
    · rw [iteF hb] at f273
      refine good_ifLtN_false (by rw [k5 117 fr_ne, g117, f273]; omega) ?_
      exact Good.skip
  · refine good_ifLtN_false (by rw [f263, k2 121 (by omega), hAS.env.h.r121]; exact hα) ?_
    exact Good.skip


/-- **The right part of the activation is good.** -/
theorem actR_good (hL : Lay P) (hXB : XB P L) {β : ℕ} {c₀ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ))
    (c : Config) (hβs : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c.nmem β = 1))
    (hS : LS P B Q T k a e own X β c₀ c) (h262 : c.nreg 262 = β) :
    FG I P L actR c := by
  have hAS := hS.as
  have g117 := hAS.env.g.r117
  have g110 := hAS.env.g.r110
  have hM := hS.mem
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hlz := hS.lez
  unfold actR
  by_cases hβ : β < 2 ^ T
  · have hpβ : tPr Q c.nmem β = 1 := (hβs.resolve_left (by omega)).2
    have hst := hM.st β hβ hpβ
    generalize huβv : tOwn Q c.nmem β = uβ
    have hownβ : own β = uβ := by rw [← huβv]; exact hM.own β hβ hpβ β le_rfl hst.1
    have huβ : uβ < hbNc P.b (2 ^ T) k := by
      rw [← hownβ]; exact hAH.ok.lt _ (hAH.ok.act β (by omega))
    have hBb : Bt' β ↔ EE P T k e β a < EE P T k e β uβ := by
      unfold Bt; rw [hownβ]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have hnxb : ¬ X β := (hM.not_hole hβ hpβ le_rfl hst.1).1
    refine good_ifLtN_true (by rw [h262, hAS.env.h.r121]; exact hβ) ?_
    refine good_seq_use (copyA hL (I := I) c hAS 263 262 fr_ne) (fg_abs0 (by decide)) ?_
    intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f263, hF₂, hN₂, hM₂⟩
    rw [h262] at f263
    refine good_seq_use (ldCurA hL (I := I) c₂ hAS₂ f263 hβ) (fg_abs0 (by decide)) ?_
    intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f275, f277, hF₃, hN₃, hM₃⟩
    rw [hN₂, huβv] at f275
    refine good_seq_use (copyA hL (I := I) c₃ hAS₃ 274 263 fr_ne) (fg_abs0 (by decide)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f274, hF₄, hN₄, hM₄⟩
    rw [hF₃.n 263 fr_ne, f263] at f274
    refine good_seq_use (btA hL (I := I) c₄ hAS₄ f274 hβ (by rw [hF₄.n 275 fr_ne, f275])
      huβ hAH.ha) (fg_abs0 (by decide)) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hAS₅, f273, hF₅, hN₅, hM₅⟩
    have N5 : c₅.nmem = c.nmem := by rw [hN₅, hN₄, hN₃, hN₂]
    have R5 : c₅.rmem = c.rmem := by rw [hM₅, hM₄, hM₃, hM₂]
    have e5 : ∀ r, ¬ (r = 263 ∨ r = 272 ∨ r = 274 ∨ r = 275 ∨ r = 277 ∨ r = 273 ∨
        (130 ≤ r ∧ r < 134)) → c₅.nreg r = c.nreg r := fun r hr => by
      rw [hF₅.n r (by omega), hF₄.n r (by omega), hF₃.n r (by omega), hF₂.n r (by omega)]
    by_cases hb : EE P T k e β a < EE P T k e β uβ
    · rw [iteT hb] at f273
      refine good_ifLtN_true (by rw [e5 117 (by omega), g117, f273]; omega) ?_
      have hBβ : Bt' β := hBb.2 hb
      -- the hole ends at `β`
      have hend : ∀ (c₆ : Config), c₆.nreg 264 ≤ c₆.nreg 265 → c₆.nreg 265 = β →
          BM P T k e own X (fun ρ => c₆.nreg 264 ≤ ρ ∧ ρ < c₆.nreg 265) Q c₆.nmem c₆.rmem →
          (∀ ρ, c₆.nreg 264 ≤ ρ → ρ < c₆.nreg 265 → Bt' ρ) →
          (∀ ρ < β, Bt' ρ ↔ c₆.nreg 264 ≤ ρ ∧ ρ < c₆.nreg 265) → AS P B Q T k a e c₀ c₆ →
          c₆.nreg 263 = β → c₆.nmem = c.nmem →
          FG I P L (.seq (.instr (.copyN 268 110)) (.whileLtN 117 268 rwBody)) c₆ := by
        intro c₆ hle6 h265 hM6 hb6 hda6 hAS6 h263 hN6
        refine good_seq_use (copyA hL (I := I) c₆ hAS6 268 110 fr_ne) (fg_abs0 (by decide)) ?_
        intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f268, hF₇, hN₇, hM₇⟩
        rw [hAS6.env.g.r110] at f268
        have k7 : ∀ r, r ≠ 268 → c₇.nreg r = c₆.nreg r := fun r h => hF₇.n r h
        have hI₇ : IRW P B Q T k a e own X β (c₆.nreg 264) c₀ c₇ c₇ :=
          ⟨hAS₇, fun _ _ => rfl, k7 264 (by omega), by rw [k7 265 (by omega), hN₇, hM₇]; exact hM6,
            by rw [k7 265 (by omega)]; exact hb6, by rw [k7 265 (by omega)]; exact hle6,
            Or.inr f268, fun _ => ⟨by rw [k7 263 (by omega), h263]; exact hβ,
              by rw [k7 263 (by omega), h263, hN₇, hN6]; exact hpβ,
              by rw [k7 265 (by omega), k7 263 (by omega), h265, h263],
              by rw [k7 263 (by omega), h263], by rw [k7 263 (by omega), h263]; exact hBβ⟩,
            fun ρ hρ => by
              rw [k7 265 (by omega)]; rw [k7 265 (by omega), h265] at hρ
              exact hda6 ρ (hρ f268)⟩
        exact rwLoop_good hL hXB hAH hOL hEB hI₇
      by_cases hne : c₅.nreg 264 < c₅.nreg 265
      · refine good_seq_ex (good_ifLtN_true hne Good.skip) ?_
        refine spec_ifLtN_true hne ?_
        refine spec_skip hw₅ ?_
        have hle : c₅.nreg 264 ≤ c₅.nreg 265 := by
          rw [e5 264 (by omega), e5 265 (by omega)]; exact hS.le
        have hb5 : ∀ ρ, c₅.nreg 264 ≤ ρ → ρ < c₅.nreg 265 → Bt' ρ := fun ρ h1 h2 => by
          rw [e5 264 (by omega)] at h1; rw [e5 265 (by omega)] at h2; exact hS.hb ρ h1 h2
        have h265 : c₅.nreg 265 = β := by
          rw [e5 265 (by omega)]
          have h1 : c.nreg 264 < c.nreg 265 := by
            rw [e5 264 (by omega), e5 265 (by omega)] at hne; exact hne
          have hlast := hS.hb (c.nreg 265 - 1) (by omega) (by omega)
          have hz := hS.lez
          rcases Nat.eq_or_lt_of_le hz with h | h
          · exact h
          · have := hAH.adj hlast hBβ (by omega)
              (fun ρ h1' h2' hB => by have := (hS.da ρ h2').1 hB; omega)
            omega
        exact hend c₅ hle h265
          (by rw [e5 264 (by omega), e5 265 (by omega), N5, R5]; exact hM) hb5
          (fun ρ hρ => by rw [e5 264 (by omega), e5 265 (by omega)]; exact hS.da ρ hρ) hAS₅
          (by rw [hF₅.n 263 fr_ne, hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, f263]) N5
      · refine good_seq_ex (good_ifLtN_false hne (fg_abs0 (by decide))) ?_
        refine spec_ifLtN_false hne ?_
        exec_block
        generalize hc₆ : (Config.mk _ _ _ _ _ _ : Config) = c₆
        have hw₆ : WordsBounded P.W c₆ := hc₆ ▸ ‹_›
        have F6 : Fr (fun r => r = 264 ∨ r = 265) (fun _ => False) c₅ c₆ :=
          ⟨fun r hr => by beta_reduce at hr; rw [← hc₆]; config_simp; upd_tac,
            fun _ _ => by rw [← hc₆], by rw [← hc₆]⟩
        have hAS₆ := hAS₅.next hL hw₆ F6 fr_incl (fun _ h => False.elim h)
          (fun x _ => by rw [← hc₆]) (fun x _ => by rw [← hc₆])
        have e262 : c₅.nreg 262 = β := by rw [e5 262 (by omega), h262]
        have f264 : c₆.nreg 264 = β := by rw [← hc₆]; config_simp; exact e262
        have f265 : c₆.nreg 265 = β := by rw [← hc₆]; config_simp; exact e262
        have N6 : c₆.nmem = c.nmem := by rw [← hc₆]; exact N5
        have R6 : c₆.rmem = c.rmem := by rw [← hc₆]; exact R5
        have hemp : c.nreg 265 ≤ c.nreg 264 := by
          rw [e5 264 (by omega), e5 265 (by omega)] at hne; omega
        exact hend c₆ (by omega) f265
          (by
            rw [f264, f265, N6, R6]
            exact hM.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
              (fun ρ hρ => absurd hρ (by omega)))
          (fun ρ h1 h2 => by omega)
          (fun ρ hρ => by rw [f264, f265, hS.da ρ hρ]; omega) hAS₆
          (by rw [F6.n 263 fr_ne, hF₅.n 263 fr_ne, hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, f263]) N6
    · rw [iteF hb] at f273
      refine good_ifLtN_false (by rw [e5 117 (by omega), g117, f273]; omega) ?_
      exact Good.skip
  · refine good_ifLtN_false (by rw [h262, hAS.env.h.r121]; exact hβ) ?_
    exact Good.skip

/-- **The activation with an active source is good.** -/
theorem actGen_good (hL : Lay P) (hXB : XB P L) {κ : ℝ} (c : Config) (hAS : AS P B Q T k a e c c)
    (hTR : TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
      Act own X κ Q c.nmem c.rmem)
    (hA : AntiM (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ T) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ T) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ T) k ρ a)
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ)) (heA : |e a| ≤ (P.N * L : ℝ)) :
    FG I P L actGen c := by
  have hM := hTR.mem
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  obtain ⟨hMH, -⟩ := hTR.heap.activate hA hna ha hκ
  have hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own
      X a := ⟨hTR.heap.ok, hA, hna, ha, fun ρ hρ hX hB =>
        absurd ((hTR.heap.frz ρ hρ hX).trans (hκ ρ hρ)) (not_le.2 hB.2)⟩
  unfold actGen
  refine good_seq_use (copyA hL (I := I) c hAS 221 260 fr_ne) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f221, hF₂, hN₂, hM₂⟩
  rw [hAS.ra] at f221
  refine good_seq_use (tBnd_exec (I := I) c₂ hw₂ hAS₂.env.g hAS₂.tc hAS₂.hQ hAS₂.env.h.r121 f221
    (by rw [hN₂]; exact hM.pr01) (by rw [hN₂]; exact hTR.anti) (by rw [hN₂]; exact hM.wl)) (fg_abs0 (by decide)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hb1, hb2, hK₃, hR₃, hN₃, hM₃, hO₃⟩
  rw [hN₂] at hb1 hb2
  have F3 : Fr (fun r => 222 ≤ r ∧ r < 229) (fun _ => False) c₂ c₃ :=
    ⟨fun r hr => hK₃ r (by beta_reduce at hr; omega), fun r _ => by rw [hR₃], hO₃⟩
  have hAS₃ := hAS₂.next hL hw₃ F3 fr_incl (fun _ h => False.elim h) (fun x _ => by rw [hN₃])
    (fun x _ => by rw [hM₃])
  generalize hβv : c₃.nreg 222 = β at hb1 hb2
  -- the owners on the two sides of `β`
  have hβs : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c.nmem β = 1) := by
    rcases hb1 with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a) := by
    intro ρ hρ hX
    obtain ⟨y, hy, hpy, hy1, hy2⟩ := (hM.cover0 (fun _ h => h) hρ).1 hX
    have hoy := hM.own y hy hpy ρ hy1 hy2
    have hact : Act (own ρ) := hTR.heap.ok.act ρ hρ
    have hne : own ρ ≠ a := fun h => hna (h ▸ hact)
    refine ⟨fun hlt => ?_, fun hle => ?_⟩
    · have := hb2 y
      by_contra hc
      have : β ≤ y := hb2 y ⟨hy, hpy, by rw [← hoy]; omega⟩
      omega
    · rcases hb1 with h | ⟨h1, h2, h3⟩
      · omega
      · have hyb : β ≤ y := by
          by_contra hc
          have := hM.disj y β (by omega) h1 hpy h2; omega
        rcases Nat.eq_or_lt_of_le hyb with e | e
        · rw [hoy, ← e]; exact h3
        · have := hTR.anti β y e hy h2 hpy; rw [hoy]; omega
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
  have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
  have F4 : Fr (fun r => r = 262 ∨ r = 221 ∨ r = 264 ∨ r = 265) (fun _ => False) c₃ c₄ :=
    ⟨fun r hr => by beta_reduce at hr; rw [← hc₄]; config_simp; upd_tac,
      fun _ _ => by rw [← hc₄], by rw [← hc₄]⟩
  have hAS₄ := hAS₃.next hL hw₄ F4 fr_incl (fun _ h => False.elim h) (fun x _ => by rw [← hc₄])
    (fun x _ => by rw [← hc₄])
  have g117 := hAS₃.env.g.r117
  have f262 : c₄.nreg 262 = β := by rw [← hc₄]; config_simp; exact hβv
  have f221' : c₄.nreg 221 = β := by rw [← hc₄]; config_simp; exact hβv
  have f264 : c₄.nreg 264 = 0 := by rw [← hc₄]; config_simp; exact g117
  have f265 : c₄.nreg 265 = 0 := by rw [← hc₄]; config_simp; exact g117
  have N4 : c₄.nmem = c.nmem := by rw [← hc₄]; config_simp; rw [hN₃, hN₂]
  have R4 : c₄.rmem = c.rmem := by rw [← hc₄]; config_simp; rw [hM₃, hM₂]
  refine good_seq_use (tPvA hL (I := I) c₄ hAS₄ f221' (by rw [N4, R4]; exact hM)) (fg_abs0 (by decide)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨hAS₅, hp1, hp2, hF₅, hN₅, hM₅⟩
  rw [N4] at hp1 hp2
  have N5 : c₅.nmem = c.nmem := by rw [hN₅, N4]
  have R5 : c₅.rmem = c.rmem := by rw [hM₅, R4]
  refine good_seq_post (actL_exec hL (I := I) hAH hOL c₅ (by rw [N5]; exact hβs)
    hAS₅ (by rw [N5, R5]; exact hM) (by rw [hF₅.n 264 fr_ne, f264])
    (by rw [hF₅.n 265 fr_ne, f265]) (by rw [N5]; exact hp1) (by rw [N5]; exact hp2))
    (actL_good hL hXB hAH hOL hEB c₅ (by rw [N5]; exact hβs)
    hAS₅ (by rw [N5, R5]; exact hM) (by rw [hF₅.n 264 fr_ne, f264])
    (by rw [hF₅.n 265 fr_ne, f265]) (by rw [N5]; exact hp1) (by rw [N5]; exact hp2)) ?_
  rintro c₆ k₆ ex₆ ⟨hk₆, hS₆, hK₆⟩
  have hβs6 : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c₆.nmem β = 1) := by
    rcases hβs with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      have hst := hM.st β h1 h2
      have hnc : ¬ X β := (hM.not_hole h1 h2 le_rfl hst.1).1
      have hlz := hS₆.lez
      obtain ⟨y, hy, hpy, hy1, hy2⟩ := (hS₆.mem.cover β (by omega)).1 ⟨hnc, fun h => by omega⟩
      have hyst := hS₆.mem.st y hy hpy
      have e1 := hS₆.mem.own y hy hpy β hy1 hy2
      rcases Nat.eq_or_lt_of_le hy1 with e | e
      · rw [← e]; exact hpy
      · exfalso
        have e2 := hS₆.mem.own y hy hpy y le_rfl hyst.1
        have hny : ¬ X y := (hS₆.mem.not_hole hy hpy le_rfl hyst.1).1
        have := (hOL y (by omega) hny).1 e
        have := (hOL β (by omega) hnc).2 le_rfl
        omega
  refine good_seq_post (actR_exec hL (I := I) hAH hOL c₆ hβs6 hS₆
    (by rw [hK₆ 262 fr_ne, hF₅.n 262 fr_ne, f262]))
    (actR_good hL hXB hAH hOL hEB c₆ hβs6 hS₆ (by rw [hK₆ 262 fr_ne, hF₅.n 262 fr_ne, f262])) ?_
  rintro c₇ k₇ ex₇ ⟨hk₇, hS₇⟩
  have hM7 := hS₇.mem
  generalize hxv : c₇.nreg 264 = hx at hM7
  generalize hyv : c₇.nreg 265 = hy at hM7
  have hda7 : ∀ ρ < 2 ^ T, Bt' ρ ↔ hx ≤ ρ ∧ ρ < hy := fun ρ hρ => by
    rw [← hxv, ← hyv]; exact hS₇.da ρ hρ
  -- the owners after the activation
  have hcov : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → ¬ (hx ≤ ρ ∧ ρ < hy) →
      newOwn (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ) own a ρ = own ρ := by
    intro ρ hρ _ hH
    unfold newOwn
    rw [iteF (fun h => hH ((hda7 ρ (by omega)).1 ⟨hρ, h⟩))]
  have hM7' := hM7.congr_own hcov
  have hAS₇ := hS₇.as
  have hw₇ : WordsBounded P.W c₇ := hAS₇.wb
  by_cases hne : hx < hy
  · refine good_ifLtN_true (by rw [hxv, hyv]; exact hne) ?_
    refine good_seq_ex (fg_abs0 (by decide)) ?_
    exec_block
    generalize hc₈ : (Config.mk _ _ _ _ _ _ : Config) = c₈
    have hw₈ : WordsBounded P.W c₈ := hc₈ ▸ ‹_›
    have F8 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c₇ c₈ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₈]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₈], by rw [← hc₈]⟩
    have hAS₈ := hAS₇.next hL hw₈ F8 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₈]) (fun x _ => by rw [← hc₈])
    have hlast : Bt' (hy - 1) := (hda7 (hy - 1) (by have := hS₇.lez; omega)).2 ⟨by omega, by omega⟩
    exact tPutA_good hL hXB (σ := a) (j1 := hx) (j2 := hy) c₈ hAS₈
      (by rw [← hc₈]; config_simp; exact hAS₇.ra) ha
      (by rw [← hc₈]; config_simp; exact hxv) (by rw [← hc₈]; config_simp; exact hyv) hne
      (by have := hlast.1; omega) heA
  · refine good_ifLtN_false (by rw [hxv, hyv]; exact hne) ?_
    exact Good.skip
/-- **The first activation is good.** -/
theorem actFirst_good (hL : Lay P) (hXB : XB P L) (c : Config) (hAS : AS P B Q T k a e c c)
    (ha : a < hbNc P.b (2 ^ T) k) (hM : BM P T k e own X (fun ρ => ρ < hbNr P.b (2 ^ T) k) Q c.nmem c.rmem)
    (heA : |e a| ≤ (P.N * L : ℝ)) :
    FG I P L actFirst c := by
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hnr1 : 1 ≤ hbNr P.b (2 ^ T) k := by
    have := hAS.ks; unfold hbNr; have := Nat.one_le_two_pow (n := T); omega
  have hc := hAS.wb
  unfold actFirst
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have F2 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c c₂ :=
    ⟨fun r hr => by beta_reduce at hr; rw [← hc₂]; config_simp; upd_tac,
      fun _ _ => by rw [← hc₂], by rw [← hc₂]⟩
  have hAS₂ := hAS.next hL hw₂ F2 fr_incl (fun _ h => False.elim h) (fun x _ => by rw [← hc₂])
    (fun x _ => by rw [← hc₂])
  exact tPutA_good hL hXB (σ := a) (j1 := 0) (j2 := hbNr P.b (2 ^ T) k) c₂ hAS₂
    (by rw [← hc₂]; config_simp; exact hAS.ra) ha
    (by rw [← hc₂]; config_simp; exact hAS.env.g.r117)
    (by rw [← hc₂]; config_simp; exact hAS.env.h.r125) (by omega) le_rfl heA

/-- **The activation of a source is good.** -/
theorem act_good (hL : Lay P) (hXB : XB P L) {κ : ℝ} (c : Config) (hAS : AS P B Q T k a e c c)
    (hA : AntiM (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ T) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ T) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ T) k ρ a)
    (hpre : (tFlag Q T c.nmem = 0 ∧ (∀ σ, ¬ Act σ) ∧ (∀ ρ, ¬ X ρ) ∧
        BM P T k e own X (fun ρ => ρ < hbNr P.b (2 ^ T) k) Q c.nmem c.rmem) ∨
      (tFlag Q T c.nmem = 1 ∧ TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
        (hbF P.b P.D P.p (2 ^ T) k) e Act own X κ Q c.nmem c.rmem))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ)) (heA : |e a| ≤ (P.N * L : ℝ)) :
    FG I P L act c := by
  have hc := hAS.wb
  have hQ := hAS.hQ
  have g := hAS.env.g
  have h121 := hAS.env.h.r121
  have g209 := hAS.tc.r209
  have e12 : 2 ^ T * 4 + (Q + 8 * 2 ^ T) = Q + 12 * 2 ^ T := by ring
  have hs1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  unfold act
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · rw [h121, g.r116]; omega
  · config_simp; rw [h121, g.r116, g209]; omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have F2 : Fr (fun r => r = 261 ∨ r = 262) (fun _ => False) c c₂ :=
    ⟨fun r hr => by beta_reduce at hr; rw [← hc₂]; config_simp; upd_tac,
      fun _ _ => by rw [← hc₂], by rw [← hc₂]⟩
  have hAS₂ := hAS.next hL hw₂ F2 fr_incl (fun _ h => False.elim h) (fun x _ => by rw [← hc₂])
    (fun x _ => by rw [← hc₂])
  have f262 : c₂.nreg 262 = tFlag Q T c.nmem := by
    rw [← hc₂]; config_simp; rw [h121, g.r116, g209, e12]; rfl
  have N2 : c₂.nmem = c.nmem := by rw [← hc₂]
  have R2 : c₂.rmem = c.rmem := by rw [← hc₂]
  refine Good.seq ?_ fun _ _ _ => fg_abs0 (by decide)
  rcases hpre with ⟨hf, hno, hX, hM⟩ | ⟨hf, hTR⟩
  · refine good_ifLtN_true (by rw [f262, hf, hAS₂.env.g.r110]; omega) ?_
    exact actFirst_good hL hXB c₂ hAS₂.rebase ha (by rw [N2, R2]; exact hM) heA
  · refine good_ifLtN_false (by rw [f262, hf, hAS₂.env.g.r110]; omega) ?_
    exact actGen_good hL hXB c₂ hAS₂.rebase (by rw [N2, R2]; exact hTR) hA hna ha hκ hEB heA

end walk

/-- **The extraction is good.** -/
theorem ext_good (hL : Lay P) {B Q T k : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
    {X : ℕ → Prop} {κ κ' : ℝ} (c : Config) (hc : WordsBounded P.W c) (hE : Env P B (2 ^ T) k c)
    (hT : TCtx Q (2 ^ T) c) (hB : B + 8 * 2 ^ T ≤ P.W) (hQ : Q + 16 * 2 ^ T ≤ P.W) (hQw : P.wb ≤ Q)
    (hBQ : Q + 16 * 2 ^ T ≤ B) (hR : QReady P B (2 ^ T) k c.nmem)
    (hTR : TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
      Act own X κ Q c.nmem c.rmem)
    (he : ∀ σ, Act σ → e σ = c.rmem (P.db + (sib k * 2 ^ T + σ)))
    {x : ℕ} (hx : x < 2 ^ T) (hpx : tPr Q c.nmem x = 1) (hκ : κ ≤ κ')
    (hval : tKey Q c.rmem (tWn Q (2 ^ T) c.nmem 1) ≤ κ')
    (hXB : XB P L) (heB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ)) :
    FG I P L ext c := by
  have hs1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  obtain ⟨hw, hpw, hX0, hρ0, hown0, hkey0, -⟩ := hTR.item hs1 hx hpx
  have hM := hTR.mem
  generalize hwv : tWn Q (2 ^ T) c.nmem 1 = w at hw hpw hX0 hρ0 hown0 hkey0 hval ⊢
  obtain ⟨m1, m2, -, -⟩ := hM.mn w hw hpw
  have hst := hM.st w hw hpw
  generalize hρv : tMin Q c.nmem w = ρ0 at hX0 hρ0 hown0 hkey0 m1 m2 ⊢
  generalize huv : tOwn Q c.nmem w = u at hown0 hkey0
  generalize hev : tEnd Q c.nmem w = ew at hst m2
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hu : u < hbNc P.b (2 ^ T) k := by
    have := hTR.heap.ok.act ρ0 hρ0; rw [hown0] at this; exact hTR.heap.ok.lt u this
  have heu : e u = c.rmem (P.db + (sib k * 2 ^ T + u)) := by
    have := hTR.heap.ok.act ρ0 hρ0; rw [hown0] at this; exact he u this
  have heuB : |e u| ≤ (P.N * L : ℝ) := by
    have := hTR.heap.ok.act ρ0 hρ0; rw [hown0] at this; exact heB u this
  have hownw : ∀ ρ, w ≤ ρ → ρ ≤ ew → own ρ = u := fun ρ h1 h2 => by
    rw [← huv]; exact hM.own w hw hpw ρ h1 (hev ▸ h2)
  have g := hE.g
  have g208 := hT.r208; have g209 := hT.r209
  have ew' : c.nmem (c.nreg 209 + c.nreg 111) = w := by
    rw [g209, g.r111, ← hwv]; unfold tWn; congr 1
  have e8 : w * 8 + Q = Q + 8 * w := by ring
  unfold ext
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  unfold extLoad
  exec_block
  · rw [g209, g.r111]; omega
  · config_simp; rw [ew', g.r118]; omega
  · config_simp; rw [ew', g.r118, g208]; omega
  · config_simp; rw [ew', g.r118, g208, g.r110]; omega
  · config_simp; rw [ew', g.r118, g208, g.r111]; omega
  · config_simp; rw [ew', g.r118, g208, g.r116]; omega
  · config_simp; rw [ew', g.r118, g208, g.r116, g.r110]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f250 : c₁.nreg 250 = w := by rw [← hc₁]; config_simp; exact ew'
  have f230 : c₁.nreg 230 = w := by rw [← hc₁]; config_simp; exact ew'
  have f252 : c₁.nreg 252 = u := by
    rw [← hc₁]; config_simp; rw [ew', g.r118, g208, g.r110, ← huv, e8]; rfl
  have f253 : c₁.nreg 253 = ew := by
    rw [← hc₁]; config_simp; rw [ew', g.r118, g208, g.r111, ← hev, e8]; rfl
  have f254 : c₁.nreg 254 = ρ0 := by
    rw [← hc₁]; config_simp; rw [ew', g.r118, g208, g.r116, g.r110, ← hρv, e8]; rfl
  have r250 : c₁.rreg 250 = tKey Q c.rmem w := by
    rw [← hc₁]; config_simp; rw [ew', g.r118, g208, e8]; rfl
  have fK : ∀ r, ¬ ExN r → c₁.nreg r = c.nreg r := fun r hr => by
    unfold ExN TPn at hr; rw [← hc₁]; config_simp; upd_tac
  have fK' : ∀ r, ¬ (r = 230 ∨ (250 ≤ r ∧ r < 255)) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 250 → c₁.rreg r = c.rreg r := fun r hr => by
    rw [← hc₁]; config_simp; rw [upd_other _ _ _ hr]
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hE₁ : Env P B (2 ^ T) k c₁ := hE.of hL (fun r h1 h2 => fK' r (by omega))
    (fun a _ => by rw [fN]) (fun a _ => by rw [fM])
  have hT₁ : TCtx Q (2 ^ T) c₁ := hT.of fun r h1 h2 => fK' r (by omega)
  -- clear `w`
  refine good_seq_use (tDel_exec (I := I) (k := k) c₁ hw₁ hE₁.g hT₁ hQ hE₁.h.r121 f230 hw
    (by rw [fN, fM]; exact hM) (by rw [fN]; exact hpw)) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hM₂, hpr₂, hF₂, hlo₂, hrm₂⟩
  have hn₂ : nst Q (2 ^ T) c₂.nmem + 1 = nst Q (2 ^ T) c.nmem := by
    rw [← fN]; exact nst_clr hw (by rw [fN]; exact hpw) hpr₂
  rw [fN, hev] at hM₂
  have hM₂' := hM₂.rearr (X' := fun ρ => X ρ ∨ ρ = ρ0)
    (H' := fun ρ => w ≤ ρ ∧ ρ ≤ ew ∧ ρ ≠ ρ0) (fun ρ hρ => ?_) (fun ρ hρ => ?_)
  rotate_left
  · constructor
    · rintro ((h' | rfl) | ⟨h1, h2, -⟩)
      · exact Or.inl h'
      · exact Or.inr (Or.inr ⟨m1, m2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · rintro (h' | (h' | ⟨h1, h2⟩))
      · exact Or.inl (Or.inl h')
      · exact absurd h' id
      · by_cases e : ρ = ρ0
        · exact Or.inl (Or.inr e)
        · exact Or.inr ⟨h1, h2, e⟩
  · obtain ⟨h1, h2, h3⟩ := hρ
    refine ⟨by omega, fun h' => h'.elim (fun h'' => ?_) h3⟩
    exact (hM.not_hole hw hpw h1 (hev ▸ h2)).1 h''
  have hlo₂' : ∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hlo₂ a ha, fN]
  have hrm₂' : c₂.rmem = c.rmem := by rw [hrm₂, fM]
  have hR₂ : QReady P B (2 ^ T) k c₂.nmem := hR.congr fun a h1 => hlo₂' a (by omega)
  have hE₂ : Env P B (2 ^ T) k c₂ := hE₁.of hL (fun r h1 h2 => hF₂.n r (by unfold TPn; omega))
    (fun a ha => by rw [hlo₂' a (by have := hL.m6; have := hL.m5; omega), fN])
    (fun a _ => by rw [hrm₂', fM])
  have hT₂ : TCtx Q (2 ^ T) c₂ := hT₁.of fun r h1 h2 => hF₂.n r (by unfold TPn; omega)
  have k2 : ∀ r, r = 250 ∨ r = 252 ∨ r = 253 ∨ r = 254 → c₂.nreg r = c₁.nreg r := fun r hr =>
    hF₂.n r (by unfold TPn; omega)
  have hsu : sib k * 2 ^ T + u < P.N := by have := hL.bN; unfold hbNc at hu; omega
  -- the right part, from any state after the left part
  have right : ∀ c₃ : Config, WordsBounded P.W c₃ → Env P B (2 ^ T) k c₃ → TCtx Q (2 ^ T) c₃ →
      QReady P B (2 ^ T) k c₃.nmem →
      BM P T k e own (fun ρ => X ρ ∨ ρ = ρ0) (fun ρ => ρ0 < ρ ∧ ρ ≤ ew) Q c₃.nmem c₃.rmem →
      c₃.nreg 252 = u → c₃.nreg 253 = ew → c₃.nreg 254 = ρ0 →
      e u = c₃.rmem (P.db + (sib k * 2 ^ T + u)) →
      FG I P L (.ifLtN 254 253 (.seq (block [.copyN 200 252, .addN 201 254 110,
          .addN 202 253 110]) tPut) .skip) c₃ := by
    intro c₃ hw₃ hE₃ hT₃ hR₃ hM₃ h252 h253 h254 he₃
    by_cases hlt : ρ0 < ew
    · refine good_ifLtN_true (by rw [h254, h253]; exact hlt) ?_
      refine good_seq_ex (fg_abs0 (by decide)) ?_
      exec_block
      · config_simp; rw [h254, hE₃.g.r110]; omega
      · config_simp; rw [h253, hE₃.g.r110]; omega
      generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
      have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
      have k4 : ∀ r, ¬ (200 ≤ r ∧ r < 203) → c₄.nreg r = c₃.nreg r := fun r hr => by
        rw [← hc₄]; config_simp; upd_tac
      have e4N : c₄.nmem = c₃.nmem := by rw [← hc₄]
      have e4M : c₄.rmem = c₃.rmem := by rw [← hc₄]
      have e4R : c₄.rreg = c₃.rreg := by rw [← hc₄]
      have e4O : c₄.output = c₃.output := by rw [← hc₄]
      exact tPut_good hL hXB (σ := u) (j1 := ρ0 + 1) (j2 := ew + 1) c₄ hw₄
        (hE₃.of hL (fun r h1 h2 => k4 r (by omega)) (fun a _ => by rw [e4N])
          (fun a _ => by rw [e4M])) hB (by rw [e4N]; exact hR₃) (by rw [e4M]; exact he₃) heuB
        (by rw [← hc₄]; config_simp; exact h252) hu
        (by rw [← hc₄]; config_simp; rw [h254, hE₃.g.r110])
        (by rw [← hc₄]; config_simp; rw [h253, hE₃.g.r110]) (by omega) (by omega)
    · refine good_ifLtN_false (by rw [h254, h253]; exact hlt) ?_
      exact Good.skip
  -- the left part
  have hpost : ∀ c₃ k₃, k₃ ≤ rmqCost T + 49 * T + 25 → WordsBounded P.W c₃ →
      Env P B (2 ^ T) k c₃ → TCtx Q (2 ^ T) c₃ →
      BM P T k e own (fun ρ => X ρ ∨ ρ = ρ0) (fun ρ => ρ0 < ρ ∧ ρ ≤ ew) Q c₃.nmem c₃.rmem →
      c₃.nreg 252 = u → c₃.nreg 253 = ew → c₃.nreg 254 = ρ0 → Fr ExP TPr c₂ c₃ →
      (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c₃.nmem a = c₂.nmem a) →
      (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c₃.rmem a = c₂.rmem a) →
      nst Q (2 ^ T) c₃.nmem ≤ nst Q (2 ^ T) c₂.nmem + 1 →
      FG I P L (.ifLtN 254 253 (.seq (block [.copyN 200 252, .addN 201 254 110,
          .addN 202 253 110]) tPut) .skip) c₃ := by
    intro c₃ k₃ hk₃ hw₃ hE₃ hT₃ hM₃ h252 h253 h254 hF₃ hlo₃ hrm₃ hn₃
    have hlo₃' : ∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
      rw [hlo₃ a ha, hlo₂' a ha]
    have hrm₃' : ∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c₃.rmem a = c.rmem a := fun a ha => by
      rw [hrm₃ a ha, hrm₂']
    exact right c₃ hw₃ hE₃ hT₃ (hR.congr fun a h1 => hlo₃' a (by omega)) hM₃
      h252 h253 h254 (by rw [hrm₃' _ (Or.inl (by have := hL.m6; omega))]; exact heu)
  have k250 : c₂.nreg 250 = w := (k2 250 (by omega)).trans f250
  have k252 : c₂.nreg 252 = u := (k2 252 (by omega)).trans f252
  have k253 : c₂.nreg 253 = ew := (k2 253 (by omega)).trans f253
  have k254 : c₂.nreg 254 = ρ0 := (k2 254 (by omega)).trans f254
  refine good_seq_ex ?_ ?_
  · by_cases hlt : w < ρ0
    · refine good_ifLtN_true (by rw [k250, k254]; exact hlt) ?_
      refine good_seq_ex (fg_abs0 (by decide)) ?_
      exec_block
      generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
      have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
      have k4 : ∀ r, ¬ (200 ≤ r ∧ r < 203) → c₄.nreg r = c₂.nreg r := fun r hr => by
        rw [← hc₄]; config_simp; upd_tac
      have e4N : c₄.nmem = c₂.nmem := by rw [← hc₄]
      have e4M : c₄.rmem = c₂.rmem := by rw [← hc₄]
      exact tPut_good hL hXB (σ := u) (j1 := w) (j2 := ρ0) c₄ hw₄
        (hE₂.of hL (fun r h1 h2 => k4 r (by omega)) (fun a _ => by rw [e4N])
          (fun a _ => by rw [e4M])) hB (by rw [e4N]; exact hR₂)
        (by rw [e4M, hrm₂', ← fM]; rw [fM]; exact heu) heuB
        (by rw [← hc₄]; config_simp; exact k252) hu
        (by rw [← hc₄]; config_simp; exact k250)
        (by rw [← hc₄]; config_simp; exact k254) hlt (by omega)
    · refine good_ifLtN_false (by rw [k250, k254]; exact hlt) ?_
      exact Good.skip
  by_cases hlt : w < ρ0
  · refine spec_ifLtN_true (by rw [k250, k254]; exact hlt) ?_
    refine spec_seq ?_
    exec_block
    generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
    have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
    have k4 : ∀ r, ¬ (200 ≤ r ∧ r < 203) → c₄.nreg r = c₂.nreg r := fun r hr => by
      rw [← hc₄]; config_simp; upd_tac
    have e4N : c₄.nmem = c₂.nmem := by rw [← hc₄]
    have e4M : c₄.rmem = c₂.rmem := by rw [← hc₄]
    have e4R : c₄.rreg = c₂.rreg := by rw [← hc₄]
    have e4O : c₄.output = c₂.output := by rw [← hc₄]
    refine spec_use (tPut_exec (I := I) (σ := u) (j1 := w) (j2 := ρ0) (e := e)
      (own := own) (X := fun ρ => X ρ ∨ ρ = ρ0) (H := fun ρ => w ≤ ρ ∧ ρ ≤ ew ∧ ρ ≠ ρ0) hL c₄ hw₄
      (hE₂.of hL (fun r h1 h2 => k4 r (by omega)) (fun a _ => by rw [e4N])
        (fun a _ => by rw [e4M]))
      (hT₂.of fun r h1 h2 => k4 r (by omega)) hB hQ (by rw [e4N]; exact hR₂)
      (by rw [e4N, e4M]; exact hM₂')
      (by rw [e4M, hrm₂', ← fM]; rw [fM]; exact heu)
      (by rw [← hc₄]; config_simp; exact k252) hu
      (by rw [← hc₄]; config_simp; exact k250)
      (by rw [← hc₄]; config_simp; exact k254) hlt (by omega)
      (fun ρ h1 h2 => ⟨h1, by omega, by omega⟩) (fun ρ h1 h2 => hownw ρ h1 (by omega))) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hM₅, hpr₅, hF₅, hlo₅, hrm₅⟩
    have hpj : tPr Q c₄.nmem w ≠ 1 := fun hp => by
      rw [e4N] at hp
      exact (hM₂'.not_hole (by omega) hp le_rfl (hM₂'.st _ (by omega) hp).1).2
        ⟨le_rfl, by omega, by omega⟩
    have hF45 : Fr ExP TPr c₂ c₅ := Fr.trans (show Fr (fun r => 200 ≤ r ∧ r < 203)
        (fun _ => False) c₂ c₄ from ⟨fun r hr => k4 r hr, fun r _ => by rw [e4R], e4O⟩) hF₅
        (fun r h => Or.inr h) (fun r h => Or.inl h) (fun r h => h.elim) (fun r h => h)
    have hiff : ∀ ρ < hbNr P.b (2 ^ T) k, ((X ρ ∨ ρ = ρ0) ∨ (ρ0 < ρ ∧ ρ ≤ ew)) ↔
        ((X ρ ∨ ρ = ρ0) ∨ ((w ≤ ρ ∧ ρ ≤ ew ∧ ρ ≠ ρ0) ∧ ¬ (w ≤ ρ ∧ ρ < ρ0))) := by
      intro ρ _
      constructor
      · rintro (h' | ⟨h1, h2⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨⟨by omega, h2, by omega⟩, by omega⟩
      · rintro (h' | ⟨⟨h1, h2, h3⟩, h4⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨by omega, h2⟩
    exact hpost c₅ (k₅ + 4) (by omega) hw₅
      (hE₂.of hL (fun r h1 h2 => hF45.n r (by unfold ExP TPn; omega))
        (fun a ha => by rw [hlo₅ a (by have := hL.m6; have := hL.m5; omega), e4N])
        (fun a ha => by rw [hrm₅ a (by have := hL.m6; have := hL.m5; omega), e4M]))
      (hT₂.of fun r h1 h2 => hF45.n r (by unfold ExP TPn; omega))
      (hM₅.rearr hiff (fun ρ hρ => hM₂'.hole ρ ⟨by omega, hρ.2, by omega⟩))
      (by rw [hF45.n 252 (by unfold ExP TPn; omega)]; exact k252)
      (by rw [hF45.n 253 (by unfold ExP TPn; omega)]; exact k253)
      (by rw [hF45.n 254 (by unfold ExP TPn; omega)]; exact k254) hF45
      (fun a ha => by rw [hlo₅ a ha, e4N]) (fun a ha => by rw [hrm₅ a ha, e4M])
      (by rw [nst_set (by omega) hpj hpr₅, e4N])
  · refine spec_ifLtN_false (by rw [k250, k254]; exact hlt) ?_
    have hwρ : w = ρ0 := by omega
    have hiff : ∀ ρ < hbNr P.b (2 ^ T) k, ((X ρ ∨ ρ = ρ0) ∨ (ρ0 < ρ ∧ ρ ≤ ew)) ↔
        ((X ρ ∨ ρ = ρ0) ∨ (w ≤ ρ ∧ ρ ≤ ew ∧ ρ ≠ ρ0)) := by
      intro ρ _
      constructor
      · rintro (h' | ⟨h1, h2⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨by omega, h2, by omega⟩
      · rintro (h' | ⟨h1, h2, h3⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨by omega, h2⟩
    exact spec_skip hw₂ (hpost c₂ 2 (by omega) hw₂ hE₂ hT₂
      (hM₂'.rearr hiff (fun ρ hρ => hM₂'.hole ρ ⟨by omega, hρ.2, by omega⟩))
      k252 k253 k254 (Fr.refl _) (fun _ _ => rfl) (fun _ _ => rfl) (by omega))



/-- **Extracting the item of a half block and offering the next one is good.** -/
theorem extStep_good (hL : Lay P) (hXB : XB P L) {t k : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop}
    {own : ℕ → ℕ} {X : ℕ → Prop} {κ κ' : ℝ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b)
    (c : Config) (hc : WordsBounded P.W c) (hE : Env P (rbB P t k) (2 ^ t) k c)
    (hT : TCtx (tbQ P t k) (2 ^ t) c)
    (hR : QReady P (rbB P t k) (2 ^ t) k c.nmem)
    (hTR : TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k) e
      Act own X κ (tbQ P t k) c.nmem c.rmem)
    (he : ∀ σ, Act σ → e σ = c.rmem (P.db + (sib k * 2 ^ t + σ)))
    {x : ℕ} (hx : x < 2 ^ t) (hpx : tPr (tbQ P t k) c.nmem x = 1) (hκ : κ ≤ κ')
    (hval : tKey (tbQ P t k) c.rmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) ≤ κ')
    (heB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ)) :
    FG I P L (.seq ext bsync) c := by
  have hw0 := hL.w
  have hBt : rbB P t k + 8 * 2 ^ t ≤ P.W := by
    have := rbB_le_W hL ht hk
    have := Nat.mul_le_mul_right (2 ^ t) (show 8 ≤ 4 * (t + 2) by omega)
    omega
  have hQB : tbQ P t k + 16 * 2 ^ t ≤ rbB P t k := by
    have := tbQ_le_bh ht hk; have := rb_le_rbB (P := P) (t := t) (k := k)
    unfold Prm.rb at this; omega
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hwt : P.wb ≤ P.tb := wb_le_tb
  exact Good.seq (ext_good hL c hc hE hT hBt (by omega) (by omega) hQB hR hTR he hx hpx hκ hval
    hXB heB) fun _ _ _ => fg_abs0 (by decide)

/-- **Activating a source and offering the item of its half block is good.** -/
theorem blkStep_good (hL : Lay P) (hXB : XB P L) {t k a : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop}
    {own : ℕ → ℕ} {X : ℕ → Prop} {κ : ℝ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) (c : Config)
    (hc : WordsBounded P.W c) (hE : Env P (rbB P t k) (2 ^ t) k c)
    (hT : TCtx (tbQ P t k) (2 ^ t) c) (h260 : c.nreg 260 = a)
    (hR : QReady P (rbB P t k) (2 ^ t) k c.nmem)
    (he : ∀ σ < hbNc P.b (2 ^ t) k, e σ = c.rmem (P.db + (sib k * 2 ^ t + σ)))
    (hA : AntiM (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ t) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ t) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ t) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ t) k ρ a)
    (hpre : (tFlag (tbQ P t k) t c.nmem = 0 ∧ (∀ σ, ¬ Act σ) ∧ (∀ ρ, ¬ X ρ) ∧
        BM P t k e own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) (tbQ P t k) c.nmem c.rmem) ∨
      (tFlag (tbQ P t k) t c.nmem = 1 ∧ TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k)
        (hbF P.b P.D P.p (2 ^ t) k) e Act own X κ (tbQ P t k) c.nmem c.rmem))
    (hEB : ∀ σ, Act σ → |e σ| ≤ (P.N * L : ℝ)) (heA : |e a| ≤ (P.N * L : ℝ)) :
    FG I P L (.seq act bsync) c := by
  have hw0 := hL.w
  have hBt : rbB P t k + 8 * 2 ^ t ≤ P.W := by
    have := rbB_le_W hL ht hk
    have := Nat.mul_le_mul_right (2 ^ t) (show 8 ≤ 4 * (t + 2) by omega)
    omega
  have hQB : tbQ P t k + 16 * 2 ^ t ≤ rbB P t k := by
    have := tbQ_le_bh ht hk; have := rb_le_rbB (P := P) (t := t) (k := k)
    unfold Prm.rb at this; omega
  have hQb := tbQ_le_bh ht hk
  have hbw := bh_le_W hL
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hwt : P.wb ≤ P.tb := wb_le_tb
  have hAS : AS P (rbB P t k) (tbQ P t k) t k a e c c :=
    ⟨hc, hE, hT, h260, hk, hBt, by omega, by omega, hQB, hR, he, Fr.refl c,
      fun _ _ => rfl, fun _ _ => rfl⟩
  exact Good.seq (act_good hL hXB c hAS hA hna ha hκ hpre hEB heA) fun _ _ _ => fg_abs0 (by decide)

end FR

end Monge

end PlanarFlow
