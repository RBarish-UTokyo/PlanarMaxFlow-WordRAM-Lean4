module

public import PlanarFlow.Monge.FRTripOps

/-!
# FR-Dijkstra on the machine: extracting the item of a half block

`ext` pops the item of the current half block (lazy extraction,
`PlanarFlow.Monge.FR.MHInv.extract`): the triplet `w` at the root of the heap over the triplets
holds the least entry, at the row `ρ₀ = tMin w`; the row `ρ₀` is extracted, and the rest of the
triplet `[w, tEnd w]` is split into `[w, ρ₀ - 1]` and `[ρ₀ + 1, tEnd w]`, each with its least entry
found by a query (`tPut`).

`ext_exec`: from a representation `TRep` at the popped key `κ`, with the item at most the new
popped key `κ'`, `ext` leaves a representation with `ρ₀` extracted, at `κ'`; the row in `r254`,
its entry (the item) in the real `r250`. Cost `2 rmqCost T + 147 T + 70`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-- The loads of the extraction: the root triplet `w = r250`, its item (real `r250`), its owner
`r252`, its last row `r253`, its least row `r254`; `r230 := w`. -/
def extLoad : Stmt :=
  block [.addN 250 209 111, .loadN 250 250, .mulN 251 250 118, .addN 251 251 208, .loadR 250 251,
    .addN 252 251 110, .loadN 252 252, .addN 253 251 111, .loadN 253 253, .addN 254 251 116,
    .addN 254 254 110, .loadN 254 254, .copyN 230 250]

/-- **Extract the item of the current half block.** -/
def ext : Stmt :=
  .seq extLoad <| .seq tDel <|
  .seq (.ifLtN 250 254 (.seq (block [.copyN 200 252, .copyN 201 250, .copyN 202 254]) tPut) .skip)
    (.ifLtN 254 253 (.seq (block [.copyN 200 252, .addN 201 254 110, .addN 202 253 110]) tPut)
      .skip)

/-- The registers changed by `ext`. -/
def ExN (r : ℕ) : Prop := TPn r ∨ (200 ≤ r ∧ r < 203) ∨ (250 ≤ r ∧ r < 255)

/-- The registers changed by `tPut` and its arguments. -/
def ExP (r : ℕ) : Prop := TPn r ∨ (200 ≤ r ∧ r < 203)

/-- The real registers changed by `ext`. -/
def ExR (r : ℕ) : Prop := TPr r ∨ r = 250

/-- The cost of `ext`. -/
def extCost (T : ℕ) : ℕ := 2 * rmqCost T + 147 * T + 70

variable {P : Prm} {I : Input}

/-- **The extraction.** -/
theorem ext_exec (hL : Lay P) {B Q T k : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
    {X : ℕ → Prop} {κ κ' : ℝ} (c : Config) (hc : WordsBounded P.W c) (hE : Env P B (2 ^ T) k c)
    (hT : TCtx Q (2 ^ T) c) (hB : B + 8 * 2 ^ T ≤ P.W) (hQ : Q + 16 * 2 ^ T ≤ P.W) (hQw : P.wb ≤ Q)
    (hBQ : Q + 16 * 2 ^ T ≤ B) (hR : QReady P B (2 ^ T) k c.nmem)
    (hTR : TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
      Act own X κ Q c.nmem c.rmem)
    (he : ∀ σ, Act σ → e σ = c.rmem (P.db + (sib k * 2 ^ T + σ)))
    {x : ℕ} (hx : x < 2 ^ T) (hpx : tPr Q c.nmem x = 1) (hκ : κ ≤ κ')
    (hval : tKey Q c.rmem (tWn Q (2 ^ T) c.nmem 1) ≤ κ') :
    ∃ c' k', Exec I P.W ext c c' k' ∧ k' ≤ extCost T ∧
      TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act
        own (fun ρ => X ρ ∨ ρ = tMin Q c.nmem (tWn Q (2 ^ T) c.nmem 1)) κ' Q c'.nmem c'.rmem ∧
      nst Q (2 ^ T) c'.nmem ≤ nst Q (2 ^ T) c.nmem + 1 ∧
      c'.nreg 254 = tMin Q c.nmem (tWn Q (2 ^ T) c.nmem 1) ∧
      c'.rreg 250 = tKey Q c.rmem (tWn Q (2 ^ T) c.nmem 1) ∧
      Fr ExN ExR c c' ∧ (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c'.rmem a = c.rmem a) := by
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
  have hownw : ∀ ρ, w ≤ ρ → ρ ≤ ew → own ρ = u := fun ρ h1 h2 => by
    rw [← huv]; exact hM.own w hw hpw ρ h1 (hev ▸ h2)
  have g := hE.g
  have g208 := hT.r208; have g209 := hT.r209
  have ew' : c.nmem (c.nreg 209 + c.nreg 111) = w := by
    rw [g209, g.r111, ← hwv]; unfold tWn; congr 1
  have e8 : w * 8 + Q = Q + 8 * w := by ring
  unfold ext
  refine spec_seq ?_
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
  refine spec_seq ?_
  refine spec_use (tDel_exec (I := I) (k := k) c₁ hw₁ hE₁.g hT₁ hQ hE₁.h.r121 f230 hw
    (by rw [fN, fM]; exact hM) (by rw [fN]; exact hpw)) ?_
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
      ∃ c' k', Exec I P.W (.ifLtN 254 253 (.seq (block [.copyN 200 252, .addN 201 254 110,
          .addN 202 253 110]) tPut) .skip) c₃ c' k' ∧ k' ≤ rmqCost T + 49 * T + 25 ∧
        BM P T k e own (fun ρ => X ρ ∨ ρ = ρ0) (fun _ => False) Q c'.nmem c'.rmem ∧
        Fr ExP TPr c₃ c' ∧ (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c₃.nmem a) ∧
        (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c'.rmem a = c₃.rmem a) ∧
        nst Q (2 ^ T) c'.nmem ≤ nst Q (2 ^ T) c₃.nmem + 1 := by
    intro c₃ hw₃ hE₃ hT₃ hR₃ hM₃ h252 h253 h254 he₃
    by_cases hlt : ρ0 < ew
    · refine spec_ifLtN_true (by rw [h254, h253]; exact hlt) ?_
      refine spec_seq ?_
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
      refine spec_use (tPut_exec (I := I) (σ := u) (j1 := ρ0 + 1) (j2 := ew + 1) (e := e)
        (own := own) (X := fun ρ => X ρ ∨ ρ = ρ0) (H := fun ρ => ρ0 < ρ ∧ ρ ≤ ew) hL c₄ hw₄
        (hE₃.of hL (fun r h1 h2 => k4 r (by omega)) (fun a _ => by rw [e4N])
          (fun a _ => by rw [e4M]))
        (hT₃.of fun r h1 h2 => k4 r (by omega)) hB hQ (by rw [e4N]; exact hR₃)
        (by rw [e4N, e4M]; exact hM₃) (by rw [e4M]; exact he₃)
        (by rw [← hc₄]; config_simp; exact h252) hu
        (by rw [← hc₄]; config_simp; rw [h254, hE₃.g.r110])
        (by rw [← hc₄]; config_simp; rw [h253, hE₃.g.r110]) (by omega) (by omega)
        (fun ρ h1 h2 => ⟨by omega, by omega⟩) (fun ρ h1 h2 => hownw ρ (by omega) (by omega))) ?_
      intro c₅ k₅ hk₅ hw₅ ⟨hM₅, hpr₅, hF₅, hlo₅, hrm₅⟩
      have hpj : tPr Q c₄.nmem (ρ0 + 1) ≠ 1 := fun hp => by
        rw [e4N] at hp
        exact (hM₃.not_hole (by omega) hp le_rfl (hM₃.st _ (by omega) hp).1).2 ⟨by omega, by omega⟩
      refine ⟨by omega, hM₅.rearr (fun ρ hρ => ?_) (fun ρ hρ => hρ.elim), ?_,
        fun a ha => by rw [hlo₅ a ha, e4N], fun a ha => by rw [hrm₅ a ha, e4M],
        by rw [nst_set (by omega) hpj hpr₅, e4N]⟩
      · constructor
        · rintro (h' | h')
          · exact Or.inl h'
          · exact h'.elim
        · rintro (h' | ⟨⟨h1, h2⟩, h3⟩)
          · exact Or.inl h'
          · exact absurd ⟨by omega, by omega⟩ h3
      · exact Fr.trans (show Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c₃ c₄ from
          ⟨fun r hr => k4 r hr, fun r _ => by rw [e4R], e4O⟩) hF₅
          (fun r h => Or.inr h) (fun r h => Or.inl h) (fun r h => h.elim) (fun r h => h)
    · refine spec_ifLtN_false (by rw [h254, h253]; exact hlt) ?_
      refine spec_skip hw₃ ⟨by omega, hM₃.rearr (fun ρ hρ => ?_) (fun ρ hρ => hρ.elim),
        Fr.refl _, fun _ _ => rfl, fun _ _ => rfl, by omega⟩
      constructor
      · rintro (h' | h')
        · exact Or.inl h'
        · exact h'.elim
      · rintro (h' | ⟨h1, h2⟩)
        · exact Or.inl h'
        · omega
  -- the left part
  refine spec_seq ?_
  have hpost : ∀ c₃ k₃, k₃ ≤ rmqCost T + 49 * T + 25 → WordsBounded P.W c₃ →
      Env P B (2 ^ T) k c₃ → TCtx Q (2 ^ T) c₃ →
      BM P T k e own (fun ρ => X ρ ∨ ρ = ρ0) (fun ρ => ρ0 < ρ ∧ ρ ≤ ew) Q c₃.nmem c₃.rmem →
      c₃.nreg 252 = u → c₃.nreg 253 = ew → c₃.nreg 254 = ρ0 → Fr ExP TPr c₂ c₃ →
      (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c₃.nmem a = c₂.nmem a) →
      (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c₃.rmem a = c₂.rmem a) →
      nst Q (2 ^ T) c₃.nmem ≤ nst Q (2 ^ T) c₂.nmem + 1 →
      ∃ c' k', Exec I P.W (.ifLtN 254 253 (.seq (block [.copyN 200 252, .addN 201 254 110,
          .addN 202 253 110]) tPut) .skip) c₃ c' k' ∧ ∀ kk, kk ≤ 13 + k₂ + k₃ + k' →
        (kk ≤ extCost T ∧
          TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act
            own (fun ρ => X ρ ∨ ρ = ρ0) κ' Q c'.nmem c'.rmem ∧
          nst Q (2 ^ T) c'.nmem ≤ nst Q (2 ^ T) c.nmem + 1 ∧ c'.nreg 254 = ρ0 ∧
          c'.rreg 250 = tKey Q c.rmem w ∧ Fr ExN ExR c c' ∧
          (∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c'.nmem a = c.nmem a) ∧
          (∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c'.rmem a = c.rmem a)) := by
    intro c₃ k₃ hk₃ hw₃ hE₃ hT₃ hM₃ h252 h253 h254 hF₃ hlo₃ hrm₃ hn₃
    have hlo₃' : ∀ a, (a < Q ∨ Q + 12 * 2 ^ T ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
      rw [hlo₃ a ha, hlo₂' a ha]
    have hrm₃' : ∀ a, (a < Q ∨ Q + 8 * 2 ^ T ≤ a) → c₃.rmem a = c.rmem a := fun a ha => by
      rw [hrm₃ a ha, hrm₂']
    refine spec_use (right c₃ hw₃ hE₃ hT₃ (hR.congr fun a h1 => hlo₃' a (by omega)) hM₃
      h252 h253 h254 (by rw [hrm₃' _ (Or.inl (by have := hL.m6; omega))]; exact heu)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hM₄, hF₄, hlo₄, hrm₄, hn₄⟩ kk hkk
    have hF : Fr ExN ExR c c₄ := by
      have F1 : Fr ExN ExR c c₁ := ⟨fK, fun r hr => fR r (by unfold ExR at hr; omega), fO⟩
      exact ((F1.trans hF₂ (fun r h => h) (fun r h => Or.inl h) (fun r h => h)
        (fun r h => Or.inl h)).trans hF₃ (fun r h => h)
        (fun r h => h.elim Or.inl fun h' => Or.inr (Or.inl h')) (fun r h => h)
        (fun r h => Or.inl h)).trans hF₄ (fun r h => h)
        (fun r h => h.elim Or.inl fun h' => Or.inr (Or.inl h')) (fun r h => h)
        (fun r h => Or.inl h)
    refine ⟨by unfold extCost; omega, ⟨hTR.heap.extract hκ ?_, hM₄⟩, by omega, ?_, ?_, hF,
      fun a ha => by rw [hlo₄ a ha, hlo₃' a ha], fun a ha => by rw [hrm₄ a ha, hrm₃' a ha]⟩
    · rw [hown0]; show e u + _ ≤ κ'; rw [← hkey0]; exact hval
    · rw [hF₄.n 254 (by unfold ExP TPn; omega)]; exact h254
    · rw [hF₄.r 250 (by unfold TPr; omega), hF₃.r 250 (by unfold TPr; omega),
        hF₂.r 250 (by unfold TPr; omega), r250]
  have k250 : c₂.nreg 250 = w := (k2 250 (by omega)).trans f250
  have k252 : c₂.nreg 252 = u := (k2 252 (by omega)).trans f252
  have k253 : c₂.nreg 253 = ew := (k2 253 (by omega)).trans f253
  have k254 : c₂.nreg 254 = ρ0 := (k2 254 (by omega)).trans f254
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
    obtain ⟨c', k', ex, hP⟩ := hpost c₅ (k₅ + 4) (by omega) hw₅
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
    exact ⟨c', k', ex, hP _ (by omega)⟩
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
    obtain ⟨c', k', ex, hP⟩ := hpost c₂ 2 (by omega) hw₂ hE₂ hT₂
      (hM₂'.rearr hiff (fun ρ hρ => hM₂'.hole ρ ⟨by omega, hρ.2, by omega⟩))
      k252 k253 k254 (Fr.refl _) (fun _ _ => rfl) (fun _ _ => rfl) (by omega)
    exact spec_skip hw₂ ⟨c', k', ex, hP _ (by omega)⟩

end FR

end Monge

end PlanarFlow
