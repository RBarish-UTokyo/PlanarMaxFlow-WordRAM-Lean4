module

public import PlanarFlow.NegSSSP.NdFullSem2

/-!
# The full branch: the first part of the preparation

**`fs_p1`**: from the context of the full branch (`hF` of `nodeS_exec`), `ndFront ; ndB Gt ;
spStage`: the children's values gathered in the node's numbering (`ndB`), the split re-run, its
end meeting `BigOut` (the large case, `msplit_big`, `spFin_big`, `bigOut_agree`); the memory below
`Hb` zero above the split's work area, the heap from `Hb` to the heap top kept, reals kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

theorem spStage_natOnly : Klein.natOnly spStage = true := by decide +kernel

variable {I : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- The cost of `ndFront ; ndB ; spStage`. -/
def fsP1Cost (m k : ℕ) : ℕ :=
  prepCost k + splitT k + (7 * m + 33) + wsCost k + ndBCost m k + (prepCost k + splitT k)

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The first part of the preparation** (see the module docstring). -/
theorem fs_p1 (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L n Hb Gt : ℕ} {P : Finset D} {d e bl el er : ℕ} {f₀ f₁ : V → ℤ} (c : Config)
    (hc : WordsBounded W c) (hg : GZ0 Hb c) (hPr : P ⊆ reps N)
    (hin : InP g N ℓ L (n + 1) P d e c)
    (r04 : c.nreg 3004 = d) (r07 : c.nreg 3007 = el) (r09 : c.nreg 3009 = er)
    (r03 : c.nreg 3003 = er) (hHb : spWs (ck N P) < Hb) (hGt : Gt + g.G ≤ Hb)
    (b1 : Hb + 5 ≤ d) (b3 : e ≤ bl) (b4 : bl + 5 ≤ el) (b5 : el + 5 ≤ er)
    (hr0 : Res g N L (msplit g N P).1 (some f₀) (bl + 5) el c)
    (hr1 : Res g N L (msplit g N P).2 (some f₁) (el + 5) er c)
    (hbig : 1000000 < P.card) (hB : (bdry N (msplit g N P).1 (msplit g N P).2).Nonempty)
    (hW : er + 10 * ck N P ≤ W) (hW2 : spWs (ck N P) + 205 ≤ W) (wL : 2 * L + 1 ≤ W)
    (h41 : 41 ≤ W) :
    ∃ (c₃ : Config) (t w : ℕ) (ν : ℕ → ℕ) (x₁ : D), Exec I W (.seq ndFront (.seq (ndB Gt) spStage)) c c₃ t ∧
      t ≤ fsP1Cost P.card (ck N P) ∧
      c₃.nreg 3003 = er ∧ c₃.nreg 3004 = d ∧ c₃.nreg 2475 = ck N P ∧ c₃.nreg 2474 = P.card ∧
      c₃.nreg 2464 = w ∧ c₃.nreg 2496 = (bdry N (msplit g N P).1 (msplit g N P).2).card ∧
      c₃.nreg 2972 = spB0 (ck N P) ∧ w = (verts N P).card ∧
      (∀ x ∈ verts N P, ν (g.gv x) < w ∧
        gInv g N (c₃.nmem (er + 2 * ck N P + ν (g.gv x))) = x) ∧
      (∀ v < w, gInv g N (c₃.nmem (er + 2 * ck N P + v)) ∈ verts N P ∧
        ν (g.gv (gInv g N (c₃.nmem (er + 2 * ck N P + v)))) = v ∧
        c₃.nmem (er + 2 * ck N P + v) = g.gv (gInv g N (c₃.nmem (er + 2 * ck N P + v)))) ∧
      (∀ a < P.card, c₃.nmem (er + a) = ν (g.gv (N.tail (cδ g N P a)))) ∧
      (∀ a < P.card, c₃.nmem (er + ck N P + a) = ν (g.gv (N.head (cδ g N P a)))) ∧
      (∀ v < w, (c₃.nmem (er + 4 * ck N P + v) : ℤ) =
          fbExt (verts N (msplit g N P).1) f₀ L (gInv g N (c₃.nmem (er + 2 * ck N P + v))) +
            (L + 1) ∧
        |fbExt (verts N (msplit g N P).1) f₀ L (gInv g N (c₃.nmem (er + 2 * ck N P + v)))| ≤
          L + 1) ∧
      (∀ v < w, (c₃.nmem (er + 6 * ck N P + v) : ℤ) =
          fbExt (verts N (msplit g N P).2) f₁ L (gInv g N (c₃.nmem (er + 2 * ck N P + v))) +
            (L + 1) ∧
        |fbExt (verts N (msplit g N P).2) f₁ L (gInv g N (c₃.nmem (er + 2 * ck N P + v)))| ≤
          L + 1) ∧
      InP g N ℓ L (n + 1) P d e c₃ ∧
      x₁ ∈ P ∧ 3 * P.card / 4 < (pcomp N P x₁).card ∧
      BigOut N P P.card (ck N P) (cδ g N P) (spB0 (ck N P)) x₁ c₃ ∧
      (∀ a, spWs (ck N P) < a → a < Hb → c₃.nmem a = 0) ∧
      (∀ a ≤ spWs (ck N P), c₃.nmem a = (spFin g N P).nmem a ∧ c₃.nmem a ≤ spWs (ck N P)) ∧
      (∀ a, Hb ≤ a → a < er → c₃.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → c₃.nreg r = c.nreg r) ∧
      c₃.rreg = c.rreg ∧ c₃.rmem = c.rmem ∧ c₃.output = c.output := by
  have hcard := msplit_card (g := g) (N := N) P
  have hmk := ck_ge (N := N) P
  have he := hin.en
  have hel := hr0.1
  have her := hr1.1
  unfold fsz at he hel her
  -- the front
  obtain ⟨c₁, t₁, e₁, ht₁, f72, f73, f74, f75, f76, f79, f81, f82, f85, f86, fn₁, hg₁, fm₁, fr₁,
    frm₁, fo₁⟩ := ndFront_exec (I := I) hM hrot hface hPr c hc hg hin r04 r07 r09 hHb
      (by omega) b3 (by unfold fsz; omega) (by unfold fsz; omega) (by omega) hW2 h41
  have F1 : ∀ r, 3000 ≤ r → c₁.nreg r = c.nreg r := fun r hr => fn₁ r (by omega)
  have M1 : ∀ a, Hb ≤ a → c₁.nmem a = c.nmem a := fm₁
  have hin₁ : InP g N ℓ L (n + 1) P d e c₁ :=
    inP_stab hin fun a h1 h2 => ⟨M1 a (by omega), by rw [frm₁]⟩
  have hr0₁ := res_stab hr0 fun a h1 h2 => ⟨M1 a (by omega), by rw [frm₁]⟩
  have hr1₁ := res_stab hr1 fun a h1 h2 => ⟨M1 a (by omega), by rw [frm₁]⟩
  -- the middle
  obtain ⟨c₂, t₂, w, ν, e₂, ht₂, g64, hwv, P1, P2, hTn, hHn, -, g96, G0, G1, m₂, n₂, r₂, rm₂,
    o₂⟩ := ndB_exec (I := I) Gt c₁ e₁.wb_right hin₁ hr0₁ hr1₁ f72 f75 f79 f81 f82 f85
      (by rw [F1 _ (by omega)]; exact r04) (by rw [F1 _ (by omega)]; exact r03)
      (fun a ha => hg₁.2.2 _ (by omega)) (by omega) b3 b4 b5 le_rfl (by omega) wL (by omega)
  have F2 : ∀ r, 3000 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [n₂ r (by omega), F1 r hr]
  have M2 : ∀ a, a < er → c₂.nmem a = c₁.nmem a := fun a ha => m₂ a (Or.inl ha)
  have hin₂ : InP g N ℓ L (n + 1) P d e c₂ :=
    inP_stab hin₁ fun a h1 h2 => ⟨M2 a (by omega), by rw [rm₂]⟩
  -- the split again
  obtain ⟨c₃, t₃, e₃, ht₃, hA, s66, s69, s72, m₃, n₃, rr₃, rm₃, o₃⟩ :=
    spStage_exec' (P := I) hM hrot hface hPr c₂ e₂.wb_right hin₂
      (by rw [F2 _ (by omega)]; exact r04) (by omega) (fun r _ => by rw [r₂]; exact hg₁.1 r)
      (fun a ha => by rw [rm₂]; exact hg₁.2.1 a (by omega)) (by omega) hW2
  have hbig0 := msplit_big (g := g) hM hrot hface hPr hbig hB
  obtain ⟨x₁, hx₁, hbx, hBO⟩ := spFin_big (g := g) hM hrot hface hPr hbig0
  have hBO₃ := bigOut_agree hBO hA hmk (by unfold spWs; omega)
  obtain ⟨hrr₃, hrm₃⟩ := exec_reals_keep spStage_natOnly e₃
  have hws : spWs (ck N P) < er := by omega
  have M3 : ∀ a, er ≤ a → c₃.nmem a = c₂.nmem a := fun a ha => m₃ a (by omega)
  have N3 : ∀ r, 2900 ≤ r → r < 2966 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    n₃ r (by omega) (Or.inl h2)
  have N3' : ∀ r, 2400 ≤ r → r < 2900 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    n₃ r (by omega) (Or.inl (by omega))
  have hf0 := res_abs hr0
  have hf1 := res_abs hr1
  refine ⟨c₃, t₁ + (t₂ + t₃), w, ν, x₁, .seq e₁ (.seq e₂ e₃), ?_,
    by rw [n₃ _ (by omega) (Or.inr (by omega)), F2 _ (by omega), r03],
    by rw [n₃ _ (by omega) (Or.inr (by omega)), F2 _ (by omega), r04],
    by rw [N3' _ (by omega) (by omega), n₂ _ (by omega), f75],
    by rw [N3' _ (by omega) (by omega), n₂ _ (by omega), f74],
    by rw [N3' _ (by omega) (by omega), g64], by rw [N3' _ (by omega) (by omega), g96], s72, hwv,
    fun x hx => ?_, fun v hv => ?_, fun a ha => ?_, fun a ha => ?_, fun v hv => ?_,
    fun v hv => ?_, inP_stab hin₂ fun a h1 h2 => ⟨m₃ a (by omega), by rw [hrm₃]⟩, hx₁, hbx,
    hBO₃, fun a h1 h2 => ?_, fun a ha => ⟨hA.nmem a ha, ?_⟩, fun a h1 h2 => ?_, fun r hr => ?_,
    by rw [hrr₃, r₂, fr₁],
    by rw [hrm₃, rm₂, frm₁], by rw [o₃, o₂, fo₁]⟩
  · unfold fsP1Cost; omega
  · rw [M3 _ (by omega)]; exact P1 x hx
  · rw [M3 _ (by omega)]; exact P2 v hv
  · rw [M3 _ (by omega)]; exact hTn a ha
  · rw [M3 _ (by omega)]; exact hHn a ha
  · rw [M3 _ (by omega), M3 _ (by omega)]
    exact fbExt_G hf0 (G0 v hv).1 (G0 v hv).2
  · rw [M3 _ (by omega), M3 _ (by omega)]
    exact fbExt_G hf1 (G1 v hv).1 (G1 v hv).2
  · rw [m₃ a h1, M2 a (by omega)]; exact hg₁.2.2 a h2
  · rw [hA.nmem a ha]
    obtain ⟨⟨t, ex, -⟩, -⟩ := spFin_run (g := g) hM hrot hface hPr
    exact ex.wb_right.2 a
  · rw [m₃ a (by omega), M2 a h2, M1 a h1]
  · rw [n₃ r (by omega) (Or.inr (by omega)), F2 r hr]

end Frame

end NegSSSP

end PlanarFlow
