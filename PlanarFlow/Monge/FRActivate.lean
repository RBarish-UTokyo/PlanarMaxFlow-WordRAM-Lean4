module

public import PlanarFlow.Monge.FRExtract

/-!
# FR-Dijkstra on the machine: activating a source in a half block

`act` activates the source `a = r260` of the current half block (the vertex `sib k s + a` was just
settled; `PlanarFlow.Monge.FR.MHInv.activate`). The rows where `a` is strictly better than their
owners form an interval (`PlanarFlow.Monge.FR.beat_convex`), next to the first triplet `β` whose
owner is before `a` (`tBnd`), with the triplets before `β` owned by later sources and the others
by earlier ones (`PlanarFlow.Monge.FR.own_order_left`, `own_order_right`):

* *the left walk* (from the last triplet `α` before `β`, `tPv`): while `a` beats the first row of
  the current triplet, it is deleted and the walk goes to the previous one if `a` beats its last
  row; otherwise a binary search (two entries per step) finds the first row that `a` beats, and
  the triplet is cut there;
* *the right walk* (from `β`), symmetric (`tNx`);
* the rows found (the *hole*) become the triplet of `a`, with its least entry by a query (`tPut`).

The first activation in a half block (its flag at `Q + 12 s` is `0`) makes `a` the owner of all
the rows.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The programs -/

/-- **The beat test**: `r273 := 1` if the source `a = r260` is strictly better than `u = r275`
at the row `r274`, `0` otherwise. -/
def bt : Stmt :=
  .seq (block [.copyN 130 274, .copyN 131 260]) <|
  .seq evE <|
  .seq (block [.copyR 260 130, .copyN 130 274, .copyN 131 275]) <|
  .seq evE <|
  .ifLtR 260 130 (.instr (.copyN 273 110)) (.instr (.copyN 273 117))

/-- One probe of a binary search in `[r269, r270]` (the row `r270` beaten exactly when `d`); a
beaten row moves the end `r270` if `d`, the start `r269` otherwise. -/
def bsBody (d : Bool) : Stmt :=
  .seq (block [.addN 271 269 270, .divN 271 271 111, .copyN 274 271]) <|
  .seq bt <|
  .seq (.ifLtN 117 273 (.instr (cond d (.copyN 270 271) (.copyN 269 271)))
    (.instr (cond d (.copyN 269 271) (.copyN 270 271)))) (.instr (.addN 276 269 110))

/-- One probe of the binary search for the first row that `a` beats, in `(r269, r270]`. -/
abbrev bsLBody : Stmt := bsBody true

/-- One probe of the binary search for the last row that `a` beats, in `[r269, r270)`. -/
abbrev bsRBody : Stmt := bsBody false

/-- The owner `r275` and the last row `r277` of the start `r263`. -/
def ldCur : Stmt :=
  block [.mulN 272 263 118, .addN 272 272 208, .addN 275 272 110, .loadN 275 275,
    .addN 277 272 111, .loadN 277 277]

/-- The left walk: delete the current triplet `r263` (all beaten), go to the previous one if `a`
beats its last row. -/
def lwDel : Stmt :=
  .seq (block [.copyN 264 263, .copyN 230 263]) <|
  .seq tDel <|
  .seq (.instr (.copyN 221 263)) <|
  .seq tPv <|
  .ifLtN 222 121
    (.seq (.instr (.copyN 263 222)) <| .seq ldCur <| .seq (.instr (.copyN 274 277)) <|
      .seq bt <| .ifLtN 117 273 .skip (.instr (.copyN 268 117)))
    (.instr (.copyN 268 117))

/-- The left walk: cut the current triplet at the first row that `a` beats. -/
def lwCut : Stmt :=
  .seq (block [.copyN 269 263, .copyN 270 277, .addN 276 263 110]) <|
  .seq (.whileLtN 276 270 bsLBody) <|
  .seq (.instr (.copyN 230 263)) <|
  .seq tDel <|
  .seq (block [.copyN 200 275, .copyN 201 263, .copyN 202 270]) <|
  .seq tPut <|
  block [.copyN 264 270, .copyN 268 117]

/-- One step of the left walk, at the start `r263` whose last row `a` beats. -/
def lwBody : Stmt :=
  .seq ldCur <| .seq (.instr (.copyN 274 263)) <| .seq bt <| .ifLtN 117 273 lwDel lwCut

/-- The right walk: delete the current triplet `r263` (all beaten), go to the next one if `a`
beats its first row. -/
def rwDel : Stmt :=
  .seq (block [.addN 265 277 110, .copyN 230 263]) <|
  .seq tDel <|
  .seq (.instr (.copyN 221 277)) <|
  .seq tNx <|
  .ifLtN 222 121
    (.seq (.instr (.copyN 263 222)) <| .seq ldCur <| .seq (.instr (.copyN 274 263)) <|
      .seq bt <| .ifLtN 117 273 .skip (.instr (.copyN 268 117)))
    (.instr (.copyN 268 117))

/-- The right walk: cut the current triplet after the last row that `a` beats. -/
def rwCut : Stmt :=
  .seq (block [.copyN 269 263, .copyN 270 277, .addN 276 263 110]) <|
  .seq (.whileLtN 276 270 bsRBody) <|
  .seq (.instr (.copyN 230 263)) <|
  .seq tDel <|
  .seq (block [.copyN 200 275, .addN 201 269 110, .addN 202 277 110]) <|
  .seq tPut <|
  block [.addN 265 269 110, .copyN 268 117]

/-- One step of the right walk, at the start `r263` whose first row `a` beats. -/
def rwBody : Stmt :=
  .seq ldCur <| .seq (.instr (.copyN 274 277)) <| .seq bt <| .ifLtN 117 273 rwDel rwCut

/-- The left part, from the last start `α = r222` before `β`. -/
def actL : Stmt :=
  .seq (.instr (.copyN 263 222)) <|
  .ifLtN 263 121
    (.seq ldCur <| .seq (.instr (.copyN 274 277)) <| .seq bt <|
      .ifLtN 117 273
        (.seq (block [.addN 264 277 110, .addN 265 277 110, .copyN 268 110])
          (.whileLtN 117 268 lwBody))
        .skip)
    .skip

/-- The right part, from the first start `β = r262` with an owner before `a`. -/
def actR : Stmt :=
  .ifLtN 262 121
    (.seq (.instr (.copyN 263 262)) <| .seq ldCur <| .seq (.instr (.copyN 274 263)) <|
      .seq bt <|
      .ifLtN 117 273
        (.seq (.ifLtN 264 265 .skip (block [.copyN 264 262, .copyN 265 262]))
          (.seq (.instr (.copyN 268 110)) (.whileLtN 117 268 rwBody)))
        .skip)
    .skip

/-- The activation when the half block already has an active source. -/
def actGen : Stmt :=
  .seq (.instr (.copyN 221 260)) <| .seq tBnd <|
  .seq (block [.copyN 262 222, .copyN 221 222, .copyN 264 117, .copyN 265 117]) <| .seq tPv <|
  .seq actL <| .seq actR <|
  .ifLtN 264 265 (.seq (block [.copyN 200 260, .copyN 201 264, .copyN 202 265]) tPut) .skip

/-- The first activation in the half block: `a` owns all the rows. -/
def actFirst : Stmt := .seq (block [.copyN 200 260, .copyN 201 117, .copyN 202 125]) tPut

/-- **Activate the source `a = r260`** of the current half block (the flag at `Q + 12 s` tells
whether it has an active source), and set the flag. -/
def act : Stmt :=
  .seq (block [.mulN 261 121 116, .addN 261 261 209, .loadN 262 261]) <|
  .seq (.ifLtN 262 110 actFirst actGen)
    (block [.mulN 261 121 116, .addN 261 261 209, .storeN 261 110])

/-! ### The beaten rows -/

section beat

variable {s nr nc : ℕ} {F : ℕ → ℕ → ℝ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
  {X H : ℕ → Prop} {Q : ℕ} {nm : ℕ → ℕ} {rm : ℕ → ℝ} {a : ℕ}

/-- The row `ρ` is *beaten* by `a`: `a` is strictly better than its owner. -/
def Bt (nr : ℕ) (F : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (own : ℕ → ℕ) (a ρ : ℕ) : Prop :=
  ρ < nr ∧ e a + F ρ a < e (own ρ) + F ρ (own ρ)

/-- The hypotheses of an activation: an owner map, the crossing inequality, a new source, the
extracted rows are not beaten (`PlanarFlow.Monge.FR.MHInv.activate`). -/
structure AH (nr nc : ℕ) (F : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (Act : ℕ → Prop) (own : ℕ → ℕ)
    (X : ℕ → Prop) (a : ℕ) : Prop where
  ok : OwnOK nr nc (fun ρ σ => e σ + F ρ σ) Act own
  anti : AntiM nr nc (fun ρ σ => e σ + F ρ σ)
  na : ¬ Act a
  ha : a < nc
  nx : ∀ ρ < nr, X ρ → ¬ Bt nr F e own a ρ

theorem AH.conv (h : AH nr nc F e Act own X a) {ρ₁ ρ₂ ρ₃ : ℕ} (h1 : Bt nr F e own a ρ₁)
    (h3 : Bt nr F e own a ρ₃) (h12 : ρ₁ ≤ ρ₂) (h23 : ρ₂ ≤ ρ₃) : Bt nr F e own a ρ₂ :=
  ⟨by have := h3.1; omega, beat_convex h.anti h.ok h.na h.ha h12 h23 h3.1 h1.2 h3.2⟩

/-- No row before a row not beaten and owned by a later source is beaten. -/
theorem AH.left_end (h : AH nr nc F e Act own X a) {ρ' : ℕ} (hρ' : ρ' < nr)
    (ho : a < own ρ') (hn : ¬ Bt nr F e own a ρ') {ρ : ℕ} (hρ : ρ ≤ ρ') :
    ¬ Bt nr F e own a ρ := by
  intro hb
  rcases Nat.eq_or_lt_of_le hρ with rfl | hlt
  · exact hn hb
  · have := own_order_right h.anti h.ok h.na h.ha hρ' hlt hb.2 (fun h' => hn ⟨hρ', h'⟩)
    omega

/-- No row after a row not beaten and owned by an earlier source is beaten. -/
theorem AH.right_start (h : AH nr nc F e Act own X a) {ρ' : ℕ} (ho : own ρ' < a)
    (hn : ¬ Bt nr F e own a ρ') {ρ : ℕ} (hρ : ρ' ≤ ρ) : ¬ Bt nr F e own a ρ := by
  intro hb
  rcases Nat.eq_or_lt_of_le hρ with rfl | hlt
  · exact hn hb
  · have := own_order_left h.anti h.ok h.na h.ha hb.1 hlt hb.2
      (fun h' => hn ⟨by have := hb.1; omega, h'⟩)
    omega

/-- A row neither covered nor in the hole is extracted, hence not beaten. -/
theorem AH.uncov (h : AH nr nc F e Act own X a) (hM : TMem s nr F e own X H Q nm rm) {ρ : ℕ}
    (hH : ¬ H ρ) (hc : ∀ z < s, tPr Q nm z = 1 → ¬ (z ≤ ρ ∧ ρ ≤ tEnd Q nm z)) :
    ¬ Bt nr F e own a ρ := by
  intro hb
  have hX : X ρ := by
    by_contra hX
    obtain ⟨z, hz, hp, h1, h2⟩ := (hM.cover ρ hb.1).1 ⟨hX, hH⟩
    exact hc z hz hp ⟨h1, h2⟩
  exact h.nx ρ hb.1 hX hb

/-- Two beaten rows with only extracted rows between them are adjacent. -/
theorem AH.adj (h : AH nr nc F e Act own X a) {ρ₁ ρ₂ : ℕ} (h1 : Bt nr F e own a ρ₁)
    (h2 : Bt nr F e own a ρ₂) (h12 : ρ₁ < ρ₂)
    (hgap : ∀ ρ, ρ₁ < ρ → ρ < ρ₂ → ¬ Bt nr F e own a ρ) : ρ₂ = ρ₁ + 1 := by
  by_contra hne
  exact hgap (ρ₁ + 1) (by omega) (by omega) (h.conv h1 h2 (by omega) (by omega))

end beat

/-! ### The state of an activation -/

/-- The registers changed by `act`. -/
def AcN (r : ℕ) : Prop :=
  TPn r ∨ (200 ≤ r ∧ r < 203) ∨ (221 ≤ r ∧ r < 229) ∨ (261 ≤ r ∧ r < 280)

/-- The real registers changed by `act`. -/
def AcR (r : ℕ) : Prop := TPr r ∨ r = 260

/-- **The state of an activation** in the half block `k` of the level `2 ^ T` (query structure at
`B`, triplets at `Q`), from the configuration `c₀`: the context, the entries `e` of the sources,
the frame. -/
structure AS (P : Prm) (B Q T k a : ℕ) (e : ℕ → ℝ) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  env : Env P B (2 ^ T) k c
  tc : TCtx Q (2 ^ T) c
  ra : c.nreg 260 = a
  ks : k * 2 ^ T < P.b
  hB : B + 8 * 2 ^ T ≤ P.W
  hQ : Q + 16 * 2 ^ T ≤ P.W
  hQw : P.wb ≤ Q
  hBQ : Q + 16 * 2 ^ T ≤ B
  qr : QReady P B (2 ^ T) k c.nmem
  eok : ∀ σ < hbNc P.b (2 ^ T) k, e σ = c.rmem (P.db + (sib k * 2 ^ T + σ))
  fr : Fr AcN AcR c₀ c
  nm : ∀ x, (x < Q ∨ Q + 16 * 2 ^ T ≤ x) → c.nmem x = c₀.nmem x
  rm : ∀ x, (x < Q ∨ Q + 8 * 2 ^ T ≤ x) → c.rmem x = c₀.rmem x

variable {P : Prm} {I : Input}

lemma src_lt_N (hL : Lay P) {s k σ : ℕ} (hσ : σ < hbNc P.b s k) : sib k * s + σ < P.N := by
  have := hL.bN; unfold hbNc at hσ; omega

/-- **The state after a routine** that changes registers of the activation only, and the memory
of the triplets only. -/
theorem AS.next (hL : Lay P) {B Q T k a : ℕ} {e : ℕ → ℝ} {c₀ c c' : Config}
    (h : AS P B Q T k a e c₀ c) (hw : WordsBounded P.W c') {M MR : ℕ → Prop} (hF : Fr M MR c c')
    (hM : ∀ r, M r → AcN r) (hMR : ∀ r, MR r → AcR r)
    (hn : ∀ x, (x < Q ∨ Q + 16 * 2 ^ T ≤ x) → c'.nmem x = c.nmem x)
    (hr : ∀ x, (x < Q ∨ Q + 8 * 2 ^ T ≤ x) → c'.rmem x = c.rmem x) : AS P B Q T k a e c₀ c' := by
  have := hL.m5; have := hL.m6; have hQw := h.hQw
  have nr : ∀ r, 100 ≤ r → r < 126 → c'.nreg r = c.nreg r := fun r h1 h2 =>
    hF.n r fun h' => by have := hM r h'; unfold AcN TPn at this; omega
  refine ⟨hw, h.env.of hL nr (fun x hx => hn x (Or.inl (by omega)))
    (fun x hx => hr x (Or.inl (by omega))), h.tc.of fun r h1 h2 => hF.n r fun h' => by
      have := hM r h'; unfold AcN TPn at this; omega, ?_, h.ks, h.hB, h.hQ, h.hQw, h.hBQ,
    h.qr.congr fun x h1 => hn x (by have := h.hBQ; omega), fun σ hσ => ?_,
    h.fr.trans hF (fun r h => h) hM (fun r h => h) hMR, fun x hx => (hn x hx).trans (h.nm x hx),
    fun x hx => (hr x hx).trans (h.rm x hx)⟩
  · rw [hF.n 260 fun h' => by have := hM 260 h'; unfold AcN TPn at this; omega]; exact h.ra
  · have := src_lt_N hL hσ
    rw [hr _ (Or.inl (by omega))]; exact h.eok σ hσ

/-- An activation state is the start of a new one. -/
theorem AS.rebase {B Q T k a : ℕ} {e : ℕ → ℝ} {c₀ c : Config} (h : AS P B Q T k a e c₀ c) :
    AS P B Q T k a e c c :=
  ⟨h.wb, h.env, h.tc, h.ra, h.ks, h.hB, h.hQ, h.hQw, h.hBQ, h.qr, h.eok, Fr.refl c,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem AS.trans {B Q T k a : ℕ} {e : ℕ → ℝ} {c₀ c₁ c : Config} (h₁ : AS P B Q T k a e c₀ c₁)
    (h : AS P B Q T k a e c₁ c) : AS P B Q T k a e c₀ c :=
  ⟨h.wb, h.env, h.tc, h.ra, h.ks, h.hB, h.hQ, h.hQw, h.hBQ, h.qr, h.eok,
    h₁.fr.trans h.fr (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h),
    fun x hx => (h.nm x hx).trans (h₁.nm x hx), fun x hx => (h.rm x hx).trans (h₁.rm x hx)⟩

/-- The entry of the matrix of the half block. -/
abbrev EE (P : Prm) (T k : ℕ) (e : ℕ → ℝ) (ρ σ : ℕ) : ℝ := e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ

/-- **The beat test.** -/
theorem bt_exec (hL : Lay P) {B Q T k a : ℕ} {e : ℕ → ℝ} {c₀ : Config} (c : Config)
    (h : AS P B Q T k a e c₀ c) {ρ u : ℕ} (h274 : c.nreg 274 = ρ) (hρ : ρ < 2 ^ T)
    (h275 : c.nreg 275 = u) (hu : u < hbNc P.b (2 ^ T) k) (ha : a < hbNc P.b (2 ^ T) k) :
    ∃ c' k', Exec I P.W bt c c' k' ∧ k' ≤ 40 ∧
      c'.nreg 273 = (if EE P T k e ρ a < EE P T k e ρ u then 1 else 0) ∧
      Fr (fun r => (130 ≤ r ∧ r < 134) ∨ r = 273) (fun r => r = 130 ∨ r = 131 ∨ r = 260) c c' ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem := by
  have hc := h.wb
  have hE := h.env
  have hka : sib k * 2 ^ T + a < P.b := by unfold hbNc at ha; omega
  have hku : sib k * 2 ^ T + u < P.b := by unfold hbNc at hu; omega
  unfold bt
  refine spec_seq ?_
  exec_block
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have k1 : ∀ r, r ≠ 130 → r ≠ 131 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  refine spec_seq ?_
  refine spec_use (evE_exec (I := I) hL c₁ hw₁ (hE.g.of fun r h1 h2 => k1 r (by omega) (by omega))
    (hE.h.of fun r h1 h2 => k1 r (by omega) (by omega))
    (hE.d.of hL (fun a _ => by rw [← hc₁]) (fun a _ => by rw [← hc₁])) h.ks
    (by rw [← hc₁]; config_simp; omega) (by rw [← hc₁]; config_simp; rw [h.ra]; exact hka)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨e130, hK₂, hR₂, hN₂, hM₂, hO₂⟩
  rw [← hc₁] at e130 hN₂ hM₂ hO₂; config_simp at e130; config_simp at hN₂
  config_simp at hM₂; config_simp at hO₂
  rw [h274, h.ra, ← h.eok a ha] at e130
  have k2 : ∀ r, (r < 130 ∨ 134 ≤ r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hK₂ r (by omega)]; exact k1 r (by omega) (by omega)
  refine spec_seq ?_
  exec_block
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have k3 : ∀ r, (r < 130 ∨ 134 ≤ r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [← hc₃]; config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact k2 r hr
  refine spec_seq ?_
  refine spec_use (evE_exec (I := I) hL c₃ hw₃ (hE.g.of fun r h1 h2 => k3 r (by omega))
    (hE.h.of fun r h1 h2 => k3 r (by omega))
    (hE.d.of hL (fun a _ => by rw [← hc₃]; config_simp; rw [hN₂])
      (fun a _ => by rw [← hc₃]; config_simp; rw [hM₂]))
    h.ks (by rw [← hc₃]; config_simp; rw [k2 274 (by omega), h274]; omega)
    (by rw [← hc₃]; config_simp; rw [k2 275 (by omega), h275]; exact hku)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨e130', hK₄, hR₄, hN₄, hM₄, hO₄⟩
  rw [← hc₃] at e130' hN₄ hM₄ hO₄ hR₄; config_simp at e130'; config_simp at hN₄
  config_simp at hM₄; config_simp at hO₄
  rw [k2 274 (by omega), k2 275 (by omega), h274, h275, hM₂,
    ← h.eok u hu] at e130'
  have r260 : c₄.rreg 260 = EE P T k e ρ a := by
    rw [hR₄ 260 (by omega)]; config_simp; rw [e130]
  have k4 : ∀ r, (r < 130 ∨ 134 ≤ r) → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hK₄ r (by omega)]; exact k3 r hr
  have kR : ∀ r, ¬ (r = 130 ∨ r = 131 ∨ r = 260) → c₄.rreg r = c.rreg r := fun r hr => by
    rw [hR₄ r (by omega)]; config_simp; rw [upd_other _ _ _ (by omega), hR₂ r (by omega)]
    rw [← hc₁]
  have hfr : ∀ v, Fr (fun r => (130 ≤ r ∧ r < 134) ∨ r = 273) (fun r => r = 130 ∨ r = 131 ∨ r = 260)
      c ({ c₄ with nreg := upd c₄.nreg 273 v } : Config) := fun v =>
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact k4 r (by omega),
      fun r hr => by config_simp; exact kR r hr, by config_simp; rw [hO₄, hO₂]⟩
  by_cases hlt : EE P T k e ρ a < EE P T k e ρ u
  · refine spec_ifLtR_true (by rw [r260, e130']; exact hlt) ?_
    refine spec_instr (Exec.copyN hw₄ 273 110) fun _ => ?_
    refine ⟨by omega, ?_, hfr _, by config_simp; rw [hN₄, hN₂], by config_simp; rw [hM₄, hM₂]⟩
    config_simp; rw [k4 110 (by omega), hE.g.r110, iteT hlt]
  · refine spec_ifLtR_false (by rw [r260, e130']; exact hlt) ?_
    refine spec_instr (Exec.copyN hw₄ 273 117) fun _ => ?_
    refine ⟨by omega, ?_, hfr _, by config_simp; rw [hN₄, hN₂], by config_simp; rw [hM₄, hM₂]⟩
    config_simp; rw [k4 117 (by omega), hE.g.r117, iteF hlt]

/-! ### The binary searches -/

/-- The state of a binary search: `r269 < r270` in `[lo₀, hi₀]`, the row `r269` satisfies `q`
exactly when not `true`, and `r270` satisfies it (`q ρ`: `a` beats `ρ` exactly when `d`). -/
structure IBq (P : Prm) (B Q T k a : ℕ) (e : ℕ → ℝ) (c₀ c₁ : Config) (u lo₀ hi₀ : ℕ)
    (d : Bool) (c : Config) : Prop where
  as : AS P B Q T k a e c₀ c
  keep : ∀ r, ¬ ((130 ≤ r ∧ r < 134) ∨ (269 ≤ r ∧ r < 275) ∨ r = 276) → c.nreg r = c₁.nreg r
  keepR : ∀ r, ¬ (r = 130 ∨ r = 131 ∨ r = 260) → c.rreg r = c₁.rreg r
  nm : c.nmem = c₁.nmem
  rm : c.rmem = c₁.rmem
  out : c.output = c₁.output
  lt : c.nreg 269 < c.nreg 270
  r276 : c.nreg 276 = c.nreg 269 + 1
  lo : ¬ (EE P T k e (c.nreg 269) a < EE P T k e (c.nreg 269) u ↔ d = true)
  hi : EE P T k e (c.nreg 270) a < EE P T k e (c.nreg 270) u ↔ d = true
  lob : lo₀ ≤ c.nreg 269
  hib : c.nreg 270 ≤ hi₀

lemma lg_half_sub {lo hi mid : ℕ} (h : lo + 1 < hi) (hm : mid = (lo + hi) / 2) :
    lg (hi - mid - 1) + 1 ≤ lg (hi - lo - 1) ∧ lg (mid - lo - 1) + 1 ≤ lg (hi - lo - 1) := by
  have e := lg_pos (show 1 ≤ hi - lo - 1 by omega)
  have a1 : lg (hi - mid - 1) ≤ lg ((hi - lo - 1) / 2) := lg_mono (by omega)
  have a2 : lg (mid - lo - 1) ≤ lg ((hi - lo - 1) / 2) := lg_mono (by omega)
  omega

theorem bsBody_exec (hL : Lay P) {B Q T k a u lo₀ hi₀ : ℕ} {e : ℕ → ℝ} {d : Bool}
    {c₀ c₁ : Config} (hu : u < hbNc P.b (2 ^ T) k) (ha : a < hbNc P.b (2 ^ T) k)
    (h275 : c₁.nreg 275 = u) (hhi : hi₀ < 2 ^ T) (c : Config)
    (hI : IBq P B Q T k a e c₀ c₁ u lo₀ hi₀ d c) (hlt : c.nreg 276 < c.nreg 270) :
    ∃ c' k', Exec I P.W (bsBody d) c c' k' ∧ IBq P B Q T k a e c₀ c₁ u lo₀ hi₀ d c' ∧
      50 * lg (c'.nreg 270 - c'.nreg 269 - 1) + k' + 2 ≤ 50 * lg (c.nreg 270 - c.nreg 269 - 1) := by
  have hc := hI.as.wb
  have hG := hI.as.env.g
  generalize hlo : c.nreg 269 = lo at hI hlt
  generalize hhv : c.nreg 270 = hi at hI hlt
  have hlt' : lo + 1 < hi := by rw [hI.r276, hlo] at hlt; exact hlt
  have hlb := hI.lob; have hhb := hI.hib
  rw [hlo] at hlb; rw [hhv] at hhb
  have hloq := hI.lo; have hhiq := hI.hi
  rw [hlo] at hloq; rw [hhv] at hhiq
  have hQ := hI.as.hQ
  unfold bsBody
  refine spec_seq ?_
  exec_block
  · rw [hlo, hhv]; omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have f274 : c₂.nreg 274 = (lo + hi) / 2 := by rw [← hc₂]; config_simp; rw [hlo, hhv, hG.r111]
  have f271 : c₂.nreg 271 = (lo + hi) / 2 := by rw [← hc₂]; config_simp; rw [hlo, hhv, hG.r111]
  have k2 : ∀ r, r ≠ 271 → r ≠ 274 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₂]; config_simp; upd_tac
  have hAS₂ : AS P B Q T k a e c₀ c₂ := hI.as.next hL hw₂
    (M := fun r => r = 271 ∨ r = 274) (MR := fun _ => False)
    ⟨fun r hr => k2 r (by omega) (by omega), fun r _ => by rw [← hc₂], by rw [← hc₂]⟩
    (fun r h => by unfold AcN; omega) (fun r h => h.elim) (fun x _ => by rw [← hc₂])
    (fun x _ => by rw [← hc₂])
  refine spec_seq ?_
  refine spec_use (bt_exec (I := I) hL c₂ hAS₂ f274 (by omega)
    (by rw [k2 275 (by omega) (by omega), hI.keep 275 (by omega)]; exact h275) hu ha) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨h273, hF₃, hN₃, hM₃⟩
  have hAS₃ := hAS₂.next hL hw₃ hF₃ (fun r h => by unfold AcN TPn; omega)
    (fun r h => by unfold AcR TPr; omega) (fun x _ => by rw [hN₃]) (fun x _ => by rw [hM₃])
  have k3 : ∀ r, ¬ ((130 ≤ r ∧ r < 134) ∨ r = 273) → r ≠ 271 → r ≠ 274 →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 => by rw [hF₃.n r h1, k2 r h2 h3]
  have f271' : c₃.nreg 271 = (lo + hi) / 2 := by rw [hF₃.n 271 (by omega), f271]
  have k110 : c₃.nreg 110 = 1 := by rw [k3 110 (by omega) (by omega) (by omega), hG.r110]
  have k117 : c₃.nreg 117 = 0 := by rw [k3 117 (by omega) (by omega) (by omega), hG.r117]
  generalize hm : (lo + hi) / 2 = mid at f271' h273
  have hmid : lo < mid ∧ mid < hi := by omega
  obtain ⟨lg1, lg2⟩ := lg_half_sub hlt' hm.symm
  -- the final increment, for a new start `lo'` and end `hi'`
  have fin : ∀ (c₄ : Config) (lo' hi' : ℕ), WordsBounded P.W c₄ → c₄.nreg 269 = lo' →
      c₄.nreg 270 = hi' → lo' < hi' → lo ≤ lo' → hi' ≤ hi →
      (¬ (EE P T k e lo' a < EE P T k e lo' u ↔ d = true)) →
      (EE P T k e hi' a < EE P T k e hi' u ↔ d = true) →
      (∀ r, r ≠ 269 → r ≠ 270 → c₄.nreg r = c₃.nreg r) → c₄.rreg = c₃.rreg →
      c₄.nmem = c₃.nmem → c₄.rmem = c₃.rmem → c₄.output = c₃.output →
      ∃ c' k', Exec I P.W (.instr (.addN 276 269 110)) c₄ c' k' ∧ k' ≤ 1 ∧
        IBq P B Q T k a e c₀ c₁ u lo₀ hi₀ d c' ∧ c'.nreg 269 = lo' ∧ c'.nreg 270 = hi' := by
    intro c₄ lo' hi' hw₄ h269 h270 hlt4 hl hh hq1 hq2 hK hR hN hM hO
    refine spec_instr (Exec.addN hw₄ 276 269 110 (by
      rw [h269, hK 110 (by omega) (by omega), k110]; omega)) fun hw₅ => ?_
    have hAS₄ : AS P B Q T k a e c₀ c₄ := hAS₃.next hL hw₄
      (M := fun r => r = 269 ∨ r = 270) (MR := fun _ => False)
      ⟨fun r hr => hK r (by omega) (by omega), fun r _ => by rw [hR], hO⟩
      (fun r h => by unfold AcN; omega) (fun r h => h.elim) (fun x _ => by rw [hN])
      (fun x _ => by rw [hM])
    have hAS₅ := hAS₄.next hL hw₅ (M := fun r => r = 276) (MR := fun _ => False)
      ⟨fun r hr => by config_simp; rw [upd_other _ _ _ hr], fun _ _ => rfl, rfl⟩
      (fun r h => by unfold AcN; omega) (fun r h => h.elim) (fun x _ => rfl) (fun x _ => rfl)
    refine ⟨le_rfl, ⟨hAS₅, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by config_simp; exact h269, by config_simp; exact h270⟩
    · config_simp
      rw [upd_other _ _ _ (by omega), hK r (by omega) (by omega),
        k3 r (by omega) (by omega) (by omega)]
      rw [← hlo, ← hhv] at *
      exact hI.keep r hr
    · config_simp; rw [hR, hF₃.r r hr, ← hc₂]; exact hI.keepR r hr
    · config_simp; rw [hN, hN₃, ← hc₂]; exact hI.nm
    · config_simp; rw [hM, hM₃, ← hc₂]; exact hI.rm
    · config_simp; rw [hO, hF₃.o, ← hc₂]; exact hI.out
    · config_simp; rw [h269, h270]; exact hlt4
    · config_simp; rw [h269, hK 110 (by omega) (by omega), k110]
    · config_simp; rw [h269]; exact hq1
    · config_simp; rw [h270]; exact hq2
    · config_simp; rw [h269]; omega
    · config_simp; rw [h270]; omega
  have k270 : c₃.nreg 270 = hi := by
    rw [k3 270 (by omega) (by omega) (by omega), hhv]
  have k269 : c₃.nreg 269 = lo := by
    rw [k3 269 (by omega) (by omega) (by omega), hlo]
  refine spec_seq ?_
  by_cases hb : EE P T k e mid a < EE P T k e mid u
  · rw [iteT hb] at h273
    refine spec_ifLtN_true (by rw [k117, h273]; omega) ?_
    cases d
    · refine spec_instr (Exec.copyN hw₃ 269 271) fun hw₄ => ?_
      obtain ⟨c', k', ex, hk', hI', e1, e2⟩ := fin _ mid hi hw₄ (by config_simp; rw [f271'])
        (by config_simp; rw [k270]) (by omega) (by omega) le_rfl (by simp [hb]) hhiq
        (fun r h1 h2 => by config_simp; rw [upd_other _ _ _ h1]) rfl rfl rfl rfl
      exact ⟨c', k', ex, hI', by rw [e1, e2]; omega⟩
    · refine spec_instr (Exec.copyN hw₃ 270 271) fun hw₄ => ?_
      obtain ⟨c', k', ex, hk', hI', e1, e2⟩ := fin _ lo mid hw₄ (by config_simp; rw [k269])
        (by config_simp; rw [f271']) (by omega) le_rfl (by omega) hloq (by simp [hb])
        (fun r h1 h2 => by config_simp; rw [upd_other _ _ _ h2]) rfl rfl rfl rfl
      exact ⟨c', k', ex, hI', by rw [e1, e2]; omega⟩
  · rw [iteF hb] at h273
    refine spec_ifLtN_false (by rw [k117, h273]; omega) ?_
    cases d
    · refine spec_instr (Exec.copyN hw₃ 270 271) fun hw₄ => ?_
      obtain ⟨c', k', ex, hk', hI', e1, e2⟩ := fin _ lo mid hw₄ (by config_simp; rw [k269])
        (by config_simp; rw [f271']) (by omega) le_rfl (by omega) hloq (by simp [hb])
        (fun r h1 h2 => by config_simp; rw [upd_other _ _ _ h2]) rfl rfl rfl rfl
      exact ⟨c', k', ex, hI', by rw [e1, e2]; omega⟩
    · refine spec_instr (Exec.copyN hw₃ 269 271) fun hw₄ => ?_
      obtain ⟨c', k', ex, hk', hI', e1, e2⟩ := fin _ mid hi hw₄ (by config_simp; rw [f271'])
        (by config_simp; rw [k270]) (by omega) (by omega) le_rfl (by simp [hb]) hhiq
        (fun r h1 h2 => by config_simp; rw [upd_other _ _ _ h1]) rfl rfl rfl rfl
      exact ⟨c', k', ex, hI', by rw [e1, e2]; omega⟩

/-- **A binary search**: from `lo < hi` in `[lo₀, hi₀]` with the row `hi` (and not `lo`)
satisfying `q`, it ends with `lo + 1 = hi`, within `50 T + 2` steps. -/
theorem bsLoop_exec (hL : Lay P) {B Q T k a u lo₀ hi₀ : ℕ} {e : ℕ → ℝ} (d : Bool)
    {c₀ : Config} (c₁ : Config) (hAS : AS P B Q T k a e c₀ c₁) (hu : u < hbNc P.b (2 ^ T) k)
    (ha : a < hbNc P.b (2 ^ T) k) (h275 : c₁.nreg 275 = u) (hhi : hi₀ < 2 ^ T)
    (hlt : c₁.nreg 269 < c₁.nreg 270) (h276 : c₁.nreg 276 = c₁.nreg 269 + 1)
    (hlo : ¬ (EE P T k e (c₁.nreg 269) a < EE P T k e (c₁.nreg 269) u ↔ d = true))
    (hhq : EE P T k e (c₁.nreg 270) a < EE P T k e (c₁.nreg 270) u ↔ d = true)
    (hlb : lo₀ ≤ c₁.nreg 269) (hhb : c₁.nreg 270 ≤ hi₀) :
    ∃ c' k', Exec I P.W (.whileLtN 276 270 (bsBody d)) c₁ c' k' ∧ k' ≤ 50 * T + 2 ∧
      IBq P B Q T k a e c₀ c₁ u lo₀ hi₀ d c' ∧ c'.nreg 269 + 1 = c'.nreg 270 := by
  obtain ⟨c', k', ex, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := P.W) (a := 276)
    (b := 270) (body := bsBody d) (IBq P B Q T k a e c₀ c₁ u lo₀ hi₀ d)
    (fun c => 50 * lg (c.nreg 270 - c.nreg 269 - 1)) (fun _ h => h.as.wb)
    (fun c hI hlt => bsBody_exec hL hu ha h275 hhi c hI hlt)
    ⟨hAS, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, hlt, h276, hlo, hhq, hlb, hhb⟩
  refine ⟨c', k', ex, ?_, hI, by have := hI.lt; have := hI.r276; omega⟩
  have := lg_lt_pow (show c₁.nreg 270 - c₁.nreg 269 - 1 < 2 ^ T by omega)
  omega

/-! ### The steps of the walks inside an activation -/

/-- The owner `r275` and the last row `r277` of the start `r263`. -/
theorem ldCur_exec {B Q T k a : ℕ} {e : ℕ → ℝ} {c₀ : Config} (c : Config)
    (h : AS P B Q T k a e c₀ c) {x : ℕ} (h263 : c.nreg 263 = x) (hx : x < 2 ^ T) :
    ∃ c' k', Exec I P.W ldCur c c' k' ∧ k' ≤ 6 ∧ c'.nreg 275 = tOwn Q c.nmem x ∧
      c'.nreg 277 = tEnd Q c.nmem x ∧
      Fr (fun r => r = 272 ∨ r = 275 ∨ r = 277) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  have hc := h.wb
  have g := h.env.g
  have g208 := h.tc.r208
  have hQ := h.hQ
  have e8 : x * 8 + Q = Q + 8 * x := by ring
  unfold ldCur
  exec_block
  · rw [h263, g.r118]; omega
  · config_simp; rw [h263, g.r118, g208]; omega
  · config_simp; rw [h263, g.r118, g208, g.r110]; omega
  · config_simp; rw [h263, g.r118, g208, g.r111]; omega
  refine ⟨by omega, ?_, ?_, ⟨fun r hr => ?_, fun _ _ => rfl, rfl⟩, rfl, rfl⟩
  · config_simp; rw [h263, g.r118, g208, g.r110, e8]; rfl
  · config_simp; rw [h263, g.r118, g208, g.r111, e8]; rfl
  · config_simp; upd_tac

/-- The rows between the last start `p` before `z` (all rows before `z`, if there is none) and
`z` are not covered. -/
lemma uncov_before {s nr : ℕ} {F : ℕ → ℕ → ℝ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X H : ℕ → Prop}
    {Q : ℕ} {nm : ℕ → ℕ} {rm : ℕ → ℝ} (hM : TMem s nr F e own X H Q nm rm) {z p : ℕ}
    (hp : p = s ∨ Pv Q s z nm p) (hmax : ∀ y, Pv Q s z nm y → p ≠ s ∧ y ≤ p) {ρ : ℕ}
    (hρ : ρ < z) (hρp : p = s ∨ tEnd Q nm p < ρ) :
    ∀ y < s, tPr Q nm y = 1 → ¬ (y ≤ ρ ∧ ρ ≤ tEnd Q nm y) := by
  intro y hy hpy ⟨h1, h2⟩
  obtain ⟨hps, hyp⟩ := hmax y ⟨hy, hpy, by omega⟩
  rcases hρp with h | h
  · exact hps h
  rcases hp with h' | ⟨hp1, hp2, -⟩
  · exact hps h'
  rcases Nat.eq_or_lt_of_le hyp with rfl | hlt
  · omega
  · have := hM.disj y p hlt hp1 hpy hp2; have := (hM.st p hp1 hp2).1; omega

/-- The rows between the end of a start `x` and the first start `n` after it (all rows after `x`,
if there is none) are not covered. -/
lemma uncov_after {s Q : ℕ} {nm : ℕ → ℕ} {z n : ℕ}
    (hmin : ∀ y, Nx Q s z nm y → n ≤ y) {ρ : ℕ} (hρ : z < ρ) (hρn : ρ < n)
    (hz : ∀ y < s, tPr Q nm y = 1 → y ≤ z → tEnd Q nm y ≤ z) :
    ∀ y < s, tPr Q nm y = 1 → ¬ (y ≤ ρ ∧ ρ ≤ tEnd Q nm y) := by
  intro y hy hpy ⟨h1, h2⟩
  by_cases hyz : z < y
  · have := hmin y ⟨hy, hpy, hyz⟩; omega
  · have := hz y hy hpy (by omega); omega

/-- The registers changed by a walk. -/
def LWn (r : ℕ) : Prop :=
  TPn r ∨ (200 ≤ r ∧ r < 203) ∨ (221 ≤ r ∧ r < 229) ∨ r = 263 ∨ r = 264 ∨ r = 265 ∨
    (268 ≤ r ∧ r < 278)

/-- The registers changed by a step of a walk that goes on. -/
def LWc (r : ℕ) : Prop :=
  TPn r ∨ (221 ≤ r ∧ r < 229) ∨ r = 263 ∨ r = 264 ∨ r = 265 ∨ (270 ≤ r ∧ r < 278)

/-- The registers changed by the left walk. -/
def LWl (r : ℕ) : Prop :=
  TPn r ∨ (200 ≤ r ∧ r < 203) ∨ (221 ≤ r ∧ r < 229) ∨ r = 263 ∨ r = 264 ∨ (268 ≤ r ∧ r < 278)

/-- The registers changed by a step of the left walk that goes on. -/
def LWm (r : ℕ) : Prop :=
  TPn r ∨ (221 ≤ r ∧ r < 229) ∨ r = 263 ∨ r = 264 ∨ (270 ≤ r ∧ r < 278)

/-- Inclusions of register sets, by unfolding. -/
macro "fr_incl" : term =>
  `(fun r h => by
    clear * - h; simp only [AcN, AcR, TPn, TPr, ExP, LWn, LWc, LWl, LWm] at h ⊢; omega)

section steps

variable (hL : Lay P) {B Q T k a : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X H : ℕ → Prop} {c₀ : Config}
include hL

/-- `tDel` inside an activation. -/
theorem tDelA (c : Config) (h : AS P B Q T k a e c₀ c) {x : ℕ} (h230 : c.nreg 230 = x)
    (hx : x < 2 ^ T) (hM : BM P T k e own X H Q c.nmem c.rmem) (hpx : tPr Q c.nmem x = 1) :
    ∃ c' k', Exec I P.W tDel c c' k' ∧ k' ≤ 49 * T + 7 ∧ AS P B Q T k a e c₀ c' ∧
      BM P T k e own X (fun ρ => H ρ ∨ (x ≤ ρ ∧ ρ ≤ tEnd Q c.nmem x)) Q c'.nmem c'.rmem ∧
      nst Q (2 ^ T) c'.nmem + 1 = nst Q (2 ^ T) c.nmem ∧ Fr TPn TPr c c' := by
  obtain ⟨c', k', ex, hk, hM', hpr, hF, hn, hr⟩ := tDel_exec (I := I) c h.wb h.env.g h.tc h.hQ
    h.env.h.r121 h230 hx hM hpx
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl fr_incl (fun x hx => hn x (by omega))
    (fun x _ => by rw [hr]),
    hM', nst_clr hx hpx hpr, hF⟩

/-- `tPut` inside an activation. -/
theorem tPutA (c : Config) (h : AS P B Q T k a e c₀ c) {σ j1 j2 : ℕ}
    (hM : BM P T k e own X H Q c.nmem c.rmem) (h200 : c.nreg 200 = σ)
    (hσ : σ < hbNc P.b (2 ^ T) k) (h201 : c.nreg 201 = j1) (h202 : c.nreg 202 = j2)
    (hj : j1 < j2) (hj2 : j2 ≤ hbNr P.b (2 ^ T) k) (hH : ∀ ρ, j1 ≤ ρ → ρ < j2 → H ρ)
    (ho : ∀ ρ, j1 ≤ ρ → ρ < j2 → own ρ = σ) :
    ∃ c' k', Exec I P.W tPut c c' k' ∧ k' ≤ rmqCost T + 49 * T + 20 ∧ AS P B Q T k a e c₀ c' ∧
      BM P T k e own X (fun ρ => H ρ ∧ ¬ (j1 ≤ ρ ∧ ρ < j2)) Q c'.nmem c'.rmem ∧
      nst Q (2 ^ T) c'.nmem = nst Q (2 ^ T) c.nmem + 1 ∧ Fr TPn TPr c c' := by
  have hnr := hM.nr_le
  have hpj : tPr Q c.nmem j1 ≠ 1 := fun hp =>
    (hM.not_hole (by omega) hp le_rfl (hM.st j1 (by omega) hp).1).2 (hH j1 le_rfl hj)
  obtain ⟨c', k', ex, hk, hM', hpr, hF, hn, hr⟩ := tPut_exec (I := I) hL c h.wb h.env h.tc h.hB
    h.hQ h.qr hM (h.eok σ hσ) h200 hσ h201 h202 hj hj2 hH ho
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl fr_incl (fun x hx => hn x (by omega))
    hr, hM',
    nst_set (by omega) hpj hpr, hF⟩

/-- `tPv` inside an activation. -/
theorem tPvA (c : Config) (h : AS P B Q T k a e c₀ c) {z : ℕ} (h221 : c.nreg 221 = z)
    (hM : BM P T k e own X H Q c.nmem c.rmem) :
    ∃ c' k', Exec I P.W tPv c c' k' ∧ k' ≤ srchCost T ∧ AS P B Q T k a e c₀ c' ∧
      (c'.nreg 222 = 2 ^ T ∨ Pv Q (2 ^ T) z c.nmem (c'.nreg 222)) ∧
      (∀ y, Pv Q (2 ^ T) z c.nmem y → c'.nreg 222 ≠ 2 ^ T ∧ y ≤ c'.nreg 222) ∧
      Fr (fun r => 222 ≤ r ∧ r < 229) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  obtain ⟨c', k', ex, hk, h1, h2, hK, hR, hN, hM', hO⟩ := tPv_exec (I := I) c h.wb h.env.g h.tc
    h.hQ h.env.h.r121 h221 hM.pr01 hM.wl
  have hF : Fr (fun r => 222 ≤ r ∧ r < 229) (fun _ => False) c c' :=
    ⟨fun r hr => hK r (by omega), fun r _ => by rw [hR], hO⟩
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl (fun _ h => False.elim h)
    (fun x _ => by rw [hN]) (fun x _ => by rw [hM']), h1, h2, hF, hN, hM'⟩

/-- `tNx` inside an activation. -/
theorem tNxA (c : Config) (h : AS P B Q T k a e c₀ c) {z : ℕ} (h221 : c.nreg 221 = z)
    (hM : BM P T k e own X H Q c.nmem c.rmem) :
    ∃ c' k', Exec I P.W tNx c c' k' ∧ k' ≤ srchCost T ∧ AS P B Q T k a e c₀ c' ∧
      (c'.nreg 222 = 2 ^ T ∨ Nx Q (2 ^ T) z c.nmem (c'.nreg 222)) ∧
      (∀ y, Nx Q (2 ^ T) z c.nmem y → c'.nreg 222 ≤ y) ∧
      Fr (fun r => 222 ≤ r ∧ r < 229) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  obtain ⟨c', k', ex, hk, h1, h2, hK, hR, hN, hM', hO⟩ := tNx_exec (I := I) c h.wb h.env.g h.tc
    h.hQ h.env.h.r121 h221 hM.pr01 hM.wl
  have hF : Fr (fun r => 222 ≤ r ∧ r < 229) (fun _ => False) c c' :=
    ⟨fun r hr => hK r (by omega), fun r _ => by rw [hR], hO⟩
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl (fun _ h => False.elim h)
    (fun x _ => by rw [hN]) (fun x _ => by rw [hM']), h1, h2, hF, hN, hM'⟩

/-- The beat test inside an activation. -/
theorem btA (c : Config) (h : AS P B Q T k a e c₀ c) {ρ u : ℕ} (h274 : c.nreg 274 = ρ)
    (hρ : ρ < 2 ^ T) (h275 : c.nreg 275 = u) (hu : u < hbNc P.b (2 ^ T) k)
    (ha : a < hbNc P.b (2 ^ T) k) :
    ∃ c' k', Exec I P.W bt c c' k' ∧ k' ≤ 40 ∧ AS P B Q T k a e c₀ c' ∧
      c'.nreg 273 = (if EE P T k e ρ a < EE P T k e ρ u then 1 else 0) ∧
      Fr (fun r => (130 ≤ r ∧ r < 134) ∨ r = 273) (fun r => r = 130 ∨ r = 131 ∨ r = 260) c c' ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem := by
  obtain ⟨c', k', ex, hk, h1, hF, hN, hM⟩ := bt_exec (I := I) hL c h h274 hρ h275 hu ha
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl fr_incl (fun x _ => by rw [hN])
    (fun x _ => by rw [hM]), h1, hF, hN, hM⟩

/-- `ldCur` inside an activation. -/
theorem ldCurA (c : Config) (h : AS P B Q T k a e c₀ c) {x : ℕ} (h263 : c.nreg 263 = x)
    (hx : x < 2 ^ T) :
    ∃ c' k', Exec I P.W ldCur c c' k' ∧ k' ≤ 6 ∧ AS P B Q T k a e c₀ c' ∧
      c'.nreg 275 = tOwn Q c.nmem x ∧ c'.nreg 277 = tEnd Q c.nmem x ∧
      Fr (fun r => r = 272 ∨ r = 275 ∨ r = 277) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  obtain ⟨c', k', ex, hk, h1, h2, hF, hN, hM⟩ := ldCur_exec (I := I) c h h263 hx
  exact ⟨c', k', ex, hk, h.next hL ex.wb_right hF fr_incl (fun _ h => False.elim h)
    (fun x _ => by rw [hN]) (fun x _ => by rw [hM]), h1, h2, hF, hN, hM⟩

/-- A copy between natural registers of the activation. -/
theorem copyA (c : Config) (h : AS P B Q T k a e c₀ c) (d s' : ℕ) (hd : AcN d) :
    ∃ c' k', Exec I P.W (.instr (.copyN d s')) c c' k' ∧ k' ≤ 1 ∧ AS P B Q T k a e c₀ c' ∧
      c'.nreg d = c.nreg s' ∧ Fr (fun r => r = d) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  refine spec_instr (Exec.copyN h.wb d s') fun hw => ?_
  have hF : Fr (fun r => r = d) (fun _ => False) c
      ({ c with nreg := upd c.nreg d (c.nreg s') } : Config) :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ hr], fun _ _ => rfl, rfl⟩
  exact ⟨le_rfl, h.next hL hw hF (fun r hr => by rw [hr]; exact hd) (fun _ h => False.elim h)
    (fun _ _ => rfl) (fun _ _ => rfl), by config_simp, hF, rfl, rfl⟩

end steps

/-! ### The left walk -/

/-- `r` is not in a set of registers (by unfolding). -/
macro "fr_ne" : term =>
  `(by clear * -; beta_reduce; (try simp only [AcN, AcR, TPn, TPr, ExP, LWn, LWc, LWl, LWm]); omega)

/-- **A loop with a potential**, keeping the final potential: the cost and the final potential
together are at most the initial potential. -/
theorem whileLtN_pot {P' : Input} {W a b : ℕ} {body : Stmt} (Inv : Config → Prop)
    (Φ : Config → ℕ) (hI : ∀ c, Inv c → WordsBounded W c)
    (hbody : ∀ c, Inv c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P' W body c c' k ∧ Inv c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : Inv c) :
    ∃ c' k, Exec P' W (.whileLtN a b body) c c' k ∧ Inv c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega⟩

/-- The cost of a step of a walk that deletes a triplet. -/
def LD (T : ℕ) : ℕ := 70 * T + 140

/-- The cost of the last step of a walk. -/
def LF (T : ℕ) : ℕ := rmqCost T + 150 * T + 140

/-- The potential of a walk: the steps that remain. -/
noncomputable def wΦ (Q T : ℕ) (c : Config) : ℕ :=
  LD T * nst Q (2 ^ T) c.nmem + if c.nreg 268 = 1 then LF T else 0

section walk

variable {B Q T k a : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X : ℕ → Prop} {Act : ℕ → Prop}

local notation "Bt'" => Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a

/-- **The state of the left walk** (`r268 = 1` while it goes on): the hole `[r264, hy)` of beaten
rows; while it goes on, the current start `r263` (its last row beaten) ends just before the hole;
the rows before `β` are beaten exactly in the hole, from the hole on (all of them at the end). -/
structure ILW (P : Prm) (B Q T k a : ℕ) (e : ℕ → ℝ) (own : ℕ → ℕ) (X : ℕ → Prop) (β hy : ℕ)
    (c₀ c₁ c : Config) : Prop where
  as : AS P B Q T k a e c₀ c
  keep : ∀ r, ¬ LWn r → c.nreg r = c₁.nreg r
  ry : c.nreg 265 = hy
  mem : BM P T k e own X (fun ρ => c.nreg 264 ≤ ρ ∧ ρ < hy) Q c.nmem c.rmem
  hb : ∀ ρ, c.nreg 264 ≤ ρ → ρ < hy →
    Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ
  le : c.nreg 264 ≤ hy
  fl : c.nreg 268 = 0 ∨ c.nreg 268 = 1
  go : c.nreg 268 = 1 → c.nreg 263 < 2 ^ T ∧ tPr Q c.nmem (c.nreg 263) = 1 ∧
    c.nreg 264 = tEnd Q c.nmem (c.nreg 263) + 1 ∧ c.nreg 263 < β ∧
    Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a (tEnd Q c.nmem (c.nreg 263))
  da : ∀ ρ, (c.nreg 268 = 1 → c.nreg 264 ≤ ρ) → ρ < β →
    (Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ ↔ c.nreg 264 ≤ ρ ∧ ρ < hy)

theorem lwBody_exec (hL : Lay P) {β hy : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (c : Config) (hI : ILW P B Q T k a e own X β hy c₀ c₁ c) (hgo : c.nreg 117 < c.nreg 268) :
    ∃ c' k', Exec I P.W lwBody c c' k' ∧ ILW P B Q T k a e own X β hy c₀ c₁ c' ∧
      wΦ Q T c' + k' + 2 ≤ wΦ Q T c := by
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
  refine spec_seq ?_
  refine spec_use (ldCurA hL (I := I) c hAS hcv hcur) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f275, f277, hF₂, hN₂, hM₂⟩
  rw [huv] at f275; rw [hev] at f277
  refine spec_seq ?_
  refine spec_use (copyA hL (I := I) c₂ hAS₂ 274 263 fr_ne) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f274, hF₃, hN₃, hM₃⟩
  rw [hF₂.n 263 fr_ne, hcv] at f274
  refine spec_seq ?_
  refine spec_use (btA hL (I := I) c₃ hAS₃ f274 hcur (by rw [hF₃.n 275 fr_ne]; exact f275) hu ha) ?_
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
  · -- delete the current triplet
    rw [iteT hb] at f273
    refine spec_ifLtN_true (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hBcur : Bt' cur := (hBc cur le_rfl hst.1).2 hb
    have hBin : ∀ ρ, cur ≤ ρ → ρ ≤ ee → Bt' ρ := fun ρ h1 h2 => hAH.conv hBcur hbe h1 h2
    unfold lwDel
    refine spec_seq ?_
    exec_block
    generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
    have hw₅ : WordsBounded P.W c₅ := hc₅ ▸ ‹_›
    have F5 : Fr (fun r => r = 264 ∨ r = 230) (fun _ => False) c₄ c₅ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₅]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₅], by rw [← hc₅]⟩
    have hAS₅ := hAS₄.next hL hw₅ F5 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₅]) (fun x _ => by rw [← hc₅])
    have N5 : c₅.nmem = c.nmem := by rw [← hc₅]; exact N4
    have R5 : c₅.rmem = c.rmem := by rw [← hc₅]; exact R4
    have f264 : c₅.nreg 264 = cur := by rw [← hc₅]; config_simp; rw [k4c]
    have f230 : c₅.nreg 230 = cur := by rw [← hc₅]; config_simp; rw [k4c]
    have f263 : c₅.nreg 263 = cur := by rw [F5.n 263 fr_ne, k4c]
    refine spec_seq ?_
    refine spec_use (tDelA hL (I := I) c₅ hAS₅ f230 hcur (by rw [N5, R5]; exact hM)
      (by rw [N5]; exact hpc)) ?_
    intro c₆ k₆ hk₆ hw₆ ⟨hAS₆, hM₆, hn₆, hF₆⟩
    rw [N5, hev] at hM₆
    have hM₆' : BM P T k e own X (fun ρ => cur ≤ ρ ∧ ρ < hy) Q c₆.nmem c₆.rmem :=
      hM₆.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₆.hole ρ (by omega))
    have F6 : Fr LWm AcR c c₆ := (F4.trans F5 (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)).trans hF₆ (fun r h => h) fr_incl (fun r h => h) fr_incl
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₆ hAS₆ 221 263 fr_ne) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f221, hF₇, hN₇, hM₇⟩
    rw [hF₆.n 263 fr_ne, f263] at f221
    refine spec_seq ?_
    refine spec_use (tPvA hL (I := I) c₇ hAS₇ f221 (by rw [hN₇, hM₇]; exact hM₆')) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hp1, hp2, hF₈, hN₈, hM₈⟩
    rw [hN₇] at hp1 hp2
    have N8 : c₈.nmem = c₆.nmem := by rw [hN₈, hN₇]
    have R8 : c₈.rmem = c₆.rmem := by rw [hM₈, hM₇]
    have F8 : Fr LWm AcR c c₈ := (F6.trans hF₇ (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)).trans hF₈ (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)
    have k8 : ∀ r, ¬ LWm r → c₈.nreg r = c.nreg r := F8.n
    have k8c : c₈.nreg 264 = cur := by
      rw [hF₈.n 264 fr_ne, hF₇.n 264 fr_ne, hF₆.n 264 fr_ne, f264]
    generalize hpe : c₈.nreg 222 = pred at hp1 hp2
    -- the rows from `cur` on are settled
    have daC : ∀ ρ, cur ≤ ρ → ρ < β → (Bt' ρ ↔ cur ≤ ρ ∧ ρ < hy) := fun ρ h1 h2 => by
      by_cases hρ : ρ ≤ ee
      · exact ⟨fun _ => ⟨h1, by omega⟩, fun _ => hBin ρ h1 hρ⟩
      · rw [hda ρ (fun _ => by omega) h2]; omega
    have hbC : ∀ ρ, cur ≤ ρ → ρ < hy → Bt' ρ := fun ρ h1 h2 => by
      by_cases hρ : ρ ≤ ee
      · exact hBin ρ h1 hρ
      · exact hhb ρ (by omega) h2
    have hn5 : nst Q (2 ^ T) c₅.nmem = nst Q (2 ^ T) c.nmem := by rw [N5]
    -- the final state when the walk stops
    have stop : ∀ (c' : Config), AS P B Q T k a e c₀ c' → Fr LWl AcR c c' →
        c'.nmem = c₆.nmem → c'.rmem = c₆.rmem → c'.nreg 268 = 0 → c'.nreg 264 = cur →
        (∀ ρ < cur, ¬ Bt' ρ) → ILW P B Q T k a e own X β hy c₀ c₁ c' := by
      intro c' hAS' hF' hN' hM' h268' h264' hlt
      refine ⟨hAS', fun r hr => (hF'.n r fun h => hr (by
        simp only [LWn, LWl, TPn] at h ⊢; omega)).trans (hI.keep r hr),
        by rw [hF'.n 265 fr_ne]; exact hI.ry, ?_, ?_, ?_, Or.inl h268',
        fun h => by omega, fun ρ _ hρ => ?_⟩
      · rw [h264', hN', hM']; exact hM₆'
      · rw [h264']; exact hbC
      · rw [h264']; omega
      · rw [h264']
        by_cases h1 : cur ≤ ρ
        · exact daC ρ h1 hρ
        · exact ⟨fun h => absurd h (hlt ρ (by omega)), fun h => by omega⟩
    by_cases hp : pred < 2 ^ T
    · have hpv : Pv Q (2 ^ T) cur c₆.nmem pred := hp1.resolve_left (by omega)
      obtain ⟨hp0, hpp, hpc'⟩ := hpv
      have hstp := hM₆'.st pred hp0 hpp
      generalize hepv : tEnd Q c₆.nmem pred = ep at hstp
      generalize hupv : tOwn Q c₆.nmem pred = up
      have hep : ep < cur := by
        by_contra hc
        exact (hM₆'.not_hole hp0 hpp (by omega) (by rw [hepv]; omega)).2 ⟨le_rfl, by omega⟩
      have hownp : own ep = up := by
        rw [← hupv]; exact hM₆'.own pred hp0 hpp ep hstp.1 (by rw [hepv])
      have hup : up < hbNc P.b (2 ^ T) k := by
        rw [← hownp]; exact hAH.ok.lt _ (hAH.ok.act ep (by omega))
      have hgap : ∀ ρ, ep < ρ → ρ < cur → ¬ Bt' ρ := fun ρ h1 h2 =>
        hAH.uncov hM₆' (fun h => by omega) (uncov_before hM₆' (Or.inr ⟨hp0, hpp, hpc'⟩)
          (fun y hy => hp2 y hy) h2 (Or.inr (by rw [hepv]; exact h1)))
      have hnx : ¬ X ep := (hM₆'.not_hole hp0 hpp hstp.1 (by rw [hepv])).1
      have hBep : Bt' ep ↔ EE P T k e ep a < EE P T k e ep up := by
        unfold Bt; rw [hownp]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      refine spec_ifLtN_true (by rw [hpe, k8 121 fr_ne, hAS.env.h.r121]; exact hp) ?_
      refine spec_seq ?_
      refine spec_use (copyA hL (I := I) c₈ hAS₈ 263 222 fr_ne) ?_
      intro c₉ k₉ hk₉ hw₉ ⟨hAS₉, f263', hF₉, hN₉, hM₉⟩
      rw [hpe] at f263'
      refine spec_seq ?_
      refine spec_use (ldCurA hL (I := I) c₉ hAS₉ f263' hp0) ?_
      intro c₁₀ k₁₀ hk₁₀ hw₁₀ ⟨hAS₁₀, f275', f277', hF₁₀, hN₁₀, hM₁₀⟩
      rw [hN₉, N8, hupv] at f275'; rw [hN₉, N8, hepv] at f277'
      refine spec_seq ?_
      refine spec_use (copyA hL (I := I) c₁₀ hAS₁₀ 274 277 fr_ne) ?_
      intro c₁₁ k₁₁ hk₁₁ hw₁₁ ⟨hAS₁₁, f274', hF₁₁, hN₁₁, hM₁₁⟩
      rw [f277'] at f274'
      refine spec_seq ?_
      refine spec_use (btA hL (I := I) c₁₁ hAS₁₁ f274' (by omega)
        (by rw [hF₁₁.n 275 fr_ne, f275']) hup ha) ?_
      intro c₁₂ k₁₂ hk₁₂ hw₁₂ ⟨hAS₁₂, f273', hF₁₂, hN₁₂, hM₁₂⟩
      have N12 : c₁₂.nmem = c₆.nmem := by rw [hN₁₂, hN₁₁, hN₁₀, hN₉, N8]
      have R12 : c₁₂.rmem = c₆.rmem := by rw [hM₁₂, hM₁₁, hM₁₀, hM₉, R8]
      have F12 : Fr LWm AcR c c₁₂ := (((F8.trans hF₉ (fun r h => h) fr_incl (fun r h => h)
        (fun _ h => False.elim h)).trans hF₁₀ (fun r h => h) fr_incl (fun r h => h)
        (fun _ h => False.elim h)).trans hF₁₁ (fun r h => h) fr_incl (fun r h => h)
        (fun _ h => False.elim h)).trans hF₁₂ (fun r h => h) fr_incl (fun r h => h) fr_incl
      have k12 : ∀ r, ¬ LWm r → c₁₂.nreg r = c.nreg r := F12.n
      have k12c : c₁₂.nreg 264 = cur := by
        rw [hF₁₂.n 264 fr_ne, hF₁₁.n 264 fr_ne, hF₁₀.n 264 fr_ne, hF₉.n 264 fr_ne, k8c]
      have k12p : c₁₂.nreg 263 = pred := by
        rw [hF₁₂.n 263 fr_ne, hF₁₁.n 263 fr_ne, hF₁₀.n 263 fr_ne, f263']
      have hn6 : nst Q (2 ^ T) c₆.nmem + 1 = nst Q (2 ^ T) c.nmem := by rw [hn₆, hn5]
      by_cases hb2 : EE P T k e ep a < EE P T k e ep up
      · rw [iteT hb2] at f273'
        refine spec_ifLtN_true (by rw [k12 117 fr_ne, g117, f273']; omega) ?_
        have hadj : cur = ep + 1 := hAH.adj (hBep.2 hb2) hBcur hep hgap
        have h268' : c₁₂.nreg 268 = 1 := by rw [k12 268 fr_ne, h268]
        refine spec_skip hw₁₂ ⟨⟨hAS₁₂, fun r hr => (F12.n r fun h => hr (by
          simp only [LWn, LWm, TPn] at h ⊢; omega)).trans (hI.keep r hr),
          by rw [F12.n 265 fr_ne]; exact hI.ry, by
          rw [k12c, N12, R12]; exact hM₆', by rw [k12c]; exact hbC, by rw [k12c]; omega,
          Or.inr h268', fun _ => ⟨by rw [k12p]; exact hp0, by rw [k12p, N12]; exact hpp,
            by rw [k12c, k12p, N12, hepv]; exact hadj, by rw [k12p]; omega,
            by rw [k12p, N12, hepv]; exact hBep.2 hb2⟩,
          fun ρ hρ hρβ => by rw [k12c]; exact daC ρ (by rw [← k12c]; exact hρ h268') hρβ⟩, ?_⟩
        have hΦ' : wΦ Q T c₁₂ = LD T * nst Q (2 ^ T) c₆.nmem + LF T := by
          unfold wΦ; rw [iteT h268', N12]
        rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
        unfold LD srchCost at *
        generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
        omega
      · rw [iteF hb2] at f273'
        refine spec_ifLtN_false (by rw [k12 117 fr_ne, g117, f273']; omega) ?_
        refine spec_use (copyA hL (I := I) c₁₂ hAS₁₂ 268 117 fr_ne) ?_
        intro c₁₃ k₁₃ hk₁₃ hw₁₃ ⟨hAS₁₃, f268, hF₁₃, hN₁₃, hM₁₃⟩
        have hlt : ∀ ρ < cur, ¬ Bt' ρ := fun ρ hρ => by
          by_cases hρe : ρ ≤ ep
          · exact hAH.left_end (by omega) ((hOL ep (by omega) hnx).1 (by omega))
              (fun h => hb2 (hBep.1 h)) hρe
          · exact hgap ρ (by omega) hρ
        refine ⟨stop c₁₃ hAS₁₃ (F12.trans hF₁₃ fr_incl fr_incl (fun r h => h)
          (fun _ h => False.elim h)) (by rw [hN₁₃, N12]) (by rw [hM₁₃, R12])
          (by rw [f268, k12 117 fr_ne, g117]) (by rw [hF₁₃.n 264 fr_ne, k12c]) hlt, ?_⟩
        have hΦ' : wΦ Q T c₁₃ = LD T * nst Q (2 ^ T) c₆.nmem := by
          unfold wΦ; rw [iteF (by rw [f268, k12 117 fr_ne, g117]; omega), hN₁₃, N12]; rfl
        rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
        unfold LD LF srchCost at *
        generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
        omega
    · refine spec_ifLtN_false (by rw [hpe, k8 121 fr_ne, hAS.env.h.r121]; exact hp) ?_
      refine spec_use (copyA hL (I := I) c₈ hAS₈ 268 117 fr_ne) ?_
      intro c₉ k₉ hk₉ hw₉ ⟨hAS₉, f268, hF₉, hN₉, hM₉⟩
      have hnone : pred = 2 ^ T := by
        rcases hp1 with h | h
        · exact h
        · exact absurd h.1 hp
      have hlt : ∀ ρ < cur, ¬ Bt' ρ := fun ρ hρ =>
        hAH.uncov hM₆' (fun h => by omega) (uncov_before hM₆' (Or.inl hnone)
          (fun y hy => hp2 y hy) hρ (Or.inl hnone))
      refine ⟨stop c₉ hAS₉ (F8.trans hF₉ fr_incl fr_incl (fun r h => h)
        (fun _ h => False.elim h)) (by rw [hN₉, N8])
        (by rw [hM₉, R8]) (by rw [f268, k8 117 fr_ne, g117]) (by rw [hF₉.n 264 fr_ne, k8c]) hlt,
        ?_⟩
      have hΦ' : wΦ Q T c₉ = LD T * nst Q (2 ^ T) c₆.nmem := by
        unfold wΦ; rw [iteF (by rw [f268, k8 117 fr_ne, g117]; omega), hN₉, N8]; rfl
      have hn6 : nst Q (2 ^ T) c₆.nmem + 1 = nst Q (2 ^ T) c.nmem := by rw [hn₆, hn5]
      rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
      unfold LD LF srchCost at *
      generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
      omega
  · -- cut the current triplet
    rw [iteF hb] at f273
    refine spec_ifLtN_false (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hnb : ¬ Bt' cur := fun h => hb ((hBc cur le_rfl hst.1).1 h)
    have hce : cur < ee := by
      rcases Nat.eq_or_lt_of_le hst.1 with h | h
      · exact absurd (h ▸ hbe) hnb
      · exact h
    have hQ := hAS.hQ
    unfold lwCut
    refine spec_seq ?_
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
    refine spec_seq ?_
    refine spec_use (bsLoop_exec (I := I) (lo₀ := cur) (hi₀ := ee) hL true c₅ hAS₅ hu ha f275
      (by omega) (by rw [f269, f270]; exact hce) (by rw [f276, f269])
      (by rw [f269]; simpa using hb) (by rw [f270]; simpa using (hBc ee hst.1 le_rfl).1 hbe)
      (by rw [f269]) (by rw [f270])) ?_
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
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₆ hAS₆ 230 263 fr_ne) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f230, hF₇, hN₇, hM₇⟩
    rw [k6 263 (by omega), f263] at f230
    refine spec_seq ?_
    refine spec_use (tDelA hL (I := I) c₇ hAS₇ f230 hcur (by rw [hN₇, hM₇, N6, R6]; exact hM)
      (by rw [hN₇, N6]; exact hpc)) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hM₈, hn₈, hF₈⟩
    rw [hN₇, N6, hev] at hM₈
    have hM₈' : BM P T k e own X (fun ρ => cur ≤ ρ ∧ ρ < hy) Q c₈.nmem c₈.rmem :=
      hM₈.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₈.hole ρ (by omega))
    refine spec_seq ?_
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
    refine spec_seq ?_
    refine spec_use (tPutA hL (I := I) (σ := u) (j1 := cur) (j2 := hi) (e := e) (own := own)
      (X := X) (H := fun ρ => cur ≤ ρ ∧ ρ < hy) c₉ hAS₉
      (by rw [← hc₉]; exact hM₈')
      (by rw [← hc₉]; config_simp; rw [k8 275 fr_ne, k6 275 (by omega), f275]) hu
      (by rw [← hc₉]; config_simp; rw [k8 263 fr_ne, k6 263 (by omega), f263])
      (by rw [← hc₉]; config_simp; rw [k8 270 fr_ne, hhiv]) (by omega) (by omega)
      (fun ρ h1 h2 => ⟨h1, by omega⟩) (fun ρ h1 h2 => hown ρ h1 (by omega))) ?_
    intro c₁₀ k₁₀ hk₁₀ hw₁₀ ⟨hAS₁₀, hM₁₀, hn₁₀, hF₁₀⟩
    have hM₁₀' : BM P T k e own X (fun ρ => hi ≤ ρ ∧ ρ < hy) Q c₁₀.nmem c₁₀.rmem :=
      hM₁₀.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₁₀.hole ρ (by omega))
    exec_block
    generalize hc₁₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁₁
    have hw₁₁ : WordsBounded P.W c₁₁ := hc₁₁ ▸ ‹_›
    have F11 : Fr (fun r => r = 264 ∨ r = 268) (fun _ => False) c₁₀ c₁₁ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₁₁]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₁₁], by rw [← hc₁₁]⟩
    have hAS₁₁ := hAS₁₀.next hL hw₁₁ F11 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₁₁]) (fun x _ => by rw [← hc₁₁])
    have k10 : ∀ r, ¬ (TPn r ∨ (200 ≤ r ∧ r < 203)) → c₁₀.nreg r = c₈.nreg r := fun r hr => by
      rw [hF₁₀.n r (fun h => hr (Or.inl h)), F9.n r (fun h => hr (Or.inr h))]
    have f264' : c₁₁.nreg 264 = hi := by
      rw [← hc₁₁]; config_simp; rw [k10 270 fr_ne, k8 270 fr_ne, hhiv]
    have f268' : c₁₁.nreg 268 = 0 := by
      rw [← hc₁₁]; config_simp; rw [k10 117 fr_ne, k8 117 fr_ne, k6 117 (by omega),
        F5.n 117 fr_ne, k4 117 fr_ne, g117]
    have F7 : Fr LWl AcR c c₇ :=
      F6.trans hF₇ (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    have F8 : Fr LWl AcR c c₈ := F7.trans hF₈ (fun r h => h) fr_incl (fun r h => h) fr_incl
    have F9' : Fr LWl AcR c c₉ :=
      F8.trans F9 (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    have F10 : Fr LWl AcR c c₁₀ := F9'.trans hF₁₀ (fun r h => h) fr_incl (fun r h => h) fr_incl
    have F11' : Fr LWl AcR c c₁₁ :=
      F10.trans F11 (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    refine ⟨⟨hAS₁₁, fun r hr => (F11'.n r fun h => hr (by
      simp only [LWn, LWl, TPn] at h ⊢; omega)).trans (hI.keep r hr),
      by rw [F11'.n 265 fr_ne]; exact hI.ry, by rw [f264', ← hc₁₁]; exact hM₁₀',
      fun ρ h1 h2 => ?_, by rw [f264']; omega,
      Or.inl f268', fun h => by omega, fun ρ _ hρ => ?_⟩, ?_⟩
    · rw [f264'] at h1
      by_cases hρ : ρ ≤ ee
      · exact hAH.conv hBhi hbe h1 hρ
      · exact hhb ρ (by omega) h2
    · rw [f264']
      by_cases h1 : hi ≤ ρ
      · by_cases hρe : ρ ≤ ee
        · exact ⟨fun _ => ⟨h1, by omega⟩, fun _ => hAH.conv hBhi hbe h1 hρe⟩
        · rw [hda ρ (fun _ => by omega) hρ]; omega
      · refine ⟨fun h => ?_, fun h => by omega⟩
        exfalso
        by_cases h2 : cur ≤ ρ
        · exact hnBlo (hAH.conv h hBhi (by omega) (by omega))
        · exact hnb (hAH.conv h hbe (by omega) hst.1)
    · have hn11 : nst Q (2 ^ T) c₁₁.nmem = nst Q (2 ^ T) c.nmem := by
        have e1 : c₁₁.nmem = c₁₀.nmem := by rw [← hc₁₁]
        have e2 : c₉.nmem = c₈.nmem := by rw [← hc₉]
        rw [e1, hn₁₀, e2, hn₈, hN₇, N6]
      have hΦ' : wΦ Q T c₁₁ = LD T * nst Q (2 ^ T) c.nmem := by
        unfold wΦ; rw [iteF (by rw [f268']; omega), hn11]; rfl
      rw [hΦ', hΦ]
      unfold LF at *
      generalize LD T * nst Q (2 ^ T) c.nmem = M
      omega

/-- **The left walk.** -/
theorem lwLoop_exec (hL : Lay P) {β hy : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hI : ILW P B Q T k a e own X β hy c₀ c₁ c₁) :
    ∃ c' k', Exec I P.W (.whileLtN 117 268 lwBody) c₁ c' k' ∧ k' + wΦ Q T c' ≤ wΦ Q T c₁ + 2 ∧
      ILW P B Q T k a e own X β hy c₀ c₁ c' ∧ c'.nreg 268 = 0 := by
  obtain ⟨c', k', ex, hI', hn, hk⟩ := whileLtN_pot (P' := I) (W := P.W) (a := 117)
    (b := 268) (body := lwBody) (ILW P B Q T k a e own X β hy c₀ c₁) (wΦ Q T)
    (fun _ h => h.as.wb) (fun c hI hlt => lwBody_exec hL hAH hOL c hI hlt) hI
  refine ⟨c', k', ex, hk, hI', ?_⟩
  have := hI'.fl; rw [hI'.as.env.g.r117] at hn; omega

/-- **The state of the right walk** (`r268 = 1` while it goes on): the hole `[hx, r265)` of
beaten rows; while it goes on, the current start `r263` (its first row beaten) begins just after
the hole; the rows before the end of the hole (all of them at the end) are beaten exactly in the
hole. -/
structure IRW (P : Prm) (B Q T k a : ℕ) (e : ℕ → ℝ) (own : ℕ → ℕ) (X : ℕ → Prop) (β hx : ℕ)
    (c₀ c₁ c : Config) : Prop where
  as : AS P B Q T k a e c₀ c
  keep : ∀ r, ¬ LWn r → c.nreg r = c₁.nreg r
  rx : c.nreg 264 = hx
  mem : BM P T k e own X (fun ρ => hx ≤ ρ ∧ ρ < c.nreg 265) Q c.nmem c.rmem
  hb : ∀ ρ, hx ≤ ρ → ρ < c.nreg 265 →
    Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ
  le : hx ≤ c.nreg 265
  fl : c.nreg 268 = 0 ∨ c.nreg 268 = 1
  go : c.nreg 268 = 1 → c.nreg 263 < 2 ^ T ∧ tPr Q c.nmem (c.nreg 263) = 1 ∧
    c.nreg 265 = c.nreg 263 ∧ β ≤ c.nreg 263 ∧
    Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a (c.nreg 263)
  da : ∀ ρ, (c.nreg 268 = 1 → ρ < c.nreg 265) →
    (Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ ↔ hx ≤ ρ ∧ ρ < c.nreg 265)

theorem rwBody_exec (hL : Lay P) {β hx : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (c : Config) (hI : IRW P B Q T k a e own X β hx c₀ c₁ c) (hgo : c.nreg 117 < c.nreg 268) :
    ∃ c' k', Exec I P.W rwBody c c' k' ∧ IRW P B Q T k a e own X β hx c₀ c₁ c' ∧
      wΦ Q T c' + k' + 2 ≤ wΦ Q T c := by
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
  refine spec_seq ?_
  refine spec_use (ldCurA hL (I := I) c hAS hcv hcur) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f275, f277, hF₂, hN₂, hM₂⟩
  rw [huv] at f275; rw [hev] at f277
  refine spec_seq ?_
  refine spec_use (copyA hL (I := I) c₂ hAS₂ 274 277 fr_ne) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f274, hF₃, hN₃, hM₃⟩
  rw [f277] at f274
  refine spec_seq ?_
  refine spec_use (btA hL (I := I) c₃ hAS₃ f274 (by omega) (by rw [hF₃.n 275 fr_ne]; exact f275)
    hu ha) ?_
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
  · -- delete the current triplet
    rw [iteT hb] at f273
    refine spec_ifLtN_true (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hBe : Bt' ee := (hBc ee hst.1 le_rfl).2 hb
    have hBin : ∀ ρ, cur ≤ ρ → ρ ≤ ee → Bt' ρ := fun ρ h1 h2 => hAH.conv hBcur hBe h1 h2
    unfold rwDel
    refine spec_seq ?_
    exec_block
    · config_simp; rw [k4e, k4 110 fr_ne, g110]; omega
    generalize hc₅ : (Config.mk _ _ _ _ _ _ : Config) = c₅
    have hw₅ : WordsBounded P.W c₅ := hc₅ ▸ ‹_›
    have F5 : Fr (fun r => r = 265 ∨ r = 230) (fun _ => False) c₄ c₅ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₅]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₅], by rw [← hc₅]⟩
    have hAS₅ := hAS₄.next hL hw₅ F5 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₅]) (fun x _ => by rw [← hc₅])
    have N5 : c₅.nmem = c.nmem := by rw [← hc₅]; exact N4
    have R5 : c₅.rmem = c.rmem := by rw [← hc₅]; exact R4
    have f265 : c₅.nreg 265 = ee + 1 := by rw [← hc₅]; config_simp; rw [k4e, k4 110 fr_ne, g110]
    have f230 : c₅.nreg 230 = cur := by rw [← hc₅]; config_simp; rw [k4c]
    refine spec_seq ?_
    refine spec_use (tDelA hL (I := I) c₅ hAS₅ f230 hcur (by rw [N5, R5]; exact hM)
      (by rw [N5]; exact hpc)) ?_
    intro c₆ k₆ hk₆ hw₆ ⟨hAS₆, hM₆, hn₆, hF₆⟩
    rw [N5, hev] at hM₆
    have hM₆' : BM P T k e own X (fun ρ => hx ≤ ρ ∧ ρ < ee + 1) Q c₆.nmem c₆.rmem :=
      hM₆.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₆.hole ρ (by omega))
    have F6 : Fr LWc AcR c c₆ := (F4.trans F5 (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)).trans hF₆ (fun r h => h) fr_incl (fun r h => h) fr_incl
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₆ hAS₆ 221 277 fr_ne) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f221, hF₇, hN₇, hM₇⟩
    rw [hF₆.n 277 fr_ne, F5.n 277 fr_ne, k4e] at f221
    refine spec_seq ?_
    refine spec_use (tNxA hL (I := I) c₇ hAS₇ f221 (by rw [hN₇, hM₇]; exact hM₆')) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hp1, hp2, hF₈, hN₈, hM₈⟩
    rw [hN₇] at hp1 hp2
    have N8 : c₈.nmem = c₆.nmem := by rw [hN₈, hN₇]
    have R8 : c₈.rmem = c₆.rmem := by rw [hM₈, hM₇]
    have F8 : Fr LWc AcR c c₈ := (F6.trans hF₇ (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)).trans hF₈ (fun r h => h) fr_incl (fun r h => h)
      (fun _ h => False.elim h)
    have k8 : ∀ r, ¬ LWc r → c₈.nreg r = c.nreg r := F8.n
    have k8h : c₈.nreg 265 = ee + 1 := by
      rw [hF₈.n 265 fr_ne, hF₇.n 265 fr_ne, hF₆.n 265 fr_ne, f265]
    have k8x : c₈.nreg 264 = hx := by
      rw [hF₈.n 264 fr_ne, hF₇.n 264 fr_ne, hF₆.n 264 fr_ne, F5.n 264 fr_ne, k4x]
    generalize hpe : c₈.nreg 222 = nxt at hp1 hp2
    have daC : ∀ ρ, ρ ≤ ee → (Bt' ρ ↔ hx ≤ ρ ∧ ρ < ee + 1) := fun ρ h1 => by
      by_cases hρ : cur ≤ ρ
      · exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => hBin ρ hρ h1⟩
      · rw [hda ρ (fun _ => by omega)]; omega
    have hbC : ∀ ρ, hx ≤ ρ → ρ < ee + 1 → Bt' ρ := fun ρ h1 h2 => by
      by_cases hρ : cur ≤ ρ
      · exact hBin ρ hρ (by omega)
      · exact hhb ρ h1 (by omega)
    -- the starts before `ee` end before it
    have hz : ∀ y < 2 ^ T, tPr Q c₆.nmem y = 1 → y ≤ ee → tEnd Q c₆.nmem y ≤ ee := by
      intro y hy hpy hye
      have hs := hM₆'.st y hy hpy
      by_contra hc
      exact (hM₆'.not_hole hy hpy (ρ := max y hx) (by omega) (by omega)).2
        ⟨by omega, by omega⟩
    have hn5 : nst Q (2 ^ T) c₅.nmem = nst Q (2 ^ T) c.nmem := by rw [N5]
    have stop : ∀ (c' : Config), AS P B Q T k a e c₀ c' → Fr LWn AcR c c' →
        c'.nmem = c₆.nmem → c'.rmem = c₆.rmem → c'.nreg 268 = 0 → c'.nreg 265 = ee + 1 →
        c'.nreg 264 = hx → (∀ ρ, ee < ρ → ¬ Bt' ρ) →
        IRW P B Q T k a e own X β hx c₀ c₁ c' := by
      intro c' hAS' hF' hN' hM' h268' h265' h264' hgt
      refine ⟨hAS', fun r hr => (hF'.n r hr).trans (hI.keep r hr), h264', ?_, ?_, ?_,
        Or.inl h268', fun h => by omega, fun ρ _ => ?_⟩
      · rw [h265', hN', hM']; exact hM₆'
      · rw [h265']; exact hbC
      · rw [h265']; omega
      · rw [h265']
        by_cases h1 : ρ ≤ ee
        · exact daC ρ h1
        · exact ⟨fun h => absurd h (hgt ρ (by omega)), fun h => by omega⟩
    by_cases hp : nxt < 2 ^ T
    · have hnv : Nx Q (2 ^ T) ee c₆.nmem nxt := hp1.resolve_left (by omega)
      obtain ⟨hn0, hnp, hen⟩ := hnv
      have hstn := hM₆'.st nxt hn0 hnp
      generalize hunv : tOwn Q c₆.nmem nxt = un
      have hownn : own nxt = un := by
        rw [← hunv]; exact hM₆'.own nxt hn0 hnp nxt le_rfl hstn.1
      have hun : un < hbNc P.b (2 ^ T) k := by
        rw [← hownn]; exact hAH.ok.lt _ (hAH.ok.act nxt (by omega))
      have hgap : ∀ ρ, ee < ρ → ρ < nxt → ¬ Bt' ρ := fun ρ h1 h2 =>
        hAH.uncov hM₆' (fun h => by omega) (uncov_after hp2 h1 h2 hz)
      have hnx : ¬ X nxt := (hM₆'.not_hole hn0 hnp le_rfl hstn.1).1
      have hBn : Bt' nxt ↔ EE P T k e nxt a < EE P T k e nxt un := by
        unfold Bt; rw [hownn]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      refine spec_ifLtN_true (by rw [hpe, k8 121 fr_ne, hAS.env.h.r121]; exact hp) ?_
      refine spec_seq ?_
      refine spec_use (copyA hL (I := I) c₈ hAS₈ 263 222 fr_ne) ?_
      intro c₉ k₉ hk₉ hw₉ ⟨hAS₉, f263', hF₉, hN₉, hM₉⟩
      rw [hpe] at f263'
      refine spec_seq ?_
      refine spec_use (ldCurA hL (I := I) c₉ hAS₉ f263' hn0) ?_
      intro c₁₀ k₁₀ hk₁₀ hw₁₀ ⟨hAS₁₀, f275', f277', hF₁₀, hN₁₀, hM₁₀⟩
      rw [hN₉, N8, hunv] at f275'
      refine spec_seq ?_
      refine spec_use (copyA hL (I := I) c₁₀ hAS₁₀ 274 263 fr_ne) ?_
      intro c₁₁ k₁₁ hk₁₁ hw₁₁ ⟨hAS₁₁, f274', hF₁₁, hN₁₁, hM₁₁⟩
      rw [hF₁₀.n 263 fr_ne, f263'] at f274'
      refine spec_seq ?_
      refine spec_use (btA hL (I := I) c₁₁ hAS₁₁ f274' hn0
        (by rw [hF₁₁.n 275 fr_ne, f275']) hun ha) ?_
      intro c₁₂ k₁₂ hk₁₂ hw₁₂ ⟨hAS₁₂, f273', hF₁₂, hN₁₂, hM₁₂⟩
      have N12 : c₁₂.nmem = c₆.nmem := by rw [hN₁₂, hN₁₁, hN₁₀, hN₉, N8]
      have R12 : c₁₂.rmem = c₆.rmem := by rw [hM₁₂, hM₁₁, hM₁₀, hM₉, R8]
      have F9 : Fr LWc AcR c c₉ :=
        F8.trans hF₉ (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
      have F10 : Fr LWc AcR c c₁₀ :=
        F9.trans hF₁₀ (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
      have F11 : Fr LWc AcR c c₁₁ :=
        F10.trans hF₁₁ (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
      have F12 : Fr LWc AcR c c₁₂ := F11.trans hF₁₂ (fun r h => h) fr_incl (fun r h => h) fr_incl
      have k12 : ∀ r, ¬ LWc r → c₁₂.nreg r = c.nreg r := F12.n
      have k12h : c₁₂.nreg 265 = ee + 1 := by
        rw [hF₁₂.n 265 fr_ne, hF₁₁.n 265 fr_ne, hF₁₀.n 265 fr_ne, hF₉.n 265 fr_ne, k8h]
      have k12x : c₁₂.nreg 264 = hx := by
        rw [hF₁₂.n 264 fr_ne, hF₁₁.n 264 fr_ne, hF₁₀.n 264 fr_ne, hF₉.n 264 fr_ne, k8x]
      have k12p : c₁₂.nreg 263 = nxt := by
        rw [hF₁₂.n 263 fr_ne, hF₁₁.n 263 fr_ne, hF₁₀.n 263 fr_ne, f263']
      have hn6 : nst Q (2 ^ T) c₆.nmem + 1 = nst Q (2 ^ T) c.nmem := by rw [hn₆, hn5]
      by_cases hb2 : EE P T k e nxt a < EE P T k e nxt un
      · rw [iteT hb2] at f273'
        refine spec_ifLtN_true (by rw [k12 117 fr_ne, g117, f273']; omega) ?_
        have hadj : nxt = ee + 1 := hAH.adj hBe (hBn.2 hb2) hen hgap
        have h268' : c₁₂.nreg 268 = 1 := by rw [k12 268 fr_ne, h268]
        refine spec_skip hw₁₂ ⟨⟨hAS₁₂, fun r hr => (F12.n r fun h => hr (by
          simp only [LWn, LWc, TPn] at h ⊢; omega)).trans (hI.keep r hr), k12x, by
          rw [k12h, N12, R12]; exact hM₆', by rw [k12h]; exact hbC, by rw [k12h]; omega,
          Or.inr h268', fun _ => ⟨by rw [k12p]; exact hn0, by rw [k12p, N12]; exact hnp,
            by rw [k12h, k12p, hadj], by rw [k12p]; omega, by rw [k12p]; exact hBn.2 hb2⟩,
          fun ρ hρ => by rw [k12h]; exact daC ρ (by have := hρ h268'; rw [k12h] at this; omega)⟩,
          ?_⟩
        have hΦ' : wΦ Q T c₁₂ = LD T * nst Q (2 ^ T) c₆.nmem + LF T := by
          unfold wΦ; rw [iteT h268', N12]
        rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
        unfold LD srchCost at *
        generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
        omega
      · rw [iteF hb2] at f273'
        refine spec_ifLtN_false (by rw [k12 117 fr_ne, g117, f273']; omega) ?_
        refine spec_use (copyA hL (I := I) c₁₂ hAS₁₂ 268 117 fr_ne) ?_
        intro c₁₃ k₁₃ hk₁₃ hw₁₃ ⟨hAS₁₃, f268, hF₁₃, hN₁₃, hM₁₃⟩
        have hgt : ∀ ρ, ee < ρ → ¬ Bt' ρ := fun ρ hρ => by
          by_cases hρn : nxt ≤ ρ
          · exact hAH.right_start ((hOL nxt (by omega) hnx).2 (by omega))
              (fun h => hb2 (hBn.1 h)) hρn
          · exact hgap ρ hρ (by omega)
        refine ⟨stop c₁₃ hAS₁₃ (F12.trans hF₁₃ fr_incl fr_incl (fun r h => h)
          (fun _ h => False.elim h)) (by rw [hN₁₃, N12]) (by rw [hM₁₃, R12])
          (by rw [f268, k12 117 fr_ne, g117]) (by rw [hF₁₃.n 265 fr_ne, k12h])
          (by rw [hF₁₃.n 264 fr_ne, k12x]) hgt, ?_⟩
        have hΦ' : wΦ Q T c₁₃ = LD T * nst Q (2 ^ T) c₆.nmem := by
          unfold wΦ; rw [iteF (by rw [f268, k12 117 fr_ne, g117]; omega), hN₁₃, N12]; rfl
        rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
        unfold LD LF srchCost at *
        generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
        omega
    · refine spec_ifLtN_false (by rw [hpe, k8 121 fr_ne, hAS.env.h.r121]; exact hp) ?_
      refine spec_use (copyA hL (I := I) c₈ hAS₈ 268 117 fr_ne) ?_
      intro c₉ k₉ hk₉ hw₉ ⟨hAS₉, f268, hF₉, hN₉, hM₉⟩
      have hnone : nxt = 2 ^ T := by
        rcases hp1 with h | h
        · exact h
        · exact absurd h.1 hp
      have hgt : ∀ ρ, ee < ρ → ¬ Bt' ρ := fun ρ hρ hB =>
        hAH.uncov hM₆' (fun h => by omega) (uncov_after hp2 hρ (by have := hB.1; omega) hz) hB
      refine ⟨stop c₉ hAS₉ (F8.trans hF₉ fr_incl fr_incl (fun r h => h)
        (fun _ h => False.elim h)) (by rw [hN₉, N8]) (by rw [hM₉, R8])
        (by rw [f268, k8 117 fr_ne, g117]) (by rw [hF₉.n 265 fr_ne, k8h])
        (by rw [hF₉.n 264 fr_ne, k8x]) hgt, ?_⟩
      have hΦ' : wΦ Q T c₉ = LD T * nst Q (2 ^ T) c₆.nmem := by
        unfold wΦ; rw [iteF (by rw [f268, k8 117 fr_ne, g117]; omega), hN₉, N8]; rfl
      have hn6 : nst Q (2 ^ T) c₆.nmem + 1 = nst Q (2 ^ T) c.nmem := by rw [hn₆, hn5]
      rw [hΦ', hΦ, ← hn6, Nat.mul_succ]
      unfold LD LF srchCost at *
      generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M
      omega
  · -- cut the current triplet
    rw [iteF hb] at f273
    refine spec_ifLtN_false (by rw [k4 117 fr_ne, g117, f273]; omega) ?_
    have hnb : ¬ Bt' ee := fun h => hb ((hBc ee hst.1 le_rfl).1 h)
    have hce : cur < ee := by
      rcases Nat.eq_or_lt_of_le hst.1 with h | h
      · exact absurd (h ▸ hBcur) hnb
      · exact h
    unfold rwCut
    refine spec_seq ?_
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
    refine spec_seq ?_
    refine spec_use (bsLoop_exec (I := I) (lo₀ := cur) (hi₀ := ee) hL false c₅ hAS₅ hu ha f275
      (by omega) (by rw [f269, f270]; exact hce) (by rw [f276, f269])
      (by rw [f269]; simpa using (hBc cur le_rfl hst.1).1 hBcur) (by rw [f270]; simpa using hb)
      (by rw [f269]) (by rw [f270])) ?_
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
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₆ hAS₆ 230 263 fr_ne) ?_
    intro c₇ k₇ hk₇ hw₇ ⟨hAS₇, f230, hF₇, hN₇, hM₇⟩
    rw [k6 263 (by omega), f263] at f230
    refine spec_seq ?_
    refine spec_use (tDelA hL (I := I) c₇ hAS₇ f230 hcur (by rw [hN₇, hM₇, N6, R6]; exact hM)
      (by rw [hN₇, N6]; exact hpc)) ?_
    intro c₈ k₈ hk₈ hw₈ ⟨hAS₈, hM₈, hn₈, hF₈⟩
    rw [hN₇, N6, hev] at hM₈
    have hM₈' : BM P T k e own X (fun ρ => hx ≤ ρ ∧ ρ < ee + 1) Q c₈.nmem c₈.rmem :=
      hM₈.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₈.hole ρ (by omega))
    refine spec_seq ?_
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
    refine spec_seq ?_
    refine spec_use (tPutA hL (I := I) (σ := u) (j1 := lo + 1) (j2 := ee + 1) (e := e) (own := own)
      (X := X) (H := fun ρ => hx ≤ ρ ∧ ρ < ee + 1) c₉ hAS₉
      (by rw [← hc₉]; exact hM₈')
      (by rw [← hc₉]; config_simp; rw [k8 275 fr_ne, k6 275 (by omega), f275]) hu
      (by rw [← hc₉]; config_simp; rw [k8 269 fr_ne, hlov, hAS₈.env.g.r110])
      (by rw [← hc₉]; config_simp; rw [k8 277 fr_ne, k6 277 (by omega), F5.n 277 fr_ne, k4e,
        hAS₈.env.g.r110]) (by omega) (by omega)
      (fun ρ h1 h2 => ⟨by omega, by omega⟩) (fun ρ h1 h2 => hown ρ (by omega) (by omega))) ?_
    intro c₁₀ k₁₀ hk₁₀ hw₁₀ ⟨hAS₁₀, hM₁₀, hn₁₀, hF₁₀⟩
    have hM₁₀' : BM P T k e own X (fun ρ => hx ≤ ρ ∧ ρ < lo + 1) Q c₁₀.nmem c₁₀.rmem :=
      hM₁₀.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
        (fun ρ hρ => hM₁₀.hole ρ (by omega))
    exec_block
    · config_simp
      rw [hF₁₀.n 269 fr_ne, F9.n 269 fr_ne, k8 269 fr_ne, hlov, hAS₁₀.env.g.r110]; omega
    generalize hc₁₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁₁
    have hw₁₁ : WordsBounded P.W c₁₁ := hc₁₁ ▸ ‹_›
    have F11 : Fr (fun r => r = 265 ∨ r = 268) (fun _ => False) c₁₀ c₁₁ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₁₁]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₁₁], by rw [← hc₁₁]⟩
    have hAS₁₁ := hAS₁₀.next hL hw₁₁ F11 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₁₁]) (fun x _ => by rw [← hc₁₁])
    have k10 : ∀ r, ¬ (TPn r ∨ (200 ≤ r ∧ r < 203)) → c₁₀.nreg r = c₈.nreg r := fun r hr => by
      rw [hF₁₀.n r (fun h => hr (Or.inl h)), F9.n r (fun h => hr (Or.inr h))]
    have f265' : c₁₁.nreg 265 = lo + 1 := by
      rw [← hc₁₁]; config_simp; rw [k10 269 fr_ne, k8 269 fr_ne, hlov, k10 110 fr_ne,
        k8 110 fr_ne, k6 110 (by omega), F5.n 110 fr_ne, k4 110 fr_ne, g110]
    have f268' : c₁₁.nreg 268 = 0 := by
      rw [← hc₁₁]; config_simp; rw [k10 117 fr_ne, k8 117 fr_ne, k6 117 (by omega),
        F5.n 117 fr_ne, k4 117 fr_ne, g117]
    have f264' : c₁₁.nreg 264 = hx := by
      rw [F11.n 264 fr_ne, k10 264 fr_ne, k8 264 fr_ne, k6 264 (by omega), F5.n 264 fr_ne, k4x]
    have F7 : Fr LWn AcR c c₇ :=
      F6.trans hF₇ (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    have F8 : Fr LWn AcR c c₈ := F7.trans hF₈ (fun r h => h) fr_incl (fun r h => h) fr_incl
    have F9' : Fr LWn AcR c c₉ :=
      F8.trans F9 (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    have F10 : Fr LWn AcR c c₁₀ := F9'.trans hF₁₀ (fun r h => h) fr_incl (fun r h => h) fr_incl
    have F11' : Fr LWn AcR c c₁₁ :=
      F10.trans F11 (fun r h => h) fr_incl (fun r h => h) (fun _ h => False.elim h)
    refine ⟨⟨hAS₁₁, fun r hr => (F11'.n r hr).trans (hI.keep r hr), f264',
      by rw [f265', ← hc₁₁]; exact hM₁₀', fun ρ h1 h2 => ?_, by rw [f265']; omega,
      Or.inl f268', fun h => by omega, fun ρ _ => ?_⟩, ?_⟩
    · rw [f265'] at h2
      by_cases hρ : cur ≤ ρ
      · exact hAH.conv hBcur hBlo hρ (by omega)
      · exact hhb ρ h1 (by omega)
    · rw [f265']
      by_cases h1 : ρ < cur
      · rw [hda ρ (fun _ => h1)]; omega
      · by_cases h2 : ρ ≤ lo
        · exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => hAH.conv hBcur hBlo (by omega) h2⟩
        · exact ⟨fun h => absurd (hAH.conv hBcur h (by omega) (by omega)) hnBhi,
            fun h => by omega⟩
    · have hn11 : nst Q (2 ^ T) c₁₁.nmem = nst Q (2 ^ T) c.nmem := by
        have e1 : c₁₁.nmem = c₁₀.nmem := by rw [← hc₁₁]
        have e2 : c₉.nmem = c₈.nmem := by rw [← hc₉]
        rw [e1, hn₁₀, e2, hn₈, hN₇, N6]
      have hΦ' : wΦ Q T c₁₁ = LD T * nst Q (2 ^ T) c.nmem := by
        unfold wΦ; rw [iteF (by rw [f268']; omega), hn11]; rfl
      rw [hΦ', hΦ]
      unfold LF at *
      generalize LD T * nst Q (2 ^ T) c.nmem = M
      omega

/-- **The right walk.** -/
theorem rwLoop_exec (hL : Lay P) {β hx : ℕ} {c₀ c₁ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (hI : IRW P B Q T k a e own X β hx c₀ c₁ c₁) :
    ∃ c' k', Exec I P.W (.whileLtN 117 268 rwBody) c₁ c' k' ∧ k' + wΦ Q T c' ≤ wΦ Q T c₁ + 2 ∧
      IRW P B Q T k a e own X β hx c₀ c₁ c' ∧ c'.nreg 268 = 0 := by
  obtain ⟨c', k', ex, hI', hn, hk⟩ := whileLtN_pot (P' := I) (W := P.W) (a := 117)
    (b := 268) (body := rwBody) (IRW P B Q T k a e own X β hx c₀ c₁) (wΦ Q T)
    (fun _ h => h.as.wb) (fun c hI hlt => rwBody_exec hL hAH hOL c hI hlt) hI
  refine ⟨c', k', ex, hk, hI', ?_⟩
  have := hI'.fl; rw [hI'.as.env.g.r117] at hn; omega

/-- **The state after a part of the activation**: the hole `[r264, r265)` of beaten rows, below
`z`, and the rows before `z` beaten exactly in the hole. -/
structure LS (P : Prm) (B Q T k a : ℕ) (e : ℕ → ℝ) (own : ℕ → ℕ) (X : ℕ → Prop) (z : ℕ)
    (c₀ c : Config) : Prop where
  as : AS P B Q T k a e c₀ c
  mem : BM P T k e own X (fun ρ => c.nreg 264 ≤ ρ ∧ ρ < c.nreg 265) Q c.nmem c.rmem
  hb : ∀ ρ, c.nreg 264 ≤ ρ → ρ < c.nreg 265 →
    Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ
  le : c.nreg 264 ≤ c.nreg 265
  lez : c.nreg 265 ≤ z
  da : ∀ ρ < z,
    (Bt (hbNr P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e own a ρ ↔
      c.nreg 264 ≤ ρ ∧ ρ < c.nreg 265)

/-- **The left part of the activation.** -/
theorem actL_exec (hL : Lay P) {β : ℕ} {c₀ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (c : Config) (hβs : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c.nmem β = 1))
    (hAS : AS P B Q T k a e c₀ c) (hM : BM P T k e own X (fun _ => False) Q c.nmem c.rmem)
    (h264 : c.nreg 264 = 0) (h265 : c.nreg 265 = 0)
    (hp1 : c.nreg 222 = 2 ^ T ∨ Pv Q (2 ^ T) β c.nmem (c.nreg 222))
    (hp2 : ∀ y, Pv Q (2 ^ T) β c.nmem y → c.nreg 222 ≠ 2 ^ T ∧ y ≤ c.nreg 222) :
    ∃ c' k', Exec I P.W actL c c' k' ∧ k' + LD T * nst Q (2 ^ T) c'.nmem ≤
        LD T * nst Q (2 ^ T) c.nmem + LF T + 60 ∧
      LS P B Q T k a e own X β c₀ c' ∧ (∀ r, ¬ LWn r → c'.nreg r = c.nreg r) := by
  have g117 := hAS.env.g.r117
  have g110 := hAS.env.g.r110
  have hQ := hAS.hQ
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hM0 : BM P T k e own X (fun ρ => c.nreg 264 ≤ ρ ∧ ρ < c.nreg 265) Q c.nmem c.rmem :=
    hM.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => h.elim⟩)
      (fun ρ hρ => absurd hρ (by omega))
  generalize hαv : c.nreg 222 = α at hp1 hp2
  unfold actL
  refine spec_seq ?_
  refine spec_use (copyA hL (I := I) c hAS 263 222 fr_ne) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f263, hF₂, hN₂, hM₂⟩
  rw [hαv] at f263
  have k2 : ∀ r, r ≠ 263 → c₂.nreg r = c.nreg r := fun r h => hF₂.n r h
  -- no beaten row before `β` (the hole stays empty)
  have none : ∀ (c' : Config) (k' : ℕ), AS P B Q T k a e c₀ c' → c'.nmem = c.nmem →
      c'.rmem = c.rmem → (∀ r, ¬ LWn r → c'.nreg r = c.nreg r) → c'.nreg 264 = 0 →
      c'.nreg 265 = 0 → k' ≤ 60 → (∀ ρ < β, ¬ Bt' ρ) →
      k' + LD T * nst Q (2 ^ T) c'.nmem ≤ LD T * nst Q (2 ^ T) c.nmem + LF T + 60 ∧
        LS P B Q T k a e own X β c₀ c' ∧ (∀ r, ¬ LWn r → c'.nreg r = c.nreg r) := by
    intro c' k' hAS' hN' hM' hK h264' h265' hk hno
    refine ⟨by rw [hN']; omega, ⟨hAS', ?_, fun ρ h1 h2 => by omega, by omega, by omega,
      fun ρ hρ => ⟨fun h => absurd h (hno ρ hρ), fun h => by omega⟩⟩, hK⟩
    rw [h264', h265', hN', hM']; rw [h264, h265] at hM0; exact hM0
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
    refine spec_ifLtN_true (by rw [f263, k2 121 (by omega), hAS.env.h.r121]; exact hα) ?_
    refine spec_seq ?_
    refine spec_use (ldCurA hL (I := I) c₂ hAS₂ f263 hα0) ?_
    intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f275, f277, hF₃, hN₃, hM₃⟩
    rw [hN₂, huαv] at f275; rw [hN₂, heαv] at f277
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₃ hAS₃ 274 277 fr_ne) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f274, hF₄, hN₄, hM₄⟩
    rw [f277] at f274
    refine spec_seq ?_
    refine spec_use (btA hL (I := I) c₄ hAS₄ f274 (by omega) (by rw [hF₄.n 275 fr_ne, f275])
      huα hAH.ha) ?_
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
      refine spec_ifLtN_true (by rw [k5 117 fr_ne, g117, f273]; omega) ?_
      refine spec_seq ?_
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
      obtain ⟨c₇, k₇, ex₇, hk₇, hI₇, h268'⟩ := lwLoop_exec hL (I := I) hAH hOL hI₆
      refine ⟨c₇, k₇, ex₇, ?_⟩
      have hΦ6 : wΦ Q T c₆ = LD T * nst Q (2 ^ T) c.nmem + LF T := by
        unfold wΦ; rw [iteT f268, N6]
      have hΦ7 : wΦ Q T c₇ = LD T * nst Q (2 ^ T) c₇.nmem := by
        unfold wΦ; rw [iteF (by omega)]; rfl
      rw [hΦ6, hΦ7] at hk₇
      have K7 : ∀ r, ¬ LWn r → c₇.nreg r = c.nreg r := fun r hr => by
        rw [hI₇.keep r hr, F6.n r (by simp only [LWn, TPn] at hr; omega), k5 r (by
          simp only [LWn, LWl, TPn] at hr ⊢; omega)]
      refine ⟨by omega, ⟨hI₇.as, by rw [hI₇.ry]; exact hI₇.mem, fun ρ h1 h2 => hI₇.hb ρ h1
        (by rw [hI₇.ry] at h2; exact h2), by rw [hI₇.ry]; exact hI₇.le, by rw [hI₇.ry]; omega,
        fun ρ hρ => by rw [hI₇.ry]; exact hI₇.da ρ (fun h => by omega) hρ⟩, K7⟩
    · rw [iteF hb] at f273
      refine spec_ifLtN_false (by rw [k5 117 fr_ne, g117, f273]; omega) ?_
      refine spec_skip hw₅ ?_
      refine none c₅ _ hAS₅ N5 R5 (fun r hr => k5 r (by
        simp only [LWn, LWl, TPn] at hr ⊢; omega))
        (by rw [hF₅.n 264 fr_ne, hF₄.n 264 fr_ne, hF₃.n 264 fr_ne, hF₂.n 264 fr_ne, h264])
        (by rw [k5 265 fr_ne, h265]) ?_ ?_
      · omega
      exact (fun ρ hρ => by
          by_cases h1 : ρ ≤ eα
          · exact hAH.left_end (by omega) ((hOL eα (by omega) hnxe).1 heβ)
              (fun h => hb (hBe.1 h)) h1
          · exact hgap ρ (by omega) hρ)
  · refine spec_ifLtN_false (by rw [f263, k2 121 (by omega), hAS.env.h.r121]; exact hα) ?_
    have hnone : α = 2 ^ T := by
      rcases hp1 with h | h
      · exact h
      · exact absurd h.1 hα
    refine spec_skip hw₂ ?_
    refine none c₂ _ hAS₂ hN₂ hM₂ (fun r hr => k2 r (by simp only [LWn, TPn] at hr; omega))
      (by rw [k2 264 (by omega), h264]) (by rw [k2 265 (by omega), h265]) ?_ ?_
    · omega
    exact (fun ρ hρ => hAH.uncov hM (fun h => h)
        (uncov_before hM (Or.inl hnone) hp2 hρ (Or.inl hnone)))

/-- **The right part of the activation.** -/
theorem actR_exec (hL : Lay P) {β : ℕ} {c₀ : Config}
    (hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own X a)
    (hOL : ∀ ρ < hbNr P.b (2 ^ T) k, ¬ X ρ → (ρ < β → a < own ρ) ∧ (β ≤ ρ → own ρ < a))
    (c : Config) (hβs : β = 2 ^ T ∨ (β < 2 ^ T ∧ tPr Q c.nmem β = 1))
    (hS : LS P B Q T k a e own X β c₀ c) (h262 : c.nreg 262 = β) :
    ∃ c' k', Exec I P.W actR c c' k' ∧ k' + LD T * nst Q (2 ^ T) c'.nmem ≤
        LD T * nst Q (2 ^ T) c.nmem + LF T + 60 ∧ LS P B Q T k a e own X (2 ^ T) c₀ c' := by
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
    refine spec_ifLtN_true (by rw [h262, hAS.env.h.r121]; exact hβ) ?_
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c hAS 263 262 fr_ne) ?_
    intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f263, hF₂, hN₂, hM₂⟩
    rw [h262] at f263
    refine spec_seq ?_
    refine spec_use (ldCurA hL (I := I) c₂ hAS₂ f263 hβ) ?_
    intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, f275, f277, hF₃, hN₃, hM₃⟩
    rw [hN₂, huβv] at f275
    refine spec_seq ?_
    refine spec_use (copyA hL (I := I) c₃ hAS₃ 274 263 fr_ne) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hAS₄, f274, hF₄, hN₄, hM₄⟩
    rw [hF₃.n 263 fr_ne, f263] at f274
    refine spec_seq ?_
    refine spec_use (btA hL (I := I) c₄ hAS₄ f274 hβ (by rw [hF₄.n 275 fr_ne, f275])
      huβ hAH.ha) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hAS₅, f273, hF₅, hN₅, hM₅⟩
    have N5 : c₅.nmem = c.nmem := by rw [hN₅, hN₄, hN₃, hN₂]
    have R5 : c₅.rmem = c.rmem := by rw [hM₅, hM₄, hM₃, hM₂]
    have e5 : ∀ r, ¬ (r = 263 ∨ r = 272 ∨ r = 274 ∨ r = 275 ∨ r = 277 ∨ r = 273 ∨
        (130 ≤ r ∧ r < 134)) → c₅.nreg r = c.nreg r := fun r hr => by
      rw [hF₅.n r (by omega), hF₄.n r (by omega), hF₃.n r (by omega), hF₂.n r (by omega)]
    by_cases hb : EE P T k e β a < EE P T k e β uβ
    · rw [iteT hb] at f273
      refine spec_ifLtN_true (by rw [e5 117 (by omega), g117, f273]; omega) ?_
      have hBβ : Bt' β := hBb.2 hb
      -- the hole ends at `β`
      have hend : ∀ (c₆ : Config), c₆.nreg 264 ≤ c₆.nreg 265 → c₆.nreg 265 = β →
          BM P T k e own X (fun ρ => c₆.nreg 264 ≤ ρ ∧ ρ < c₆.nreg 265) Q c₆.nmem c₆.rmem →
          (∀ ρ, c₆.nreg 264 ≤ ρ → ρ < c₆.nreg 265 → Bt' ρ) →
          (∀ ρ < β, Bt' ρ ↔ c₆.nreg 264 ≤ ρ ∧ ρ < c₆.nreg 265) → AS P B Q T k a e c₀ c₆ →
          c₆.nreg 263 = β → c₆.nmem = c.nmem → (k₆ : ℕ) → k₆ ≤ 56 →
          ∃ c' k', Exec I P.W (.seq (.instr (.copyN 268 110)) (.whileLtN 117 268 rwBody)) c₆ c'
            k' ∧ k₆ + k' + LD T * nst Q (2 ^ T) c'.nmem ≤
              LD T * nst Q (2 ^ T) c.nmem + LF T + 60 ∧
            LS P B Q T k a e own X (2 ^ T) c₀ c' := by
        intro c₆ hle6 h265 hM6 hb6 hda6 hAS6 h263 hN6 k₆ hk₆
        refine spec_seq ?_
        refine spec_use (copyA hL (I := I) c₆ hAS6 268 110 fr_ne) ?_
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
        obtain ⟨c₈, k₈, ex₈, hk₈, hI₈, h268'⟩ := rwLoop_exec hL (I := I) hAH hOL hI₇
        refine ⟨c₈, k₈, ex₈, ?_⟩
        have hΦ7 : wΦ Q T c₇ = LD T * nst Q (2 ^ T) c.nmem + LF T := by
          unfold wΦ; rw [iteT f268, hN₇, hN6]
        have hΦ8 : wΦ Q T c₈ = LD T * nst Q (2 ^ T) c₈.nmem := by
          unfold wΦ; rw [iteF (by omega)]; rfl
        rw [hΦ7, hΦ8] at hk₈
        have hx8 := hI₈.rx
        refine ⟨by omega, hI₈.as, by rw [hx8]; exact hI₈.mem, by rw [hx8]; exact hI₈.hb,
          by rw [hx8]; exact hI₈.le, ?_, fun ρ _ => by rw [hx8]; exact hI₈.da ρ (by omega)⟩
        by_cases hne : c₈.nreg 264 < c₈.nreg 265
        · have := (hI₈.hb (c₈.nreg 265 - 1) (by rw [← hx8]; omega) (by omega)).1; omega
        · rw [hx8] at hne; omega
      by_cases hne : c₅.nreg 264 < c₅.nreg 265
      · refine spec_seq ?_
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
        obtain ⟨c', k', ex, hk, hS'⟩ := hend c₅ hle h265
          (by rw [e5 264 (by omega), e5 265 (by omega), N5, R5]; exact hM) hb5
          (fun ρ hρ => by rw [e5 264 (by omega), e5 265 (by omega)]; exact hS.da ρ hρ) hAS₅
          (by rw [hF₅.n 263 fr_ne, hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, f263]) N5
          (k₂ + k₃ + k₄ + k₅ + 3) (by omega)
        exact ⟨c', k', ex, by omega, hS'⟩
      · refine spec_seq ?_
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
        obtain ⟨c', k', ex, hk, hS'⟩ := hend c₆ (by omega) f265
          (by
            rw [f264, f265, N6, R6]
            exact hM.rearr (fun ρ _ => or_congr_right ⟨fun h => by omega, fun h => by omega⟩)
              (fun ρ hρ => absurd hρ (by omega)))
          (fun ρ h1 h2 => by omega)
          (fun ρ hρ => by rw [f264, f265, hS.da ρ hρ]; omega) hAS₆
          (by rw [F6.n 263 fr_ne, hF₅.n 263 fr_ne, hF₄.n 263 fr_ne, hF₃.n 263 fr_ne, f263]) N6
          (k₂ + k₃ + k₄ + k₅ + 6) (by omega)
        exact ⟨c', k', ex, by omega, hS'⟩
    · rw [iteF hb] at f273
      refine spec_ifLtN_false (by rw [e5 117 (by omega), g117, f273]; omega) ?_
      refine spec_skip hw₅ ⟨by rw [N5]; omega, hAS₅, ?_, ?_, ?_, ?_, fun ρ hρ => ?_⟩
      · rw [e5 264 (by omega), e5 265 (by omega), N5, R5]; exact hM
      · rw [e5 264 (by omega), e5 265 (by omega)]; exact hS.hb
      · rw [e5 264 (by omega), e5 265 (by omega)]; exact hS.le
      · rw [e5 265 (by omega)]; omega
      · rw [e5 264 (by omega), e5 265 (by omega)]
        by_cases h1 : ρ < β
        · exact hS.da ρ h1
        · exact ⟨fun h => absurd h (hAH.right_start ((hOL β (by omega) hnxb).2 le_rfl)
            (fun h' => hb (hBb.1 h')) (by omega)), fun h => by omega⟩
  · refine spec_ifLtN_false (by rw [h262, hAS.env.h.r121]; exact hβ) ?_
    have hβe : β = 2 ^ T := by omega
    refine spec_skip hAS.wb ⟨by omega, hAS, hM, hS.hb, hS.le, by omega, fun ρ hρ => ?_⟩
    exact hS.da ρ (by omega)

/-- The cost of an activation, besides the deleted triplets. -/
def actCost (T : ℕ) : ℕ := 3 * rmqCost T + 500 * T + 700

/-- **The activation when the half block has an active source** (`PlanarFlow.Monge.FR.MHInv`
at the popped key `κ`, the values of `a` at least `κ`): the owners become
`PlanarFlow.Monge.FR.newOwn`. -/
theorem actGen_exec (hL : Lay P) {κ : ℝ} (c : Config) (hAS : AS P B Q T k a e c c)
    (hTR : TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
      Act own X κ Q c.nmem c.rmem)
    (hA : AntiM (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ T) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ T) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ T) k ρ a) :
    ∃ c' k', Exec I P.W actGen c c' k' ∧
      k' + LD T * nst Q (2 ^ T) c'.nmem ≤ LD T * nst Q (2 ^ T) c.nmem + actCost T ∧
      AS P B Q T k a e c c' ∧
      TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
        (fun σ => Act σ ∨ σ = a)
        (newOwn (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ) own a) X κ Q c'.nmem c'.rmem := by
  have hM := hTR.mem
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  obtain ⟨hMH, -⟩ := hTR.heap.activate hA hna ha hκ
  have hAH : AH (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e Act own
      X a := ⟨hTR.heap.ok, hA, hna, ha, fun ρ hρ hX hB =>
        absurd ((hTR.heap.frz ρ hρ hX).trans (hκ ρ hρ)) (not_le.2 hB.2)⟩
  unfold actGen
  refine spec_seq ?_
  refine spec_use (copyA hL (I := I) c hAS 221 260 fr_ne) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hAS₂, f221, hF₂, hN₂, hM₂⟩
  rw [hAS.ra] at f221
  refine spec_seq ?_
  refine spec_use (tBnd_exec (I := I) c₂ hw₂ hAS₂.env.g hAS₂.tc hAS₂.hQ hAS₂.env.h.r121 f221
    (by rw [hN₂]; exact hM.pr01) (by rw [hN₂]; exact hTR.anti) (by rw [hN₂]; exact hM.wl)) ?_
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
  refine spec_seq ?_
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
  refine spec_seq ?_
  refine spec_use (tPvA hL (I := I) c₄ hAS₄ f221' (by rw [N4, R4]; exact hM)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨hAS₅, hp1, hp2, hF₅, hN₅, hM₅⟩
  rw [N4] at hp1 hp2
  have N5 : c₅.nmem = c.nmem := by rw [hN₅, N4]
  have R5 : c₅.rmem = c.rmem := by rw [hM₅, R4]
  refine spec_seq ?_
  obtain ⟨c₆, k₆, ex₆, hk₆, hS₆, hK₆⟩ := actL_exec hL (I := I) hAH hOL c₅ (by rw [N5]; exact hβs)
    hAS₅ (by rw [N5, R5]; exact hM) (by rw [hF₅.n 264 fr_ne, f264])
    (by rw [hF₅.n 265 fr_ne, f265]) (by rw [N5]; exact hp1) (by rw [N5]; exact hp2)
  refine ⟨c₆, k₆, ex₆, ?_⟩
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
  refine spec_seq ?_
  obtain ⟨c₇, k₇, ex₇, hk₇, hS₇⟩ := actR_exec hL (I := I) hAH hOL c₆ hβs6 hS₆
    (by rw [hK₆ 262 fr_ne, hF₅.n 262 fr_ne, f262])
  refine ⟨c₇, k₇, ex₇, ?_⟩
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
  · refine spec_ifLtN_true (by rw [hxv, hyv]; exact hne) ?_
    refine spec_seq ?_
    exec_block
    generalize hc₈ : (Config.mk _ _ _ _ _ _ : Config) = c₈
    have hw₈ : WordsBounded P.W c₈ := hc₈ ▸ ‹_›
    have F8 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c₇ c₈ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₈]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₈], by rw [← hc₈]⟩
    have hAS₈ := hAS₇.next hL hw₈ F8 fr_incl (fun _ h => False.elim h)
      (fun x _ => by rw [← hc₈]) (fun x _ => by rw [← hc₈])
    have hlast : Bt' (hy - 1) := (hda7 (hy - 1) (by have := hS₇.lez; omega)).2 ⟨by omega, by omega⟩
    refine spec_use (tPutA hL (I := I) (σ := a) (j1 := hx) (j2 := hy) (e := e) (X := X)
      (own := newOwn (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ) own a)
      (H := fun ρ => hx ≤ ρ ∧ ρ < hy) c₈ hAS₈
      (by rw [← hc₈]; exact hM7') (by rw [← hc₈]; config_simp; exact hAS₇.ra) ha
      (by rw [← hc₈]; config_simp; exact hxv) (by rw [← hc₈]; config_simp; exact hyv) hne
      (by have := hlast.1; omega) (fun ρ h1 h2 => ⟨h1, h2⟩) (fun ρ h1 h2 => by
        unfold newOwn
        rw [iteT ((hda7 ρ (by have := hS₇.lez; omega)).2 ⟨h1, h2⟩).2])) ?_
    intro c₉ k₉ hk₉ hw₉ ⟨hAS₉, hM₉, hn₉, hF₉⟩
    refine ⟨?_, hAS₉, hMH, hM₉.rearr (fun ρ _ => or_congr_right ⟨fun h => h.elim,
      fun h => absurd h.1 h.2⟩) (fun ρ h => h.elim)⟩
    have e8 : c₈.nmem = c₇.nmem := by rw [← hc₈]
    rw [hn₉, e8, Nat.mul_succ, ← N5]
    unfold actCost LF LD srchCost tBndCost at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₇.nmem = M7 at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M6 at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₅.nmem = M5 at *
    omega
  · refine spec_ifLtN_false (by rw [hxv, hyv]; exact hne) ?_
    refine spec_skip hS₇.as.wb ⟨?_, hAS₇, hMH, hM7'.rearr (fun ρ _ => or_congr_right
      ⟨fun h => h.elim, fun h => by omega⟩) (fun ρ h => h.elim)⟩
    rw [← N5]
    unfold actCost LF LD srchCost tBndCost at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₇.nmem = M7 at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₆.nmem = M6 at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c₅.nmem = M5 at *
    omega

/-- The flag of a half block: it has an active source. -/
def tFlag (Q T : ℕ) (nm : ℕ → ℕ) : ℕ := nm (Q + 12 * 2 ^ T)

/-- **The first activation**: no active source, no extracted row, all rows in the hole; `a`
becomes the owner of all the rows. -/
theorem actFirst_exec (hL : Lay P) {κ : ℝ} (c : Config) (hAS : AS P B Q T k a e c c)
    (ha : a < hbNc P.b (2 ^ T) k) (hno : ∀ σ, ¬ Act σ) (hX : ∀ ρ, ¬ X ρ)
    (hM : BM P T k e own X (fun ρ => ρ < hbNr P.b (2 ^ T) k) Q c.nmem c.rmem) :
    ∃ c' k', Exec I P.W actFirst c c' k' ∧
      k' + LD T * nst Q (2 ^ T) c'.nmem ≤ LD T * nst Q (2 ^ T) c.nmem + actCost T ∧
      AS P B Q T k a e c c' ∧
      TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k) e
        (fun σ => Act σ ∨ σ = a) (fun _ => a) X κ Q c'.nmem c'.rmem := by
  have hnr : hbNr P.b (2 ^ T) k ≤ 2 ^ T := hM.nr_le
  have hnr1 : 1 ≤ hbNr P.b (2 ^ T) k := by
    have := hAS.ks; unfold hbNr; have := Nat.one_le_two_pow (n := T); omega
  have hc := hAS.wb
  unfold actFirst
  refine spec_seq ?_
  exec_block
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded P.W c₂ := hc₂ ▸ ‹_›
  have F2 : Fr (fun r => 200 ≤ r ∧ r < 203) (fun _ => False) c c₂ :=
    ⟨fun r hr => by beta_reduce at hr; rw [← hc₂]; config_simp; upd_tac,
      fun _ _ => by rw [← hc₂], by rw [← hc₂]⟩
  have hAS₂ := hAS.next hL hw₂ F2 fr_incl (fun _ h => False.elim h) (fun x _ => by rw [← hc₂])
    (fun x _ => by rw [← hc₂])
  have hM₂ : BM P T k e (fun _ => a) X (fun ρ => ρ < hbNr P.b (2 ^ T) k) Q c₂.nmem c₂.rmem := by
    rw [← hc₂]; exact hM.congr_own fun ρ _ _ h => absurd h (by simpa using ‹_ < _›)
  refine spec_use (tPutA hL (I := I) (σ := a) (j1 := 0) (j2 := hbNr P.b (2 ^ T) k) (e := e)
    (X := X) (own := fun _ => a) (H := fun ρ => ρ < hbNr P.b (2 ^ T) k) c₂ hAS₂ hM₂
    (by rw [← hc₂]; config_simp; exact hAS.ra) ha
    (by rw [← hc₂]; config_simp; exact hAS.env.g.r117)
    (by rw [← hc₂]; config_simp; exact hAS.env.h.r125) (by omega) le_rfl
    (fun ρ _ h2 => h2) (fun _ _ _ => rfl)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hAS₃, hM₃, hn₃, hF₃⟩
  refine ⟨?_, hAS₃, ⟨⟨⟨fun σ h => h.elim (fun h' => absurd h' (hno σ)) (fun h' => h' ▸ ha),
    fun _ _ => Or.inr rfl, fun ρ _ σ hσ => ?_, fun _ _ _ _ => le_rfl⟩,
    fun ρ _ h => absurd h (hX ρ)⟩, hM₃.rearr (fun ρ _ => or_congr_right
      ⟨fun h => h.elim, fun h => absurd ⟨by omega, h.1⟩ h.2⟩) (fun ρ h => h.elim)⟩⟩
  · have e2 : c₂.nmem = c.nmem := by rw [← hc₂]
    rw [hn₃, e2, Nat.mul_succ]
    unfold actCost LD at *
    generalize (70 * T + 140) * nst Q (2 ^ T) c.nmem = M
    omega
  · rcases hσ with h | rfl
    · exact absurd h (hno σ)
    · exact le_rfl

/-- **The activation of a source** `a` in the current half block (`r260 = a`): from the
representation of the bipartite Monge heap at the popped key `κ` (or, when the flag is `0`, no
active source, no extracted row), with the values of `a` at least `κ`, `act` leaves the
representation with `a` active (owners `PlanarFlow.Monge.FR.newOwn`, or `a` everywhere), and the
flag `1`; its cost, besides the triplets it deletes (each paying `LD T`), is `actCost T + 9`. -/
theorem act_exec (hL : Lay P) {κ : ℝ} (c : Config) (hAS : AS P B Q T k a e c c)
    (hA : AntiM (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ T) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ T) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ T) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ T) k ρ a)
    (hpre : (tFlag Q T c.nmem = 0 ∧ (∀ σ, ¬ Act σ) ∧ (∀ ρ, ¬ X ρ) ∧
        BM P T k e own X (fun ρ => ρ < hbNr P.b (2 ^ T) k) Q c.nmem c.rmem) ∨
      (tFlag Q T c.nmem = 1 ∧ TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
        (hbF P.b P.D P.p (2 ^ T) k) e Act own X κ Q c.nmem c.rmem)) :
    ∃ c' k', Exec I P.W act c c' k' ∧
      k' + LD T * nst Q (2 ^ T) c'.nmem ≤ LD T * nst Q (2 ^ T) c.nmem + actCost T + 9 ∧
      AS P B Q T k a e c c' ∧ tFlag Q T c'.nmem = 1 ∧
      ∃ own', TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k)
        e (fun σ => Act σ ∨ σ = a) own' X κ Q c'.nmem c'.rmem ∧
        ∀ ρ, own' ρ = a ∨ own' ρ = own ρ := by
  have hc := hAS.wb
  have hQ := hAS.hQ
  have g := hAS.env.g
  have h121 := hAS.env.h.r121
  have g209 := hAS.tc.r209
  have e12 : 2 ^ T * 4 + (Q + 8 * 2 ^ T) = Q + 12 * 2 ^ T := by ring
  have hs1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  unfold act
  refine spec_seq ?_
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
  -- the final write of the flag
  have fin : ∀ (c₃ : Config) (k₃ : ℕ) (own' : ℕ → ℕ), AS P B Q T k a e c c₃ →
      k₃ + LD T * nst Q (2 ^ T) c₃.nmem ≤ LD T * nst Q (2 ^ T) c.nmem + actCost T + 6 →
      TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k) (hbF P.b P.D P.p (2 ^ T) k)
        e (fun σ => Act σ ∨ σ = a) own' X κ Q c₃.nmem c₃.rmem →
      (∀ ρ, own' ρ = a ∨ own' ρ = own ρ) →
      ∃ c' k', Exec I P.W (block [.mulN 261 121 116, .addN 261 261 209, .storeN 261 110]) c₃
        c' k' ∧ k₃ + k' + LD T * nst Q (2 ^ T) c'.nmem ≤
          LD T * nst Q (2 ^ T) c.nmem + actCost T + 9 ∧
        AS P B Q T k a e c c' ∧ tFlag Q T c'.nmem = 1 ∧
        ∃ own', TRep (2 ^ T) (hbNr P.b (2 ^ T) k) (hbNc P.b (2 ^ T) k)
          (hbF P.b P.D P.p (2 ^ T) k) e (fun σ => Act σ ∨ σ = a) own' X κ Q c'.nmem c'.rmem ∧
          ∀ ρ, own' ρ = a ∨ own' ρ = own ρ := by
    intro c₃ k₃ own' hAS₃ hk₃ hTR₃ hown'
    have hw₃ := hAS₃.wb
    have h121' := hAS₃.env.h.r121
    have g' := hAS₃.env.g
    have g209' := hAS₃.tc.r209
    exec_block
    · rw [h121', g'.r116]; omega
    · config_simp; rw [h121', g'.r116, g209']; omega
    generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
    have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
    have e4 : c₄.nmem = upd c₃.nmem (Q + 12 * 2 ^ T) 1 := by
      rw [← hc₄]; config_simp; rw [h121', g'.r116, g209', e12, g'.r110]
    have F4 : Fr (fun r => r = 261) (fun _ => False) c₃ c₄ :=
      ⟨fun r hr => by beta_reduce at hr; rw [← hc₄]; config_simp; upd_tac,
        fun _ _ => by rw [← hc₄], by rw [← hc₄]⟩
    have hAS₄ := hAS₃.next hL hw₄ F4 fr_incl (fun _ h => False.elim h)
      (fun x hx => by rw [e4, upd_other _ _ _ (by omega)]) (fun x _ => by rw [← hc₄])
    have N4 : nst Q (2 ^ T) c₄.nmem = nst Q (2 ^ T) c₃.nmem := by
      unfold nst; congr 1; ext y
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> unfold tPr at h2 ⊢ <;>
        rw [e4, upd_other _ _ _ (by omega)] at * <;> exact h2
    refine ⟨by rw [N4]; omega, hAS₄, by unfold tFlag; rw [e4, upd_same], own',
      ⟨hTR₃.heap, hTR₃.mem.congr_mem (fun x h1 h2 => by rw [e4, upd_other _ _ _ (by omega)])
        (fun x _ _ => by rw [← hc₄])⟩, hown'⟩
  rcases hpre with ⟨hf, hno, hX, hM⟩ | ⟨hf, hTR⟩
  · refine spec_seq ?_
    obtain ⟨c₃, k₃, ex₃, hk₃, hAS₃, hTR₃⟩ := actFirst_exec hL (I := I) (κ := κ) c₂ hAS₂.rebase
      ha hno hX (by rw [N2, R2]; exact hM)
    refine ⟨c₃, k₃ + 1, .ifLtN_true (by rw [f262, hf, hAS₂.env.g.r110]; omega) ex₃, ?_⟩
    obtain ⟨c', k', ex, hk, rest⟩ := fin c₃ (3 + (k₃ + 1)) (fun _ => a) (hAS₂.trans hAS₃)
      (by rw [N2] at hk₃; omega) hTR₃ (fun _ => Or.inl rfl)
    exact ⟨c', k', ex, by omega, rest⟩
  · refine spec_seq ?_
    obtain ⟨c₃, k₃, ex₃, hk₃, hAS₃, hTR₃⟩ := actGen_exec hL (I := I) c₂ hAS₂.rebase
      (by rw [N2, R2]; exact hTR) hA hna ha hκ
    refine ⟨c₃, k₃ + 2, .ifLtN_false (by rw [f262, hf, hAS₂.env.g.r110]; omega) ex₃, ?_⟩
    obtain ⟨c', k', ex, hk, rest⟩ := fin c₃ (3 + (k₃ + 2)) _ (hAS₂.trans hAS₃)
      (by rw [N2] at hk₃; omega) hTR₃ (fun ρ => by
        unfold newOwn; split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl)
    exact ⟨c', k', ex, by omega, rest⟩

end walk

end FR

end Monge

end PlanarFlow
