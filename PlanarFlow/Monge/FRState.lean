module

public import PlanarFlow.Monge.FRBlocks
public import PlanarFlow.Monge.FRInv

/-!
# FR-Dijkstra on the machine: the state of a run

The state of a run of FR-Dijkstra with lazy extraction, in terms of the memory, at the popped
key `κ` (`MSt`):

* the heap of the vertices (`Hp`), the ghost run `(K, v, d)` (`Gh`), the claims of the explicit
  arcs (`Arcs`), and every key of the heap of the vertices at least `κ` (`kmin`);
* every half block `(t, k)` (`BS`): its range-minimum structure is built (when it has a source),
  the record of its leaf in the heap of the half blocks holds its parameters, its extracted rows
  `X t k` have settled targets (or the target `xe` being settled), and either it has no active
  source and no triplet (flag `0`), or its triplets represent the bipartite Monge heap
  (`PlanarFlow.Monge.FR.TRep`) of the active sources, the settled sources except the pending ones
  `pA` (`hbAct`), with every row not extracted at least `κ`; its leaf holds its item;
* the heap of the half blocks (`BH`).

* `BS.congr`: a half block depends only on its triplets, its leaf, the memory from `rb` on, its
  active sources and their distances, and the targets of its extracted rows.
* `MSt.raise`: the popped key may be raised to a key not larger than both roots.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The definitions -/

/-- **The state of the half block `(t, k)`** at the popped key `κ`, with the pending activations
`pA`, the target `xe` being settled and the extracted rows `X`. -/
structure BS (P : Prm) (κ : ℝ) (pA : ℕ → ℕ → Prop) (xe : ℕ → Prop) (X : ℕ → Prop)
    (nm : ℕ → ℕ) (rm : ℕ → ℝ) (t k : ℕ) : Prop where
  ready : 0 < hbNc P.b (2 ^ t) k → QReady P (rbB P t k) (2 ^ t) k nm
  leaf : LeafP P nm t k
  xs : ∀ ρ, X ρ → ρ < hbNr P.b (2 ^ t) k ∧
    (sfV P nm (k * 2 ^ t + ρ) = 1 ∨ xe (k * 2 ^ t + ρ))
  rep : ∃ own : ℕ → ℕ,
    (tFlag (tbQ P t k) t nm = 0 ∧ (∀ σ, ¬ hbAct P pA nm t k σ) ∧ (∀ ρ, ¬ X ρ) ∧
      BM P t k (hbe P rm t k) own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) (tbQ P t k) nm rm) ∨
    (tFlag (tbQ P t k) t nm = 1 ∧
      TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k)
        (hbe P rm t k) (hbAct P pA nm t k) own X κ (tbQ P t k) nm rm ∧
      ∀ ρ < hbNr P.b (2 ^ t) k, ¬ X ρ →
        κ ≤ hbe P rm t k (own ρ) + hbF P.b P.D P.p (2 ^ t) k ρ (own ρ))
  sync : tPr P.bh nm (bid P t k) =
    if tPr (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) = 1 then 1 else 0
  key : tPr (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) = 1 →
    tKey P.bh rm (bid P t k) = tKey (tbQ P t k) rm (tWn (tbQ P t k) (2 ^ t) nm 1)

/-- **The heap of the half blocks**: both tournaments, the present flags at most `1`, and a
present leaf is the leaf of a half block. -/
structure BH (P : Prm) (nm : ℕ → ℕ) (rm : ℕ → ℝ) : Prop where
  pr : ∀ y < 2 ^ P.TB, tPr P.bh nm y ≤ 1
  win : WinOK (2 ^ P.TB) (tPr P.bh nm) (tKey P.bh rm) (tWn P.bh (2 ^ P.TB) nm) 0
  wl : WinOK (2 ^ P.TB) (tPr P.bh nm) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) nm) 0
  leaf : ∀ y < 2 ^ P.TB, tPr P.bh nm y = 1 →
    ∃ t k, 2 ^ t < P.b ∧ k * 2 ^ t < P.b ∧ y = bid P t k

/-- **The state of a run** at the popped key `κ`: the ghost run `(K, v, d)`, the pending
activations `pA`, the target `xe` being settled, the explicit arcs `ex` not relaxed yet, the
extracted rows `X t k` of the half blocks. -/
structure MSt (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (κ : ℝ) (pA : ℕ → ℕ → Prop)
    (xe : ℕ → Prop) (ex : ℕ → ℕ → Prop) (X : ℕ → ℕ → ℕ → Prop) (nm : ℕ → ℕ) (rm : ℕ → ℝ) :
    Prop where
  hp : Hp P nm rm
  gh : Gh P K v d nm rm
  arcs : Arcs P ex nm rm
  kmin : ∀ y < P.N, prV P nm y = 1 → κ ≤ keyV P rm y
  blk : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → BS P κ pA xe (X t k) nm rm t k
  bh : BH P nm rm

/-- No target being settled. -/
def F1 (_ : ℕ) : Prop := False

/-- **The price function is feasible** for the arcs. -/
def Feas (P : Prm) : Prop := ∀ u y ℓ, IsArc P u y ℓ → P.p y ≤ P.p u + ℓ

variable {P : Prm}

/-! ### Congruences -/

section congr

variable {nr nc : ℕ} {E E' : ℕ → ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ} {X : ℕ → Prop} {κ : ℝ}

/-- An owner map depends only on the entries of the active sources. -/
theorem OwnOK.congr_E (h : OwnOK nr nc E Act own)
    (hE : ∀ ρ σ, Act σ → E' ρ σ = E ρ σ) : OwnOK nr nc E' Act own :=
  ⟨h.lt, h.act, fun ρ hρ σ hσ => by rw [hE _ _ (h.act ρ hρ), hE _ _ hσ]; exact h.best ρ hρ σ hσ,
    h.anti⟩

theorem MHInv.congr_E (h : MHInv nr nc E Act own X κ)
    (hE : ∀ ρ σ, Act σ → E' ρ σ = E ρ σ) : MHInv nr nc E' Act own X κ :=
  ⟨h.ok.congr_E hE, fun ρ hρ hX => by rw [hE _ _ (h.ok.act ρ hρ)]; exact h.frz ρ hρ hX⟩

/-- **The representation depends only on the entries of the active sources.** -/
theorem TRep.congr_e {s : ℕ} {F : ℕ → ℕ → ℝ} {e e' : ℕ → ℝ} {Q : ℕ} {nm : ℕ → ℕ}
    {rm : ℕ → ℝ} (h : TRep s nr nc F e Act own X κ Q nm rm) (he : ∀ σ, Act σ → e' σ = e σ) :
    TRep s nr nc F e' Act own X κ Q nm rm := by
  refine ⟨h.heap.congr_E fun ρ σ hσ => by simp only [he σ hσ], h.mem.congr_e fun x hx hp => ?_⟩
  have hst := h.mem.st x hx hp
  rw [← h.mem.own x hx hp x le_rfl hst.1]
  exact he _ (h.heap.ok.act _ (by omega))

end congr

/-- A half block in the state of flag `0` has no present triplet. -/
lemma BM.no_start {t k : ℕ} {e : ℕ → ℝ} {own : ℕ → ℕ} {X : ℕ → Prop} {Q : ℕ} {nm : ℕ → ℕ}
    {rm : ℕ → ℝ} (h : BM P t k e own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) Q nm rm) {x : ℕ}
    (hx : x < 2 ^ t) : tPr Q nm x ≠ 1 := by
  intro hp
  have hst := h.st x hx hp
  exact ((h.cover x (by omega)).2 ⟨x, hx, hp, le_rfl, hst.1⟩).2 (by omega)

/-- The entries of a half block in the state of flag `0` do not matter. -/
lemma BM.congr_e0 {t k : ℕ} {e e' : ℕ → ℝ} {own : ℕ → ℕ} {X : ℕ → Prop} {Q : ℕ} {nm : ℕ → ℕ}
    {rm : ℕ → ℝ} (h : BM P t k e own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) Q nm rm) :
    BM P t k e' own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) Q nm rm :=
  TMem.congr_e h fun _ hx hp => absurd hp (h.no_start hx)

/-- The triplets of a half block, its flag and its root depend on its `16 s` cells. -/
lemma tRoot_congr {Q s : ℕ} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} (hs : 1 ≤ s)
    (hq : ∀ a, Q ≤ a → a < Q + 16 * s → nm' a = nm a)
    (hqr : ∀ a, Q ≤ a → a < Q + 8 * s → rm' a = rm a)
    (hw : tWn Q s nm 1 < s) :
    tWn Q s nm' 1 = tWn Q s nm 1 ∧ tPr Q nm' (tWn Q s nm 1) = tPr Q nm (tWn Q s nm 1) ∧
      tKey Q rm' (tWn Q s nm 1) = tKey Q rm (tWn Q s nm 1) ∧
      tMin Q nm' (tWn Q s nm 1) = tMin Q nm (tWn Q s nm 1) := by
  refine ⟨hq _ (by omega) (by omega), hq _ (by omega) (by omega),
    hqr _ (by omega) (by omega), hq _ (by omega) (by omega)⟩

/-- **A half block depends only on** its triplets, its leaf, the memory from `rb` on, its active
sources and their distances, and the targets of its extracted rows. -/
theorem BS.congr {κ : ℝ} {pA pA' : ℕ → ℕ → Prop} {xe xe' : ℕ → Prop} {X : ℕ → Prop}
    {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {t k : ℕ} (h : BS P κ pA xe X nm rm t k)
    (hA : ∀ σ, hbAct P pA' nm' t k σ ↔ hbAct P pA nm t k σ)
    (he : ∀ σ, hbAct P pA nm t k σ → hbe P rm' t k σ = hbe P rm t k σ)
    (hx : ∀ ρ, X ρ → (sfV P nm (k * 2 ^ t + ρ) = 1 ∨ xe (k * 2 ^ t + ρ)) →
      (sfV P nm' (k * 2 ^ t + ρ) = 1 ∨ xe' (k * 2 ^ t + ρ)))
    (hq : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 16 * 2 ^ t → nm' a = nm a)
    (hqr : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 8 * 2 ^ t → rm' a = rm a)
    (hl : ∀ j < 6, nm' (P.bh + 8 * bid P t k + j) = nm (P.bh + 8 * bid P t k + j))
    (hlr : rm' (P.bh + 8 * bid P t k) = rm (P.bh + 8 * bid P t k))
    (hr : ∀ a, P.rb ≤ a → nm' a = nm a) : BS P κ pA' xe' X nm' rm' t k := by
  obtain ⟨hR, hLf, hX, ⟨own, hrep⟩, hsy, hk⟩ := h
  have eA : hbAct P pA' nm' t k = hbAct P pA nm t k := funext fun σ => propext (hA σ)
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hq12 : ∀ a, tbQ P t k ≤ a → a < tbQ P t k + 12 * 2 ^ t → nm' a = nm a :=
    fun a h1 h2 => hq a h1 (by omega)
  have hflag : tFlag (tbQ P t k) t nm' = tFlag (tbQ P t k) t nm := hq _ (by omega) (by omega)
  -- the root of the triplets
  have hroot : ∀ (hw : tWn (tbQ P t k) (2 ^ t) nm 1 < 2 ^ t),
      tWn (tbQ P t k) (2 ^ t) nm' 1 = tWn (tbQ P t k) (2 ^ t) nm 1 ∧
      tPr (tbQ P t k) nm' (tWn (tbQ P t k) (2 ^ t) nm 1) =
        tPr (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) ∧
      tKey (tbQ P t k) rm' (tWn (tbQ P t k) (2 ^ t) nm 1) =
        tKey (tbQ P t k) rm (tWn (tbQ P t k) (2 ^ t) nm 1) ∧
      tMin (tbQ P t k) nm' (tWn (tbQ P t k) (2 ^ t) nm 1) =
        tMin (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) := fun hw =>
    tRoot_congr hs1 hq hqr hw
  have hlp : tPr P.bh nm' (bid P t k) = tPr P.bh nm (bid P t k) := by
    have := hl 0 (by omega); simp only [Nat.add_zero] at this; exact this
  have hlk : tKey P.bh rm' (bid P t k) = tKey P.bh rm (bid P t k) := hlr
  -- the triplets
  have hrep' : (tFlag (tbQ P t k) t nm' = 0 ∧ (∀ σ, ¬ hbAct P pA' nm' t k σ) ∧ (∀ ρ, ¬ X ρ) ∧
      BM P t k (hbe P rm' t k) own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) (tbQ P t k) nm' rm') ∨
    (tFlag (tbQ P t k) t nm' = 1 ∧
      TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k)
        (hbe P rm' t k) (hbAct P pA' nm' t k) own X κ (tbQ P t k) nm' rm' ∧
      ∀ ρ < hbNr P.b (2 ^ t) k, ¬ X ρ →
        κ ≤ hbe P rm' t k (own ρ) + hbF P.b P.D P.p (2 ^ t) k ρ (own ρ)) := by
    rw [hflag, eA]
    rcases hrep with ⟨h0, hno, hX0, hM⟩ | ⟨h1, hT, hκ⟩
    · exact Or.inl ⟨h0, hno, hX0, BM.congr_e0 (hM.congr_mem (fun a h1 h2 => hq12 a h1 h2)
        (fun a h1 h2 => hqr a h1 h2))⟩
    · refine Or.inr ⟨h1, (⟨hT.heap, hT.mem.congr_mem (fun a h1 h2 => hq12 a h1 h2)
        (fun a h1 h2 => hqr a h1 h2)⟩ : TRep _ _ _ _ _ _ _ _ _ _ _ _).congr_e
        fun σ hσ => he σ hσ, fun ρ hρ hXρ => ?_⟩
      rw [he _ (hT.heap.ok.act ρ hρ)]; exact hκ ρ hρ hXρ
  have hw : tWn (tbQ P t k) (2 ^ t) nm 1 < 2 ^ t := by
    rcases hrep with ⟨-, -, -, hM⟩ | ⟨-, hT, -⟩
    · exact (win_root hM.win hs1).1
    · exact (win_root hT.mem.win hs1).1
  obtain ⟨r1, r2, r3, -⟩ := hroot hw
  refine ⟨fun hnc => (hR hnc).congr fun a ha => hr a (le_trans rb_le_rbB ha), ?_,
    fun ρ hXρ => ⟨(hX ρ hXρ).1, hx ρ hXρ (hX ρ hXρ).2⟩, ⟨own, hrep'⟩, ?_, fun h1 => ?_⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hLf
    exact ⟨by rw [hl 1 (by omega)]; exact l1, by rw [hl 2 (by omega)]; exact l2,
      by rw [hl 3 (by omega)]; exact l3, by rw [hl 4 (by omega)]; exact l4,
      by rw [hl 5 (by omega)]; exact l5⟩
  · rw [hlp, hsy, r1, r2]
  · rw [r1, r2] at h1; rw [hlk, r1, r3]; exact hk h1

/-- **A half block after a change of the memory below the triplets.** -/
theorem BS.low {κ : ℝ} {pA pA' : ℕ → ℕ → Prop} {xe xe' : ℕ → Prop} {X : ℕ → Prop}
    {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {t k : ℕ} (h : BS P κ pA xe X nm rm t k)
    (hA : ∀ σ, hbAct P pA' nm' t k σ ↔ hbAct P pA nm t k σ)
    (he : ∀ σ, hbAct P pA nm t k σ → hbe P rm' t k σ = hbe P rm t k σ)
    (hx : ∀ ρ, X ρ → (sfV P nm (k * 2 ^ t + ρ) = 1 ∨ xe (k * 2 ^ t + ρ)) →
      (sfV P nm' (k * 2 ^ t + ρ) = 1 ∨ xe' (k * 2 ^ t + ρ)))
    (hn : ∀ a, P.tb ≤ a → nm' a = nm a) (hr : ∀ a, P.tb ≤ a → rm' a = rm a) :
    BS P κ pA' xe' X nm' rm' t k := by
  have h1 : P.tb ≤ tbQ P t k := tb_le_tbQ
  have h2 : P.tb ≤ P.bh := by unfold Prm.bh; omega
  have h3 : P.bh ≤ P.rb := by unfold Prm.rb; omega
  exact h.congr hA he hx (fun a ha _ => hn a (by omega)) (fun a ha _ => hr a (by omega))
    (fun j _ => hn _ (by omega)) (hr _ (by omega)) (fun a ha => hn a (by omega))

/-- The heap of the half blocks after a change of the memory below the triplets. -/
theorem BH.low {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} (h : BH P nm rm)
    (hn : ∀ a, P.tb ≤ a → nm' a = nm a) (hr : ∀ a, P.tb ≤ a → rm' a = rm a) : BH P nm' rm' := by
  have h2 : P.tb ≤ P.bh := by unfold Prm.bh; omega
  have p : ∀ y < 2 ^ P.TB, tPr P.bh nm' y = tPr P.bh nm y := fun y _ => hn _ (by omega)
  have ky : ∀ y < 2 ^ P.TB, tKey P.bh rm' y = tKey P.bh rm y := fun y _ => hr _ (by omega)
  have wn : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWn P.bh (2 ^ P.TB) nm' i =
      tWn P.bh (2 ^ P.TB) nm i := fun i _ _ => hn _ (by omega)
  have wl : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWl P.bh (2 ^ P.TB) nm' i =
      tWl P.bh (2 ^ P.TB) nm i := fun i _ _ => hn _ (by omega)
  exact ⟨fun y hy => by rw [p y hy]; exact h.pr y hy,
    (h.win.congr_wn wn).congr (fun y hy => p y hy) (fun y hy => ky y hy),
    (h.wl.congr_wn wl).congr (fun y hy => p y hy) (fun _ _ => rfl),
    fun y hy hp => h.leaf y hy (by rw [← p y hy]; exact hp)⟩

/-- The memory above the vertices. -/
lemma tb_ge (P : Prm) : P.wb + 3 * P.N ≤ P.tb := by unfold Prm.tb Prm.hb; omega

/-! ### Settling a vertex: the header -/

/-- **The state after the header of the settling of `x`**: `x` is settled with its distance
`dK = κ + p x`, absent from the heap, and pending at every level; none of its arcs is relaxed;
the target being settled was `x`. -/
theorem MSt.header (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {xe : ℕ → Prop}
    {X : ℕ → ℕ → ℕ → Prop} {nm nm₂ : ℕ → ℕ} {rm rm₂ : ℕ → ℝ}
    (hS : MSt P K v d κ F2 xe F2 X nm rm) {x : ℕ} {dK : ℤ} (hx : x < P.N)
    (hsx : sfV P nm x = 0) (hxe : ∀ y, xe y → y = x)
    (hn1 : nm₂ (P.sb + x) = 1) (hn2 : nm₂ (P.wb + x) = 0) (hr1 : rm₂ (P.db + x) = (dK : ℝ))
    (hn : ∀ a, a ≠ P.sb + x → a ≠ P.wb + x → (a < P.wb + P.N + 1 ∨ P.wb + 2 * P.N ≤ a) →
      nm₂ a = nm a)
    (hr : ∀ a, a ≠ P.db + x → rm₂ a = rm a)
    (hW : WinOK P.N (prV P nm₂) (keyV P rm₂) (wnV P nm₂) 0) :
    MSt P (K + 1) (Function.update v K x) (Function.update d K dK) κ (pend x 0) F1
      (arcEx x (P.off x)) X nm₂ rm₂ := by
  have := lay_low hL
  have htb := tb_ge P
  have hnv : ∀ j < K, v j ≠ x := fun j hj e => by
    have := (hS.gh.sf x hx).2 ⟨j, hj, e⟩; omega
  have epr : ∀ y < P.N, y ≠ x → prV P nm₂ y = prV P nm y := fun y hy hne =>
    hn _ (by omega) (by omega) (Or.inl (by omega))
  have ekey : ∀ y < P.N, keyV P rm₂ y = keyV P rm y := fun y hy => hr _ (by omega)
  have esf : ∀ y < P.N, y ≠ x → sfV P nm₂ y = sfV P nm y := fun y hy hne =>
    hn _ (by omega) (by omega) (Or.inl (by omega))
  have edV : ∀ y < P.N, y ≠ x → dV P rm₂ y = dV P rm y := fun y hy hne => hr _ (by omega)
  have hhn : ∀ a, P.tb ≤ a → nm₂ a = nm a := fun a ha =>
    hn _ (by omega) (by omega) (Or.inr (by omega))
  have hhr : ∀ a, P.tb ≤ a → rm₂ a = rm a := fun a ha => hr _ (by omega)
  have uv : ∀ j < K, Function.update v K x j = v j := fun j hj =>
    Function.update_of_ne (by omega) _ _
  have ud : ∀ j < K, Function.update d K dK j = d j := fun j hj =>
    Function.update_of_ne (by omega) _ _
  have hsN : ∀ y < P.N, sfV P nm y = 1 ↔ ∃ i < K, v i = y := hS.gh.sf
  refine ⟨⟨hW, fun y hy => ?_, fun y hy => ?_, fun y hy h1 => ?_⟩,
    ⟨fun i hi => ?_, fun y hy => ?_, fun i hi => ?_, fun y hy h1 => ?_⟩,
    fun u hu hsu e h1 h2 hse => ?_, fun y hy h1 => ?_, fun t k ht hk => ?_,
    hS.bh.low hhn hhr⟩
  -- the heap
  · by_cases hyx : y = x
    · subst hyx; unfold prV; rw [hn2]; omega
    · rw [epr y hy hyx]; exact hS.hp.pr_le y hy
  · by_cases hyx : y = x
    · subst hyx; unfold sfV; rw [hn1]
    · rw [esf y hy hyx]; exact hS.hp.sf_le y hy
  · by_cases hyx : y = x
    · subst hyx; unfold prV at h1; rw [hn2] at h1; omega
    · rw [epr y hy hyx] at h1; rw [esf y hy hyx]; exact hS.hp.pr_sf y hy h1
  -- the ghost run
  · rcases Nat.lt_or_ge i K with h | h
    · rw [uv i h]; exact hS.gh.vlt i h
    · rw [show i = K by omega, Function.update_self]; exact hx
  · by_cases hyx : y = x
    · subst hyx; unfold sfV; rw [hn1]
      exact ⟨fun _ => ⟨K, by omega, Function.update_self ..⟩, fun _ => rfl⟩
    · rw [esf y hy hyx, hsN y hy]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, uv i hi⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i K with h | h
        · exact ⟨i, h, by rw [← uv i h]; exact e⟩
        · rw [show i = K by omega, Function.update_self] at e; exact absurd e.symm hyx
  · rcases Nat.lt_or_ge i K with h | h
    · rw [uv i h, ud i h, edV _ (hS.gh.vlt i h) (hnv i h)]; exact hS.gh.dist i h
    · rw [show i = K by omega, Function.update_self, Function.update_self]; exact hr1
  · have hyx : y ≠ x := fun e => by subst e; unfold prV at h1; rw [hn2] at h1; omega
    rw [epr y hy hyx] at h1; rw [ekey y hy]
    rcases hS.gh.just y hy h1 with h' | ⟨i, hi, ℓ, ha, hv⟩
    · exact Or.inl h'
    · exact Or.inr ⟨i, by omega, ℓ, by rw [uv i hi]; exact ha, by rw [ud i hi]; exact hv⟩
  -- the explicit arcs
  · have hdst := dst_lt' hL hu h2
    by_cases hux : u = x
    · exact Or.inl ⟨hux, by rw [← hux]; exact h1⟩
    · rw [esf u hu hux] at hsu
      have hdx : P.dst e ≠ x := fun e' => by
        rw [e'] at hse; unfold sfV at hse; rw [hn1] at hse; omega
      rw [esf _ hdst hdx] at hse
      rcases hS.arcs u hu hsu e h1 h2 hse with h' | h'
      · exact h'.elim
      · refine Or.inr ⟨by rw [epr _ hdst hdx]; exact h'.1, ?_⟩
        rw [ekey _ hdst, edV u hu hux]; exact h'.2
  -- the keys
  · have hyx : y ≠ x := fun e => by subst e; unfold prV at h1; rw [hn2] at h1; omega
    rw [epr y hy hyx] at h1; rw [ekey y hy]; exact hS.kmin y hy h1
  -- the half blocks
  · refine (hS.blk t k ht hk).low (fun σ => ?_) (fun σ hσ => ?_) (fun ρ _ h' => ?_) hhn hhr
    · unfold hbAct pend F2
      constructor
      · rintro ⟨h1, h2, h3⟩
        have : sib k * 2 ^ t + σ < P.N := by unfold hbNc at h1; omega
        have hyx : sib k * 2 ^ t + σ ≠ x := fun e => h3 ⟨e, Nat.zero_le _⟩
        rw [esf _ this hyx] at h2
        exact ⟨h1, h2, id⟩
      · rintro ⟨h1, h2, -⟩
        have : sib k * 2 ^ t + σ < P.N := by unfold hbNc at h1; omega
        have hyx : sib k * 2 ^ t + σ ≠ x := fun e => by rw [e] at h2; omega
        rw [esf _ this hyx]
        exact ⟨h1, h2, fun h => hyx h.1⟩
    · obtain ⟨h1, h2, -⟩ := hσ
      have : sib k * 2 ^ t + σ < P.N := by unfold hbNc at h1; omega
      have hyx : sib k * 2 ^ t + σ ≠ x := fun e => by rw [e] at h2; omega
      unfold hbe; exact edV _ this hyx
    · have hρ := ((hS.blk t k ht hk).xs ρ ‹_›).1
      have hlt : k * 2 ^ t + ρ < P.N := by unfold hbNr at hρ; omega
      left
      by_cases hyx : k * 2 ^ t + ρ = x
      · rw [hyx]; unfold sfV; exact hn1
      · rw [esf _ hlt hyx]
        rcases h' with h' | h'
        · exact h'
        · exact absurd (hxe _ h') hyx

/-! ### Settling a vertex: one level -/

/-- The source `σ` of a half block `k` of the level `s` is `x` exactly in the half block
`sib (x / s)`, at `x - x / s * s`. -/
lemma src_eq_iff {k s σ x : ℕ} (hσ : σ < s) :
    sib k * s + σ = x ↔ k = sib (x / s) ∧ σ = x - x / s * s := by
  constructor
  · intro h
    have h1 : x / s = sib k := by rw [← h]; exact div_eq_of_mul hσ
    refine ⟨by rw [h1, sib_sib], ?_⟩
    rw [h1]; omega
  · rintro ⟨rfl, rfl⟩
    rw [sib_sib]
    have := Nat.div_mul_le_self x s
    omega

/-- The vertices, below the triplets, are kept. -/
theorem MSt.low (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA : ℕ → ℕ → Prop}
    {xe : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ}
    {rm rm' : ℕ → ℝ} (hS : MSt P K v d κ pA xe ex X nm rm) (hn : ∀ a < P.hb, nm' a = nm a)
    (hr : ∀ a < P.hb, rm' a = rm a) :
    Hp P nm' rm' ∧ Gh P K v d nm' rm' ∧ Arcs P ex nm' rm' ∧
      (∀ y < P.N, prV P nm' y = 1 → κ ≤ keyV P rm' y) ∧
      (∀ y < P.N, sfV P nm' y = sfV P nm y) ∧ (∀ y < P.N, dV P rm' y = dV P rm y) := by
  have := lay_low hL
  have hhb : P.hb = P.wb + 3 * P.N := rfl
  refine ⟨hS.hp.low hL hn hr, hS.gh.low hL hn hr, hS.arcs.low hL hn hr fun _ _ _ _ _ h => h,
    fun y hy h1 => ?_, fun y hy => hn _ (by omega), fun y hy => hr _ (by omega)⟩
  unfold prV at h1; unfold keyV
  rw [hn _ (by omega)] at h1; rw [hr _ (by omega)]
  exact hS.kmin y hy h1

/-- **One level of the settling of `x`**: after the activation of `x` in its half block
`k₀ = sib (x / 2 ^ t₀)` of the level `2 ^ t₀` and the offer of its item (the effects of
`PlanarFlow.Monge.FR.blkStep_exec`), `x` is pending from the next level on. -/
theorem MSt.level (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {ex : ℕ → ℕ → Prop}
    {X : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {x t₀ : ℕ}
    (hS : MSt P K v d κ (pend x t₀) F1 ex X nm rm) (hx : x < P.b) (hxs : sfV P nm x = 1)
    (ht : 2 ^ t₀ < P.b) (hk : sib (x / 2 ^ t₀) * 2 ^ t₀ < P.b)
    (hf : tFlag (tbQ P t₀ (sib (x / 2 ^ t₀))) t₀ nm' = 1)
    (hTR : ∃ own' : ℕ → ℕ,
      TRep (2 ^ t₀) (hbNr P.b (2 ^ t₀) (sib (x / 2 ^ t₀))) (hbNc P.b (2 ^ t₀) (sib (x / 2 ^ t₀)))
        (hbF P.b P.D P.p (2 ^ t₀) (sib (x / 2 ^ t₀))) (hbe P rm t₀ (sib (x / 2 ^ t₀)))
        (fun σ => hbAct P (pend x t₀) nm t₀ (sib (x / 2 ^ t₀)) σ ∨ σ = x - x / 2 ^ t₀ * 2 ^ t₀)
        own' (X t₀ (sib (x / 2 ^ t₀))) κ (tbQ P t₀ (sib (x / 2 ^ t₀))) nm' rm' ∧
      ∀ ρ < hbNr P.b (2 ^ t₀) (sib (x / 2 ^ t₀)), ¬ X t₀ (sib (x / 2 ^ t₀)) ρ →
        κ ≤ hbe P rm t₀ (sib (x / 2 ^ t₀)) (own' ρ) +
          hbF P.b P.D P.p (2 ^ t₀) (sib (x / 2 ^ t₀)) ρ (own' ρ))
    (hp : ∀ y < 2 ^ P.TB, tPr P.bh nm' y = if y = bid P t₀ (sib (x / 2 ^ t₀)) then
      (if tPr (tbQ P t₀ (sib (x / 2 ^ t₀))) nm'
        (tWn (tbQ P t₀ (sib (x / 2 ^ t₀))) (2 ^ t₀) nm' 1) = 1 then 1 else 0)
      else tPr P.bh nm y)
    (hkey : tPr (tbQ P t₀ (sib (x / 2 ^ t₀))) nm'
        (tWn (tbQ P t₀ (sib (x / 2 ^ t₀))) (2 ^ t₀) nm' 1) = 1 →
      tKey P.bh rm' (bid P t₀ (sib (x / 2 ^ t₀))) = tKey (tbQ P t₀ (sib (x / 2 ^ t₀))) rm'
        (tWn (tbQ P t₀ (sib (x / 2 ^ t₀))) (2 ^ t₀) nm' 1))
    (hW : WinOK (2 ^ P.TB) (tPr P.bh nm') (tKey P.bh rm') (tWn P.bh (2 ^ P.TB) nm') 0)
    (hWl : WinOK (2 ^ P.TB) (tPr P.bh nm') (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) nm') 0)
    (hn : ∀ a, (a < tbQ P t₀ (sib (x / 2 ^ t₀)) ∨
        tbQ P t₀ (sib (x / 2 ^ t₀)) + 16 * 2 ^ t₀ ≤ a) →
      (a < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ a ∨
        (a < P.bh + 8 * 2 ^ P.TB ∧ a ≠ P.bh + 8 * bid P t₀ (sib (x / 2 ^ t₀)))) → nm' a = nm a)
    (hr : ∀ a, (a < tbQ P t₀ (sib (x / 2 ^ t₀)) ∨
        tbQ P t₀ (sib (x / 2 ^ t₀)) + 8 * 2 ^ t₀ ≤ a) →
      a ≠ P.bh + 8 * bid P t₀ (sib (x / 2 ^ t₀)) → rm' a = rm a) :
    MSt P K v d κ (pend x (t₀ + 1)) F1 ex X nm' rm' := by
  generalize hk₀ : sib (x / 2 ^ t₀) = k₀ at *
  have hs1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t₀ k₀ := tb_le_tbQ
  have htb := tb_ge P
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  have hxl := bid_lt ht hk
  have hk₀b : k₀ < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hs1) hk
  have hlo : ∀ a < P.hb, nm' a = nm a := fun a ha => hn a (Or.inl (by unfold Prm.hb at ha; omega))
    (Or.inl (by unfold Prm.hb at ha; omega))
  have hlor : ∀ a < P.hb, rm' a = rm a := fun a ha => hr a (Or.inl (by unfold Prm.hb at ha; omega))
    (by unfold Prm.hb at ha; omega)
  obtain ⟨h1, h2, h3, h4, hsf, hdv⟩ := hS.low hL hlo hlor
  have hrb : ∀ a, P.rb ≤ a → nm' a = nm a := fun a ha => hn a (Or.inr (by omega))
    (Or.inr (Or.inl (by omega)))
  have hsk : sib k₀ = x / 2 ^ t₀ := by rw [← hk₀, sib_sib]
  have hnc0 : hbNc P.b (2 ^ t₀) k₀ ≤ 2 ^ t₀ := hbNc_le
  have hdvx : x / 2 ^ t₀ * 2 ^ t₀ ≤ x := Nat.div_mul_le_self x _
  have hσx : x - x / 2 ^ t₀ * 2 ^ t₀ < hbNc P.b (2 ^ t₀) k₀ := by
    have := Nat.lt_div_mul_add (a := x) (b := 2 ^ t₀) (by omega)
    unfold hbNc; rw [hsk]; omega
  have hsrcN : ∀ t k σ, σ < hbNc P.b (2 ^ t) k → sib k * 2 ^ t + σ < P.N := fun t k σ h => by
    unfold hbNc at h; have := hL.bN; omega
  have he' : ∀ t k σ, σ < hbNc P.b (2 ^ t) k → hbe P rm' t k σ = hbe P rm t k σ :=
    fun t k σ h => hdv _ (hsrcN t k σ h)
  have hpr1 : ∀ y < 2 ^ P.TB, tPr P.bh nm' y ≤ 1 := fun y hy => by
    rw [hp y hy]; split_ifs
    · omega
    · omega
    · exact hS.bh.pr y hy
  refine ⟨h1, h2, h3, h4, fun t k ht' hk' => ?_, ⟨hpr1, hW, hWl, fun y hy hpy => ?_⟩⟩
  rotate_left
  · rw [hp y hy] at hpy
    split_ifs at hpy with hyb
    · exact ⟨t₀, k₀, ht, hk, hyb⟩
    · exact hS.bh.leaf y hy hpy
  have hB := hS.blk t k ht' hk'
  by_cases hb : t = t₀ ∧ k = k₀
  · obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨own', hT, hκ⟩ := hTR
    have hAct : hbAct P (pend x (t + 1)) nm' t k = fun σ =>
        hbAct P (pend x t) nm t k σ ∨ σ = x - x / 2 ^ t * 2 ^ t := by
      funext σ
      refine propext ⟨fun ⟨a1, a2, _⟩ => ?_, fun h => ?_⟩
      · rw [hsf _ (hsrcN _ _ _ a1)] at a2
        by_cases hx' : sib k * 2 ^ t + σ = x
        · exact Or.inr ((src_eq_iff (by omega)).1 hx').2
        · exact Or.inl ⟨a1, a2, fun h => hx' h.1⟩
      · rcases h with ⟨a1, a2, _⟩ | rfl
        · exact ⟨a1, by rw [hsf _ (hsrcN _ _ _ a1)]; exact a2, fun h => by unfold pend at h; omega⟩
        · refine ⟨hσx, ?_, fun h => by unfold pend at h; omega⟩
          rw [hsf _ (hsrcN _ _ _ hσx), (src_eq_iff (by omega)).2 ⟨hk₀.symm, rfl⟩]; exact hxs
    have hT' : TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k)
        (hbe P rm' t k) (hbAct P (pend x (t + 1)) nm' t k) own' (X t k) κ (tbQ P t k)
        nm' rm' := by
      rw [hAct]
      exact hT.congr_e fun σ hσ => he' t k σ (hT.heap.ok.lt σ hσ)
    have hroot := (win_root hT.mem.win hs1).1
    refine ⟨fun hnc => (hB.ready hnc).congr fun a ha => hrb a (le_trans rb_le_rbB ha), ?_,
      fun ρ hX => ?_, ⟨own', Or.inr ⟨hf, hT', fun ρ hρ hX => ?_⟩⟩, ?_, hkey⟩
    · obtain ⟨l1, l2, l3, l4, l5⟩ := hB.leaf
      have hl : ∀ j, 1 ≤ j → j < 6 → nm' (P.bh + 8 * bid P t k + j) =
          nm (P.bh + 8 * bid P t k + j) := fun j hj1 hj2 =>
        hn _ (Or.inr (by omega)) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      exact ⟨by rw [hl 1 (by omega) (by omega)]; exact l1,
        by rw [hl 2 (by omega) (by omega)]; exact l2, by rw [hl 3 (by omega) (by omega)]; exact l3,
        by rw [hl 4 (by omega) (by omega)]; exact l4, by rw [hl 5 (by omega) (by omega)]; exact l5⟩
    · obtain ⟨a1, a2⟩ := hB.xs ρ hX
      refine ⟨a1, ?_⟩
      rw [hsf _ (by unfold hbNr at a1; have := hL.bN; omega)]; exact a2
    · rw [he' t k _ (hT.heap.ok.lt _ (hT.heap.ok.act ρ hρ))]; exact hκ ρ hρ hX
    · simp only [hp _ hxl, ↓reduceIte]
  -- another half block
  · have hdisj := tbQ_disj ht' hk' ht hk hb
    have hkb : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) hk'
    have hbne : bid P t k ≠ bid P t₀ k₀ := fun h => hb (bid_inj hkb hk₀b h)
    have hQb' := tbQ_le_bh ht' hk'
    have hxl' := bid_lt ht' hk'
    refine hB.congr (fun σ => ?_) (fun σ hσ => he' t k σ hσ.1) (fun ρ hX h => ?_)
      (fun a h1 h2 => hn a (by omega) (Or.inl (by omega)))
      (fun a h1 h2 => hr a (by omega) (by omega))
      (fun j hj => hn _ (Or.inr (by omega)) (Or.inr (Or.inr ⟨by omega, fun h => hbne (by omega)⟩)))
      (hr _ (Or.inr (by omega)) (fun h => hbne (by omega))) hrb
    · unfold hbAct pend
      constructor
      · rintro ⟨a1, a2, a3⟩
        refine ⟨a1, by rw [← hsf _ (hsrcN _ _ _ a1)]; exact a2, fun ⟨h1, h2⟩ => a3 ⟨h1, ?_⟩⟩
        rcases Nat.eq_or_lt_of_le h2 with h2 | h2
        · subst h2
          have := (src_eq_iff (lt_of_lt_of_le a1 hbNc_le)).1 h1
          exact absurd ⟨rfl, this.1.trans hk₀⟩ hb
        · omega
      · rintro ⟨a1, a2, a3⟩
        exact ⟨a1, by rw [hsf _ (hsrcN _ _ _ a1)]; exact a2, fun ⟨h1, h2⟩ => a3 ⟨h1, by omega⟩⟩
    · have a1 := (hB.xs ρ hX).1
      rw [hsf _ (by unfold hbNr at a1; have := hL.bN; omega)]; exact h

/-! ### The pending activations, the target being settled -/

/-- **The state with other pending activations**, equivalent on the sources of the half
blocks. -/
theorem MSt.congr_pA {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA pA' : ℕ → ℕ → Prop}
    {xe xe' : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ}
    {rm : ℕ → ℝ} (hS : MSt P K v d κ pA xe ex X nm rm)
    (h : ∀ t k σ, 2 ^ t < P.b → k * 2 ^ t < P.b → σ < hbNc P.b (2 ^ t) k →
      (pA' t (sib k * 2 ^ t + σ) ↔ pA t (sib k * 2 ^ t + σ)))
    (hx : ∀ y, xe y → sfV P nm y = 1 ∨ xe' y) :
    MSt P K v d κ pA' xe' ex X nm rm :=
  ⟨hS.hp, hS.gh, hS.arcs, hS.kmin, fun t k ht hk => (hS.blk t k ht hk).congr
    (fun σ => by
      unfold hbAct
      exact ⟨fun ⟨a1, a2, a3⟩ => ⟨a1, a2, fun h' => a3 ((h t k σ ht hk a1).2 h')⟩,
        fun ⟨a1, a2, a3⟩ => ⟨a1, a2, fun h' => a3 ((h t k σ ht hk a1).1 h')⟩⟩)
    (fun _ _ => rfl) (fun ρ _ h' => h'.elim Or.inl (fun h'' => hx _ h''))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl (fun _ _ => rfl), hS.bh⟩

/-- **No pending activation** after the last level, or for a vertex which is not a corner. -/
theorem MSt.pend_end {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {xe : ℕ → Prop}
    {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ} {x t₁ : ℕ}
    (hS : MSt P K v d κ (pend x t₁) xe ex X nm rm) (h : ¬ 2 ^ t₁ < P.b ∨ ¬ x < P.b) :
    MSt P K v d κ F2 xe ex X nm rm := by
  refine hS.congr_pA (fun t k σ ht hk hσ => ?_) (fun y hy => Or.inr hy)
  unfold F2 pend
  refine ⟨False.elim, fun ⟨h1, h2⟩ => ?_⟩
  rcases h with h | h
  · exact h (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h2) ht)
  · unfold hbNc at hσ; omega

/-- **The target being settled is settled.** -/
theorem MSt.xe_done {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA : ℕ → ℕ → Prop}
    {xe : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ}
    (hS : MSt P K v d κ pA xe ex X nm rm) (h : ∀ y, xe y → sfV P nm y = 1) :
    MSt P K v d κ pA F1 ex X nm rm :=
  hS.congr_pA (fun _ _ _ _ _ _ => Iff.rfl) (fun y hy => Or.inl (h y hy))

/-! ### Decreasing a key -/

/-- **A decrease of a key** (justified, at least the popped key) keeps the state. -/
theorem MSt.dec (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA : ℕ → ℕ → Prop}
    {xe : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ}
    {rm rm' : ℕ → ℝ} {y₀ : ℕ} {val : ℝ} {D : Prop}
    (hS : MSt P K v d κ pA xe ex X nm rm) (h : DecEff P nm rm nm' rm' y₀ val D)
    (hJ : D → Just P K v d y₀ val) (hκ : D → κ ≤ val) : MSt P K v d κ pA xe ex X nm' rm' := by
  have := lay_low hL
  have htb := tb_ge P
  have hn : ∀ a, P.tb ≤ a → nm' a = nm a := fun a ha => h.nmo a (Or.inr (by omega))
  have hr : ∀ a, P.tb ≤ a → rm' a = rm a := fun a ha => h.rmo a (Or.inr (by omega))
  refine ⟨hS.hp.dec hL h, hS.gh.dec hL h hJ, fun u hu hsu e h1 h2 hse => ?_, fun y hy h1 => ?_,
    fun t k ht hk => (hS.blk t k ht hk).low (fun σ => ?_) (fun σ hσ => ?_) (fun ρ hX h' => ?_)
      hn hr, hS.bh.low hn hr⟩
  · rw [h.sf hL hu] at hsu
    have hdst := dst_lt' hL hu h2
    rw [h.sf hL hdst] at hse
    rcases hS.arcs u hu hsu e h1 h2 hse with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [h.dist hL hu]; exact h.claim hdst h')
  · by_cases hD : D ∧ y = y₀
    · obtain ⟨hD, rfl⟩ := hD
      rw [h.key1 y hy hD rfl]; exact hκ hD
    · rw [h.pr2 y hy hD] at h1; rw [h.key2 y hy hD]; exact hS.kmin y hy h1
  · unfold hbAct
    constructor
    · rintro ⟨a1, a2, a3⟩
      have : sib k * 2 ^ t + σ < P.N := by unfold hbNc at a1; omega
      exact ⟨a1, by rw [← h.sf hL this]; exact a2, a3⟩
    · rintro ⟨a1, a2, a3⟩
      have : sib k * 2 ^ t + σ < P.N := by unfold hbNc at a1; omega
      exact ⟨a1, by rw [h.sf hL this]; exact a2, a3⟩
  · have := hσ.1; unfold hbNc at this
    unfold hbe; exact h.dist hL (by omega)
  · have a1 := ((hS.blk t k ht hk).xs ρ hX).1
    rw [h.sf hL (by unfold hbNr at a1; omega)]; exact h'

/-- **Relaxing the explicit arc `e` of the settled vertex `x`** (its distance `κ + p x`, the
price function feasible). -/
theorem MSt.arc (hL : Lay P) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {x e i : ℕ}
    (hS : MSt P K v d κ F2 F1 (arcEx x e) X nm rm)
    (hD : DecEff P nm rm nm' rm' (P.dst e) (dV P rm x + P.len e - P.p (P.dst e))
      (DecDo P nm rm (P.dst e) (dV P rm x + P.len e - P.p (P.dst e))))
    (hx : x < P.N) (hi : i < K) (hvi : v i = x) (h1 : P.off x ≤ e) (h2 : e < P.off (x + 1))
    (hdx : dV P rm x = κ + P.p x) :
    MSt P K v d κ F2 F1 (arcEx x (e + 1)) X nm' rm' := by
  have hdst := dst_lt' hL hx h2
  have hJ : Just P K v d (P.dst e) (dV P rm x + P.len e - P.p (P.dst e)) := by
    refine Or.inr ⟨i, hi, P.len e, Or.inr ⟨by rw [hvi]; exact hx, e, by rw [hvi]; exact h1,
      by rw [hvi]; exact h2, rfl, rfl⟩, ?_⟩
    rw [← hvi, hS.gh.dist i hi]; push_cast; ring
  have hfe := hF x (P.dst e) (P.len e) (Or.inr ⟨hx, e, h1, h2, rfl, rfl⟩)
  have hκ : κ ≤ dV P rm x + P.len e - P.p (P.dst e) := by
    rw [hdx]; have : ((P.p (P.dst e) : ℤ) : ℝ) ≤ P.p x + P.len e := by exact_mod_cast hfe
    linarith
  have hS' := hS.dec hL hD (fun _ => hJ) (fun _ => hκ)
  refine ⟨hS'.hp, hS'.gh, fun u hu hsu e' h1' h2' hse => ?_, hS'.kmin, hS'.blk, hS'.bh⟩
  by_cases he : u = x ∧ e' = e
  · obtain ⟨rfl, rfl⟩ := he
    rw [hD.sf hL hdst] at hse
    refine Or.inr ?_
    rw [hD.dist hL hu]
    exact hD.fresh hS.hp hdst hse id
  · rcases hS'.arcs u hu hsu e' h1' h2' hse with ⟨h3, h4⟩ | h'
    · exact Or.inl ⟨h3, by
        rcases Nat.eq_or_lt_of_le h4 with h5 | h5
        · exact absurd ⟨h3, h5.symm⟩ he
        · omega⟩
    · exact Or.inr h'

/-! ### Raising the popped key, extracting an item -/

/-- **Raising the popped key** to a key not larger than every key of both heaps. -/
theorem MSt.raise {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ κ' : ℝ} {pA : ℕ → ℕ → Prop}
    {xe : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ}
    (hS : MSt P K v d κ pA xe ex X nm rm) (hκ : κ ≤ κ')
    (hv : ∀ y < P.N, prV P nm y = 1 → κ' ≤ keyV P rm y)
    (hb : ∀ y < 2 ^ P.TB, tPr P.bh nm y = 1 → κ' ≤ tKey P.bh rm y) :
    MSt P K v d κ' pA xe ex X nm rm := by
  refine ⟨hS.hp, hS.gh, hS.arcs, hv, fun t k ht hk => ?_, hS.bh⟩
  obtain ⟨hR, hLf, hX, ⟨own, hrep⟩, hsy, hky⟩ := hS.blk t k ht hk
  refine ⟨hR, hLf, hX, ⟨own, ?_⟩, hsy, hky⟩
  rcases hrep with h0 | ⟨h1, hT, -⟩
  · exact Or.inl h0
  refine Or.inr ⟨h1, ⟨hT.heap.raise hκ, hT.mem⟩, fun ρ hρ hXρ => ?_⟩
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  obtain ⟨x, hx, hpx, -⟩ := (hT.mem.cover0 (fun _ h => h) hρ).1 hXρ
  obtain ⟨-, hpw, -, -, -, -, hle⟩ := hT.item hs1 hx hpx
  have hl1 : tPr P.bh nm (bid P t k) = 1 := by rw [hsy, iteT hpw]
  have := hb _ (bid_lt ht hk) hl1
  rw [hky hpw] at this
  exact this.trans (hle ρ hρ hXρ _ (hT.heap.ok.act ρ hρ))

/-- **An operation on one half block** `(t₀, k₀)` (its triplets, its leaf and the tournaments of
the heap of the half blocks) keeps the state of the others. -/
theorem MSt.one (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {pA pA' : ℕ → ℕ → Prop}
    {xe xe' : ℕ → Prop} {ex : ℕ → ℕ → Prop} {X X' : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ}
    {rm rm' : ℕ → ℝ} {t₀ k₀ : ℕ} (hS : MSt P K v d κ pA xe ex X nm rm) (ht : 2 ^ t₀ < P.b)
    (hk : k₀ * 2 ^ t₀ < P.b) (hB : BS P κ pA' xe' (X' t₀ k₀) nm' rm' t₀ k₀)
    (hA : ∀ t k σ, 2 ^ t < P.b → k * 2 ^ t < P.b → ¬ (t = t₀ ∧ k = k₀) →
      σ < hbNc P.b (2 ^ t) k → (pA' t (sib k * 2 ^ t + σ) ↔ pA t (sib k * 2 ^ t + σ)))
    (hX : ∀ t k, ¬ (t = t₀ ∧ k = k₀) → X' t k = X t k)
    (hxe : ∀ y, xe y → xe' y)
    (hp : ∀ y < 2 ^ P.TB, y ≠ bid P t₀ k₀ → tPr P.bh nm' y = tPr P.bh nm y)
    (hpr : tPr P.bh nm' (bid P t₀ k₀) ≤ 1)
    (hW : WinOK (2 ^ P.TB) (tPr P.bh nm') (tKey P.bh rm') (tWn P.bh (2 ^ P.TB) nm') 0)
    (hWl : WinOK (2 ^ P.TB) (tPr P.bh nm') (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) nm') 0)
    (hn : ∀ a, (a < tbQ P t₀ k₀ ∨ tbQ P t₀ k₀ + 16 * 2 ^ t₀ ≤ a) →
      (a < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ a ∨
        (a < P.bh + 8 * 2 ^ P.TB ∧ a ≠ P.bh + 8 * bid P t₀ k₀)) → nm' a = nm a)
    (hr : ∀ a, (a < tbQ P t₀ k₀ ∨ tbQ P t₀ k₀ + 8 * 2 ^ t₀ ≤ a) →
      a ≠ P.bh + 8 * bid P t₀ k₀ → rm' a = rm a) :
    MSt P K v d κ pA' xe' ex X' nm' rm' := by
  have hs1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t₀ k₀ := tb_le_tbQ
  have htb := tb_ge P
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  have hxl := bid_lt ht hk
  have hk₀b : k₀ < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hs1) hk
  have hlo : ∀ a < P.hb, nm' a = nm a := fun a ha => hn a (Or.inl (by unfold Prm.hb at ha; omega))
    (Or.inl (by unfold Prm.hb at ha; omega))
  have hlor : ∀ a < P.hb, rm' a = rm a := fun a ha => hr a (Or.inl (by unfold Prm.hb at ha; omega))
    (by unfold Prm.hb at ha; omega)
  obtain ⟨h1, h2, h3, h4, hsf, hdv⟩ := hS.low hL hlo hlor
  have hrb : ∀ a, P.rb ≤ a → nm' a = nm a := fun a ha => hn a (Or.inr (by omega))
    (Or.inr (Or.inl (by omega)))
  have hsrcN : ∀ t k σ, σ < hbNc P.b (2 ^ t) k → sib k * 2 ^ t + σ < P.N := fun t k σ h => by
    unfold hbNc at h; have := hL.bN; omega
  have hpr1 : ∀ y < 2 ^ P.TB, tPr P.bh nm' y ≤ 1 := fun y hy => by
    by_cases hyb : y = bid P t₀ k₀
    · rw [hyb]; exact hpr
    · rw [hp y hy hyb]; exact hS.bh.pr y hy
  refine ⟨h1, h2, h3, h4, fun t k ht' hk' => ?_, ⟨hpr1, hW, hWl, fun y hy hpy => ?_⟩⟩
  rotate_left
  · by_cases hyb : y = bid P t₀ k₀
    · exact ⟨t₀, k₀, ht, hk, hyb⟩
    · rw [hp y hy hyb] at hpy; exact hS.bh.leaf y hy hpy
  by_cases hb : t = t₀ ∧ k = k₀
  · obtain ⟨rfl, rfl⟩ := hb; exact hB
  have hBk := hS.blk t k ht' hk'
  rw [hX t k hb]
  have hdisj := tbQ_disj ht' hk' ht hk hb
  have hkb : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) hk'
  have hbne : bid P t k ≠ bid P t₀ k₀ := fun h => hb (bid_inj hkb hk₀b h)
  have hQb' := tbQ_le_bh ht' hk'
  have hxl' := bid_lt ht' hk'
  refine hBk.congr (fun σ => ?_) (fun σ hσ => hdv _ (hsrcN t k σ hσ.1)) (fun ρ hXρ h => ?_)
    (fun a h1 h2 => hn a (by omega) (Or.inl (by omega)))
    (fun a h1 h2 => hr a (by omega) (by omega))
    (fun j hj => hn _ (Or.inr (by omega)) (Or.inr (Or.inr ⟨by omega, fun h => hbne (by omega)⟩)))
    (hr _ (Or.inr (by omega)) (fun h => hbne (by omega))) hrb
  · unfold hbAct
    constructor
    · rintro ⟨a1, a2, a3⟩
      exact ⟨a1, by rw [← hsf _ (hsrcN _ _ _ a1)]; exact a2,
        fun h' => a3 ((hA t k σ ht' hk' hb a1).2 h')⟩
    · rintro ⟨a1, a2, a3⟩
      exact ⟨a1, by rw [hsf _ (hsrcN _ _ _ a1)]; exact a2,
        fun h' => a3 ((hA t k σ ht' hk' hb a1).1 h')⟩
  · have a1 := (hBk.xs ρ hXρ).1
    rw [hsf _ (by unfold hbNr at a1; have := hL.bN; omega)]
    exact h.elim Or.inl (fun h' => Or.inr (hxe _ h'))

/-- **The extraction of the item of the half block `(t₀, k₀)`** (the effects of
`PlanarFlow.Monge.FR.extStep_exec`), at the popped key `κ`: the row `m` of the item is
extracted; its target becomes the target being settled. -/
theorem MSt.extract (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {t₀ k₀ m : ℕ} {own : ℕ → ℕ}
    (hS : MSt P K v d κ F2 F1 F2 X nm rm) (ht : 2 ^ t₀ < P.b) (hk : k₀ * 2 ^ t₀ < P.b)
    (hm : m < hbNr P.b (2 ^ t₀) k₀)
    (hT : TRep (2 ^ t₀) (hbNr P.b (2 ^ t₀) k₀) (hbNc P.b (2 ^ t₀) k₀)
      (hbF P.b P.D P.p (2 ^ t₀) k₀) (hbe P rm t₀ k₀) (hbAct P F2 nm t₀ k₀) own
      (fun ρ => X t₀ k₀ ρ ∨ ρ = m) κ (tbQ P t₀ k₀) nm' rm')
    (hown : ∀ ρ < hbNr P.b (2 ^ t₀) k₀, ¬ X t₀ k₀ ρ →
      κ ≤ hbe P rm t₀ k₀ (own ρ) + hbF P.b P.D P.p (2 ^ t₀) k₀ ρ (own ρ))
    (hf : tFlag (tbQ P t₀ k₀) t₀ nm' = 1)
    (hp : ∀ y < 2 ^ P.TB, tPr P.bh nm' y = if y = bid P t₀ k₀ then
      (if tPr (tbQ P t₀ k₀) nm' (tWn (tbQ P t₀ k₀) (2 ^ t₀) nm' 1) = 1 then 1 else 0)
      else tPr P.bh nm y)
    (hkey : tPr (tbQ P t₀ k₀) nm' (tWn (tbQ P t₀ k₀) (2 ^ t₀) nm' 1) = 1 →
      tKey P.bh rm' (bid P t₀ k₀) = tKey (tbQ P t₀ k₀) rm' (tWn (tbQ P t₀ k₀) (2 ^ t₀) nm' 1))
    (hW : WinOK (2 ^ P.TB) (tPr P.bh nm') (tKey P.bh rm') (tWn P.bh (2 ^ P.TB) nm') 0)
    (hWl : WinOK (2 ^ P.TB) (tPr P.bh nm') (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) nm') 0)
    (hn : ∀ a, (a < tbQ P t₀ k₀ ∨ tbQ P t₀ k₀ + 16 * 2 ^ t₀ ≤ a) →
      (a < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ a ∨
        (a < P.bh + 8 * 2 ^ P.TB ∧ a ≠ P.bh + 8 * bid P t₀ k₀)) → nm' a = nm a)
    (hr : ∀ a, (a < tbQ P t₀ k₀ ∨ tbQ P t₀ k₀ + 8 * 2 ^ t₀ ≤ a) →
      a ≠ P.bh + 8 * bid P t₀ k₀ → rm' a = rm a) :
    MSt P K v d κ F2 (fun y => y = k₀ * 2 ^ t₀ + m) F2
      (fun t k ρ => X t k ρ ∨ (t = t₀ ∧ k = k₀ ∧ ρ = m)) nm' rm' := by
  have hs1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t₀ k₀ := tb_le_tbQ
  have htb := tb_ge P
  have hbr : P.bh + 16 * 2 ^ P.TB = P.rb := rfl
  have hxl := bid_lt ht hk
  have hlo : ∀ a < P.hb, nm' a = nm a := fun a ha => hn a (Or.inl (by unfold Prm.hb at ha; omega))
    (Or.inl (by unfold Prm.hb at ha; omega))
  have hlor : ∀ a < P.hb, rm' a = rm a := fun a ha => hr a (Or.inl (by unfold Prm.hb at ha; omega))
    (by unfold Prm.hb at ha; omega)
  obtain ⟨-, -, -, -, hsf, hdv⟩ := hS.low hL hlo hlor
  have hsrcN : ∀ σ, σ < hbNc P.b (2 ^ t₀) k₀ → sib k₀ * 2 ^ t₀ + σ < P.N := fun σ h => by
    unfold hbNc at h; have := hL.bN; omega
  have hrb : ∀ a, P.rb ≤ a → nm' a = nm a := fun a ha => hn a (Or.inr (by omega))
    (Or.inr (Or.inl (by omega)))
  have hB := hS.blk t₀ k₀ ht hk
  have hAct : hbAct P F2 nm' t₀ k₀ = hbAct P F2 nm t₀ k₀ := by
    funext σ; unfold hbAct
    refine propext ⟨fun ⟨a1, a2, a3⟩ => ⟨a1, by rw [← hsf _ (hsrcN σ a1)]; exact a2, a3⟩,
      fun ⟨a1, a2, a3⟩ => ⟨a1, by rw [hsf _ (hsrcN σ a1)]; exact a2, a3⟩⟩
  have he : ∀ σ, hbAct P F2 nm t₀ k₀ σ → hbe P rm' t₀ k₀ σ = hbe P rm t₀ k₀ σ :=
    fun σ hσ => hdv _ (hsrcN σ hσ.1)
  have hX' : (fun ρ => X t₀ k₀ ρ ∨ (t₀ = t₀ ∧ k₀ = k₀ ∧ ρ = m)) = fun ρ => X t₀ k₀ ρ ∨ ρ = m := by
    funext ρ; simp
  have hB' : BS P κ F2 (fun y => y = k₀ * 2 ^ t₀ + m)
      ((fun t k ρ => X t k ρ ∨ (t = t₀ ∧ k = k₀ ∧ ρ = m)) t₀ k₀) nm' rm' t₀ k₀ := by
    show BS P κ F2 _ (fun ρ => X t₀ k₀ ρ ∨ (t₀ = t₀ ∧ k₀ = k₀ ∧ ρ = m)) nm' rm' t₀ k₀
    rw [hX']
    refine ⟨fun hnc => (hB.ready hnc).congr fun a ha => hrb a (le_trans rb_le_rbB ha), ?_,
      fun ρ hXρ => ?_, ⟨own, Or.inr ⟨hf, ?_, fun ρ hρ hXρ => ?_⟩⟩, ?_, hkey⟩
    · obtain ⟨l1, l2, l3, l4, l5⟩ := hB.leaf
      have hl : ∀ j, 1 ≤ j → j < 6 → nm' (P.bh + 8 * bid P t₀ k₀ + j) =
          nm (P.bh + 8 * bid P t₀ k₀ + j) := fun j hj1 hj2 =>
        hn _ (Or.inr (by omega)) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      exact ⟨by rw [hl 1 (by omega) (by omega)]; exact l1,
        by rw [hl 2 (by omega) (by omega)]; exact l2, by rw [hl 3 (by omega) (by omega)]; exact l3,
        by rw [hl 4 (by omega) (by omega)]; exact l4, by rw [hl 5 (by omega) (by omega)]; exact l5⟩
    · rcases hXρ with hXρ | rfl
      · obtain ⟨a1, a2⟩ := hB.xs ρ hXρ
        refine ⟨a1, ?_⟩
        rw [hsf _ (by unfold hbNr at a1; have := hL.bN; omega)]
        exact a2.elim Or.inl (fun h => h.elim)
      · exact ⟨hm, Or.inr rfl⟩
    · rw [hAct]; exact hT.congr_e fun σ hσ => he σ hσ
    · rw [he _ (hT.heap.ok.act ρ hρ)]; exact hown ρ hρ fun h => hXρ (Or.inl h)
    · simp only [hp _ hxl, ↓reduceIte]
  refine hS.one hL ht hk hB' (fun _ _ _ _ _ _ _ => Iff.rfl) (fun t k hb => ?_)
    (fun y h => h.elim) (fun y hy hyb => by rw [hp y hy]; simp only [hyb, ↓reduceIte])
    (by rw [hp _ hxl]; simp only [↓reduceIte]; split_ifs <;> omega) hW hWl hn hr
  funext ρ
  refine propext ⟨fun h => ?_, Or.inl⟩
  rcases h with h | ⟨rfl, rfl, -⟩
  · exact h
  · exact absurd ⟨rfl, rfl⟩ hb

/-! ### Dijkstra's algorithm -/

/-- **Every arc from a settled vertex to an unsettled one is covered**: by a present vertex
(an explicit arc, its claim) or by a present leaf of the heap of the half blocks (an arc of the
dense distance graph, by the item of its half block, `PlanarFlow.Monge.FR.TRep.item`). -/
theorem MSt.cover (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ} (hS : MSt P K v d κ F2 F1 F2 X nm rm)
    {i y : ℕ} {ℓ : ℤ} (hi : i < K) (ha : IsArc P (v i) y ℓ) (hy : sfV P nm y = 0) :
    (∃ z < P.N, Claim P nm rm z ((d i + ℓ - P.p y : ℤ) : ℝ)) ∨
      ∃ w < 2 ^ P.TB, tPr P.bh nm w = 1 ∧ tKey P.bh rm w ≤ ((d i + ℓ - P.p y : ℤ) : ℝ) := by
  have hvN := hS.gh.vlt i hi
  have hvs : sfV P nm (v i) = 1 := (hS.gh.sf _ hvN).2 ⟨i, hi, rfl⟩
  have hvd := hS.gh.dist i hi
  rcases ha with ⟨hu, hyb, hne, rfl⟩ | ⟨-, e, h1, h2, rfl, rfl⟩
  · right
    obtain ⟨t, k, ht, hk, hρ, hρe, hσ, hσe⟩ := arc_block hu hyb hne
    have hB := hS.blk t k ht hk
    have hact : hbAct P F2 nm t k (v i - sib k * 2 ^ t) := ⟨hσ, by rw [hσe]; exact hvs, id⟩
    obtain ⟨own, h0 | ⟨-, hT, -⟩⟩ := hB.rep
    · exact absurd hact (h0.2.1 _)
    have hρ' : y - k * 2 ^ t < hbNr P.b (2 ^ t) k := hρ
    have hXρ : ¬ X t k (y - k * 2 ^ t) := fun hX => by
      have := (hB.xs _ hX).2
      rw [hρe] at this
      rcases this with h | h
      · omega
      · exact h
    obtain ⟨x, hx, hpx, -⟩ := (hT.mem.cover0 (fun _ h => h) hρ').1 hXρ
    obtain ⟨-, hpw, -, -, -, -, hle⟩ := hT.item Nat.one_le_two_pow hx hpx
    refine ⟨bid P t k, bid_lt ht hk, by rw [hB.sync]; simp only [hpw, ↓reduceIte], ?_⟩
    rw [hB.key hpw]
    refine (hle _ hρ' hXρ _ hact).trans_eq ?_
    unfold hbe; rw [hσe, hvd, hbF_live (by omega), hρe, hσe]
    push_cast; ring
  · left
    have hdst := dst_lt' hL hvN h2
    rcases hS.arcs (v i) hvN hvs e h1 h2 hy with h' | h'
    · exact absurd h' id
    · refine ⟨P.dst e, hdst, h'.1, h'.2.trans_eq ?_⟩
      rw [hvd]; push_cast; ring

/-- **A key not larger than every key of both heaps is a lower bound of every arc** from a
settled vertex to an unsettled one. -/
theorem MSt.least (hL : Lay P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ κ' : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {nm : ℕ → ℕ} {rm : ℕ → ℝ} (hS : MSt P K v d κ F2 F1 F2 X nm rm)
    (hv : ∀ y < P.N, prV P nm y = 1 → κ' ≤ keyV P rm y)
    (hb : ∀ w < 2 ^ P.TB, tPr P.bh nm w = 1 → κ' ≤ tKey P.bh rm w) :
    ∀ i < K, ∀ y ℓ, IsArc P (v i) y ℓ → (∀ j < K, y ≠ v j) →
      κ' ≤ ((d i + ℓ - P.p y : ℤ) : ℝ) := by
  intro i hi y ℓ ha hy
  have hyN := ha.dst_lt hL
  have hys : sfV P nm y = 0 := by
    have := hS.hp.sf_le y hyN
    by_contra h'
    obtain ⟨j, hj, e⟩ := (hS.gh.sf y hyN).1 (by omega)
    exact hy j hj e.symm
  rcases hS.cover hL hi ha hys with ⟨z, hz, hc⟩ | ⟨w, hw, hpw, hkw⟩
  · exact (hv z hz hc.1).trans hc.2
  · exact (hb w hw hpw).trans hkw

/-- **Extending a run of Dijkstra's algorithm** by a vertex whose distance is the least over
the arcs from the settled vertices, and justified by one of them (or the root). -/
theorem MRun.ext {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} (hR : MRun P K v d) {x : ℕ} {dK : ℤ}
    (hnv : ∀ j < K, v j ≠ x) (hroot : K = 0 → x = P.r ∧ dK = 0)
    (hpar : 0 < K → ∃ i < K, ∃ ℓ, IsArc P (v i) x ℓ ∧ dK = d i + ℓ)
    (hleast : ∀ i < K, ∀ y ℓ, IsArc P (v i) y ℓ → (∀ j < K, y ≠ v j) →
      dK - P.p x ≤ d i + ℓ - P.p y) :
    MRun P (K + 1) (Function.update v K x) (Function.update d K dK) := by
  have uv : ∀ j < K, Function.update v K x j = v j := fun j hj =>
    Function.update_of_ne (by omega) _ _
  have ud : ∀ j < K, Function.update d K dK j = d j := fun j hj =>
    Function.update_of_ne (by omega) _ _
  refine ⟨fun _ => ?_, fun _ => ?_, fun i j hi hj e => ?_, fun k hk0 hk => ?_,
    fun k hk i hik y ℓ ha hy => ?_⟩
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0; rw [Function.update_self]; exact (hroot rfl).1
    · rw [uv 0 h0]; exact hR.root h0
  · rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0; rw [Function.update_self]; exact (hroot rfl).2
    · rw [ud 0 h0]; exact hR.root_d h0
  · rcases Nat.lt_or_ge i K with hi' | hi' <;> rcases Nat.lt_or_ge j K with hj' | hj'
    · rw [uv i hi', uv j hj'] at e; exact hR.inj i j hi' hj' e
    · rw [uv i hi', show j = K by omega, Function.update_self] at e
      exact absurd e (hnv i hi')
    · rw [uv j hj', show i = K by omega, Function.update_self] at e
      exact absurd e.symm (hnv j hj')
    · omega
  · rcases Nat.lt_or_ge k K with hk' | hk'
    · obtain ⟨i, hi, ℓ, ha, he⟩ := hR.parent k hk0 hk'
      exact ⟨i, hi, ℓ, by rw [uv i (by omega), uv k hk']; exact ha, by
        rw [ud k hk', ud i (by omega)]; exact he⟩
    · obtain rfl : k = K := by omega
      obtain ⟨i, hi, ℓ, ha, he⟩ := hpar hk0
      exact ⟨i, hi, ℓ, by rw [uv i hi, Function.update_self]; exact ha, by
        rw [Function.update_self, ud i hi]; exact he⟩
  · rcases Nat.lt_or_ge k K with hk' | hk'
    · rw [uv i (by omega)] at ha
      rw [ud k hk', ud i (by omega), uv k hk']
      exact hR.least k hk' i hik y ℓ ha fun j hj => by rw [← uv j (by omega)]; exact hy j hj
    · obtain rfl : k = K := by omega
      rw [uv i hik] at ha
      rw [ud i hik, Function.update_self, Function.update_self]
      exact hleast i hik y ℓ ha fun j hj => by rw [← uv j hj]; exact hy j hj

end FR

end Monge

end PlanarFlow
