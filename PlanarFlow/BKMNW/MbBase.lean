module

public import PlanarFlow.BKMNW.MbBaseC
public import PlanarFlow.BKMNW.ScertFull

/-!
# Miller's base as one program, and its specification `MbSpec'`

* **`MbSpec'`**: the revised specification of a base program for the `NoCut` case (Miller):
  as `MbSpec` (`ScertFull.lean`) but only for states that `scertD` can reach from a piece map:
  `PMap M s.1 Hs s.2.1`, `s.1` nonempty, the rotation the first return `ret τ s.1` on `s.1`, the
  weight bound `Σ_{s.1} (1 + ex) ≤ T₀`, the weight array in a word (`Σ_{j<n} EX[j] ≤ W`). (Round
  28: `MbSpec` cannot be met by a program running Miller's machine.)
* `PathNH` (the path given by the flags of its new hole at `NHb`), `pathStable_NH`;
* `mb_sem` (pure: the labels and flags computed by stages B, C mean the items and the new hole
  of `scBase`), `card_sVert_le`, `card_face_le`, `msT_mono`;
* **`mbBase := mbA ; mbB ; mbC`**, `mbT`, **`mbBase_spec`**: `mbBase` meets `MbSpec'` for the
  separator `sepC M e n Bz` it computes, within
  `mbT n Bz T₀ = 19 (Bz + 25 n + 3 T₀ + 15) + encT n + msT n (2 n) + 237 n + 1223` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **Miller's base as one program.** -/
def mbBase : Stmt := .seq mbA (.seq mbB mbC)

/-- The cost bound of `mbBase`. -/
def mbT (n Bz T₀ : ℕ) : ℕ :=
  19 * (Bz + 25 * n + 3 * T₀ + 15) + encT n + msT n (2 * n) + 237 * n + 1223

lemma msT_mono {m m' k k' : ℕ} (h1 : m ≤ m') (h2 : k ≤ k') : msT m k ≤ msT m' k' := by
  unfold msT
  have hl : Nat.log 2 k ≤ Nat.log 2 k' := Nat.log_mono_right h2
  have : (231 * m + 60 * k + 156) * Nat.log 2 k ≤ (231 * m' + 60 * k' + 156) * Nat.log 2 k' :=
    Nat.mul_le_mul (by omega) hl
  omega

section Spec

open Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map PlanarSeparator.StDart

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (P W M) in
/-- **The revised specification of a base program for the `NoCut` case** (Miller's separator):
`MbSpec` restricted to the states `scertD` reaches from a piece map (a piece map `PMap`,
nonempty, rotation the first return of `τ`, weights bounded by `T₀`, the weight array in a word).
-/
def MbSpec' (ch : ScChoice M) (Hs : List (Finset V)) (τ : Perm D) (N₀ : Finset D) (mb : Stmt)
    (T n b A W₀ ITEMb NHb T₀ : ℕ) (e : ℕ → D) (B : Finset D) (m₀ r₀ : ℕ → ℕ)
    (PathOut : Config → HPath M → Prop) : Prop :=
  ∀ (s : ScSt D) (c : Config), WordsBounded W c → LvRegs c n b Hs.length A W₀ →
    LvIn M c.nmem n b e B s.1 Hs s.2.2 → NoCut M s.1 Hs → PMap M s.1 Hs s.2.1 →
    s.1.Nonempty → (∀ x ∈ s.1, s.2.1 x = ret τ s.1 x) → s.1 ⊆ N₀ →
    ∑ d ∈ s.1, (1 + s.2.2 d) ≤ T₀ → ∑ j ∈ range n, c.nmem (b + 3 * n + j) ≤ W →
    c.nreg 4955 = ITEMb → c.nreg 4956 = NHb → (∀ a < b, c.nmem a = m₀ a) →
    (∀ x, SlFr x → (x < 4974 ∨ 4975 < x) → c.nreg x = r₀ x) →
    ∃ c' t, Exec P W mb c c' t ∧ t ≤ T ∧
      (∀ a, a < ITEMb → c'.nmem a = c.nmem a) ∧
      (∀ x, (x = 4900 ∨ x = 4931 ∨ x = 4933 ∨ x = 4936) → c'.nreg x = c.nreg x) ∧
      ((c'.nreg 4970 = 0 ∧ scBase ch Hs s = none) ∨
       (c'.nreg 4970 = 1 ∧ ∃ ρ I₀, scBase ch Hs s = some (ρ, I₀) ∧
         ItemRep e n I₀ (fun i => c'.nmem (ITEMb + i)) ∧ (∀ X ∈ I₀, X ⊆ s.1) ∧
         (∀ i < n, (c'.nmem (NHb + i) ≠ 0 ↔ M.tail (e i) ∈ newHole Hs ρ.mverts)) ∧
         1 ≤ c'.nreg 4944 ∧ c'.nreg 4944 ≤ n + 2 ∧
         (∀ i < n, c'.nmem (ITEMb + i) < c'.nreg 4944) ∧
         c'.nreg 4943 = NHb ∧ c'.nreg 4502 = ITEMb ∧ PathOut c' ρ))

variable (M) in
/-- The path described by the flags of its new hole at `NHb`. -/
def PathNH (e : ℕ → D) (n NHb : ℕ) (Hs : List (Finset V)) (c : Config) (ρ : HPath M) : Prop :=
  ∀ i < n, (c.nmem (NHb + i) ≠ 0 ↔ M.tail (e i) ∈ newHole Hs ρ.mverts)

lemma pathStable_NH {e : ℕ → D} {n ITEMb NHb : ℕ} {Hs : List (Finset V)}
    (h : ITEMb + n ≤ NHb) : PathStable ITEMb n (PathNH M e n NHb Hs) := by
  intro c c' ρ hp hm _ _ _ _ i hi
  rw [hm _ (Or.inr (by omega))]
  exact hp i hi

lemma card_sVert_le {σ : Perm D} {N : Finset D} : Fintype.card (SVert σ N) ≤ #N := by
  have := Fintype.card_le_of_surjective (Quotient.mk (orbSetoid σ N))
    (fun q => Quotient.exists_rep q |>.imp fun _ h => h)
  rwa [Fintype.card_coe] at this

lemma card_face_le {X Q : Type*} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (Mp : PlanarSeparator.Map X Q) : Fintype.card Mp.Face ≤ Fintype.card X :=
  Fintype.card_le_of_surjective Mp.face (fun f => Quotient.exists_rep f |>.imp fun _ h => h)

set_option maxHeartbeats 1600000 in
open Classical in
/-- **What stages B and C compute** (pure): from the marks `KM` of the keys of the vertices on the
cycle, the face marks `ZFm`, the labels and flags as computed, the labels represent the two items
of Miller's base, the flags its new hole, and the labels are `< 3`. -/
theorem mb_sem (hloopM : ∀ d, M.head d ≠ M.tail d) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {e : ℕ → D} {n Bz : ℕ} {N : Finset D} {σ : Perm D}
    (hN : PMap M N Hs σ) (hne : N.Nonempty) (hnc : NoCut M N Hs) {ex : D → ℕ}
    {C : (psep M hN.stable hN.rev).stellar.SCycle}
    {Z : Finset (psep M hN.stable hN.rev).stellar.Face}
    (hR : sepC M e n Bz N σ hN.stable hN.rev ex = some (C, Z))
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsN : ∀ d ∈ N, ∃ i, i < n ∧ e i = d)
    {TK RV NF RK KM ZFm lab nh : ℕ → ℕ} {z z44 : ℕ}
    (hkey : ∀ i < n, ∀ j < n, (TK i = TK j ↔ HRel Hs (M.tail (e i)) (M.tail (e j))))
    (hrv : ∀ i < n, RV i < n ∧ e (RV i) = M.rev (e i))
    (hnf : ∀ i < n, (NF i ≠ 0 ↔ e i ∈ N))
    (hRK : ∀ i < n, e i ∈ N → RK i = eRk e n N (e i))
    (hTK : ∀ i < n, TK i < n)
    (hKM : ∀ x < n, (KM x ≠ 0 ↔ ∃ l < C.k, ∃ y : SDart N, (psep M hN.stable hN.rev).stellar.vert (C.d l) =
      .inl ((psep M hN.stable hN.rev).vert y) ∧ TK (eIdx e n y.1) = x))
    (hZ : ∀ G, G ∈ Z ↔ (ZFm ((psep M hN.stable hN.rev).stFn (cNe e n N) G) ≠ z ↔ z44 = 1))
    (hlab : ∀ i < n, lab i = if NF i ≠ 0 then
      lbV (KM (TK i)) (ZFm (RK i)) (KM (TK (RV i))) (ZFm (RK (RV i))) z
        (1 - ((z44 - 1) + (1 - z44))) else 0)
    (hnh : ∀ i < n, nh i = KM (TK i)) :
    ItemRep e n {sideItem hN.stable hN.rev (coreI hN.stable hN.rev C Z),
      sideItem hN.stable hN.rev (coreO hN.stable hN.rev C Z)} lab ∧
    (∀ i < n, (nh i ≠ 0 ↔ M.tail (e i) ∈ newHole Hs (corePath hN.stable hN.rev C).mverts)) ∧
    (∀ i < n, lab i < 3) := by
  obtain ⟨hsep, hsim⟩ := sepC_facts hloopM hd e n Bz hN hne hnc ex hR
  set K : SDart N → ℕ := fun y => TK (eIdx e n y.1) with hKdef
  have hidx : ∀ y : SDart N, ∃ j < n, e j = y.1 ∧ eIdx e n y.1 = j := fun y => by
    obtain ⟨j, hj, hej⟩ := hsN y.1 y.2
    exact ⟨j, hj, hej, by rw [← hej, eIdx_e hinj hj]⟩
  have hKv : ∀ y y' : SDart N, K y = K y' ↔
      (psep M hN.stable hN.rev).vert y = (psep M hN.stable hN.rev).vert y' := fun y y' => by
    obtain ⟨j, hj, hej, hij⟩ := hidx y
    obtain ⟨j', hj', hej', hij'⟩ := hidx y'
    rw [psep_hsc hN, hKdef]
    simp only
    rw [hij, hij', hkey j hj j' hj', hej, hej']
  have hKe : ∀ i < n, ∀ h : e i ∈ N, K ⟨e i, h⟩ = TK i := fun i hi h => by
    simp only [hKdef]; rw [eIdx_e hinj hi]
  -- the marks of the vertices
  have honC : ∀ i < n, ∀ h : e i ∈ N, (KM (TK i) = 0 ↔
      (.inl ((psep M hN.stable hN.rev).vert ⟨e i, h⟩) :
        SVert σ N ⊕ (psep M hN.stable hN.rev).Face) ∉ C.verts) := fun i hi h => by
    rw [← onC_iff C K hKv ⟨e i, h⟩, hKe i hi h, ← hKM _ (hTK i hi)]
    simp
  -- the new hole
  have hnh' : ∀ i < n, (nh i ≠ 0 ↔
      M.tail (e i) ∈ newHole Hs (corePath hN.stable hN.rev C).mverts) := fun i hi => by
    rw [hnh i hi, hKM _ (hTK i hi)]
    refine nh_iff hloopM hd hN hne hnc C hsim K fun y => ?_
    obtain ⟨j, hj, hej, hij⟩ := hidx y
    simp only [hKdef]
    rw [hij, hkey j hj i hi, hej]
  -- the face marks
  have hz : ∀ x : SDart N, ∀ i < n, e i = x.1 → (lbZ (ZFm (RK i)) z (1 - ((z44 - 1) + (1 - z44))) = 1 ↔
      (psep M hN.stable hN.rev).stellar.face (old x) ∈ Z) := fun x i hi hx => by
    have hiN : e i ∈ N := hx ▸ x.2
    rw [hRK i hi hiN, hx, ← cNe_apply hsN x]
    have := zmark_iff (mem := ZFm) (ZFb := 0) (z := z) (z44 := z44) (cNe e n N) Z
      (fun G => by rw [zero_add]; exact hZ G) x
    rw [zero_add] at this
    exact this
  have hlab' : ∀ i < n, lab i = if e i ∈ sideItem hN.stable hN.rev (coreI hN.stable hN.rev C Z)
      then 1 else if e i ∈ sideItem hN.stable hN.rev (coreO hN.stable hN.rev C Z) then 2
      else 0 := fun i hi => by
    rw [hlab i hi]
    by_cases hiN : e i ∈ N
    · rw [iteT ((hnf i hi).2 hiN)]
      obtain ⟨hr, hre⟩ := hrv i hi
      have hrN : e (RV i) ∈ N := by rw [hre]; exact hN.rev _ hiN
      set x : SDart N := ⟨e i, hiN⟩ with hx
      have hαx : ((psep M hN.stable hN.rev).α x).1 = e (RV i) := by rw [psep_α, hre]
      have hαx' : (psep M hN.stable hN.rev).α x = ⟨e (RV i), hrN⟩ := Subtype.ext hαx
      exact lab_eq hN.stable hN.rev hsep x (honC i hi hiN)
        (by rw [hαx']; exact honC _ hr hrN) (hz x i hi rfl) (hz _ (RV i) hr hαx.symm)
    · rw [iteF (fun h => hiN ((hnf i hi).1 h))]
      have h1 : e i ∉ sideItem hN.stable hN.rev (coreI hN.stable hN.rev C Z) :=
        fun h => hiN (sideItem_subset _ _ _ h)
      have h2 : e i ∉ sideItem hN.stable hN.rev (coreO hN.stable hN.rev C Z) :=
        fun h => hiN (sideItem_subset _ _ _ h)
      rw [iteF h1, iteF h2]
  refine ⟨itemRep_two (sideItem_core_disj hN.stable hN.rev hsep)
    (fun d h => hsN d (sideItem_subset _ _ _ h)) (fun d h => hsN d (sideItem_subset _ _ _ h))
    hlab', hnh', fun i hi => ?_⟩
  rw [hlab' i hi]; split_ifs <;> omega

end Spec

end BKMNW

end PlanarFlow
