module

public import PlanarFlow.BKMNW.NpDiv
public import PlanarFlow.BKMNW.NrComm
public import PlanarFlow.BKMNW.NrDkM
public import PlanarFlow.BKMNW.NrPushAll
public import PlanarFlow.BKMNW.NpPushC
public import PlanarFlow.BKMNW.NrPchL

/-!
# The push-back of a call from the frame (pure part of `pchP`)

At a call with frame `Lay` (`m > 0` darts `en 0, …, en (m-1)` in the `gid` order):

* **faces**: an index array `f` of the face walk (`FaceArr`, e.g. `SG[RV[i]]`, `Lay.faceArr_nx`)
  is a permutation of `[0, m)` (`Lay.permOn_face`); two darts are on the same face of the piece
  map iff their orbit labels `olab f` agree (**`Lay.face_eq_iffP`**);
* **compact keys**: `rcnt X` (the prefix counts of the fixed points, `NrPchL.lean`) numbers the
  labels `0 … nf - 1` (`rcnt_lt`, `rcnt_surj`, `rkey_lt`, `rkey_eq_iff`, `rkey_surj`);
  `fkOf`, **`fKey_of`** (`FKey` of `NrDkM.lean` from such keys), **`Lay.fKey`**;
* **the darts as indices**: `edF` (the dart `en i`), **`Lay.ixMap`** (`IxMap` of `NrPushRun.lean`
  with the frame's `RV` and the vertex labels `olab SG`);
* **the order**: **`Lay.sorted_eq`** (the `gid`-sorted list of the darts of `pchCall` is the frame
  order), **`Lay.pchCall_eq`** (`pchCall gid x h = pushFwdL … (face (en 0)) …` with the lists of
  the frame order);
* **Kahn's order**: **`kahn_list`** (the queue of `kahnP` as a list of vertices: no duplicates,
  every vertex, topological for the flow);
* **`nrGt_eq_pchCall`**: the visits of `pushP` along Kahn's queue of the cancelled flow compute
  `pchCall`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab

/-! ### Compact keys from the prefix counts -/

lemma rcnt_succ (X : ℕ → ℕ) (i : ℕ) : rcnt X (i + 1) = rcnt X i + (1 - (i - X i)) := rfl

lemma rcnt_mono (X : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : rcnt X a ≤ rcnt X b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · have := ih (by omega); rw [rcnt_succ]; omega

lemma rcnt_lt (X : ℕ → ℕ) {a b : ℕ} (hab : a < b) (ha : X a = a) : rcnt X a < rcnt X b := by
  have h1 : rcnt X (a + 1) = rcnt X a + 1 := by rw [rcnt_succ, ha]; omega
  have h2 := rcnt_mono X (show a + 1 ≤ b by omega)
  omega

lemma rcnt_surj (X : ℕ → ℕ) (hX : ∀ j, X j ≤ j) :
    ∀ n, ∀ y < rcnt X n, ∃ a < n, X a = a ∧ rcnt X a = y
  | 0, y, hy => by simp [rcnt] at hy
  | n + 1, y, hy => by
    rw [rcnt_succ] at hy
    by_cases h : y < rcnt X n
    · obtain ⟨a, ha, h1, h2⟩ := rcnt_surj X hX n y h
      exact ⟨a, by omega, h1, h2⟩
    · have hXn := hX n
      have hb : 1 - (n - X n) = 1 := by omega
      refine ⟨n, by omega, by omega, by omega⟩

/-- The compact key of `i`: the number of labels below its label. -/
noncomputable def rkey (f : ℕ → ℕ) (i : ℕ) : ℕ := rcnt (olab f) (olab f i)

lemma rkey_lt {f : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) {i : ℕ} (hi : i < m) :
    rkey f i < rcnt (olab f) m :=
  rcnt_lt _ (olab_lt hp hi) (olab_olab hp hi)

lemma rkey_eq_iff {f : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    rkey f i = rkey f j ↔ olab f i = olab f j := by
  constructor
  · intro e
    unfold rkey at e
    rcases lt_trichotomy (olab f i) (olab f j) with h | h | h
    · have := rcnt_lt (olab f) h (olab_olab hp hi); omega
    · exact h
    · have := rcnt_lt (olab f) h (olab_olab hp hj); omega
  · intro e; unfold rkey; rw [e]

lemma rkey_surj {f : ℕ → ℕ} {m : ℕ} (hp : PermOn f m) {y : ℕ} (hy : y < rcnt (olab f) m) :
    ∃ a < m, rkey f a = y := by
  obtain ⟨a, ha, h1, h2⟩ := rcnt_surj (olab f) (olab_le f) m y hy
  exact ⟨a, ha, by unfold rkey; rw [h1, h2]⟩

/-! ### Face keys of a map -/

section Gen

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

/-- A face numbering from the keys of the darts. -/
noncomputable def fkOf (Mp : CombMap D' V' F') (m : ℕ) (ed : ℕ → D') (key : ℕ → ℕ) (y : F') :
    ℕ := by
  classical
  exact if h : ∃ i < m, Mp.face (ed i) = y then key (Classical.choose h) else 0

/-- **`FKey` from keys that identify the faces.** -/
theorem fKey_of {Mp : CombMap D' V' F'} {m n : ℕ} {ed : ℕ → D'} {rv key : ℕ → ℕ}
    (hsurj : ∀ x, ∃ i < m, ed i = x) (hrv : ∀ i < m, rv i < m ∧ ed (rv i) = Mp.rev (ed i))
    (hlt : ∀ i < m, key i < n)
    (hiff : ∀ i < m, ∀ j < m, key i = key j ↔ Mp.face (ed i) = Mp.face (ed j))
    (hfs : ∀ y : F', ∃ x, Mp.face x = y) :
    FKey Mp m n ed rv key (fkOf Mp m ed key) := by
  classical
  have hf : ∀ i < m, fkOf Mp m ed key (Mp.face (ed i)) = key i := by
    intro i hi
    have hex : ∃ j < m, Mp.face (ed j) = Mp.face (ed i) := ⟨i, hi, rfl⟩
    unfold fkOf
    simp only [hex, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := Classical.choose_spec hex
    exact (hiff _ h1 i hi).2 h2
  have hfsurj : ∀ y : F', ∃ i < m, Mp.face (ed i) = y := fun y => by
    obtain ⟨x, rfl⟩ := hfs y
    obtain ⟨i, hi, rfl⟩ := hsurj x
    exact ⟨i, hi, rfl⟩
  refine ⟨hsurj, hrv, hf, hlt, fun x y e => ?_, hfsurj⟩
  obtain ⟨i, hi, rfl⟩ := hfsurj x
  obtain ⟨j, hj, rfl⟩ := hfsurj y
  rw [hf i hi, hf j hj] at e
  exact (hiff i hi j hj).1 e

end Gen

/-! ### Kahn's queue as a list of vertices -/

section Kahn

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

lemma idxOf_map_getElem {α β : Type*} [DecidableEq α] [DecidableEq β] {L : List α} (hL : L.Nodup)
    {φ : α → β} (hφ : ∀ a ∈ L, ∀ b ∈ L, φ a = φ b → a = b) {k : ℕ} (hk : k < L.length) :
    (L.map φ).idxOf (φ L[k]) = k := by
  have hnd : (L.map φ).Nodup := hL.map_on hφ
  have hk' : k < (L.map φ).length := by simpa using hk
  have := List.Nodup.idxOf_getElem hnd k hk'
  simpa using this

/-- **Kahn's queue as a list of vertices**: the vertices of the labels of the queue, without
duplicates, all of them, the tail of every positive dart before its head. -/
theorem kahn_list {Mp : CombMap D' V' F'} {m : ℕ} {ed : ℕ → D'} {rv vl : ℕ → ℕ}
    (hI : IxMap Mp m ed rv vl) (hV : ∀ v : V', ∃ e, Mp.tail e = v) {g₁ : D' → ℤ}
    (hac : ∀ v, ¬ Relation.TransGen (Pos Mp g₁) v v) {ps : ℕ → ℕ}
    (hps : ∀ j < m, ps j ≠ 0 ↔ 0 < g₁ (ed j)) {Q IND : ℕ → ℕ} {t : ℕ}
    (hk : KSt m vl vl (fun j => vl (rv j)) ps Q IND t t) :
    ((kQ Q t).map fun v => Mp.tail (ed v)).Nodup ∧
      (∀ v, v ∈ (kQ Q t).map fun v => Mp.tail (ed v)) ∧
      ∀ e, 0 < g₁ e → ((kQ Q t).map fun v => Mp.tail (ed v)).idxOf (Mp.tail e) <
        ((kQ Q t).map fun v => Mp.tail (ed v)).idxOf (Mp.head e) := by
  classical
  -- the tail of the label is the tail
  have hvt : ∀ j < m, Mp.tail (ed (vl j)) = Mp.tail (ed j) := fun j hj =>
    (hI.vl_iff _ (hI.vlt j hj).1 j hj).2 (hI.vlt j hj).2.1
  have hvh : ∀ j < m, Mp.tail (ed (vl (rv j))) = Mp.head (ed j) := fun j hj => by
    rw [hvt _ (hI.rv j hj).1, (hI.rv j hj).2]; rfl
  have hall : ∀ w, KRep m vl w → w ∈ kQ Q t := kst_final hk
    (fun w => rk Mp g₁ (Mp.tail (ed w)))
    (fun j hj hp => by
      show rk Mp g₁ (Mp.tail (ed (vl j))) < rk Mp g₁ (Mp.tail (ed (vl (rv j))))
      rw [hvt j hj, hvh j hj]
      exact rk_lt hac ((hps j hj).1 hp))
    (fun j hj => ⟨(hI.vlt j hj).1, (hI.vlt j hj).2.1⟩)
  have hrep : ∀ w ∈ kQ Q t, KRep m vl w := fun w hw => by
    simp only [kQ, List.mem_map, List.mem_range] at hw
    obtain ⟨k, hk', rfl⟩ := hw
    exact hk.rep k hk'
  have hinj : ∀ a ∈ kQ Q t, ∀ b ∈ kQ Q t, Mp.tail (ed a) = Mp.tail (ed b) → a = b :=
    fun a ha b hb e => by
      obtain ⟨a1, a2⟩ := hrep a ha
      obtain ⟨b1, b2⟩ := hrep b hb
      have := (hI.vl_iff a a1 b b1).1 e
      rw [a2, b2] at this; exact this
  refine ⟨hk.nd.map_on hinj, fun v => ?_, fun e he => ?_⟩
  · obtain ⟨e, rfl⟩ := hV v
    obtain ⟨i, hi, rfl⟩ := hI.surj e
    refine List.mem_map.2 ⟨vl i, hall _ ⟨(hI.vlt i hi).1, (hI.vlt i hi).2.1⟩, hvt i hi⟩
  · obtain ⟨j, hj, rfl⟩ := hI.surj e
    have hw := hall (vl (rv j)) ⟨(hI.vlt _ (hI.rv j hj).1).1, (hI.vlt _ (hI.rv j hj).1).2.1⟩
    simp only [kQ, List.mem_map, List.mem_range] at hw
    obtain ⟨k, hkt, hk'⟩ := hw
    obtain ⟨k', hk'k, hq⟩ := hk.topo k hkt j hj ((hps j hj).2 he) hk'.symm
    have hlen : (kQ Q t).length = t := by simp [kQ]
    have g1 : (kQ Q t)[k]'(by omega) = Q k := by simp [kQ]
    have g2 : (kQ Q t)[k']'(by omega) = Q k' := by simp [kQ]
    have e1 := idxOf_map_getElem hk.nd hinj (k := k) (by omega)
    have e2 := idxOf_map_getElem hk.nd hinj (k := k') (by omega)
    rw [g1, hk', hvh j hj] at e1
    rw [g2, hq, hvt j hj] at e2
    rw [e1, e2]; exact hk'k

end Kahn

namespace MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-! ### Faces from the frame -/

variable (M) in
/-- An index array of the face walk `σ ∘ rev` of the piece map. -/
def FaceArr (x : MCall M) (m : ℕ) (en : ℕ → D) (f : ℕ → ℕ) : Prop :=
  ∀ i < m, f i < m ∧ en (f i) = x.2.2 (M.rev (en i))

/-- The face array of the frame: `SG[RV[i]]`. -/
def nxFP (d m : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (d + 4 + 2 * m + mem (d + 4 + m + i))

lemma Lay.faceArr_nx {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) : FaceArr M x m en (nxFP d m mem) := fun i hi => by
  obtain ⟨r1, r2⟩ := hL.rv i hi
  obtain ⟨s1, s2⟩ := hL.sg _ r1
  exact ⟨s1, by unfold nxFP; rw [s2, r2]⟩

lemma faceArr_iter {x : MCall M} {m : ℕ} {en : ℕ → D} {f : ℕ → ℕ}
    (hf : FaceArr M x m en f) :
    ∀ t i, i < m → f^[t] i < m ∧ en (f^[t] i) = ((x.2.2 * revPerm M) ^ t) (en i)
  | 0, i, hi => ⟨hi, by simp⟩
  | t + 1, i, hi => by
    obtain ⟨h1, h2⟩ := faceArr_iter hf t i hi
    rw [Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := hf _ h1
    refine ⟨g1, ?_⟩
    rw [g2, h2, pow_succ', Perm.mul_apply, Perm.mul_apply]
    rfl

lemma Lay.permOn_face {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) {f : ℕ → ℕ} (hf : FaceArr M x m en f) :
    PermOn f m where
  lt i hi := (hf i hi).1
  inj i hi j hj e := by
    have h1 := (hf i hi).2
    have h2 := (hf j hj).2
    rw [e, h2] at h1
    exact hL.en_inj hi hj (M.rev_injective (x.2.2.injective h1.symm))

/-- **Two darts of the frame are on the same face of the piece map iff their face labels
agree.** -/
lemma Lay.face_eq_iffP {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {f : ℕ → ℕ} (hf : FaceArr M x m en f) {i j : ℕ} (hi : i < m) (hj : j < m) :
    (pmap h).face (vDart hL hi) = (pmap h).face (vDart hL hj) ↔ olab f i = olab f j := by
  show Quotient.mk _ (vDart hL hi) = Quotient.mk _ (vDart hL hj) ↔ _
  rw [sVert_eq_iff, olab_eq_iff (hL.permOn_face hf) hi hj]
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := hs.exists_nat_pow_eq
    refine ⟨t, hL.en_inj (faceArr_iter hf t i hi).1 hj ?_⟩
    rw [(faceArr_iter hf t i hi).2]; exact ht
  · rintro ⟨t, ht⟩
    refine ⟨(t : ℤ), ?_⟩
    have := (faceArr_iter hf t i hi).2
    rw [ht] at this
    simp only [vDart, zpow_natCast]
    exact this.symm

/-! ### The darts as indices -/

/-- The dart `en i` of the piece map (`en 0` beyond `m`). -/
noncomputable def edF {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m) (i : ℕ) :
    SDart (pdarts M x.1.piece x.2.1) :=
  if hi : i < m then vDart hL hi else vDart hL hm

lemma edF_lt {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {i : ℕ} (hi : i < m) :
    edF hL hm i = vDart hL hi := by simp [edF, hi]

lemma edF_val {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m) {i : ℕ} (hi : i < m) :
    (edF hL hm i).1 = en i := by rw [edF_lt hL hm hi]; rfl

lemma Lay.edF_surj {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m)
    (y : SDart (pdarts M x.1.piece x.2.1)) : ∃ i < m, edF hL hm i = y := by
  obtain ⟨i, hi, e⟩ := hL.en_surj y.1 y.2
  exact ⟨i, hi, Subtype.ext (by rw [edF_val hL hm hi, e])⟩

lemma Lay.edF_rv {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {i : ℕ} (hi : i < m) :
    mem (d + 4 + m + i) < m ∧ edF hL hm (mem (d + 4 + m + i)) = (pmap h).rev (edF hL hm i) := by
  obtain ⟨r1, r2⟩ := hL.rv i hi
  refine ⟨r1, Subtype.ext ?_⟩
  rw [edF_val hL hm r1, pmap_rev, edF_val hL hm hi, r2]

/-- **The frame's darts as indices** (`IxMap`): the frame's `RV`, the vertex labels `olab SG`. -/
theorem Lay.ixMap {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {rv vl : ℕ → ℕ} (hrv : ∀ i < m, rv i = mem (d + 4 + m + i))
    (hvl : ∀ i < m, vl i = olab (sgF d m mem) i) :
    IxMap (pmap h) m (edF hL hm) rv vl where
  surj := hL.edF_surj hm
  inj i hi j hj e := by
    have := congrArg Subtype.val e
    rw [edF_val hL hm hi, edF_val hL hm hj] at this
    exact hL.en_inj hi hj this
  rv i hi := by rw [hrv i hi]; exact hL.edF_rv h hm hi
  vlt i hi := by
    have hp := hL.permOn_sg
    rw [hvl i hi, hvl _ (olab_lt hp hi)]
    exact ⟨olab_lt hp hi, olab_olab hp hi, olab_le _ _⟩
  vl_iff i hi j hj := by
    rw [hvl i hi, hvl j hj, edF_lt hL hm hi, edF_lt hL hm hj]
    exact hL.vert_eq_iff h hi hj

/-- **The compact face keys of the frame** (`FKey`). -/
theorem Lay.fKey {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {f : ℕ → ℕ} (hf : FaceArr M x m en f) {rv key : ℕ → ℕ}
    (hrv : ∀ i < m, rv i = mem (d + 4 + m + i)) (hkey : ∀ i < m, key i = rkey f i) :
    FKey (pmap h) m (rcnt (olab f) m) (edF hL hm) rv key
      (fkOf (pmap h) m (edF hL hm) key) := by
  have hp := hL.permOn_face hf
  refine fKey_of (hL.edF_surj hm) (fun i hi => by rw [hrv i hi]; exact hL.edF_rv h hm hi)
    (fun i hi => by rw [hkey i hi]; exact rkey_lt hp hi) (fun i hi j hj => ?_)
    (fun y => ⟨Quotient.out y, Quotient.out_eq y⟩)
  rw [hkey i hi, hkey j hj, rkey_eq_iff hp hi hj, edF_lt hL hm hi, edF_lt hL hm hj,
    hL.face_eq_iffP h hf hi hj]

/-- The number of compact face keys is at most the number of faces. -/
lemma Lay.rcnt_le_card {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    {f : ℕ → ℕ} (hf : FaceArr M x m en f) :
    rcnt (olab f) m ≤ Fintype.card (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) := by
  classical
  have hp := hL.permOn_face hf
  have hK := hL.fKey h hm hf (rv := fun i => mem (d + 4 + m + i)) (key := rkey f)
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hsub : range (rcnt (olab f) m) ⊆
      (univ : Finset (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M))).image
        (fkOf (pmap h) m (edF hL hm) (rkey f)) := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := rkey_surj hp (mem_range.1 hy)
    exact mem_image.2 ⟨_, mem_univ _, hK.fkey a ha⟩
  have := card_le_card hsub
  rw [card_range] at this
  exact this.trans card_image_le

/-! ### The order of the darts -/

/-- **The `gid`-sorted list of the darts is the frame order.** -/
theorem Lay.sorted_eq {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (hm : 0 < m) :
    ((univ : Finset (SDart (pdarts M x.1.piece x.2.1))).toList.mergeSort
      fun a b => decide (gid a.1 ≤ gid b.1)) = (List.range m).map (edF hL hm) := by
  classical
  have hperm := List.mergeSort_perm
    ((univ : Finset (SDart (pdarts M x.1.piece x.2.1))).toList)
    fun a b => decide (gid a.1 ≤ gid b.1)
  have hsort := List.pairwise_mergeSort (le := fun a b : SDart (pdarts M x.1.piece x.2.1) =>
      decide (gid a.1 ≤ gid b.1))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((univ : Finset (SDart (pdarts M x.1.piece x.2.1))).toList)
  have hinj : ∀ i < m, ∀ j < m, edF hL hm i = edF hL hm j → i = j := fun i hi j hj e => by
    have := congrArg Subtype.val e
    rw [edF_val hL hm hi, edF_val hL hm hj] at this
    exact hL.en_inj hi hj this
  have hnd2 : ((List.range m).map (edF hL hm)).Nodup :=
    (List.nodup_range).map_on fun a ha b hb e =>
      hinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) e
  refine List.Perm.eq_of_pairwise (le := fun a b : SDart (pdarts M x.1.piece x.2.1) =>
    gid a.1 ≤ gid b.1) (fun a b _ _ h1 h2 => ?_) (hsort.imp fun h => by simpa using h) ?_ ?_
  · obtain ⟨i, hi, rfl⟩ := hL.edF_surj hm a
    obtain ⟨j, hj, rfl⟩ := hL.edF_surj hm b
    rw [edF_val hL hm hi, edF_val hL hm hj] at h1 h2
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := hL.en_mono i j hij hj; omega
    · rfl
    · have := hL.en_mono j i hij hi; omega
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range).imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    rw [edF_val hL hm ha', edF_val hL hm hb']
    exact (hL.en_mono a b hab hb').le
  · refine hperm.trans ((List.perm_ext_iff_of_nodup (hperm.nodup_iff.1
      (hperm.nodup_iff.2 (Finset.nodup_toList _))) hnd2).2 fun y => ?_)
    simp only [Finset.mem_toList, Finset.mem_univ, true_iff, List.mem_map, List.mem_range]
    obtain ⟨i, hi, e⟩ := hL.edF_surj hm y
    exact ⟨i, hi, e⟩

/-- **The machine's push-back at a call from the frame order.** -/
theorem Lay.pchCall_eq {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m) :
    NsStep.pchCall gid x h = pushFwdL (pmap h) (frRef _) ((pmap h).face (edF hL hm 0))
      (ordRk (pmap h) ((List.range m).map (edF hL hm)))
      (outsL (pmap h) ((List.range m).map (edF hL hm))) := by
  unfold NsStep.pchCall
  rw [hL.sorted_eq hm]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons]
  rfl

/-- **The visits along Kahn's queue of the cancelled flow compute `pchCall`.** -/
theorem nrGt_eq_pchCall {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hm : 0 < m)
    (hpl : (pmap h).IsPlane) {rv vl : ℕ → ℕ} (hI : IxMap (pmap h) m (edF hL hm) rv vl)
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hg : (pmap h).IsAntisymm g)
    {ps : ℕ → ℕ}
    (hps : ∀ j < m, ps j ≠ 0 ↔
      0 < cancelR (pmap h) (frRef _) ((pmap h).face (edF hL hm 0)) g (edF hL hm j))
    {Q IND : ℕ → ℕ} {t : ℕ} (hk : KSt m vl vl (fun j => vl (rv j)) ps Q IND t t)
    (β : SVert x.2.2 (pdarts M x.1.piece x.2.1) → ℤ)
    (Fr : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))) :
    nrGt (pmap h) (edF hL hm) m β Fr
        (cancelR (pmap h) (frRef _) ((pmap h).face (edF hL hm 0)) g) Q t =
      NsStep.pchCall gid x h β Fr g := by
  classical
  obtain ⟨a₀, -, -, ac₀⟩ := cancelR_spec hpl (frRef_spec _) ((pmap h).face (edF hL hm 0)) hg
  have hV : ∀ v, ∃ e, (pmap h).tail e = v := fun v => by
    induction v using Quotient.inductionOn with
    | h y => exact ⟨y, rfl⟩
  obtain ⟨k1, k2, k3⟩ := kahn_list hI hV ac₀ hps hk
  have hLs : (List.range m).map (edF hL hm) = ((List.range m).map (edF hL hm)) := rfl
  have hnd : ((List.range m).map (edF hL hm)).Nodup :=
    (List.nodup_range).map_on fun a ha b hb e => by
      have := congrArg Subtype.val e
      rw [edF_val hL hm (List.mem_range.1 ha), edF_val hL hm (List.mem_range.1 hb)] at this
      exact hL.en_inj (List.mem_range.1 ha) (List.mem_range.1 hb) this
  have hall : ∀ y, y ∈ (List.range m).map (edF hL hm) := fun y => by
    obtain ⟨i, hi, rfl⟩ := hL.edF_surj hm y
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  rw [hL.pchCall_eq h hm, nr_pushFwdL_eq hpl (frRef_spec _) _ (ordRk_topo hall hV)
    (outsL_ok hnd hall) β Fr hg _ k1 k2 k3]
  rfl

end MfDrv

end BKMNW

end PlanarFlow
