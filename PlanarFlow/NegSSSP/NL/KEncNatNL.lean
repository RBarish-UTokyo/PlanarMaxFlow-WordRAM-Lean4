module

public import PlanarFlow.NegSSSP.NL.KNatFace
public import PlanarFlow.NegSSSP.KEncNatW

/-!
# The explicit encoding for `KInputNL`: the lengths zeroed, a linear word bound

`Klein.kval_kInputTNL`: the explicit words `kInputT` **with the lengths zeroed** (the array `LN`,
read by no program, built for the lengths `0`) meet `Klein.KValNL` (`KVal` with `KInputNL`, the
copied chain of `PlanarFlow/Klein/NL/`) with the **linear** word bound
`kBL #D n k t 0 = 9 #D + 7 n + k + 4 + 2 t + aOUT #D + k t + n + 2 #D`: every word is at most
`#D + n` (`kInputT_le` with `lenMax 0 = 0`). The reach bits of the targets do not depend on the
lengths (`reach_pieceGraph_len`). `NegSSSP.fencNat_existsNL`: `FEncNatNL` with this linear `Bw`,
so the work space `Kw = Bw + 16 (n + 1)` of the natural node (`node_exec_natNNL`, the term
`17 Kw` of `partNCost`) is `O(#D' + k²)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **Reachability in a piece does not depend on the lengths.** -/
lemma lwalk_pieceGraph_len {M : CombMap D V F} {S : Finset D} {ℓ ℓ' : D → ℤ} {x y : V}
    {l : List {d // d ∈ S}} (h : LWalk (pieceGraph M S ℓ) x y l) :
    LWalk (pieceGraph M S ℓ') x y l := by
  induction h with
  | nil x => exact .nil x
  | cons _ ih => exact .cons ih

lemma reach_pieceGraph_len {M : CombMap D V F} {S : Finset D} {ℓ ℓ' : D → ℤ} {x y : V} :
    Reach (pieceGraph M S ℓ) x y ↔ Reach (pieceGraph M S ℓ') x y :=
  ⟨fun ⟨l, h⟩ => ⟨l, lwalk_pieceGraph_len h⟩, fun ⟨l, h⟩ => ⟨l, lwalk_pieceGraph_len h⟩⟩

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **The explicit words with the lengths zeroed meet `KValNL` with the linear word bound
`kBL #D n k t 0`** (same hypotheses as `kval_kInputT`). -/
theorem kval_kInputTNL (H : Hyp M k g S ℓ) {t : ℕ} {X : ℕ → V}
    (hX : ∀ i < t, ¬ IsRoot M k g (X i)) {n : ℕ} (σ : D ≃ Fin (Fintype.card D))
    {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} (hL : Layout M n ιv ιg ιf ιe)
    {T : DTree M.dual} {C : DTree M} {vs ts : List V} {fs cs : List F}
    (hOT : Orders T vs ts) (hOC : Orders C fs cs) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k))
      (tpar (pieceGraph M S ℓ) (tripSrc M k g 0))) :
    KValNL M k g S ℓ σ n (kBL (Fintype.card D) n k t 0) t X
      (kInputT M S (fun _ : D => (0 : ℤ)) σ ιv ιg ιf ιe n k g T C vs ts fs cs t X) := by
  classical
  set P₀ := kInput M S (fun _ : D => (0 : ℤ)) σ ιv ιg ιf ιe n k g T C vs ts fs cs with hP₀
  set P := kInputT M S (fun _ : D => (0 : ℤ)) σ ιv ιg ιf ιe n k g T C vs ts fs cs t X with hP
  have hTr : ∀ a, a < iXT (Fintype.card D) n k → P.data.getD a 0 = P₀.data.getD a 0 := fun a ha =>
    kInputT_getD ha
  have hB : kBL (Fintype.card D) n k t 0 = 9 * (Fintype.card D) + 7 * n + k + 4 +
      2 * t + aOUT (Fintype.card D) + k * t + n +
      2 * (Fintype.card D) + 0 := rfl
  set B := kBL (Fintype.card D) n k t 0 with hBdef
  have hk := H.two_le_k
  have hnD1 : 1 ≤ (Fintype.card D) := Fintype.card_pos_iff.2 ⟨g 0⟩
  have hσ : ∀ d : D, (σ d : ℕ) < (Fintype.card D) := fun d => (σ d).2
  have hvl := hOT.flen
  have htl := hOT.ylen
  have hfl := hOC.flen
  have hcl := hOC.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hSn : S.card ≤ (Fintype.card D) := card_le_univ S
  refine ⟨ιv, ιg, ιf, ιe, T, C, vs, ts, fs, cs, by omega, by omega, by omega,
    by unfold aRB; omega, fun i => ?_, hL,
    ⟨fun d => (hTr _ (by unfold iRV iXT; have := hσ d; omega)).trans (kInput_rv d),
      fun d => (hTr _ (by unfold iNF iXT; have := hσ d; omega)).trans (kInput_nf d),
      fun d => (hTr _ (by unfold iNE iXT; have := hσ d; omega)).trans (kInput_ne d),
      fun d => (hTr _ (by unfold iNG iXT; have := hσ d; omega)).trans (kInput_ng d),
      fun d => (hTr _ (by unfold iNT iXT; have := hσ d; omega)).trans (kInput_nt d),
      fun d => (hTr _ (by unfold iNH iXT; have := hσ d; omega)).trans (kInput_nh d),
      fun d => (hTr _ (by unfold iIS iXT; have := hσ d; omega)).trans (kInput_is d),
      fun d => by
        rw [hTr _ (by unfold iED iXT; have := hL.dual.e_lt d; omega)]
        exact kInput_ed hL.dual d⟩,
    fun i hi => (hTr _ (by unfold iGB iXT; omega)).trans (kInput_gb hi), fun x => ?_,
    ⟨hX, fun i hi => kInputT_xn hi, fun i hi => (kInputT_xr hi).trans (by
      simp only [reach_pieceGraph_len (ℓ := (fun _ : D => (0 : ℤ))) (ℓ' := ℓ)])⟩,
    ⟨hOT, hOC, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩,
    hoff, hCr, hT⟩
  · have h1 : P.data.getD i 0 ≤ _ := kInputT_le (S := S) (ℓ := (fun _ : D => (0 : ℤ))) (k := k) (g := g) σ hL hOT hOC t X i
    have h2 : lenMax (fun _ : D => (0 : ℤ)) = 0 := by
      unfold lenMax; exact (Finset.sup_eq_bot_iff _ _).2 (fun d _ => by simp)
    rw [h2] at h1
    omega
  · -- the out-darts
    have hx := hL.prim.f_lt x
    have hsplit := allOut_split M S x
    have hlen : outB M S x + (outL M S x).length ≤ (Fintype.card D) := by
      have := congrArg List.length hsplit
      rw [allOut_length] at this
      simp only [List.length_append] at this
      unfold outB; omega
    have bOB : iOB (Fintype.card D) n k + ιv x < iXT (Fintype.card D) n k := by unfold iOB iXT; omega
    have bOE : iOE (Fintype.card D) n k + ιv x < iXT (Fintype.card D) n k := by unfold iOE iXT; omega
    refine ⟨outL M S x, nodup_toList _, fun d => by simp [outL], ?_, ?_, fun i hi => ?_⟩
    · rw [hTr _ bOE, hTr _ bOB, kInput_oe hL.prim.f_inj hL.prim.f_lt,
        kInput_ob hL.prim.f_inj hL.prim.f_lt]
    · rw [hTr _ bOE, kInput_oe hL.prim.f_inj hL.prim.f_lt]; exact hlen
    · rw [hTr _ bOB, kInput_ob hL.prim.f_inj hL.prim.f_lt,
        hTr _ (by unfold iOL iXT; omega), kInput_ol (by omega)]
      rw [hsplit]
      simp only [List.map_append, List.getD_eq_getElem?_getD]
      have hi' : outB M S x + i < (List.map (fun d => (σ d : ℕ))
          (((univ : Finset V).toList.take ((univ : Finset V).toList.idxOf x)).flatMap
            (outL M S)) ++ List.map (fun d => (σ d : ℕ)) (outL M S x)).length := by
        simp only [List.length_append, List.length_map]; unfold outB; omega
      rw [List.getElem?_append_left hi', List.getElem?_append_right (by simp [outB])]
      simp [outB, hi]
  · rw [hTr _ (by unfold iIV iXT; omega), kInput_iv (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [show iIT (Fintype.card D) n k = iIV (Fintype.card D) n k + 1 * n by unfold iIT; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_it (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [show iIF (Fintype.card D) n k = iIV (Fintype.card D) n k + 2 * n by unfold iIF; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_if (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [show iIC (Fintype.card D) n k = iIV (Fintype.card D) n k + 3 * n by unfold iIC; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_ic (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    have := kInput_hd (M := M) (S := S) (ℓ := (fun _ : D => (0 : ℤ))) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 0) (by norm_num)
    simpa using this
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := (fun _ : D => (0 : ℤ))) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 1) (by norm_num)
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := (fun _ : D => (0 : ℤ))) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 2) (by norm_num)
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := (fun _ : D => (0 : ℤ))) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 3) (by norm_num)

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **`FEncNatNL` met with a linear work space**: for every one-face instance, lengths and
numbering `σ`, some isolating weight `w` and the explicit words with the lengths zeroed meet
`FEncNatNL` with `n = 2 (#V' + #F' + #D')` and `Bw = kBL #D' n k k 0`
(`= 9 #D' + 8 n + k + 4 + 2 k + aOUT #D' + k² + 2 #D'`, linear in the size of the map plus `k²`). -/
theorem fencNat_existsNL {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) :
    ∃ (w : Klein.SrcD fd.DQ fd.k → ℤ) (Pk : Input),
      FEncNatNL fd ℓ (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) +
          Fintype.card (Klein.SrcF fd.FQ fd.k) + Fintype.card (Klein.SrcD fd.DQ fd.k)))
        (Klein.kBL (Fintype.card (Klein.SrcD fd.DQ fd.k))
          (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
            Fintype.card (Klein.SrcD fd.DQ fd.k))) fd.k fd.k 0) σ w Pk := by
  classical
  have hnnQ : ∀ y ∈ fd.P'.image fd.e, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y _ =>
    faceLen_nonneg _ _ _ y
  obtain ⟨w, hw, hwB⟩ := MSSP.exists_isoW (Klein.srcMap_isPlane fd.inst.cycle fd.inst.plane)
    ((Klein.srcMap fd.inst.cycle).face (Klein.srcG fd.inst.cycle 0))
  obtain ⟨H, -⟩ := Klein.srcIso_hyp fd.inst.cycle fd.inst.plane fd.inst.rot hnnQ hw hwB σ
  have hR := Klein.srcMap_sameReach fd.inst.cycle (S := fd.P'.image fd.e)
    (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
  have hX : ∀ i < fd.k, ¬ MSSP.IsRoot (Klein.srcMap fd.inst.cycle) fd.k
      (Klein.srcG fd.inst.cycle) (.inl (fd.Q.tail (fd.g i))) := by
    rintro i - ⟨j, hj, hji⟩
    rw [Klein.srcTail_srcG fd.inst.cycle hj] at hji
    cases hji
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := Klein.exists_layout (Klein.srcMap fd.inst.cycle)
  obtain ⟨T, C, vs, ts, fs, cs, hOT, hOC, hoff, hCr, hT⟩ := Klein.klein_init_exists H hR
  exact ⟨w, _, rfl, hw, hwB, Klein.kval_kInputTNL H hX σ hL hOT hOC hoff hCr hT⟩

/-- **The work space of the encoding of `fencNat_existsNL` is linear**: for a one-face instance
of a node (`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`), `Kw = Bw + 16 (n + 1) ≤ 16000 m + 23`, so the term
`17 Kw` of `partNCost` in `node_exec_natNNL` is `O(m)`. -/
theorem kw_existsNL_le {P X : Finset D} {B : Finset V} (fd : FaceData N X B)
    (hq : fd.q ≤ 18 * P.card) (hk : fd.k ^ 2 ≤ 1200 * P.card) :
    Klein.kBL (Fintype.card (Klein.SrcD fd.DQ fd.k))
        (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
          Fintype.card (Klein.SrcD fd.DQ fd.k))) fd.k fd.k 0 +
      16 * (2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
          Fintype.card (Klein.SrcD fd.DQ fd.k)) + 1) ≤ 16000 * P.card + 23 := by
  have hc := fd.inst.card
  have hkV : fd.k ≤ Fintype.card fd.VQ := by
    have hinj : Function.Injective fun i : Fin fd.k => fd.Q.tail (fd.g i) := fun i j h =>
      Fin.ext (fd.inst.cycle.inj _ i.2 _ j.2 h)
    simpa using Fintype.card_le_of_injective _ hinj
  have eD : Fintype.card (Klein.SrcD fd.DQ fd.k) = Fintype.card fd.DQ + 8 * fd.k := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Klein.card_srcKind]; ring
  have eV : Fintype.card (Klein.SrcV fd.VQ fd.k) = Fintype.card fd.VQ + 2 * fd.k := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  have eF : Fintype.card (Klein.SrcF fd.FQ fd.k) = Fintype.card fd.FQ + 2 * fd.k := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [eD, eV, eF]
  unfold Klein.kBL Klein.aOUT
  have hk2 : fd.k * fd.k = fd.k ^ 2 := by ring
  omega

end NegSSSP

end PlanarFlow
