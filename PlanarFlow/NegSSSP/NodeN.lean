module

public import PlanarFlow.NegSSSP.KPartNRun

/-!
# The two parts of a node on natural words

`kPairN`: `partSet` and `kPartN` for the part with the smaller work space of Klein's program,
then for the other one, in the zones `zf ≠ zs` of the scratch area (as `kPair`, on natural
words). `kpairN_exec`: the orders and the matrices of `bfStartP` of both parts, the flags as
natural words and the lengths as residues modulo `M` at `βN + …`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge

/-- **The two parts of a node on natural words.** -/
def kPairN (zf δrf : ℕ) (pf : KPN) (zs δrs : ℕ) (ps : KPN) : Stmt :=
  .seq (partSet zf δrf) <| .seq (kPartN pf) <| .seq (partSet zs δrs) (kPartN ps)

theorem kPairN_natOnly (zf δrf : ℕ) (pf : KPN) (zs δrs : ℕ) (ps : KPN) :
    Klein.natOnly (kPairN zf δrf pf zs δrs ps) = true := by
  have h1 : Klein.natOnly (partSet zf δrf) = true := by kernel_rfl
  have h2 : Klein.natOnly (partSet zs δrs) = true := by kernel_rfl
  simp only [kPairN, Klein.natOnly, h1, h2, kPartN_natOnly, Bool.and_self]

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- The constants of the natural program of a part, from its instance and encoding. -/
noncomputable def kpnOf {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ) (n Bw : ℕ)
    (Pk : Input) (β RkN Pb Hc βK βN M : ℕ) : KPN :=
  ⟨fd.k, Fintype.card (Klein.SrcD fd.DQ fd.k), n, Bw, Pk.data.length, β, RkN, Pb, Hc,
    Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k,
    (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat, βK, βN, M⟩

set_option maxHeartbeats 8000000 in
/-- **The two parts of a node on natural words as one run.** -/
theorem kpairN_exec {P P₀ P₁ : Finset D} {ℓ : D → ℤ}
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    {Xf Xs : Finset D} {δf δs : V → ℤ}
    {fdf : FaceData N Xf (bdry N P₀ P₁)} {nf Bwf : ℕ}
    {σf : Klein.SrcD fdf.DQ fdf.k ≃ Fin (Fintype.card (Klein.SrcD fdf.DQ fdf.k))}
    {wtf : Klein.SrcD fdf.DQ fdf.k → ℤ} {Pkf : Input} {Hcf : ℕ}
    (hf : KPartRunN N P P₀ P₁ Xf ℓ δf mssp fdf nf Bwf σf wtf Pkf Hcf)
    {fds : FaceData N Xs (bdry N P₀ P₁)} {ns Bws : ℕ}
    {σs : Klein.SrcD fds.DQ fds.k ≃ Fin (Fintype.card (Klein.SrcD fds.DQ fds.k))}
    {wts : Klein.SrcD fds.DQ fds.k → ℤ} {Pks : Input} {Hcs : ℕ}
    (hs : KPartRunN N P P₀ P₁ Xs ℓ δs mssp fds ns Bws σs wts Pks Hcs)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    {src : ℕ → V} (hsrc : IsEnum b src (bdry N P₀ P₁))
    {zf zs δrf δrs : ℕ} (hzf : zf ≤ 1) (hzs : zs ≤ 1) (hz : zf ≠ zs)
    (hδrf : 752 ≤ δrf ∧ δrf < 900) (hδrs : 752 ≤ δrs ∧ δrs < 900)
    (Pbf βf Rkf δbf Pbs βs Rks δbs Y S βK βN M W' WN : ℕ) (I : Input) (c : Config)
    (hKf : KLayN b w fdf.k (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) nf (Bwf + 16 * (nf + 1))
      (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf βK βN W')
    (hKs : KLayN b w fds.k (Fintype.card (Klein.SrcD fds.DQ fds.k)) ns (Bws + 16 * (ns + 1))
      (Y + 2 * S) Pbs δbs (Y + (3 + 5 * zs) * S) S βs Rks βK βN W')
    (hWf : βK + (2 * (Bwf + 16 * (nf + 1)) + 1) + (2 * Hcf + 1) * (2 * Hcf + 1) + (2 * Hcf + 1)
      ≤ WN)
    (hWs : βK + (2 * (Bws + 16 * (ns + 1)) + 1) + (2 * Hcs + 1) * (2 * Hcs + 1) + (2 * Hcs + 1)
      ≤ WN)
    (hM0 : 0 < M) (hMf : 2 * Hcf + 1 + 2 * M ≤ WN) (hMs : 2 * Hcs + 1 + 2 * M ≤ WN)
    (hNf : Klein.srcN1 fdf.VQ fdf.FQ fdf.DQ fdf.k ≤ WN)
    (hNs : Klein.srcN1 fds.VQ fds.FQ fds.DQ fds.k ≤ WN)
    (hCf : (Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf))).toNat ≤ WN)
    (hCs : (Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs))).toNat ≤ WN)
    (hKK : Bwf + 16 * (nf + 1) ≤ Bws + 16 * (ns + 1))
    (hIn : Y + 13 * S ≤ Pbs ∧ Y + 13 * S ≤ βs ∧ Y + 13 * S ≤ Rks)
    (hδbs : δbs + w ≤ Y)
    (hc : WordsBounded WN c) (h802 : c.nreg 802 = b) (hx : XCtx Y S c)
    (hrf : c.nreg δrf = δbf) (hrs : c.nreg δrs = δbs)
    (hsl : ∀ i < b, c.nmem (Y + 2 * S + i) = ν (src i))
    (hposf : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbf + ν x) < fdf.k ∧
      fdf.Q.tail (fdf.g (c.nmem (Pbf + ν x))) = fdf.j x)
    (hposs : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbs + ν x) < fds.k ∧
      fds.Q.tail (fds.g (c.nmem (Pbs + ν x))) = fds.j x)
    (hδf : ∀ v < w, ModNat.Res M (δf (ι v) : ℝ) (c.nmem (βN + δbf + v)))
    (hδs : ∀ v < w, ModNat.Res M (δs (ι v) : ℝ) (c.nmem (βN + δbs + v)))
    (hEf : KSlotN (Klein.srcMap fdf.inst.cycle) fdf.k (Klein.srcG fdf.inst.cycle)
      (Klein.srcPiece fdf.k (fdf.P'.image fdf.e))
      (Klein.srcIso (V := fdf.VQ) (F := fdf.FQ) fdf.k (fdf.P'.image fdf.e)
        (faceLen fdf.P' fdf.e (redLen N ℓ δf)) wtf σf) σf Bwf nf βf Rkf (2 * Hcf + 1) Pkf c)
    (hEs : KSlotN (Klein.srcMap fds.inst.cycle) fds.k (Klein.srcG fds.inst.cycle)
      (Klein.srcPiece fds.k (fds.P'.image fds.e))
      (Klein.srcIso (V := fds.VQ) (F := fds.FQ) fds.k (fds.P'.image fds.e)
        (faceLen fds.P' fds.e (redLen N ℓ δs)) wts σs) σs Bws ns βs Rks (2 * Hcs + 1) Pks c)
    (hlow : ∀ a ≤ Bws + 16 * (ns + 1), c.nmem a ≤ Bwf + 16 * (nf + 1))
    (hRW : ∀ r < 752, c.nreg r ≤ W') (hMW : ∀ a ≤ W', c.nmem a ≤ W') :
    ∃ c' t, ∃ βf' βs' : ℕ → V,
      Exec I WN (kPairN zf δrf (kpnOf fdf (redLen N ℓ δf) nf Bwf Pkf βf Rkf Pbf Hcf βK βN M) zs
        δrs (kpnOf fds (redLen N ℓ δs) ns Bws Pks βs Rks Pbs Hcs βK βN M)) c c' t ∧
      t ≤ partNCost P.card fdf.k b (Bwf + 16 * (nf + 1)) (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) +
        partNCost P.card fds.k b (Bws + 16 * (ns + 1)) (Fintype.card (Klein.SrcD fds.DQ fds.k)) +
        14 ∧
      IsEnum b βf' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zf) * S + S + x) = ν (βf' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)).len (βf' i)
        (βf' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf') s t ∧
          ModNat.Res M (matOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf' s t : ℝ)
            (c'.nmem (βN + (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t))))) ∧
      IsEnum b βs' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zs) * S + S + x) = ν (βs' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)).len (βs' i)
        (βs' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs') s t ∧
          ModNat.Res M (matOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs' s t : ℝ)
            (c'.nmem (βN + (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t))))) ∧
      (∀ r, (752 ≤ r ∧ r < 910) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, 2 * (Bws + 16 * (ns + 1)) + 1 < a → (a < Y + 3 * S ∨ Y + 13 * S ≤ a) →
        (a < βN + (Y + (3 + 5 * zf) * S + 3 * S) ∨
          βN + (Y + (3 + 5 * zf) * S + 3 * S) + b * b ≤ a) →
        (a < βN + (Y + (3 + 5 * zs) * S + 3 * S) ∨
          βN + (Y + (3 + 5 * zs) * S + 3 * S) + b * b ≤ a) →
        (a < βK ∨ βK + (2 * (Bws + 16 * (ns + 1)) + 1) < a) → c'.nmem a = c.nmem a) ∧
      c'.output = c.output ∧
      (∀ r, r < 408 ∨ (910 ≤ r ∧ r < 919) → c'.nreg r = 0) ∧ (∀ r < 752, c'.nreg r ≤ W') ∧
      (∀ r, 960 ≤ r → r < 967 → c'.nreg r ≤ W') ∧ (∀ a ≤ W', c'.nmem a ≤ W') := by
  have hx' := hx.reg
  obtain ⟨hδrf1, hδrf2⟩ := hδrf
  obtain ⟨hδrs1, hδrs2⟩ := hδrs
  obtain ⟨hIn1, hIn2, hIn3⟩ := hIn
  have hKf' := hKf
  have hKs' := hKs
  obtain ⟨sk, sb, sbb, kY, rbY, yW, lK, lY, lW, pK, pY, pW, dY, dW, bK, bY, bW, rK, rY, rW, nW,
    kN, wW, bbW⟩ := hKf'
  obtain ⟨sk', sb', sbb', kY', rbY', yW', lK', lY', lW', pK', pY', pW', dY', dW', bK', bY', bW',
    rK', rY', rW', nW', kN', wW', bbW'⟩ := hKs'
  -- 1., 2. the first part
  obtain ⟨c₁, k₁, e₁, hk₁, a960, a961, a962, a963, a964, a965, a966, an₁, anm₁, -, ao₁⟩ :=
    partSet_exec (I := I) (δr := δrf) hzf (by omega) c hc
  have z1 : ∀ i ≤ 4, c.nreg (933 + 5 * zf + i) = Y + (3 + 5 * zf) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zf + i = 930 + (3 + 5 * zf + i) by omega, hx' _ (by omega)]; ring
  obtain ⟨c₂, k₂, βf', e₂, hk₂, hen₂, hO₂, hcr₂, hF₂, hn₂, hm₂, -, -, hl₂, ho₂, hz₂, hRW₂,
      hMW₂⟩ :=
    hf hN hsrc (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf βK βN M W' WN I c₁ hKf hWf
      hM0 hMf hNf hCf e₁.wb_right (by rw [an₁ 802 (by omega), h802])
      (by rw [a960, hx' 2 (by omega)])
      (by rw [a961, show 933 + 5 * zf = 933 + 5 * zf + 0 by rfl, z1 0 (by omega)]; ring)
      (by rw [a962, show 934 + 5 * zf = 933 + 5 * zf + 1 by omega, z1 1 (by omega)]; ring)
      (by rw [a963, show 935 + 5 * zf = 933 + 5 * zf + 2 by omega, z1 2 (by omega)])
      (by rw [a964, show 936 + 5 * zf = 933 + 5 * zf + 3 by omega, z1 3 (by omega)])
      (by rw [a965, show 937 + 5 * zf = 933 + 5 * zf + 4 by omega, z1 4 (by omega)])
      (by rw [a966, hrf])
      (fun i hi => by rw [anm₁]; exact hsl i hi)
      (fun x hx => by rw [anm₁]; exact hposf x hx)
      (fun v hv => by rw [anm₁]; exact hδf v hv)
      ⟨fun i hi => by rw [anm₁]; exact hEf.dat i hi, fun a ha => by rw [anm₁]; exact hEf.res a ha⟩
      (fun a ha => by rw [anm₁]; exact hlow a (by omega))
      (fun r hr => by rw [an₁ r (by omega)]; exact hRW r hr)
      (fun a ha => by rw [anm₁]; exact hMW a ha)
  have z2 : ∀ i ≤ 4, c.nreg (933 + 5 * zs + i) = Y + (3 + 5 * zs) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zs + i = 930 + (3 + 5 * zs + i) by omega, hx' _ (by pomega)]; ring
  have hx2 := hx' 2 (by pomega)
  -- 3., 4. the second part
  obtain ⟨c₃, k₃, e₃, hk₃, b960, b961, b962, b963, b964, b965, b966, bn₃, bnm₃, -, bo₃⟩ :=
    partSet_exec (I := I) (δr := δrs) hzs (by pomega) c₂ e₂.wb_right
  obtain ⟨Af, As, hAf, hAs, hA⟩ : ∃ Af As, Y + (3 + 5 * zf) * S = Y + 3 * S + Af ∧
      Y + (3 + 5 * zs) * S = Y + 3 * S + As ∧ ((Af = 0 ∧ As = 5 * S) ∨ (Af = 5 * S ∧ As = 0)) := by
    rcases (by omega : (zf = 0 ∧ zs = 1) ∨ (zf = 1 ∧ zs = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, 5 * S, by ring, by ring, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨5 * S, 0, by ring, by ring, Or.inr ⟨rfl, rfl⟩⟩
  simp only [hAf, hAs] at *
  have hR₂ : ∀ r, (752 ≤ r ∧ r < 910) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r ∨ r = δrs →
      c₂.nreg r = c.nreg r := fun r hr => by rw [hn₂ r (by pomega), an₁ r (by pomega)]
  have hm₂' : ∀ a, 2 * (Bwf + 16 * (nf + 1)) + 1 < a →
      (a < Y + 3 * S + Af ∨ Y + 3 * S + Af + 5 * S ≤ a) →
      (a < βN + (Y + 3 * S + Af + 3 * S) ∨ βN + (Y + 3 * S + Af + 3 * S) + b * b ≤ a) →
      (a < βK ∨ βK + (2 * (Bwf + 16 * (nf + 1)) + 1) < a) →
      c₂.nmem a = c.nmem a := fun a h1 h2 h3 h4 => by rw [hm₂ a h1 h2 h3 h4, anm₁]
  obtain ⟨c₄, k₄, βs', e₄, hk₄, hen₄, hO₄, hcr₄, hF₄, hn₄, hm₄, -, -, hl₄, ho₄, hz₄, hRW₄,
      hMW₄⟩ :=
    hs hN hsrc (Y + 2 * S) Pbs δbs (Y + 3 * S + As) S βs Rks βK βN M W' WN I c₃ hKs hWs hM0 hMs
      hNs hCs e₃.wb_right (by rw [bn₃ 802 (by pomega), hR₂ 802 (by pomega), h802])
      (by rw [b960, hR₂ 932 (by pomega), hx2])
      (by rw [b961, show 933 + 5 * zs = 933 + 5 * zs + 0 by rfl, hR₂ _ (by pomega),
        z2 0 (by pomega)]; ring)
      (by rw [b962, show 934 + 5 * zs = 933 + 5 * zs + 1 by omega, hR₂ _ (by pomega),
        z2 1 (by pomega)]; ring)
      (by rw [b963, show 935 + 5 * zs = 933 + 5 * zs + 2 by omega, hR₂ _ (by pomega),
        z2 2 (by pomega)])
      (by rw [b964, show 936 + 5 * zs = 933 + 5 * zs + 3 by omega, hR₂ _ (by pomega),
        z2 3 (by pomega)])
      (by rw [b965, show 937 + 5 * zs = 933 + 5 * zs + 4 by omega, hR₂ _ (by pomega),
        z2 4 (by pomega)])
      (by rw [b966, hR₂ δrs (by pomega), hrs])
      (fun i hi => by
        rw [bnm₃, hm₂' _ (by pomega) (by pomega) (by pomega) (by pomega)]; exact hsl i hi)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [bnm₃, hm₂' _ (by pomega) (by pomega) (by pomega) (by pomega)]; exact hposs x hx)
      (fun v hv => by
        rw [bnm₃, hm₂' _ (by pomega) (by pomega) (by pomega) (by pomega)]; exact hδs v hv)
      ⟨fun i hi => by
          rw [bnm₃, hm₂' _ (by pomega) (by pomega) (by pomega) (by pomega)]; exact hEs.dat i hi,
        fun a ha => by
          rw [bnm₃, hm₂' _ (by pomega) (by pomega) (by pomega) (by pomega)]; exact hEs.res a ha⟩
      (fun a ha => by
        rw [bnm₃]
        by_cases h1 : a ≤ 2 * (Bwf + 16 * (nf + 1)) + 1
        · exact (hl₂ a h1).trans hKK
        · rw [hm₂' a (by pomega) (by pomega) (by pomega) (by pomega)]
          exact (hlow a ha).trans hKK)
      (fun r hr => by rw [bn₃ r (by pomega)]; exact hRW₂ r hr)
      (fun a ha => by rw [bnm₃]; exact hMW₂ a ha)
  clear hlow hposs hposf hsl hδf hδs hEf hEs hf hs
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), βf', βs', Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), ?_,
    hen₂, fun x hx => ?_, hcr₂, fun s' hs' t ht => ?_, hen₄, hO₄, hcr₄, hF₄, fun r hr => ?_,
    fun a h1 h2 h3 h3' h4 => ?_, by rw [ho₄, bo₃, ho₂, ao₁], hz₄, hRW₄, fun r h1 h2 => ?_, hMW₄⟩
  · pomega
  · rw [hm₄ _ (by pomega) (by pomega) (by pomega) (by pomega), bnm₃]; exact hO₂ x hx
  · have := rmLt hs' ht
    rw [hm₄ _ (by pomega) (by pomega) (by pomega) (by pomega), bnm₃,
      hm₄ _ (by pomega) (by pomega) (by pomega) (by pomega), bnm₃]
    exact hF₂ s' hs' t ht
  · rw [hn₄ r (by pomega), bn₃ r (by pomega), hR₂ r (by pomega)]
  · rw [hm₄ a (by pomega) (by pomega) (by pomega) (by pomega), bnm₃,
      hm₂' a (by pomega) (by pomega) (by pomega) (by pomega)]
  · rw [hn₄ r (by pomega)]
    rcases (by omega : r = 960 ∨ r = 961 ∨ r = 962 ∨ r = 963 ∨ r = 964 ∨ r = 965 ∨ r = 966)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b960, hR₂ 932 (by pomega), hx2]; pomega
    · rw [b961, show 933 + 5 * zs = 933 + 5 * zs + 0 by rfl, hR₂ _ (by pomega),
        z2 0 (by pomega)]; pomega
    · rw [b962, show 934 + 5 * zs = 933 + 5 * zs + 1 by omega, hR₂ _ (by pomega),
        z2 1 (by pomega)]; pomega
    · rw [b963, show 935 + 5 * zs = 933 + 5 * zs + 2 by omega, hR₂ _ (by pomega),
        z2 2 (by pomega)]; pomega
    · rw [b964, show 936 + 5 * zs = 933 + 5 * zs + 3 by omega, hR₂ _ (by pomega),
        z2 3 (by pomega)]; pomega
    · rw [b965, show 937 + 5 * zs = 933 + 5 * zs + 4 by omega, hR₂ _ (by pomega),
        z2 4 (by pomega)]; pomega
    · rw [b966, hR₂ δrs (by pomega), hrs]; pomega

end NegSSSP

end PlanarFlow
