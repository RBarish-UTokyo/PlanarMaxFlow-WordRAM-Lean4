module

public import PlanarFlow.NegSSSP.Enc.SrcNum
public import PlanarFlow.NegSSSP.KEncLay
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The dart arrays of the map with the sources copied: numberings and the writer

The encoding of a one-face instance is given on the map with the sources copied
(`Klein.srcMap`), with the darts numbered by `Klein.srcNum σ₀`. Here:

* `Klein.srcVNum νv₀`, `Klein.srcFNum τ₀`: the explicit numberings of its vertices and faces
  (the old ones keep their numbers, the vertex `(i, b)` of the face gets `nV + (b + 2 i)`, the
  face `(i, b)` gets `nF + (b + 2 i)`), `val_fpred`.
* `wrI`: the **writer**, a straight-line block storing, for one dart `x` (register `2393`) and
  its values in the registers `2394 … 2399` (reverse, tail node, head node, face node, flag,
  length), the words of the arrays `RV`, `NF`, `NE`, `NG`, `NT`, `NH`, `IS`, `LN` (zero) of
  Klein's input at `β + j N + x`, the word of `ED` at the node of its edge, and the length at
  `SLb + x`; `wr_exec` (24 steps, memory `wrMem`).
* `DW`: the words of one dart (all but `NF`); `wrMem_dw`, `wrMem_nf`, `wrMem_other`,
  `dw_wrMem`: what the writer writes and keeps.

Registers read by the writer: `2304` (`β`), `2341 … 2348` (the bases of `NF … LN` and of the
`ED` words of the edge nodes), `2305` (`SLb`), `2331` (`ag`), `2332` (`ae`), `2321` (zero);
scratch `2390 … 2392`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

variable {V F : Type*} [Fintype V] [Fintype F] {k : ℕ}

/-- **The explicit numbering of the vertices of the map with the sources copied**: the old ones
keep `νv₀ x`, the vertex `(i, b)` gets `nV + (b + 2 i)`. -/
def srcVNum (νv₀ : V ≃ Fin (Fintype.card V)) : SrcV V k ≃ Fin (Fintype.card (SrcV V k)) :=
  ((Equiv.sumCongr νv₀ ((Equiv.refl (Fin k)).prodCongr finTwoEquiv.symm)).trans
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans
    (finCongr (by simp [Fintype.card_sum, Fintype.card_prod]))

lemma srcVNum_inl (νv₀ : V ≃ Fin (Fintype.card V)) (x : V) :
    (srcVNum (k := k) νv₀ (.inl x) : ℕ) = νv₀ x := by
  simp [srcVNum]

lemma srcVNum_inr (νv₀ : V ≃ Fin (Fintype.card V)) (i : Fin k) (b : Bool) :
    (srcVNum νv₀ (.inr (i, b)) : ℕ) = Fintype.card V + ((if b then 1 else 0) + 2 * i) := by
  cases b <;> simp [srcVNum, finProdFinEquiv] <;> rfl

/-- **The explicit numbering of the faces of the map with the sources copied**. -/
def srcFNum (τ₀ : F ≃ Fin (Fintype.card F)) : SrcF F k ≃ Fin (Fintype.card (SrcF F k)) :=
  ((Equiv.sumCongr τ₀ ((Equiv.refl (Fin k)).prodCongr finTwoEquiv.symm)).trans
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans
    (finCongr (by simp [Fintype.card_sum, Fintype.card_prod]))

lemma srcFNum_inl (τ₀ : F ≃ Fin (Fintype.card F)) (y : F) :
    (srcFNum (k := k) τ₀ (.inl y) : ℕ) = τ₀ y := by
  simp [srcFNum]

lemma srcFNum_inr (τ₀ : F ≃ Fin (Fintype.card F)) (i : Fin k) (b : Bool) :
    (srcFNum τ₀ (.inr (i, b)) : ℕ) = Fintype.card F + ((if b then 1 else 0) + 2 * i) := by
  cases b <;> simp [srcFNum, finProdFinEquiv] <;> rfl

lemma card_srcV : Fintype.card (SrcV V k) = Fintype.card V + 2 * k := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

lemma card_srcF : Fintype.card (SrcF F k) = Fintype.card F + 2 * k := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

lemma val_fpred (i : Fin k) : (fpred i : ℕ) = ((i : ℕ) + k - 1) % k := by
  have h1 := val_fsucc (fpred i)
  rw [fsucc_fpred] at h1
  have hp := (fpred i).2
  have hi := i.2
  by_cases h : (fpred i : ℕ) + 1 < k
  · rw [Nat.mod_eq_of_lt h] at h1
    rw [show (i : ℕ) + k - 1 = ((i : ℕ) - 1) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · have e : (fpred i : ℕ) + 1 = k := by omega
    rw [e, Nat.mod_self] at h1
    rw [h1, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

end Klein

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The writer -/

/-- **The writer**: the words of the dart `x = r2393` from its values `r2394 … r2399`
(`rv`, `tl`, `hd`, `fc`, `is`, `sl`); `e = x - (x - rv) = min x rv` the index of its edge. -/
def wrI : List Instr :=
  [.subN 2390 2393 2394, .subN 2390 2393 2390,
    .addN 2391 2304 2393, .storeN 2391 2394,
    .addN 2391 2341 2393, .storeN 2391 2397,
    .addN 2392 2332 2390, .addN 2391 2342 2393, .storeN 2391 2392,
    .addN 2392 2331 2390, .addN 2391 2343 2393, .storeN 2391 2392,
    .addN 2391 2344 2393, .storeN 2391 2395,
    .addN 2391 2345 2393, .storeN 2391 2396,
    .addN 2391 2346 2393, .storeN 2391 2398,
    .addN 2391 2347 2393, .storeN 2391 2321,
    .addN 2391 2348 2390, .storeN 2391 2390,
    .addN 2391 2305 2393, .storeN 2391 2399]

/-- The memory after the writer. -/
def wrMem (β N ae ag SLb : ℕ) (m : ℕ → ℕ) (x rv tl hd fc is sl : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m (β + x) rv) (β + N + x) fc)
    (β + 2 * N + x) (ae + (x - (x - rv)))) (β + 3 * N + x) (ag + (x - (x - rv))))
    (β + 4 * N + x) tl) (β + 5 * N + x) hd) (β + 6 * N + x) is) (β + 7 * N + x) 0)
    (β + 8 * N + ae + (x - (x - rv))) (x - (x - rv))) (SLb + x) sl

/-- **The words of one dart** (all but `NF`): `RV`, `NE`, `NG`, `NT`, `NH`, `IS`, `LN` (zero),
the `ED` word of its edge node, and its length at `SLb`. -/
structure DW (β N ae ag SLb : ℕ) (m : ℕ → ℕ) (x rv tl hd is sl : ℕ) : Prop where
  wrv : m (β + x) = rv
  wne : m (β + 2 * N + x) = ae + min x rv
  wng : m (β + 3 * N + x) = ag + min x rv
  wnt : m (β + 4 * N + x) = tl
  wnh : m (β + 5 * N + x) = hd
  wis : m (β + 6 * N + x) = is
  wln : m (β + 7 * N + x) = 0
  wed : m (β + 8 * N + (ae + min x rv)) = min x rv
  wsl : m (SLb + x) = sl

/-- The registers of the writer's bases. -/
structure WrRegs (β N ae ag SLb : ℕ) (c : Config) : Prop where
  b0 : c.nreg 2304 = β
  b1 : c.nreg 2341 = β + N
  b2 : c.nreg 2342 = β + 2 * N
  b3 : c.nreg 2343 = β + 3 * N
  b4 : c.nreg 2344 = β + 4 * N
  b5 : c.nreg 2345 = β + 5 * N
  b6 : c.nreg 2346 = β + 6 * N
  b7 : c.nreg 2347 = β + 7 * N
  b8 : c.nreg 2348 = β + 8 * N + ae
  bs : c.nreg 2305 = SLb
  ag : c.nreg 2331 = ag
  ae : c.nreg 2332 = ae
  z : c.nreg 2321 = 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The writer's run.** -/
theorem wr_exec {β N ae ag SLb : ℕ} (c : Config) (hc : WordsBounded W c)
    (hR : WrRegs β N ae ag SLb c) (hx : c.nreg 2393 < N) (hW : β + 8 * N + ae + N ≤ W)
    (hS : SLb + N ≤ W) (hag : ag + N ≤ W) :
    ∃ c' k, Exec P W (block wrI) c c' k ∧ k = 24 ∧
      c'.nmem = wrMem β N ae ag SLb c.nmem (c.nreg 2393) (c.nreg 2394) (c.nreg 2395)
        (c.nreg 2396) (c.nreg 2397) (c.nreg 2398) (c.nreg 2399) ∧
      (∀ r, r < 2390 ∨ 2392 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz⟩ := hR
  unfold wrI
  exec_block
  all_goals try ((try config_simp); (try simp only [b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
    simp only [b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz, wrMem]
  · config_simp; simp (disch := omega) only [upd_other]

section WrMem

variable {β N ae ag SLb : ℕ} {m : ℕ → ℕ} {x rv tl hd fc is sl : ℕ}

/-- The writer keeps every other address. -/
lemma wrMem_other {a : ℕ} (h : a ≠ β + x ∧ a ≠ β + N + x ∧ a ≠ β + 2 * N + x ∧
    a ≠ β + 3 * N + x ∧ a ≠ β + 4 * N + x ∧ a ≠ β + 5 * N + x ∧ a ≠ β + 6 * N + x ∧
    a ≠ β + 7 * N + x ∧ a ≠ β + 8 * N + ae + min x rv ∧ a ≠ SLb + x) :
    wrMem β N ae ag SLb m x rv tl hd fc is sl a = m a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have e : x - (x - rv) = min x rv := by omega
  unfold wrMem
  rw [e]
  rw [upd_other _ _ _ h9, upd_other _ _ _ h8, upd_other _ _ _ h7, upd_other _ _ _ h6,
    upd_other _ _ _ h5, upd_other _ _ _ h4, upd_other _ _ _ h3, upd_other _ _ _ h2,
    upd_other _ _ _ h1, upd_other _ _ _ h0]

/-- **What the writer writes** (the slot `[β, β + 8 N + ae + N)` apart from `[SLb, SLb + N)`). -/
lemma wrMem_dw (hx : x < N) (hrv : rv < N) (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) :
    DW β N ae ag SLb (wrMem β N ae ag SLb m x rv tl hd fc is sl) x rv tl hd is sl := by
  have e : x - (x - rv) = min x rv := by omega
  unfold wrMem
  simp only [e]
  constructor
  all_goals
    simp (disch := omega) only [upd_other, upd_same]
  · rw [show β + 8 * N + (ae + min x rv) = β + 8 * N + ae + min x rv by omega, upd_same]

lemma wrMem_nf (hx : x < N) (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) :
    wrMem β N ae ag SLb m x rv tl hd fc is sl (β + N + x) = fc := by
  have e : x - (x - rv) = min x rv := by omega
  unfold wrMem
  simp only [e]
  simp (disch := omega) only [upd_other, upd_same]

/-- **The writer keeps the words of the other darts** (an `ED` word of the same edge node is
written with the same value). -/
lemma dw_wrMem {y rv' tl' hd' is' sl' : ℕ} (h : DW β N ae ag SLb m y rv' tl' hd' is' sl')
    (hxy : y ≠ x) (hx : x < N) (hy : y < N) (hrv : rv < N) (hrv' : rv' < N)
    (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) :
    DW β N ae ag SLb (wrMem β N ae ag SLb m x rv tl hd fc is sl) y rv' tl' hd' is' sl' := by
  obtain ⟨h0, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wrMem_other (by omega)]; exact h0
  · rw [wrMem_other (by omega)]; exact h2
  · rw [wrMem_other (by omega)]; exact h3
  · rw [wrMem_other (by omega)]; exact h4
  · rw [wrMem_other (by omega)]; exact h5
  · rw [wrMem_other (by omega)]; exact h6
  · rw [wrMem_other (by omega)]; exact h7
  · by_cases he : min y rv' = min x rv
    · rw [he]; exact (wrMem_dw (m := m) (tl := tl) (hd := hd) (fc := fc) (is := is) (sl := sl)
        (ag := ag) hx hrv hS).wed
    · rw [wrMem_other (by omega)]; exact h8
  · rw [wrMem_other (by omega)]; exact h9

lemma nf_wrMem {y : ℕ} (hxy : y ≠ x) (hx : x < N) (hy : y < N)
    (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) :
    wrMem β N ae ag SLb m x rv tl hd fc is sl (β + N + y) = m (β + N + y) :=
  wrMem_other (by omega)

end WrMem


/-! ### Lists of writes -/

/-- The values of one write. -/
structure WT where
  x : ℕ
  rv : ℕ
  tl : ℕ
  hd : ℕ
  fc : ℕ
  is : ℕ
  sl : ℕ

section WrL

variable {β N ae ag SLb : ℕ}

/-- One write. -/
def wrT (β N ae ag SLb : ℕ) (m : ℕ → ℕ) (w : WT) : ℕ → ℕ :=
  wrMem β N ae ag SLb m w.x w.rv w.tl w.hd w.fc w.is w.sl

/-- Writes in order. -/
def wrL (β N ae ag SLb : ℕ) (m : ℕ → ℕ) (l : List WT) : ℕ → ℕ :=
  l.foldl (wrT β N ae ag SLb) m

/-- The words of a write. -/
def DWT (β N ae ag SLb : ℕ) (m : ℕ → ℕ) (w : WT) : Prop :=
  DW β N ae ag SLb m w.x w.rv w.tl w.hd w.is w.sl

/-- A write within the arrays. -/
def OkT (N : ℕ) (w : WT) : Prop := w.x < N ∧ w.rv < N

@[simp] lemma wrL_nil (m : ℕ → ℕ) : wrL β N ae ag SLb m [] = m := rfl

@[simp] lemma wrL_cons (m : ℕ → ℕ) (w : WT) (l : List WT) :
    wrL β N ae ag SLb m (w :: l) = wrL β N ae ag SLb (wrT β N ae ag SLb m w) l := rfl

lemma dwT_wrL (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) {w : WT} (hw : OkT N w) :
    ∀ (l : List WT) (m : ℕ → ℕ), DWT β N ae ag SLb m w → (∀ w' ∈ l, OkT N w') →
      (∀ w' ∈ l, w'.x ≠ w.x) → DWT β N ae ag SLb (wrL β N ae ag SLb m l) w
  | [], _, h, _, _ => h
  | w' :: l, m, h, hl, hx => by
    rw [wrL_cons]
    refine dwT_wrL hS hw l _ ?_ (fun w'' h'' => hl w'' (List.mem_cons_of_mem _ h''))
      (fun w'' h'' => hx w'' (List.mem_cons_of_mem _ h''))
    have h1 := hl w' (List.mem_cons_self ..)
    have h2 := hx w' (List.mem_cons_self ..)
    exact dw_wrMem h (Ne.symm h2) h1.1 hw.1 h1.2 hw.2 hS

lemma nf_wrL (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) {y : ℕ} (hy : y < N) :
    ∀ (l : List WT) (m : ℕ → ℕ), (∀ w' ∈ l, OkT N w') → (∀ w' ∈ l, w'.x ≠ y) →
      wrL β N ae ag SLb m l (β + N + y) = m (β + N + y)
  | [], _, _, _ => rfl
  | w' :: l, m, hl, hx => by
    rw [wrL_cons, nf_wrL hS hy l _ (fun w'' h'' => hl w'' (List.mem_cons_of_mem _ h''))
      (fun w'' h'' => hx w'' (List.mem_cons_of_mem _ h''))]
    exact nf_wrMem (Ne.symm (hx w' (List.mem_cons_self ..))) (hl w' (List.mem_cons_self ..)).1
      hy hS

lemma wrL_dwT (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) :
    ∀ (l : List WT) (m : ℕ → ℕ) {w : WT}, w ∈ l → (l.map WT.x).Nodup → (∀ w' ∈ l, OkT N w') →
      DWT β N ae ag SLb (wrL β N ae ag SLb m l) w ∧
        wrL β N ae ag SLb m l (β + N + w.x) = w.fc
  | [], _, _, h, _, _ => absurd h (List.not_mem_nil)
  | w' :: l, m, w, h, hn, hl => by
    rw [wrL_cons]
    have hl' : ∀ w'' ∈ l, OkT N w'' := fun w'' h'' => hl w'' (List.mem_cons_of_mem _ h'')
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with rfl | h
    · have hx : ∀ w'' ∈ l, w''.x ≠ w.x := fun w'' h'' e => hn.1 (e ▸ List.mem_map_of_mem h'')
      have h1 := hl w (List.mem_cons_self ..)
      refine ⟨dwT_wrL hS h1 l _ (wrMem_dw h1.1 h1.2 hS) hl' hx, ?_⟩
      rw [nf_wrL hS h1.1 l _ hl' hx]
      exact wrMem_nf h1.1 hS
    · exact wrL_dwT hS l _ h hn.2 hl'

lemma wrL_other (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) {a : ℕ}
    (ha : a < β ∨ β + 8 * N + ae + N ≤ a) (hb : a < SLb ∨ SLb + N ≤ a) :
    ∀ (l : List WT) (m : ℕ → ℕ), (∀ w' ∈ l, OkT N w') → wrL β N ae ag SLb m l a = m a
  | [], _, _ => rfl
  | w' :: l, m, hl => by
    rw [wrL_cons, wrL_other hS ha hb l _ (fun w'' h'' => hl w'' (List.mem_cons_of_mem _ h''))]
    have h1 := hl w' (List.mem_cons_self ..)
    exact wrMem_other (by have := h1.1; omega)

end WrL

/-! ### One dart from registers -/

/-- **One dart**: copy its values from the registers `rx … rsl` into `2393 … 2399`, then the
writer. -/
def dartS (rx rrv rtl rhd rfc ris rsl : ℕ) : Stmt :=
  .seq (block [.copyN 2393 rx, .copyN 2394 rrv, .copyN 2395 rtl, .copyN 2396 rhd,
    .copyN 2397 rfc, .copyN 2398 ris, .copyN 2399 rsl]) (block wrI)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The run of one dart** (the registers `rx … rsl` below `2390`). -/
theorem dart_exec {β N ae ag SLb : ℕ} {rx rrv rtl rhd rfc ris rsl : ℕ}
    (h1 : rx < 2390) (h2 : rrv < 2390) (h3 : rtl < 2390) (h4 : rhd < 2390) (h5 : rfc < 2390)
    (h6 : ris < 2390) (h7 : rsl < 2390)
    (c : Config) (hc : WordsBounded W c)
    (hR : WrRegs β N ae ag SLb c) (hx : c.nreg rx < N) (hW : β + 8 * N + ae + N ≤ W)
    (hS : SLb + N ≤ W) (hag : ag + N ≤ W) :
    ∃ c' k, Exec P W (dartS rx rrv rtl rhd rfc ris rsl) c c' k ∧ k = 31 ∧
      c'.nmem = wrMem β N ae ag SLb c.nmem (c.nreg rx) (c.nreg rrv) (c.nreg rtl)
        (c.nreg rhd) (c.nreg rfc) (c.nreg ris) (c.nreg rsl) ∧
      (∀ r, r < 2390 ∨ 2399 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hm₁, hrr₁, hrm₁, ho₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 2393 rx, .copyN 2394 rrv, .copyN 2395 rtl, .copyN 2396 rhd,
        .copyN 2397 rfc, .copyN 2398 ris, .copyN 2399 rsl]) c c₁ k₁ ∧ k₁ = 7 ∧
      c₁.nreg = (fun r => if r = 2393 then c.nreg rx else if r = 2394 then c.nreg rrv else
        if r = 2395 then c.nreg rtl else if r = 2396 then c.nreg rhd else
        if r = 2397 then c.nreg rfc else if r = 2398 then c.nreg ris else
        if r = 2399 then c.nreg rsl else c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
    funext r
    simp only [Config.nreg_mk]
    simp (disch := omega) only [upd_other]
    simp only [upd_apply]
    split_ifs <;> first | omega | rfl
  have g : ∀ r, r < 2390 → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hn₁]; simp only; split_ifs <;> omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz⟩ := hR
  have hR₁ : WrRegs β N ae ag SLb c₁ := ⟨by rw [g _ (by omega), b0], by rw [g _ (by omega), b1],
    by rw [g _ (by omega), b2], by rw [g _ (by omega), b3], by rw [g _ (by omega), b4],
    by rw [g _ (by omega), b5], by rw [g _ (by omega), b6], by rw [g _ (by omega), b7],
    by rw [g _ (by omega), b8], by rw [g _ (by omega), bs], by rw [g _ (by omega), rag],
    by rw [g _ (by omega), rae], by rw [g _ (by omega), rz]⟩
  have r3 : c₁.nreg 2393 = c.nreg rx := by rw [hn₁]; simp
  obtain ⟨c₂, k₂, e₂, hk₂, hm₂, hn₂, hrr₂, hrm₂, ho₂⟩ :=
    wr_exec (P := P) c₁ e₁.wb_right hR₁ (by rw [r3]; exact hx) hW hS hag
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_, fun r hr => ?_, by rw [hrr₂, hrr₁],
    by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩
  · rw [hm₂, hm₁]; simp only [hn₁]; rfl
  · rcases hr with hr | hr
    · rw [hn₂ r (Or.inl hr), g r hr]
    · rw [hn₂ r (Or.inr (by omega)), hn₁]; simp only; split_ifs <;> first | omega | rfl

end NegSSSP

end PlanarFlow
