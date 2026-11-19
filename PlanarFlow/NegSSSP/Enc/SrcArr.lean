module

public import PlanarFlow.NegSSSP.Enc.SrcArrW

/-!
# The dart arrays of the map with the sources copied, on natural words

From the plain arrays of a map `M` with a face cycle `g` of length `k` (by the numbers
`σ₀ d` of its darts: `QRV` the reverses, `QNT` the vertex numbers `νv₀` of the tails, `QNF` the
face numbers `τ₀`, `QIS` the flags of the piece `S`, `QLN` the lengths `(ℓ d).toNat`; `QG` the
darts `σ₀ (g i)`, `i < k`), `srcArrProg` (natural words only) writes the arrays of Klein's
input (`Klein.KInputNL`: `RV`, `NF`, `NE`, `NG`, `NT`, `NH`, `IS`, `ED`, with `LN` zero) of the
map with the sources copied `Klein.srcMap hf` in the numbering `Klein.srcNum σ₀`, for the layout
`cLayout (srcVNum νv₀) (srcNum σ₀) (srcFNum τ₀)`, the boundary darts `GB` (`Klein.KBnd`), the
target nodes `XN` (`ιv (inl (tail (g i)))`), and the lengths with the sources copied
`(srcLen ℓ (srcW S ℓ) d).toNat` at `SLb` (as `encResProg_fd` reads them).

* `semT`: the words of a dart of the map with the sources copied; `semT_inr`: their closed
  form for the added darts (the case analysis of `srcRev`, `srcTail`, `srcFace` per kind).
* `saInit_exec`, `saOrig_exec` (the original darts), `saAdd_exec` (the added darts),
  `srcArrProg_exec`: **the arrays, within `43 nD + 284 k + 45` steps** (`nD` the number of
  darts of `M`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Klein

variable {P : Input} {W : ℕ}

/-! ### The program

Registers (inputs): `2300` `nD`, `2301` `k`, `2302` `nV`, `2303` `nF`, `2304` `β`, `2305`
`SLb`, `2306 … 2311` the bases `QRV`, `QNT`, `QNF`, `QIS`, `QLN`, `QG`. Computed: `2320` one,
`2321` zero, `2322` eight, `2323` two, `2330` `N = nD + 8 k`, `2331` `a = nV + 2 k`,
`2332` `ae = a + N + (nF + 2 k)`, `2333` `fo = a + N`, `2334` `fo + nF`, `2335` `n = 2 ae`,
`2341 … 2348` the bases of the writer, `2349` `GB`, `2350` `XN`; the counters `2351`, `2364`,
the sum `2352`, `srcW` in `2353`; scratch up to `2399`. -/

/-- The registers of the layout. -/
def saInit : Stmt :=
  block [.constN 2320 1, .constN 2321 0, .constN 2322 8, .constN 2323 2,
    .mulN 2380 2322 2301, .addN 2330 2300 2380,
    .mulN 2380 2323 2301, .addN 2331 2302 2380, .addN 2381 2303 2380,
    .addN 2333 2331 2330, .addN 2332 2333 2381, .addN 2334 2333 2303, .addN 2335 2332 2332,
    .addN 2341 2304 2330, .addN 2342 2341 2330, .addN 2343 2342 2330, .addN 2344 2343 2330,
    .addN 2345 2344 2330, .addN 2346 2345 2330, .addN 2347 2346 2330, .addN 2380 2347 2330,
    .addN 2348 2380 2332, .addN 2349 2380 2335,
    .addN 2381 2349 2330, .constN 2383 6, .mulN 2382 2383 2335, .addN 2381 2381 2382,
    .addN 2381 2381 2301, .constN 2383 4, .addN 2350 2381 2383,
    .constN 2351 0, .constN 2352 0]

/-- The values of the original dart `r2351`. -/
def saPre : Stmt :=
  block [.copyN 2393 2351,
    .addN 2391 2306 2351, .loadN 2394 2391,
    .addN 2391 2307 2351, .loadN 2395 2391,
    .addN 2391 2307 2394, .loadN 2396 2391,
    .addN 2391 2308 2351, .loadN 2397 2391, .addN 2397 2397 2333,
    .addN 2391 2309 2351, .loadN 2398 2391,
    .addN 2391 2310 2351, .loadN 2399 2391,
    .mulN 2391 2398 2399, .addN 2352 2352 2391,
    .addN 2351 2351 2320]

/-- **The original darts.** -/
def saOrig : Stmt := .whileLtN 2351 2300 (.seq saPre (block wrI))

/-- Between the loops: `srcW`, the face node of `g 0`, the counters. -/
def saMid : Stmt :=
  block [.addN 2353 2352 2320, .loadN 2384 2311, .addN 2391 2308 2384, .loadN 2385 2391,
    .addN 2385 2385 2333, .constN 2364 0, .copyN 2365 2300, .copyN 2373 2302, .copyN 2377 2334]

/-- The values shared by the eight darts of the face vertex `i = r2364`. -/
def saHead : Stmt :=
  block [.addN 2366 2365 2320, .addN 2367 2366 2320, .addN 2368 2367 2320,
    .addN 2369 2368 2320, .addN 2370 2369 2320, .addN 2371 2370 2320, .addN 2372 2371 2320,
    .addN 2374 2373 2320, .addN 2378 2377 2320,
    .addN 2383 2364 2320, .modN 2383 2383 2301, .addN 2383 2383 2383, .addN 2375 2302 2383,
    .addN 2376 2375 2320,
    .addN 2383 2364 2301, .subN 2383 2383 2320, .modN 2383 2383 2301, .addN 2383 2383 2383,
    .addN 2379 2334 2383, .addN 2380 2379 2320,
    .addN 2383 2311 2364, .loadN 2384 2383, .addN 2383 2307 2384, .loadN 2381 2383]

/-- The face node of `g i`, `GB[i]`, `XN[i]`, and the counters. -/
def saTail : Stmt :=
  block [.addN 2383 2341 2384, .storeN 2383 2377,
    .addN 2383 2349 2364, .storeN 2383 2365,
    .addN 2383 2350 2364, .storeN 2383 2381,
    .addN 2365 2365 2322, .addN 2373 2373 2323, .addN 2377 2377 2323, .addN 2364 2364 2320]

/-- The eight darts of the face vertex `i`. -/
def saDarts : Stmt :=
  .seq (dartS 2365 2366 2373 2375 2385 2321 2321) <|
  .seq (dartS 2366 2365 2375 2373 2378 2321 2321) <|
  .seq (dartS 2367 2368 2373 2374 2378 2320 2321) <|
  .seq (dartS 2368 2367 2374 2373 2380 2321 2321) <|
  .seq (dartS 2369 2370 2374 2381 2377 2320 2321) <|
  .seq (dartS 2370 2369 2381 2374 2379 2321 2321) <|
  .seq (dartS 2371 2372 2374 2376 2378 2320 2353) (dartS 2372 2371 2376 2374 2377 2321 2321)

/-- The face vertex `i`. -/
def saBody : Stmt := .seq saHead (.seq saDarts saTail)

/-- **The added darts.** -/
def saAdd : Stmt := .whileLtN 2364 2301 saBody

/-- **The dart arrays of the map with the sources copied.** -/
def srcArrProg : Stmt := .seq saInit (.seq saOrig (.seq saMid saAdd))

/-- **`srcArrProg` has no real instruction** (checked by the kernel). -/
theorem srcArrProg_natOnly : Klein.natOnly srcArrProg = true := by kernel_rfl

/-! ### The words of the darts -/

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
  (σ₀ : D ≃ Fin (Fintype.card D)) (νv₀ : V ≃ Fin (Fintype.card V))
  (τ₀ : F ≃ Fin (Fintype.card F))

/-- **The words of a dart of the map with the sources copied** (`fo` the offset of the face
nodes). -/
noncomputable def semT (fo : ℕ) (d : SrcD D k) : WT :=
  ⟨srcNum σ₀ d, srcNum σ₀ (srcRev M k d), srcVNum νv₀ (srcTail M k g d),
    srcVNum νv₀ (srcTail M k g (srcRev M k d)), fo + srcFNum τ₀ (srcFace M k g d),
    if inSrc k S d then 1 else 0, (srcLen ℓ (srcW S ℓ) d).toNat⟩

/-- The words written for an original dart (its face before the face of `g` is cut). -/
def oT (fo : ℕ) (d : D) : WT :=
  ⟨σ₀ d, σ₀ (M.rev d), νv₀ (M.tail d), νv₀ (M.tail (M.rev d)), fo + τ₀ (M.face d),
    if d ∈ S then 1 else 0, (ℓ d).toNat⟩

/-- The words of the added darts, in closed form. -/
def addT (X0 V0 Vs0 F0 Fp0 TG FG SW : ℕ) : SrcKind → WT
  | .ring => ⟨X0, X0 + 1, V0, Vs0, FG, 0, 0⟩
  | .ringR => ⟨X0 + 1, X0, Vs0, V0, F0 + 1, 0, 0⟩
  | .down => ⟨X0 + 2, X0 + 3, V0, V0 + 1, F0 + 1, 1, 0⟩
  | .up => ⟨X0 + 3, X0 + 2, V0 + 1, V0, Fp0 + 1, 0, 0⟩
  | .out => ⟨X0 + 4, X0 + 5, V0 + 1, TG, F0, 1, 0⟩
  | .outR => ⟨X0 + 5, X0 + 4, TG, V0 + 1, Fp0, 0, 0⟩
  | .side => ⟨X0 + 6, X0 + 7, V0 + 1, Vs0 + 1, F0 + 1, 1, SW⟩
  | .sideR => ⟨X0 + 7, X0 + 6, Vs0 + 1, V0 + 1, F0, 0, 0⟩

variable {M k g S ℓ σ₀ νv₀ τ₀}

lemma dwt_oT {β N ae ag SLb fo : ℕ} {m : ℕ → ℕ} (d : D) :
    DWT β N ae ag SLb m (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inl d)) ↔
      DWT β N ae ag SLb m (oT M S ℓ σ₀ νv₀ τ₀ fo d) := by
  simp [semT, oT, DWT, srcNum_inl, srcRev, srcTail, srcVNum_inl, inSrc, srcLen]

/-- **The words of the added darts** (the case analysis of `srcRev`, `srcTail`, `srcFace`,
`inSrc`, `srcLen` per kind). -/
lemma semT_inr (fo : ℕ) (i : Fin k) (κ : SrcKind) :
    semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ)) =
      addT (Fintype.card D + 8 * i) (Fintype.card V + 2 * i)
        (Fintype.card V + 2 * (((i : ℕ) + 1) % k)) (fo + Fintype.card F + 2 * i)
        (fo + Fintype.card F + 2 * (((i : ℕ) + k - 1) % k)) (νv₀ (M.tail (g i)))
        (fo + τ₀ (M.face (g 0))) (srcW S ℓ).toNat κ := by
  cases κ <;>
    simp only [semT, addT, srcRev, srcTail, srcFace, srcNum_inr, srcVNum_inr, srcVNum_inl,
      srcFNum_inr, srcFNum_inl, kindIdx, inSrc, srcLen, val_fsucc, val_fpred, WT.mk.injEq,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Bool.false_eq_true, ite_true,
      ite_false] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | omega | simp

end Sem

/-! ### The runs -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem saInit_exec {nD k nV nF β SLb N a ae : ℕ} (hN : N = nD + 8 * k) (ha : a = nV + 2 * k)
    (hae : ae = a + N + (nF + 2 * k)) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 2300 = nD) (h01 : c.nreg 2301 = k) (h02 : c.nreg 2302 = nV)
    (h03 : c.nreg 2303 = nF) (h04 : c.nreg 2304 = β) (h05 : c.nreg 2305 = SLb)
    (hW : β + 9 * N + 14 * ae + 2 * k + 4 ≤ W) (h8 : 8 ≤ W) :
    ∃ c' t, Exec P W saInit c c' t ∧ t = 32 ∧
      WrRegs β N ae a SLb c' ∧ c'.nreg 2320 = 1 ∧ c'.nreg 2322 = 8 ∧ c'.nreg 2323 = 2 ∧
      c'.nreg 2330 = N ∧ c'.nreg 2333 = a + N ∧ c'.nreg 2334 = a + N + nF ∧
      c'.nreg 2335 = 2 * ae ∧ c'.nreg 2349 = β + 8 * N + 2 * ae ∧
      c'.nreg 2350 = β + 9 * N + 14 * ae + k + 4 ∧ c'.nreg 2351 = 0 ∧ c'.nreg 2352 = 0 ∧
      (∀ r, r < 2320 ∨ 2399 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  subst hN ha hae
  unfold saInit
  exec_block
  all_goals try ((try config_simp); (try simp only [h00, h01, h02, h03, h04, h05]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h00, h01, h02, h03, h04, h05]
  all_goals try omega
  simp (disch := omega) only [upd_other]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem saPre_exec {j acc QRVb QNTb QNFb QISb QLNb fo : ℕ} (c : Config) (hc : WordsBounded W c)
    (h51 : c.nreg 2351 = j) (h52 : c.nreg 2352 = acc) (h06 : c.nreg 2306 = QRVb)
    (h07 : c.nreg 2307 = QNTb) (h08 : c.nreg 2308 = QNFb) (h09 : c.nreg 2309 = QISb)
    (h10 : c.nreg 2310 = QLNb) (h20 : c.nreg 2320 = 1) (h33 : c.nreg 2333 = fo)
    (w1 : QRVb + j ≤ W) (w2 : QNTb + j ≤ W) (w3 : QNTb + c.nmem (QRVb + j) ≤ W)
    (w4 : QNFb + j ≤ W) (w5 : c.nmem (QNFb + j) + fo ≤ W) (w6 : QISb + j ≤ W)
    (w7 : QLNb + j ≤ W) (w8 : acc + c.nmem (QISb + j) * c.nmem (QLNb + j) ≤ W)
    (w9 : j + 1 ≤ W) :
    ∃ c' t, Exec P W saPre c c' t ∧ t = 17 ∧ c'.nreg 2393 = j ∧
      c'.nreg 2394 = c.nmem (QRVb + j) ∧ c'.nreg 2395 = c.nmem (QNTb + j) ∧
      c'.nreg 2396 = c.nmem (QNTb + c.nmem (QRVb + j)) ∧ c'.nreg 2397 = c.nmem (QNFb + j) + fo ∧
      c'.nreg 2398 = c.nmem (QISb + j) ∧ c'.nreg 2399 = c.nmem (QLNb + j) ∧
      c'.nreg 2352 = acc + c.nmem (QISb + j) * c.nmem (QLNb + j) ∧ c'.nreg 2351 = j + 1 ∧
      (∀ r, r ≠ 2351 → r ≠ 2352 → (r < 2390 ∨ 2399 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saPre
  exec_block
  all_goals try ((try config_simp); (try simp only [h51, h52, h06, h07, h08, h09, h10, h20, h33]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h51, h52, h06, h07, h08, h09, h10, h20, h33]
  simp (disch := omega) only [upd_other]

lemma WrRegs.of_frame {β N ae ag SLb : ℕ} {c c' : Config} (h : WrRegs β N ae ag SLb c)
    (hf : ∀ r < 2390, c'.nreg r = c.nreg r) : WrRegs β N ae ag SLb c' := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz⟩ := h
  exact ⟨by rw [hf _ (by omega), b0], by rw [hf _ (by omega), b1], by rw [hf _ (by omega), b2],
    by rw [hf _ (by omega), b3], by rw [hf _ (by omega), b4], by rw [hf _ (by omega), b5],
    by rw [hf _ (by omega), b6], by rw [hf _ (by omega), b7], by rw [hf _ (by omega), b8],
    by rw [hf _ (by omega), bs], by rw [hf _ (by omega), rag], by rw [hf _ (by omega), rae],
    by rw [hf _ (by omega), rz]⟩

lemma WrRegs.of_frame' {β N ae ag SLb : ℕ} {c c' : Config} (h : WrRegs β N ae ag SLb c)
    (hf : ∀ r, (r = 2304 ∨ r = 2305 ∨ r = 2321 ∨ r = 2331 ∨ r = 2332 ∨ (2341 ≤ r ∧ r ≤ 2348)) →
      c'.nreg r = c.nreg r) : WrRegs β N ae ag SLb c' := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz⟩ := h
  exact ⟨by rw [hf _ (by omega), b0], by rw [hf _ (by omega), b1], by rw [hf _ (by omega), b2],
    by rw [hf _ (by omega), b3], by rw [hf _ (by omega), b4], by rw [hf _ (by omega), b5],
    by rw [hf _ (by omega), b6], by rw [hf _ (by omega), b7], by rw [hf _ (by omega), b8],
    by rw [hf _ (by omega), bs], by rw [hf _ (by omega), rag], by rw [hf _ (by omega), rae],
    by rw [hf _ (by omega), rz]⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem saMid_exec {acc QGb QNFb fo nD nV fB : ℕ} (c : Config) (hc : WordsBounded W c)
    (h52 : c.nreg 2352 = acc) (h20 : c.nreg 2320 = 1) (h11 : c.nreg 2311 = QGb)
    (h08 : c.nreg 2308 = QNFb) (h33 : c.nreg 2333 = fo) (h00 : c.nreg 2300 = nD)
    (h02 : c.nreg 2302 = nV) (h34 : c.nreg 2334 = fB)
    (w1 : acc + 1 ≤ W) (w2 : QNFb + c.nmem QGb ≤ W) (w3 : c.nmem (QNFb + c.nmem QGb) + fo ≤ W) :
    ∃ c' t, Exec P W saMid c c' t ∧ t = 9 ∧ c'.nreg 2353 = acc + 1 ∧
      c'.nreg 2385 = c.nmem (QNFb + c.nmem QGb) + fo ∧ c'.nreg 2364 = 0 ∧
      c'.nreg 2365 = nD ∧ c'.nreg 2373 = nV ∧ c'.nreg 2377 = fB ∧
      (∀ r, (r < 2353 ∨ (2353 < r ∧ r < 2364) ∨ 2399 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saMid
  exec_block
  all_goals try ((try config_simp); (try simp only [h52, h20, h11, h08, h33, h00, h02, h34]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h52, h20, h11, h08, h33, h00, h02, h34]
  simp (disch := omega) only [upd_other]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem saHead_exec {i k X0 V0 F0 nV fB QGb QNTb : ℕ} (c : Config) (hc : WordsBounded W c)
    (h64 : c.nreg 2364 = i) (h65 : c.nreg 2365 = X0) (h73 : c.nreg 2373 = V0)
    (h77 : c.nreg 2377 = F0) (h20 : c.nreg 2320 = 1) (h01 : c.nreg 2301 = k)
    (h02 : c.nreg 2302 = nV) (h34 : c.nreg 2334 = fB) (h11 : c.nreg 2311 = QGb)
    (h07 : c.nreg 2307 = QNTb) (hk : 1 ≤ k)
    (w1 : X0 + 7 ≤ W) (w2 : V0 + 1 ≤ W) (w3 : F0 + 1 ≤ W) (w4 : i + k ≤ W)
    (w5 : nV + 2 * k ≤ W) (w6 : fB + 2 * k ≤ W) (w7 : QGb + i ≤ W)
    (w8 : QNTb + c.nmem (QGb + i) ≤ W) :
    ∃ c' t, Exec P W saHead c c' t ∧ t = 24 ∧
      c'.nreg 2366 = X0 + 1 ∧ c'.nreg 2367 = X0 + 2 ∧ c'.nreg 2368 = X0 + 3 ∧
      c'.nreg 2369 = X0 + 4 ∧ c'.nreg 2370 = X0 + 5 ∧ c'.nreg 2371 = X0 + 6 ∧
      c'.nreg 2372 = X0 + 7 ∧ c'.nreg 2374 = V0 + 1 ∧ c'.nreg 2378 = F0 + 1 ∧
      c'.nreg 2375 = nV + 2 * ((i + 1) % k) ∧ c'.nreg 2376 = nV + 2 * ((i + 1) % k) + 1 ∧
      c'.nreg 2379 = fB + 2 * ((i + k - 1) % k) ∧
      c'.nreg 2380 = fB + 2 * ((i + k - 1) % k) + 1 ∧
      c'.nreg 2384 = c.nmem (QGb + i) ∧ c'.nreg 2381 = c.nmem (QNTb + c.nmem (QGb + i)) ∧
      (∀ r, (r < 2366 ∨ r = 2373 ∨ r = 2377 ∨ 2384 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have m1 : (i + 1) % k < k := Nat.mod_lt _ (by omega)
  have m2 : (i + k - 1) % k < k := Nat.mod_lt _ (by omega)
  unfold saHead
  exec_block
  all_goals try ((try config_simp); (try simp only [h64, h65, h73, h77, h20, h01, h02, h34, h11, h07]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl,
    rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h64, h65, h73, h77, h20, h01, h02, h34, h11, h07]
  all_goals try omega
  rcases hr with hr | hr | hr | hr
  · simp (disch := omega) only [upd_other]
  · subst hr; simp (disch := omega) only [upd_other]
  · subst hr; simp (disch := omega) only [upd_other]
  · simp (disch := omega) only [upd_other]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem saTail_exec {i X0 V0 F0 bN gi bG bX TG : ℕ} (c : Config) (hc : WordsBounded W c)
    (h41 : c.nreg 2341 = bN) (h84 : c.nreg 2384 = gi) (h77 : c.nreg 2377 = F0)
    (h49 : c.nreg 2349 = bG) (h64 : c.nreg 2364 = i) (h65 : c.nreg 2365 = X0)
    (h50 : c.nreg 2350 = bX) (h81 : c.nreg 2381 = TG) (h22 : c.nreg 2322 = 8)
    (h23 : c.nreg 2323 = 2) (h73 : c.nreg 2373 = V0) (h20 : c.nreg 2320 = 1)
    (w1 : bN + gi ≤ W) (w2 : bG + i ≤ W) (w3 : bX + i ≤ W) (w4 : X0 + 8 ≤ W) (w5 : V0 + 2 ≤ W)
    (w6 : F0 + 2 ≤ W) (w7 : i + 1 ≤ W) :
    ∃ c' t, Exec P W saTail c c' t ∧ t = 10 ∧
      c'.nmem = upd (upd (upd c.nmem (bN + gi) F0) (bG + i) X0) (bX + i) TG ∧
      c'.nreg 2365 = X0 + 8 ∧ c'.nreg 2373 = V0 + 2 ∧ c'.nreg 2377 = F0 + 2 ∧
      c'.nreg 2364 = i + 1 ∧
      (∀ r, r ≠ 2383 → r ≠ 2365 → r ≠ 2373 → r ≠ 2377 → r ≠ 2364 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold saTail
  exec_block
  all_goals try ((try config_simp); (try simp only [h41, h84, h77, h49, h64, h65, h50, h81, h22, h23, h73, h20]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h41, h84, h77, h49, h64, h65, h50, h81, h22, h23, h73, h20]
  simp (disch := omega) only [upd_other]

/-- The kinds of the added darts, in the order of `saDarts`. -/
def kinds : List SrcKind := [.ring, .ringR, .down, .up, .out, .outR, .side, .sideR]

lemma mem_kinds (κ : SrcKind) : κ ∈ kinds := by cases κ <;> simp [kinds]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- **The eight darts**: the writes `addT … κ`, `κ ∈ kinds`, in order. -/
theorem saDarts_exec {β N ae ag SLb X0 V0 Vs0 F0 Fp0 TG FG SW : ℕ} (c : Config)
    (hc : WordsBounded W c) (hR : WrRegs β N ae ag SLb c)
    (h65 : c.nreg 2365 = X0) (h66 : c.nreg 2366 = X0 + 1) (h67 : c.nreg 2367 = X0 + 2)
    (h68 : c.nreg 2368 = X0 + 3) (h69 : c.nreg 2369 = X0 + 4) (h70 : c.nreg 2370 = X0 + 5)
    (h71 : c.nreg 2371 = X0 + 6) (h72 : c.nreg 2372 = X0 + 7) (h73 : c.nreg 2373 = V0)
    (h74 : c.nreg 2374 = V0 + 1) (h75 : c.nreg 2375 = Vs0) (h76 : c.nreg 2376 = Vs0 + 1)
    (h77 : c.nreg 2377 = F0) (h78 : c.nreg 2378 = F0 + 1) (h79 : c.nreg 2379 = Fp0)
    (h80 : c.nreg 2380 = Fp0 + 1) (h81 : c.nreg 2381 = TG) (h85 : c.nreg 2385 = FG)
    (h53 : c.nreg 2353 = SW) (h20 : c.nreg 2320 = 1) (h21 : c.nreg 2321 = 0)
    (hx : X0 + 7 < N) (hW : β + 8 * N + ae + N ≤ W) (hS : SLb + N ≤ W) (hag : ag + N ≤ W) :
    ∃ c' t, Exec P W saDarts c c' t ∧ t = 248 ∧
      c'.nmem = wrL β N ae ag SLb c.nmem (kinds.map (addT X0 V0 Vs0 F0 Fp0 TG FG SW)) ∧
      (∀ r, r < 2390 ∨ 2399 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, hm₁, hn₁, hrr₁, hrm₁, ho₁⟩ := dart_exec (P := P) (rx := 2365) (rrv := 2366) (rtl := 2373) (rhd := 2375) (rfc := 2385) (ris := 2321) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c hc hR
    (by rw [h65]; omega) hW hS hag
  have f1 : ∀ r < 2390, c₁.nreg r = c.nreg r := fun r hr => hn₁ r (Or.inl hr)
  obtain ⟨c₂, k₂, e₂, hk₂, hm₂, hn₂, hrr₂, hrm₂, ho₂⟩ := dart_exec (P := P) (rx := 2366) (rrv := 2365) (rtl := 2375) (rhd := 2373) (rfc := 2378) (ris := 2321) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₁
    e₁.wb_right (hR.of_frame f1) (by rw [f1 _ (by norm_num), h66]; omega) hW hS hag
  have f2 : ∀ r < 2390, c₂.nreg r = c.nreg r := fun r hr => (hn₂ r (Or.inl hr)).trans (f1 r hr)
  obtain ⟨c₃, k₃, e₃, hk₃, hm₃, hn₃, hrr₃, hrm₃, ho₃⟩ := dart_exec (P := P) (rx := 2367) (rrv := 2368) (rtl := 2373) (rhd := 2374) (rfc := 2378) (ris := 2320) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₂
    e₂.wb_right (hR.of_frame f2) (by rw [f2 _ (by norm_num), h67]; omega) hW hS hag
  have f3 : ∀ r < 2390, c₃.nreg r = c.nreg r := fun r hr => (hn₃ r (Or.inl hr)).trans (f2 r hr)
  obtain ⟨c₄, k₄, e₄, hk₄, hm₄, hn₄, hrr₄, hrm₄, ho₄⟩ := dart_exec (P := P) (rx := 2368) (rrv := 2367) (rtl := 2374) (rhd := 2373) (rfc := 2380) (ris := 2321) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₃
    e₃.wb_right (hR.of_frame f3) (by rw [f3 _ (by norm_num), h68]; omega) hW hS hag
  have f4 : ∀ r < 2390, c₄.nreg r = c.nreg r := fun r hr => (hn₄ r (Or.inl hr)).trans (f3 r hr)
  obtain ⟨c₅, k₅, e₅, hk₅, hm₅, hn₅, hrr₅, hrm₅, ho₅⟩ := dart_exec (P := P) (rx := 2369) (rrv := 2370) (rtl := 2374) (rhd := 2381) (rfc := 2377) (ris := 2320) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₄
    e₄.wb_right (hR.of_frame f4) (by rw [f4 _ (by norm_num), h69]; omega) hW hS hag
  have f5 : ∀ r < 2390, c₅.nreg r = c.nreg r := fun r hr => (hn₅ r (Or.inl hr)).trans (f4 r hr)
  obtain ⟨c₆, k₆, e₆, hk₆, hm₆, hn₆, hrr₆, hrm₆, ho₆⟩ := dart_exec (P := P) (rx := 2370) (rrv := 2369) (rtl := 2381) (rhd := 2374) (rfc := 2379) (ris := 2321) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₅
    e₅.wb_right (hR.of_frame f5) (by rw [f5 _ (by norm_num), h70]; omega) hW hS hag
  have f6 : ∀ r < 2390, c₆.nreg r = c.nreg r := fun r hr => (hn₆ r (Or.inl hr)).trans (f5 r hr)
  obtain ⟨c₇, k₇, e₇, hk₇, hm₇, hn₇, hrr₇, hrm₇, ho₇⟩ := dart_exec (P := P) (rx := 2371) (rrv := 2372) (rtl := 2374) (rhd := 2376) (rfc := 2378) (ris := 2320) (rsl := 2353)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₆
    e₆.wb_right (hR.of_frame f6) (by rw [f6 _ (by norm_num), h71]; omega) hW hS hag
  have f7 : ∀ r < 2390, c₇.nreg r = c.nreg r := fun r hr => (hn₇ r (Or.inl hr)).trans (f6 r hr)
  obtain ⟨c₈, k₈, e₈, hk₈, hm₈, hn₈, hrr₈, hrm₈, ho₈⟩ := dart_exec (P := P) (rx := 2372) (rrv := 2371) (rtl := 2376) (rhd := 2374) (rfc := 2377) (ris := 2321) (rsl := 2321)
    (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c₇
    e₇.wb_right (hR.of_frame f7) (by rw [f7 _ (by norm_num), h72]; omega) hW hS hag
  refine ⟨c₈, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    by omega, ?_, fun r hr => ?_, by rw [hrr₈, hrr₇, hrr₆, hrr₅, hrr₄, hrr₃, hrr₂, hrr₁],
    by rw [hrm₈, hrm₇, hrm₆, hrm₅, hrm₄, hrm₃, hrm₂, hrm₁],
    by rw [ho₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂, ho₁]⟩
  · rw [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁]
    simp only [f7 _ (show (2365 : ℕ) < 2390 by norm_num), f7 _ (show (2366 : ℕ) < 2390 by norm_num),
      f7 _ (show (2367 : ℕ) < 2390 by norm_num), f7 _ (show (2368 : ℕ) < 2390 by norm_num),
      f7 _ (show (2369 : ℕ) < 2390 by norm_num), f7 _ (show (2370 : ℕ) < 2390 by norm_num),
      f7 _ (show (2371 : ℕ) < 2390 by norm_num), f7 _ (show (2372 : ℕ) < 2390 by norm_num),
      f7 _ (show (2373 : ℕ) < 2390 by norm_num), f7 _ (show (2374 : ℕ) < 2390 by norm_num),
      f7 _ (show (2375 : ℕ) < 2390 by norm_num), f7 _ (show (2376 : ℕ) < 2390 by norm_num),
      f7 _ (show (2377 : ℕ) < 2390 by norm_num), f7 _ (show (2378 : ℕ) < 2390 by norm_num),
      f7 _ (show (2379 : ℕ) < 2390 by norm_num), f7 _ (show (2380 : ℕ) < 2390 by norm_num),
      f7 _ (show (2381 : ℕ) < 2390 by norm_num), f7 _ (show (2385 : ℕ) < 2390 by norm_num),
      f7 _ (show (2353 : ℕ) < 2390 by norm_num), f7 _ (show (2320 : ℕ) < 2390 by norm_num),
      f7 _ (show (2321 : ℕ) < 2390 by norm_num),
      f6 _ (show (2365 : ℕ) < 2390 by norm_num), f6 _ (show (2366 : ℕ) < 2390 by norm_num),
      f6 _ (show (2367 : ℕ) < 2390 by norm_num), f6 _ (show (2368 : ℕ) < 2390 by norm_num),
      f6 _ (show (2369 : ℕ) < 2390 by norm_num), f6 _ (show (2370 : ℕ) < 2390 by norm_num),
      f6 _ (show (2371 : ℕ) < 2390 by norm_num), f6 _ (show (2372 : ℕ) < 2390 by norm_num),
      f6 _ (show (2373 : ℕ) < 2390 by norm_num), f6 _ (show (2374 : ℕ) < 2390 by norm_num),
      f6 _ (show (2375 : ℕ) < 2390 by norm_num), f6 _ (show (2376 : ℕ) < 2390 by norm_num),
      f6 _ (show (2377 : ℕ) < 2390 by norm_num), f6 _ (show (2378 : ℕ) < 2390 by norm_num),
      f6 _ (show (2379 : ℕ) < 2390 by norm_num), f6 _ (show (2380 : ℕ) < 2390 by norm_num),
      f6 _ (show (2381 : ℕ) < 2390 by norm_num), f6 _ (show (2385 : ℕ) < 2390 by norm_num),
      f6 _ (show (2353 : ℕ) < 2390 by norm_num), f6 _ (show (2320 : ℕ) < 2390 by norm_num),
      f6 _ (show (2321 : ℕ) < 2390 by norm_num),
      f5 _ (show (2365 : ℕ) < 2390 by norm_num), f5 _ (show (2366 : ℕ) < 2390 by norm_num),
      f5 _ (show (2367 : ℕ) < 2390 by norm_num), f5 _ (show (2368 : ℕ) < 2390 by norm_num),
      f5 _ (show (2369 : ℕ) < 2390 by norm_num), f5 _ (show (2370 : ℕ) < 2390 by norm_num),
      f5 _ (show (2371 : ℕ) < 2390 by norm_num), f5 _ (show (2372 : ℕ) < 2390 by norm_num),
      f5 _ (show (2373 : ℕ) < 2390 by norm_num), f5 _ (show (2374 : ℕ) < 2390 by norm_num),
      f5 _ (show (2375 : ℕ) < 2390 by norm_num), f5 _ (show (2376 : ℕ) < 2390 by norm_num),
      f5 _ (show (2377 : ℕ) < 2390 by norm_num), f5 _ (show (2378 : ℕ) < 2390 by norm_num),
      f5 _ (show (2379 : ℕ) < 2390 by norm_num), f5 _ (show (2380 : ℕ) < 2390 by norm_num),
      f5 _ (show (2381 : ℕ) < 2390 by norm_num), f5 _ (show (2385 : ℕ) < 2390 by norm_num),
      f5 _ (show (2353 : ℕ) < 2390 by norm_num), f5 _ (show (2320 : ℕ) < 2390 by norm_num),
      f5 _ (show (2321 : ℕ) < 2390 by norm_num),
      f4 _ (show (2365 : ℕ) < 2390 by norm_num), f4 _ (show (2366 : ℕ) < 2390 by norm_num),
      f4 _ (show (2367 : ℕ) < 2390 by norm_num), f4 _ (show (2368 : ℕ) < 2390 by norm_num),
      f4 _ (show (2369 : ℕ) < 2390 by norm_num), f4 _ (show (2370 : ℕ) < 2390 by norm_num),
      f4 _ (show (2371 : ℕ) < 2390 by norm_num), f4 _ (show (2372 : ℕ) < 2390 by norm_num),
      f4 _ (show (2373 : ℕ) < 2390 by norm_num), f4 _ (show (2374 : ℕ) < 2390 by norm_num),
      f4 _ (show (2375 : ℕ) < 2390 by norm_num), f4 _ (show (2376 : ℕ) < 2390 by norm_num),
      f4 _ (show (2377 : ℕ) < 2390 by norm_num), f4 _ (show (2378 : ℕ) < 2390 by norm_num),
      f4 _ (show (2379 : ℕ) < 2390 by norm_num), f4 _ (show (2380 : ℕ) < 2390 by norm_num),
      f4 _ (show (2381 : ℕ) < 2390 by norm_num), f4 _ (show (2385 : ℕ) < 2390 by norm_num),
      f4 _ (show (2353 : ℕ) < 2390 by norm_num), f4 _ (show (2320 : ℕ) < 2390 by norm_num),
      f4 _ (show (2321 : ℕ) < 2390 by norm_num),
      f3 _ (show (2365 : ℕ) < 2390 by norm_num), f3 _ (show (2366 : ℕ) < 2390 by norm_num),
      f3 _ (show (2367 : ℕ) < 2390 by norm_num), f3 _ (show (2368 : ℕ) < 2390 by norm_num),
      f3 _ (show (2369 : ℕ) < 2390 by norm_num), f3 _ (show (2370 : ℕ) < 2390 by norm_num),
      f3 _ (show (2371 : ℕ) < 2390 by norm_num), f3 _ (show (2372 : ℕ) < 2390 by norm_num),
      f3 _ (show (2373 : ℕ) < 2390 by norm_num), f3 _ (show (2374 : ℕ) < 2390 by norm_num),
      f3 _ (show (2375 : ℕ) < 2390 by norm_num), f3 _ (show (2376 : ℕ) < 2390 by norm_num),
      f3 _ (show (2377 : ℕ) < 2390 by norm_num), f3 _ (show (2378 : ℕ) < 2390 by norm_num),
      f3 _ (show (2379 : ℕ) < 2390 by norm_num), f3 _ (show (2380 : ℕ) < 2390 by norm_num),
      f3 _ (show (2381 : ℕ) < 2390 by norm_num), f3 _ (show (2385 : ℕ) < 2390 by norm_num),
      f3 _ (show (2353 : ℕ) < 2390 by norm_num), f3 _ (show (2320 : ℕ) < 2390 by norm_num),
      f3 _ (show (2321 : ℕ) < 2390 by norm_num),
      f2 _ (show (2365 : ℕ) < 2390 by norm_num), f2 _ (show (2366 : ℕ) < 2390 by norm_num),
      f2 _ (show (2367 : ℕ) < 2390 by norm_num), f2 _ (show (2368 : ℕ) < 2390 by norm_num),
      f2 _ (show (2369 : ℕ) < 2390 by norm_num), f2 _ (show (2370 : ℕ) < 2390 by norm_num),
      f2 _ (show (2371 : ℕ) < 2390 by norm_num), f2 _ (show (2372 : ℕ) < 2390 by norm_num),
      f2 _ (show (2373 : ℕ) < 2390 by norm_num), f2 _ (show (2374 : ℕ) < 2390 by norm_num),
      f2 _ (show (2375 : ℕ) < 2390 by norm_num), f2 _ (show (2376 : ℕ) < 2390 by norm_num),
      f2 _ (show (2377 : ℕ) < 2390 by norm_num), f2 _ (show (2378 : ℕ) < 2390 by norm_num),
      f2 _ (show (2379 : ℕ) < 2390 by norm_num), f2 _ (show (2380 : ℕ) < 2390 by norm_num),
      f2 _ (show (2381 : ℕ) < 2390 by norm_num), f2 _ (show (2385 : ℕ) < 2390 by norm_num),
      f2 _ (show (2353 : ℕ) < 2390 by norm_num), f2 _ (show (2320 : ℕ) < 2390 by norm_num),
      f2 _ (show (2321 : ℕ) < 2390 by norm_num),
      f1 _ (show (2365 : ℕ) < 2390 by norm_num), f1 _ (show (2366 : ℕ) < 2390 by norm_num),
      f1 _ (show (2367 : ℕ) < 2390 by norm_num), f1 _ (show (2368 : ℕ) < 2390 by norm_num),
      f1 _ (show (2369 : ℕ) < 2390 by norm_num), f1 _ (show (2370 : ℕ) < 2390 by norm_num),
      f1 _ (show (2371 : ℕ) < 2390 by norm_num), f1 _ (show (2372 : ℕ) < 2390 by norm_num),
      f1 _ (show (2373 : ℕ) < 2390 by norm_num), f1 _ (show (2374 : ℕ) < 2390 by norm_num),
      f1 _ (show (2375 : ℕ) < 2390 by norm_num), f1 _ (show (2376 : ℕ) < 2390 by norm_num),
      f1 _ (show (2377 : ℕ) < 2390 by norm_num), f1 _ (show (2378 : ℕ) < 2390 by norm_num),
      f1 _ (show (2379 : ℕ) < 2390 by norm_num), f1 _ (show (2380 : ℕ) < 2390 by norm_num),
      f1 _ (show (2381 : ℕ) < 2390 by norm_num), f1 _ (show (2385 : ℕ) < 2390 by norm_num),
      f1 _ (show (2353 : ℕ) < 2390 by norm_num), f1 _ (show (2320 : ℕ) < 2390 by norm_num),
      f1 _ (show (2321 : ℕ) < 2390 by norm_num),
      h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h85,
      h53, h20, h21]
    rfl
  · rw [hn₈ r hr, hn₇ r hr, hn₆ r hr, hn₅ r hr, hn₄ r hr, hn₃ r hr, hn₂ r hr, hn₁ r hr]

section Orig

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

variable (σ₀ S ℓ) in
/-- The term of the dart number `j` in the total length of the piece. -/
def accT (j : ℕ) : ℕ :=
  if h : j < Fintype.card D then
    (if σ₀.symm ⟨j, h⟩ ∈ S then 1 else 0) * (ℓ (σ₀.symm ⟨j, h⟩)).toNat else 0

variable (σ₀ S ℓ) in
/-- The total length of the darts of the piece with numbers `< r`. -/
def accF (r : ℕ) : ℕ := ∑ j ∈ range r, accT S ℓ σ₀ j

lemma accF_succ (r : ℕ) : accF S ℓ σ₀ (r + 1) = accF S ℓ σ₀ r + accT S ℓ σ₀ r := by
  simp [accF, Finset.sum_range_succ]

lemma accF_mono {r r' : ℕ} (h : r ≤ r') : accF S ℓ σ₀ r ≤ accF S ℓ σ₀ r' :=
  Finset.sum_le_sum_of_subset (range_subset_range.2 h)

/-- **The total is `srcW - 1`.** -/
lemma accF_full (hnn : ∀ d ∈ S, 0 ≤ ℓ d) :
    (accF S ℓ σ₀ (Fintype.card D) : ℤ) + 1 = srcW S ℓ := by
  have e1 : accF S ℓ σ₀ (Fintype.card D) = ∑ d, (if d ∈ S then 1 else 0) * (ℓ d).toNat := by
    unfold accF
    rw [← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp σ₀.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [accT, i.2]
  rw [e1, srcW, add_comm]
  congr 1
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
  have e2 : ∑ x ∈ univ.filter (fun d => ¬ d ∈ S),
      ((if x ∈ S then (1 : ℤ) else 0) * ((ℓ x).toNat : ℤ)) = 0 :=
    Finset.sum_eq_zero fun x hx => by simp only [mem_filter] at hx; simp [hx.2]
  rw [e2, add_zero, Finset.filter_mem_eq_inter, univ_inter]
  refine Finset.sum_congr rfl fun x hx => ?_
  simp [hx, Int.toNat_of_nonneg (hnn x hx)]

/-- Reading an input array placed apart from the writes. -/
lemma lay_in {b len β E SLb SE x : ℕ} (d : b + len ≤ β ∨ E ≤ b)
    (e : b + len ≤ SLb ∨ SE ≤ b) (hx : x < len) :
    (b + x < β ∨ E ≤ b + x) ∧ (b + x < SLb ∨ SE ≤ b + x) := by
  omega

set_option maxHeartbeats 4000000 in
/-- **The original darts**: their words, with the face of every dart before the face of `g` is
cut (`oT`), and the total length of the piece in `r2352`. -/
theorem saOrig_exec {β SLb N a ae fo QRVb QNTb QNFb QISb QLNb : ℕ}
    (hND : Fintype.card D ≤ N) (hW : β + 8 * N + ae + N ≤ W) (hS : SLb + N ≤ W)
    (hag : a + N ≤ W) (hSd : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb)
    (q1 : QRVb + Fintype.card D ≤ W) (q2 : QNTb + Fintype.card D ≤ W)
    (q3 : QNFb + Fintype.card D ≤ W) (q4 : QISb + Fintype.card D ≤ W)
    (q5 : QLNb + Fintype.card D ≤ W)
    (d1 : QRVb + Fintype.card D ≤ β ∨ β + 8 * N + ae + N ≤ QRVb)
    (d2 : QNTb + Fintype.card D ≤ β ∨ β + 8 * N + ae + N ≤ QNTb)
    (d3 : QNFb + Fintype.card D ≤ β ∨ β + 8 * N + ae + N ≤ QNFb)
    (d4 : QISb + Fintype.card D ≤ β ∨ β + 8 * N + ae + N ≤ QISb)
    (d5 : QLNb + Fintype.card D ≤ β ∨ β + 8 * N + ae + N ≤ QLNb)
    (e1 : QRVb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QRVb)
    (e2 : QNTb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNTb)
    (e3 : QNFb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNFb)
    (e4 : QISb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QISb)
    (e5 : QLNb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QLNb)
    (hfo : fo + Fintype.card F ≤ W) (hsum : accF S ℓ σ₀ (Fintype.card D) ≤ W)
    (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 2300 = Fintype.card D)
    (h06 : c.nreg 2306 = QRVb) (h07 : c.nreg 2307 = QNTb) (h08 : c.nreg 2308 = QNFb)
    (h09 : c.nreg 2309 = QISb) (h10 : c.nreg 2310 = QLNb) (h20 : c.nreg 2320 = 1)
    (h33 : c.nreg 2333 = fo) (hR : WrRegs β N ae a SLb c) (h51 : c.nreg 2351 = 0)
    (h52 : c.nreg 2352 = 0)
    (hQRV : ∀ d, c.nmem (QRVb + σ₀ d) = σ₀ (M.rev d))
    (hQNT : ∀ d, c.nmem (QNTb + σ₀ d) = νv₀ (M.tail d))
    (hQNF : ∀ d, c.nmem (QNFb + σ₀ d) = τ₀ (M.face d))
    (hQIS : ∀ d, c.nmem (QISb + σ₀ d) = if d ∈ S then 1 else 0)
    (hQLN : ∀ d, c.nmem (QLNb + σ₀ d) = (ℓ d).toNat) :
    ∃ c' t, Exec P W saOrig c c' t ∧ t ≤ 43 * Fintype.card D + 2 ∧
      (∀ d, DWT β N ae a SLb c'.nmem (oT M S ℓ σ₀ νv₀ τ₀ fo d) ∧
        c'.nmem (β + N + σ₀ d) = fo + τ₀ (M.face d)) ∧
      c'.nreg 2352 = accF S ℓ σ₀ (Fintype.card D) ∧ c'.nreg 2351 = Fintype.card D ∧
      (∀ x, (x < β ∨ β + 8 * N + ae + N ≤ x) → (x < SLb ∨ SLb + N ≤ x) →
        c'.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 2351 → r ≠ 2352 → (r < 2390 ∨ 2399 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun r c' =>
    (∀ d, (σ₀ d : ℕ) < r → DWT β N ae a SLb c'.nmem (oT M S ℓ σ₀ νv₀ τ₀ fo d) ∧
        c'.nmem (β + N + σ₀ d) = fo + τ₀ (M.face d)) ∧
      c'.nreg 2352 = accF S ℓ σ₀ r ∧
      (∀ x, (x < β ∨ β + 8 * N + ae + N ≤ x) → (x < SLb ∨ SLb + N ≤ x) →
        c'.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 2351 → r ≠ 2352 → (r < 2390 ∨ 2399 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧ c'.nreg 2351 = r
  have r1 := fun x (hx : x < Fintype.card D) => lay_in d1 e1 hx
  have r2 := fun x (hx : x < Fintype.card D) => lay_in d2 e2 hx
  have r3 := fun x (hx : x < Fintype.card D) => lay_in d3 e3 hx
  have r4 := fun x (hx : x < Fintype.card D) => lay_in d4 e4 hx
  have r5 := fun x (hx : x < Fintype.card D) => lay_in d5 e5 hx
  clear d1 d2 d3 d4 d5 e1 e2 e3 e4 e5
  obtain ⟨c', t, ex, ht, hw', hJ⟩ := forLoop_exec (P := P) (W := W) (a := 2351) (bR := 2300)
    (body := .seq saPre (block wrI)) J (n := Fintype.card D) (K := 41) c hc h51 h00
    ⟨fun d hd => absurd hd (by omega), by rw [h52]; rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      rfl, rfl, rfl, h51⟩
    (fun r c₁ hr hw₁ ha hb ⟨gd, gacc, gm, gn, grr, grm, go, _⟩ => by
      set d₀ := σ₀.symm ⟨r, hr⟩ with hd₀
      have hσ : (σ₀ d₀ : ℕ) = r := by rw [hd₀, Equiv.apply_symm_apply]
      have hrv := (σ₀ (M.rev d₀)).2
      have m1 : c₁.nmem (QRVb + r) = σ₀ (M.rev d₀) := by
        rw [gm _ (r1 r hr).1 (r1 r hr).2, ← hσ]; exact hQRV d₀
      have m2 : c₁.nmem (QNTb + r) = νv₀ (M.tail d₀) := by
        rw [gm _ (r2 r hr).1 (r2 r hr).2, ← hσ]; exact hQNT d₀
      have m3 : c₁.nmem (QNTb + σ₀ (M.rev d₀)) = νv₀ (M.tail (M.rev d₀)) := by
        rw [gm _ (r2 _ hrv).1 (r2 _ hrv).2]; exact hQNT _
      have m4 : c₁.nmem (QNFb + r) = τ₀ (M.face d₀) := by
        rw [gm _ (r3 r hr).1 (r3 r hr).2, ← hσ]; exact hQNF d₀
      have m5 : c₁.nmem (QISb + r) = if d₀ ∈ S then 1 else 0 := by
        rw [gm _ (r4 r hr).1 (r4 r hr).2, ← hσ]; exact hQIS d₀
      have m6 : c₁.nmem (QLNb + r) = (ℓ d₀).toNat := by
        rw [gm _ (r5 r hr).1 (r5 r hr).2, ← hσ]; exact hQLN d₀
      have hT : accT S ℓ σ₀ r = (if d₀ ∈ S then 1 else 0) * (ℓ d₀).toNat := by
        simp [accT, hr, hd₀]
      have hsr := accF_mono (σ₀ := σ₀) (S := S) (ℓ := ℓ) (show r + 1 ≤ Fintype.card D by omega)
      rw [accF_succ, hT] at hsr
      have hf := (τ₀ (M.face d₀)).2
      have hv := (νv₀ (M.tail (M.rev d₀))).2
      obtain ⟨c₂, k₂, e₂, hk₂, p93, p94, p95, p96, p97, p98, p99, p52, p51, pn, pm, prr, prm,
          po⟩ :=
        saPre_exec (P := P) (QRVb := QRVb) (QNTb := QNTb) (QNFb := QNFb) (QISb := QISb)
          (QLNb := QLNb) (fo := fo) c₁ hw₁ ha gacc
          (by rw [gn _ (by omega) (by omega) (by omega), h06])
          (by rw [gn _ (by omega) (by omega) (by omega), h07])
          (by rw [gn _ (by omega) (by omega) (by omega), h08])
          (by rw [gn _ (by omega) (by omega) (by omega), h09])
          (by rw [gn _ (by omega) (by omega) (by omega), h10])
          (by rw [gn _ (by omega) (by omega) (by omega), h20])
          (by rw [gn _ (by omega) (by omega) (by omega), h33])
          (by omega) (by omega) (by rw [m1]; omega) (by omega) (by rw [m4]; omega) (by omega)
          (by omega) (by rw [m5, m6]; omega) (by omega)
      have hR₂ : WrRegs β N ae a SLb c₂ := by
        obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bs, rag, rae, rz⟩ := hR
        have g' : ∀ r', r' ≠ 2351 → r' ≠ 2352 → (r' < 2390 ∨ 2399 < r') →
            c₂.nreg r' = c.nreg r' := fun r' h1 h2 h3 => by rw [pn r' h1 h2 h3, gn r' h1 h2 h3]
        exact ⟨by rw [g' _ (by omega) (by omega) (by omega), b0],
          by rw [g' _ (by omega) (by omega) (by omega), b1],
          by rw [g' _ (by omega) (by omega) (by omega), b2],
          by rw [g' _ (by omega) (by omega) (by omega), b3],
          by rw [g' _ (by omega) (by omega) (by omega), b4],
          by rw [g' _ (by omega) (by omega) (by omega), b5],
          by rw [g' _ (by omega) (by omega) (by omega), b6],
          by rw [g' _ (by omega) (by omega) (by omega), b7],
          by rw [g' _ (by omega) (by omega) (by omega), b8],
          by rw [g' _ (by omega) (by omega) (by omega), bs],
          by rw [g' _ (by omega) (by omega) (by omega), rag],
          by rw [g' _ (by omega) (by omega) (by omega), rae],
          by rw [g' _ (by omega) (by omega) (by omega), rz]⟩
      obtain ⟨c₃, k₃, e₃, hk₃, hm₃, hn₃, hrr₃, hrm₃, ho₃⟩ :=
        wr_exec (P := P) c₂ e₂.wb_right hR₂ (by rw [p93]; omega) hW hS hag
      have hmem : c₃.nmem = wrT β N ae a SLb c₁.nmem (oT M S ℓ σ₀ νv₀ τ₀ fo d₀) := by
        rw [hm₃, pm, p93, p94, p95, p96, p97, p98, p99, m1, m2, m3, m4, m5, m6, ← hσ]
        simp only [wrT, oT]
        rw [add_comm (τ₀ (M.face d₀) : ℕ) fo]
      have hok : OkT N (oT M S ℓ σ₀ νv₀ τ₀ fo d₀) := ⟨by simp only [oT]; omega,
        by simp only [oT]; omega⟩
      refine ⟨c₃, _, .seq e₂ e₃, by omega, by rw [hn₃ _ (by omega), p51], ?_, ?_⟩
      · rw [hn₃ _ (by omega), pn _ (by omega) (by omega) (by omega)]; exact hb
      refine ⟨fun d hd => ?_, by rw [hn₃ _ (by omega), p52, accF_succ, hT, m5, m6], ?_,
        fun r' h1 h2 h3 => by rw [hn₃ _ (by omega), pn r' h1 h2 h3, gn r' h1 h2 h3],
        by rw [hrr₃, prr, grr], by rw [hrm₃, prm, grm], by rw [ho₃, po, go],
        by rw [hn₃ _ (by omega), p51]⟩
      · rw [hmem]
        by_cases hdd : d = d₀
        · rw [hdd]
          have := wrL_dwT (ag := a) hSd [oT M S ℓ σ₀ νv₀ τ₀ fo d₀] c₁.nmem
            (List.mem_singleton_self _) (by simp) (by simpa using hok)
          simp only [wrL_cons, wrL_nil] at this
          exact ⟨this.1, this.2⟩
        · have hlt : (σ₀ d : ℕ) < r := by
            have : (σ₀ d : ℕ) ≠ r := by
              intro e
              apply hdd
              rw [hd₀]
              exact σ₀.eq_symm_apply.2 (Fin.ext e)
            omega
          obtain ⟨h1, h2⟩ := gd d hlt
          have hok' : OkT N (oT M S ℓ σ₀ νv₀ τ₀ fo d) := ⟨by simp only [oT]; omega,
            by simp only [oT]; have := (σ₀ (M.rev d)).2; omega⟩
          have hne : (oT M S ℓ σ₀ νv₀ τ₀ fo d₀).x ≠ (oT M S ℓ σ₀ νv₀ τ₀ fo d).x := by
            simp only [oT]; omega
          refine ⟨?_, ?_⟩
          · have := dwT_wrL (ag := a) hSd hok' [oT M S ℓ σ₀ νv₀ τ₀ fo d₀] c₁.nmem h1
              (by simpa using hok) (by simpa using hne)
            simpa using this
          · have := nf_wrL (ag := a) hSd (show (σ₀ d : ℕ) < N by omega)
              [oT M S ℓ σ₀ νv₀ τ₀ fo d₀] c₁.nmem (by simpa using hok) (by simpa [oT] using hne)
            simp only [wrL_cons, wrL_nil] at this
            rw [this, h2]
      · intro x hx1 hx2
        rw [hmem, ← gm x hx1 hx2]
        have := wrL_other (ag := a) hSd hx1 hx2 [oT M S ℓ σ₀ νv₀ τ₀ fo d₀] c₁.nmem
          (by simpa using hok)
        simpa using this)
  obtain ⟨gd, gacc, gm, gn, grr, grm, go, g51⟩ := hJ
  exact ⟨c', t, ex, by omega, fun d => gd d (σ₀ d).2, gacc, g51, gm, gn, grr, grm, go⟩

end Orig

end NegSSSP

end PlanarFlow
