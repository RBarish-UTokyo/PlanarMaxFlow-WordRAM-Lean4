module

public import PlanarFlow.BKMNW.StTreeD

/-!
# Distances and tight parents in memory, for any injective node numbering

One program `stdP` for the initial tree of the s-t flow (and any shortest-path tree with tight
parents): from the arrays by darts `NT[σ d] = ιv (tail d)`, `NH[σ d] = ιv (head d)`,
`L[σ d] = (ℓ d).toNat` (`ℓ > 0`) of a map whose every vertex is reached from the root `u`:

1. `onesProg`: `A[y] := 1` for the `n` nodes (the flags and the reach bits of `tpProg`);
2. `osProg`: the out-lists (counting sort by the tail nodes);
3. `dkProg`: the distances (`dkProg_dist'`, no onto numbering needed);
4. `tpProg`: the last tight dart into every node.

The scratch is laid out above `Ab` (the setup computes the bases): `A [Ab, Ab+n)`, counting sort
`[Ab+n, Ab+3n+1)`, out-lists `[Ab+3n+1, Ab+5n+1+nD)`, distances `D [Db, Db+n)`, Dijkstra scratch
`[Db+n, Db+4n)`, parents `PAR [Db+4n, Db+5n)`, `Db = Ab + 5n + 1 + nD`.

* `onesProg_exec`; `stdP`; `dist_toNat_le` (`dist ≤ #V · Lmax` for a reached vertex);
* **`stdP_exec`**: within `stdCost n nD` steps (`O((n + nD) log n)`), `D[ιv x] = dist u x` for every
  vertex and, for every `x ≠ u`, `PAR[ιv x] = σ d` for a dart `d` into `x` tight for the distances
  (`dist (tail d) + ℓ d = dist x`); memory below `Ab` and from `Db + 5n` on kept.

Registers: inputs `7860 nD`, `7861 n`, `7862 NTb`, `7863 NHb`, `7864 Lb`, `7865 Ab`, `7870 Inf`,
`7871 ιv u`; scratch `7866 … 7869`, `7872 … 7875`, and those of `osProg` (`1500 … 1520`),
`dkProg` (`2500 … 2547`), `tpProg` (`2300 … 2321`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

variable {P : Input} {W : ℕ}

/-! ### The ones -/

/-- `A[y] := 1` for `y < n` (`r7865 = Ab`, `r7861 = n`). -/
def onesProg : Stmt :=
  .seq (block [.constN 7874 1, .constN 7873 0])
    (.whileLtN 7873 7861 (block [.addN 7875 7865 7873, .storeN 7875 7874, .addN 7873 7873 7874]))

theorem onesProg_exec {n Ab : ℕ} (hW : Ab + n ≤ W) (h1 : 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (h61 : c.nreg 7861 = n) (h65 : c.nreg 7865 = Ab) :
    ∃ c' t, Exec P W onesProg c c' t ∧ t ≤ 5 * n + 4 ∧
      ((∀ y < n, c'.nmem (Ab + y) = 1) ∧ (∀ a, a < Ab ∨ Ab + n ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 7873 ∨ 7876 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold onesProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < i, c'.nmem (Ab + y) = 1) ∧ (∀ a, a < Ab ∨ Ab + i ≤ a → c'.nmem a = c.nmem a) ∧
      c'.nreg 7874 = 1 ∧ (∀ r, r < 7873 ∨ 7876 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7873) (bR := 7861)
    (body := block [.addN 7875 7865 7873, .storeN 7875 7874, .addN 7873 7873 7874]) J (K := 3)
    (n := n) _ ‹_› (by config_simp) (by config_simp; exact h61) ?_
    (fun i c₁ hi hw ha hb ⟨g, gm, g74, gn, gr, grm, go⟩ => by
      have e65 : c₁.nreg 7865 = Ab := (gn _ (by omega)).trans h65
      exec_block
      all_goals try ((try config_simp); (try simp only [e65, ha, g74]); omega)
      dsimp only [J]
      config_simp
      simp only [e65, ha, g74]
      and_intros
      all_goals first
        | omega | rfl | trivial | assumption
        | (intros; simp only [upd_apply] <;>
           split_ifs <;> (first | omega | rfl | (apply g; omega) | (apply gm; omega) |
             (apply gn; omega))))) ?_
  · dsimp only [J]
    config_simp
    and_intros
    all_goals first
      | omega | rfl | trivial
      | (intros; simp only [upd_apply] <;> split_ifs <;> (first | omega | rfl))
  intro c₂ k₂ hk₂ _ hJ
  obtain ⟨_, g, gm, _, gn, gr, grm, go⟩ := hJ
  exact ⟨by omega, g, gm, gn, gr, grm, go⟩


/-! ### The out-lists as arcs -/

section Arcs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

theorem outMem_arcs {M : CombMap D V F} {S : Finset D} {nD : ℕ} {σ : D ≃ Fin nD} {ιv : V → ℕ}
    {mem : ℕ → ℕ} {OBb OEb OLb : ℕ} (h : OutMem M S σ ιv mem OBb OEb OLb) :
    (∀ x i, mem (OBb + ιv x) ≤ i → i < mem (OEb + ιv x) →
      ∃ d ∈ S, M.tail d = x ∧ mem (OLb + i) = σ d) ∧
    (∀ d ∈ S, ∃ i, mem (OBb + ιv (M.tail d)) ≤ i ∧ i < mem (OEb + ιv (M.tail d)) ∧
      mem (OLb + i) = σ d) := by
  refine ⟨fun x i h1 h2 => ?_, fun d hd => ?_⟩
  · obtain ⟨ds, -, hm, he, -, hol⟩ := h x
    have hk : i - mem (OBb + ιv x) < ds.length := by omega
    have hmem := (hm ds[i - mem (OBb + ιv x)]).1 (List.getElem_mem hk)
    refine ⟨_, hmem.1, hmem.2, ?_⟩
    have := hol _ hk
    rwa [show mem (OBb + ιv x) + (i - mem (OBb + ιv x)) = i by omega] at this
  · obtain ⟨ds, -, hm, he, -, hol⟩ := h (M.tail d)
    have hdm : d ∈ ds := (hm d).2 ⟨hd, rfl⟩
    obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdm
    refine ⟨mem (OBb + ιv (M.tail d)) + k, by omega, by omega, ?_⟩
    rw [hol k hk, hkd]

end Arcs


/-! ### The program -/

/-- The bases: `Ob = Ab + n` (`7866`), `OBb = Ob + 2n + 1` (`7867`), `Db = OBb + 2n + nD`
(`7868`), `Xb = Db + n` (`7869`), `Pb = Db + 4n` (`7872`). -/
def stdSet0 : Stmt :=
  block [.addN 7866 7865 7861, .addN 7867 7866 7861, .addN 7867 7867 7861, .constN 7876 1,
    .addN 7867 7867 7876, .addN 7868 7867 7861, .addN 7868 7868 7861, .addN 7868 7868 7860,
    .addN 7869 7868 7861, .addN 7872 7869 7861, .addN 7872 7872 7861, .addN 7872 7872 7861]

def stdOsSet : Stmt :=
  block [.copyN 1500 7860, .copyN 1501 7861, .copyN 1502 7862, .copyN 1504 7865, .copyN 1505 7866,
    .addN 1506 7866 7861, .addN 1506 1506 7876, .copyN 1507 7867, .addN 1508 7867 7861,
    .addN 1509 1508 7861]

def stdDkSet : Stmt :=
  block [.copyN 2500 7861, .copyN 2501 7868, .copyN 2502 7869, .copyN 2504 7867,
    .addN 2505 7867 7861, .addN 2506 2505 7861, .copyN 2507 7863, .copyN 2508 7864,
    .copyN 2509 7870, .copyN 2510 7871]

def stdTpSet : Stmt :=
  block [.copyN 2300 7860, .copyN 2301 7865, .copyN 2302 7862, .copyN 2303 7863, .copyN 2304 7864,
    .copyN 2305 7865, .copyN 2306 7868, .copyN 2307 7872]

/-- **Distances and tight parents in memory.** -/
def stdA : Stmt := .seq onesProg (.seq stdSet0 (.seq stdOsSet osProg))
def stdB : Stmt := .seq stdDkSet dkProg
def stdC : Stmt := .seq stdTpSet tpProg
def stdP : Stmt := .seq stdA (.seq stdB stdC)

theorem stdP_natOnly : Klein.natOnly stdP = true := by kernel_rfl

/-- The step bound of `stdP`. -/
def stdCost (n nD : ℕ) : ℕ :=
  5 * n + 4 + 12 + 10 + osCost nD n + 10 +
    (17 * n + 13 * lg (2 * n) + 22 + n * (23 * lg (2 * n) + 21) + (13 * lg (2 * n) + 20) * nD) +
    8 + (29 * nD + 5)

section Run

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

theorem stdSet0_exec {n nD Ab : ℕ} (hW : Ab + 10 * n + 1 + nD ≤ W) (c : Config)
    (hc : WordsBounded W c) (h60 : c.nreg 7860 = nD) (h61 : c.nreg 7861 = n)
    (h65 : c.nreg 7865 = Ab) :
    ∃ c' t, Exec P W stdSet0 c c' t ∧ t ≤ 12 ∧
      (c'.nreg 7866 = Ab + n ∧ c'.nreg 7867 = Ab + 3 * n + 1 ∧
        c'.nreg 7868 = Ab + 5 * n + 1 + nD ∧ c'.nreg 7869 = Ab + 6 * n + 1 + nD ∧
        c'.nreg 7872 = Ab + 9 * n + 1 + nD ∧ c'.nreg 7876 = 1 ∧
        (∀ r, r < 7866 ∨ (7870 ≤ r ∧ r < 7872) ∨ 7877 ≤ r ∨ (7873 ≤ r ∧ r < 7876) →
          c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold stdSet0
  exec_block
  all_goals try ((try config_simp); (try simp only [h60, h61, h65]); omega)
  config_simp
  simp only [h60, h61, h65]
  and_intros
  all_goals first
    | omega | rfl | trivial
    | (intros; simp only [upd_apply] <;> split_ifs <;> (first | omega | rfl))



theorem stdOsSet_exec {n nD NTb Ab Ob OBb : ℕ} (hW : OBb + 2 * n ≤ W) (hW' : Ob + n + 1 ≤ W)
    (c : Config)
    (hc : WordsBounded W c) (h60 : c.nreg 7860 = nD) (h61 : c.nreg 7861 = n)
    (h62 : c.nreg 7862 = NTb) (h65 : c.nreg 7865 = Ab) (h66 : c.nreg 7866 = Ob)
    (h67 : c.nreg 7867 = OBb) (h76 : c.nreg 7876 = 1) :
    ∃ c' t, Exec P W stdOsSet c c' t ∧ t ≤ 10 ∧
      (c'.nreg 1500 = nD ∧ c'.nreg 1501 = n ∧ c'.nreg 1502 = NTb ∧ c'.nreg 1504 = Ab ∧
        c'.nreg 1505 = Ob ∧ c'.nreg 1506 = Ob + n + 1 ∧ c'.nreg 1507 = OBb ∧
        c'.nreg 1508 = OBb + n ∧ c'.nreg 1509 = OBb + n + n ∧
        (∀ r, r < 1500 ∨ 1510 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold stdOsSet
  exec_block
  all_goals try ((try config_simp); (try simp only [h61, h66, h67, h76]); omega)
  config_simp
  simp only [h60, h61, h62, h65, h66, h67, h76]
  and_intros
  all_goals first
    | omega | rfl | trivial
    | (intros; simp only [upd_apply] <;> split_ifs <;> (first | omega | rfl))

theorem stdDkSet_exec {n Db Xb OBb NHb Lb Inf rt : ℕ} (hW : OBb + 2 * n ≤ W) (c : Config)
    (hc : WordsBounded W c) (h61 : c.nreg 7861 = n) (h63 : c.nreg 7863 = NHb)
    (h64 : c.nreg 7864 = Lb) (h67 : c.nreg 7867 = OBb) (h68 : c.nreg 7868 = Db)
    (h69 : c.nreg 7869 = Xb) (h70 : c.nreg 7870 = Inf) (h71 : c.nreg 7871 = rt) :
    ∃ c' t, Exec P W stdDkSet c c' t ∧ t ≤ 10 ∧
      (c'.nreg 2500 = n ∧ c'.nreg 2501 = Db ∧ c'.nreg 2502 = Xb ∧ c'.nreg 2504 = OBb ∧
        c'.nreg 2505 = OBb + n ∧ c'.nreg 2506 = OBb + n + n ∧ c'.nreg 2507 = NHb ∧
        c'.nreg 2508 = Lb ∧ c'.nreg 2509 = Inf ∧ c'.nreg 2510 = rt ∧
        (∀ r, r < 2500 ∨ 2511 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold stdDkSet
  exec_block
  all_goals try ((try config_simp); (try simp only [h61, h67]); omega)
  config_simp
  simp only [h61, h63, h64, h67, h68, h69, h70, h71]
  and_intros
  all_goals first
    | omega | rfl | trivial
    | (intros; simp only [upd_apply] <;> split_ifs <;> (first | omega | rfl))

theorem stdTpSet_exec {nD NTb NHb Lb Ab Db Pb : ℕ} (c : Config)
    (hc : WordsBounded W c) (h60 : c.nreg 7860 = nD) (h62 : c.nreg 7862 = NTb)
    (h63 : c.nreg 7863 = NHb) (h64 : c.nreg 7864 = Lb) (h65 : c.nreg 7865 = Ab)
    (h68 : c.nreg 7868 = Db) (h72 : c.nreg 7872 = Pb) :
    ∃ c' t, Exec P W stdTpSet c c' t ∧ t ≤ 8 ∧
      (c'.nreg 2300 = nD ∧ c'.nreg 2301 = Ab ∧ c'.nreg 2302 = NTb ∧ c'.nreg 2303 = NHb ∧
        c'.nreg 2304 = Lb ∧ c'.nreg 2305 = Ab ∧ c'.nreg 2306 = Db ∧ c'.nreg 2307 = Pb ∧
        (∀ r, r < 2300 ∨ 2308 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold stdTpSet
  exec_block
  config_simp
  simp only [h60, h62, h63, h64, h65, h68, h72]
  and_intros
  all_goals first
    | omega | rfl | trivial
    | (intros; simp only [upd_apply] <;> split_ifs <;> (first | omega | rfl))

lemma dist_toNat_le {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {u x : V} {Lmax : ℕ}
    (hpos : ∀ d ∈ S, 0 < ℓ d) (hL : ∀ d ∈ S, (ℓ d).toNat ≤ Lmax)
    (hx : MSSP.Reach (MSSP.pieceGraph M S ℓ) u x) :
    (MSSP.dist (MSSP.pieceGraph M S ℓ) u x).toNat ≤ Fintype.card V * Lmax := by
  classical
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  obtain ⟨l, hl, hw⟩ := MSSP.exists_walk_dist hnn hx
  obtain ⟨l', hl', hsub, hnd⟩ := MSSP.exists_nodup_walk hl
  have hlen : l'.length ≤ Fintype.card V := by
    have := hnd.length_le_card
    rw [List.length_map] at this
    omega
  have hw' : MSSP.wlen (MSSP.pieceGraph M S ℓ) l' ≤ MSSP.wlen (MSSP.pieceGraph M S ℓ) l :=
    List.Sublist.sum_le_sum (hsub.map _) (fun a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact hnn b)
  have h2 := wlen_le_length (M := M) hL hpos l'
  have h3 : l'.length * Lmax ≤ Fintype.card V * Lmax := Nat.mul_le_mul_right _ hlen
  have h5 := MSSP.dist_nonneg hnn hx
  have h6 := MSSP.dist_le hnn hl'
  have : ((l'.length * Lmax : ℕ) : ℤ) ≤ ((Fintype.card V * Lmax : ℕ) : ℤ) := by exact_mod_cast h3
  omega



lemma stdOsLay {nD n NTb Ab : ℕ} (T K : ℕ → ℕ) (hDn : nD ≤ n) (hNTA : NTb + nD ≤ Ab)
    (hW : Ab + 10 * n + 1 + nD ≤ W) (htlt : ∀ i < nD, T i < n) :
    OsLay nD n NTb Ab (Ab + n) (Ab + n + n + 1) (Ab + 3 * n + 1) (Ab + 4 * n + 1)
      (Ab + 5 * n + 1) W T K :=
  ⟨fun i hi _ => htlt i hi, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- Stage A: the ones, the bases, the out-lists. -/
theorem stdA_exec {M : CombMap D V F} {nD n : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιn : ∀ x, ιv x < n) (hDn : nD ≤ n)
    {NTb Ab : ℕ} (hNTA : NTb + nD ≤ Ab)
    (hW : Ab + 10 * n + 1 + nD ≤ W) (c : Config) (hc : WordsBounded W c)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d))
    (h60 : c.nreg 7860 = nD) (h61 : c.nreg 7861 = n) (h62 : c.nreg 7862 = NTb)
    (h65 : c.nreg 7865 = Ab) :
    ∃ c' t, Exec P W stdA c c' t ∧ t ≤ 5 * n + 4 + 12 + 10 + osCost nD n ∧
      (OutMem M univ σ ιv c'.nmem (Ab + 3 * n + 1) (Ab + 4 * n + 1) (Ab + 5 * n + 1) ∧
        (∃ mm ≤ nD, (∀ x < n, c'.nmem (Ab + 3 * n + 1 + x) ≤ c'.nmem (Ab + 4 * n + 1 + x) ∧
            c'.nmem (Ab + 4 * n + 1 + x) ≤ mm) ∧
          ∑ y ∈ range n, (c'.nmem (Ab + 4 * n + 1 + y) - c'.nmem (Ab + 3 * n + 1 + y)) ≤ mm) ∧
        (∀ y < n, (∀ x, ιv x ≠ y) → c'.nmem (Ab + 4 * n + 1 + y) ≤ c'.nmem (Ab + 3 * n + 1 + y)) ∧
        (∀ y < n, c'.nmem (Ab + y) = 1) ∧
        (∀ a, a < Ab ∨ Ab + 5 * n + 1 + nD ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 7867 = Ab + 3 * n + 1 ∧ c'.nreg 7868 = Ab + 5 * n + 1 + nD ∧
        c'.nreg 7869 = Ab + 6 * n + 1 + nD ∧ c'.nreg 7872 = Ab + 9 * n + 1 + nD ∧
        (∀ r, r < 1500 ∨ (1521 ≤ r ∧ r < 7866) ∨ r = 7870 ∨ r = 7871 ∨ 7877 ≤ r →
          c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσs : ∀ i < nD, ∃ d, (σ d : ℕ) = i := fun i hi =>
    ⟨σ.symm ⟨i, hi⟩, by rw [Equiv.apply_symm_apply]⟩
  unfold stdA
  refine spec_seq ?_
  refine spec_use (onesProg_exec (P := P) (n := n) (Ab := Ab) (by omega) (by omega) c hc h61 h65) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a1, am, an, ar, arm, ao⟩
  refine spec_seq ?_
  refine spec_use (stdSet0_exec (P := P) (n := n) (nD := nD) (Ab := Ab) hW c₁ hw₁
    ((an _ (by omega)).trans h60) ((an _ (by omega)).trans h61) ((an _ (by omega)).trans h65)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b66, b67, b68, b69, b72, b76, bn, bm, br, brm, bo⟩
  have e : ∀ r, 7860 ≤ r → r ≤ 7865 ∨ r = 7870 ∨ r = 7871 → c₂.nreg r = c.nreg r := fun r h1 h2 =>
    by rw [bn r (by omega), an r (by omega)]
  refine spec_seq ?_
  refine spec_use (stdOsSet_exec (P := P) (nD := nD) (NTb := NTb) (Ob := Ab + n)
    (OBb := Ab + 3 * n + 1) (by omega) (by omega) c₂ hw₂
    ((e _ le_rfl (by omega)).trans h60) ((e _ (by omega) (by omega)).trans h61)
    ((e _ (by omega) (by omega)).trans h62) ((e _ (by omega) (by omega)).trans h65)
    b66 b67 b76) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨d00, d01, d02, d04, d05, d06, d07, d08, d09, dn, dm, dr, drm, d_o⟩
  have m3 : ∀ a, a < Ab → c₃.nmem a = c.nmem a := fun a ha => by
    rw [dm, bm, am a (Or.inl ha)]
  have o3 : ∀ y < n, c₃.nmem (Ab + y) = 1 := fun y hy => by rw [dm, bm, a1 y hy]
  have hlay := stdOsLay (fun i => c₃.nmem (NTb + i)) (fun i => c₃.nmem (Ab + i)) hDn hNTA hW
    (fun i hi => by
      obtain ⟨d, rfl⟩ := hσs i hi
      show c₃.nmem (NTb + σ d) < n
      rw [m3 _ (by have := hσ d; omega), hNT]; exact hιn _)
  have hin : OsIn nD n NTb Ab (Ab + n) (Ab + n + n + 1) (Ab + 3 * n + 1)
      (Ab + 4 * n + 1) (Ab + 5 * n + 1) (fun i => c₃.nmem (NTb + i))
      (fun i => c₃.nmem (Ab + i)) c₃ :=
    ⟨d00, d01, d02, d04, d05, by omega, d07, by omega, by omega, fun i _ => rfl, fun i _ => rfl⟩
  refine spec_use (osProg_emp (P := P) (Mp := M) (S := univ) σ hinj hιn
    (fun d => by rw [m3 _ (by have := hσ d; omega)]; exact hNT d)
    (fun d => by simp only [mem_univ, ↓reduceIte]; exact o3 _ (by have := hσ d; omega))
    hlay c₃ hw₃ hin) ?_
  intro c₄ k₄ hk₄ hw₄ hJ4
  obtain ⟨hOM, ⟨mm, hmm, hOBE, -, hdeg⟩, hemp, fm, fn, fr, frm, fo⟩ := hJ4
  refine ⟨by unfold osCost at *; omega, ?_, ⟨mm, hmm, fun x hx => ?_, ?_⟩, fun y hy hne => ?_,
    fun y hy => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · exact hOM
  · exact hOBE x hx
  · exact hdeg
  · exact hemp y hy hne
  · rw [fm _ (Or.inl (by omega)) (Or.inl (by omega)), o3 y hy]
  · rcases ha with ha | ha
    · rw [fm a (Or.inl (by omega)) (Or.inl (by omega)), m3 a ha]
    · rw [fm a (Or.inr (by omega)) (Or.inr (by omega)), dm, bm, am a (Or.inr (by omega))]
  · rw [fn _ (by omega), dn _ (by omega)]; exact b67
  · rw [fn _ (by omega), dn _ (by omega)]; exact b68
  · rw [fn _ (by omega), dn _ (by omega)]; exact b69
  · rw [fn _ (by omega), dn _ (by omega)]; exact b72
  · rw [fn _ (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega)]
  · rw [fr, dr, br, ar]
  · rw [frm, drm, brm, arm]
  · rw [fo, d_o, bo, ao]

lemma stdDkLay {nD n mm NHb Lb Ab Inf Lmax : ℕ} (hDn : nD ≤ n) (hn : 1 ≤ n) (hmm : mm ≤ nD)
    (hNHA : NHb + nD ≤ Ab) (hLA : Lb + nD ≤ Ab) (hW : Ab + 10 * n + 1 + nD ≤ W)
    (hIW : Inf + Lmax ≤ W) :
    DkLay n nD mm (Ab + 5 * n + 1 + nD) (Ab + 6 * n + 1 + nD) (Ab + 3 * n + 1) (Ab + 4 * n + 1)
      (Ab + 5 * n + 1) NHb Lb Inf Lmax W :=
  ⟨hn, by omega, by omega, by omega, hIW, by omega, by omega, by omega, by omega, by omega,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩⟩

set_option maxHeartbeats 1000000 in
/-- Stage B: the distances. -/
theorem stdB_exec {M : CombMap D V F} {nD n : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιn : ∀ x, ιv x < n) (hDn : nD ≤ n) (hn : 1 ≤ n)
    {ℓ : D → ℤ} (hpos : ∀ d, 0 < ℓ d) {Lmax Inf : ℕ} (hL : ∀ d, (ℓ d).toNat ≤ Lmax)
    (hRL : Fintype.card V * Lmax < Inf) (hIW : Inf + Lmax ≤ W) {u : V}
    {NHb Lb Ab : ℕ} (hNHA : NHb + nD ≤ Ab) (hLA : Lb + nD ≤ Ab)
    (hW : Ab + 10 * n + 1 + nD ≤ W) (c : Config) (hc : WordsBounded W c)
    (hOM : OutMem M univ σ ιv c.nmem (Ab + 3 * n + 1) (Ab + 4 * n + 1) (Ab + 5 * n + 1))
    {mm : ℕ} (hmm : mm ≤ nD)
    (hOBE : ∀ x < n, c.nmem (Ab + 3 * n + 1 + x) ≤ c.nmem (Ab + 4 * n + 1 + x) ∧
      c.nmem (Ab + 4 * n + 1 + x) ≤ mm)
    (hdeg : ∑ y ∈ range n, (c.nmem (Ab + 4 * n + 1 + y) - c.nmem (Ab + 3 * n + 1 + y)) ≤ mm)
    (hemp : ∀ y < n, (∀ x, ιv x ≠ y) → c.nmem (Ab + 4 * n + 1 + y) ≤ c.nmem (Ab + 3 * n + 1 + y))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (h61 : c.nreg 7861 = n) (h63 : c.nreg 7863 = NHb) (h64 : c.nreg 7864 = Lb)
    (h67 : c.nreg 7867 = Ab + 3 * n + 1) (h68 : c.nreg 7868 = Ab + 5 * n + 1 + nD)
    (h69 : c.nreg 7869 = Ab + 6 * n + 1 + nD) (h70 : c.nreg 7870 = Inf)
    (h71 : c.nreg 7871 = ιv u) :
    ∃ c' t, Exec P W stdB c c' t ∧
      t ≤ 10 + (17 * n + 13 * lg (2 * n) + 22 + n * (23 * lg (2 * n) + 21) +
        (13 * lg (2 * n) + 20) * nD) ∧
      ((∀ x, MSSP.Reach (MSSP.pieceGraph M univ ℓ) u x →
          c'.nmem (Ab + 5 * n + 1 + nD + ιv x) = (MSSP.dist (MSSP.pieceGraph M univ ℓ) u x).toNat) ∧
        (∀ a, a < Ab + 5 * n + 1 + nD ∨ Ab + 9 * n + 1 + nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2500 ∨ 2548 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨hOut1, hOut2⟩ := outMem_arcs hOM
  unfold stdB
  refine spec_seq ?_
  refine spec_use (stdDkSet_exec (P := P) (n := n) (OBb := Ab + 3 * n + 1) (by omega) c hc
    h61 h63 h64 h67 h68 h69 h70 h71) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨g00, g01, g02, g04, g05, g06, g07, g08, g09, g10, gn, gm, gr, grm, go⟩
  have hlay := stdDkLay (W := W) (mm := mm) (Lmax := Lmax) hDn hn hmm hNHA hLA hW hIW
  refine spec_use (dkProg_dist' (P := P) (M := M) (S := univ) (ℓ := ℓ) (u := u) hinj hιn σ
    (mm := mm) (fun d _ => hpos d) (fun d _ => hL d) hlay hRL c₅ hw₅
    (fun x i h1 h2 => by
      rw [gm] at h1 h2 ⊢
      obtain ⟨d, -, hd, he⟩ := hOut1 x i h1 h2
      exact ⟨d, mem_univ d, hd, he⟩)
    (fun d _ => by
      obtain ⟨i, h1, h2, he⟩ := hOut2 d (mem_univ d)
      exact ⟨i, by rw [gm]; exact h1, by rw [gm]; exact h2, by rw [gm]; exact he⟩)
    (fun y hy => by rw [gm]; exact hOBE y hy) (by rw [gm]; exact hdeg)
    (fun y hy hne => by rw [gm]; exact hemp y hy hne)
    (fun d => by rw [gm]; exact hNH d) (fun d _ => by rw [gm]; exact hLv d)
    g00 g01 g02 g04 (by omega) (by omega) g07 g08 g09 g10) ?_
  intro c₆ k₆ hk₆ hw₆ hJ6
  obtain ⟨hD, -, km, kn, kr, krm, ko⟩ := hJ6
  have hmul := Nat.mul_le_mul_left (13 * lg (2 * n) + 20) hmm
  refine ⟨by omega, hD, fun a ha => ?_, fun r hr => ?_, kr.trans (gr.trans rfl), krm.trans grm,
    ko.trans go⟩
  · rw [km a (by omega) (by omega), gm]
  · rw [kn r hr, gn r (by omega)]

/-- Stage C: the tight parents (index level). -/
theorem stdC_exec {nD n NTb NHb Lb Ab : ℕ} (hDn : nD ≤ n) (hNTA : NTb + nD ≤ Ab)
    (hNHA : NHb + nD ≤ Ab) (hLA : Lb + nD ≤ Ab) (hW : Ab + 10 * n + 1 + nD ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (h60 : c.nreg 7860 = nD) (h62 : c.nreg 7862 = NTb) (h63 : c.nreg 7863 = NHb)
    (h64 : c.nreg 7864 = Lb) (h65 : c.nreg 7865 = Ab) (h68 : c.nreg 7868 = Ab + 5 * n + 1 + nD)
    (h72 : c.nreg 7872 = Ab + 9 * n + 1 + nD)
    (hNT : ∀ j < nD, c.nmem (NTb + j) < n) (hNH : ∀ j < nD, c.nmem (NHb + j) < n) :
    ∃ c' t, Exec P W stdC c c' t ∧ t ≤ 8 + (29 * nD + 5) ∧
      ((∀ y < n, c'.nmem (Ab + 9 * n + 1 + nD + y) = tpW (fun j => c.nmem (Ab + j))
          (fun j => c.nmem (NTb + j)) (fun j => c.nmem (NHb + j)) (fun j => c.nmem (Lb + j))
          (fun y => c.nmem (Ab + y)) (fun y => c.nmem (Ab + 5 * n + 1 + nD + y))
          (fun y => c.nmem (Ab + 9 * n + 1 + nD + y)) nD y) ∧
        (∀ a, a < Ab + 9 * n + 1 + nD ∨ Ab + 10 * n + 1 + nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2300 ∨ 2322 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold stdC
  refine spec_seq ?_
  refine spec_use (stdTpSet_exec (P := P) c hc h60 h62 h63 h64 h65 h68 h72) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a0, a1, a2, a3, a4, a5, a6, a7, an, am, ar, arm, ao⟩
  have hlay : TPLay nD n Ab NTb NHb Lb Ab (Ab + 5 * n + 1 + nD) (Ab + 9 * n + 1 + nD) W :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
  refine spec_use (tpProg_exec (P := P) hlay c₁ hw₁ a0 a1 a2 a3 a4 a5 a6 a7
    (fun j hj => by rw [am]; exact hNT j hj) (fun j hj => by rw [am]; exact hNH j hj)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b1, bm, bn, br, brm, bo⟩
  refine ⟨by omega, fun y hy => by rw [b1 y hy, am], fun a ha => by rw [bm a (by omega), am],
    fun r hr => by rw [bn r (by omega), an r (by omega)], br.trans ar, brm.trans arm,
    bo.trans ao⟩

set_option maxHeartbeats 2000000 in
/-- **Distances and tight parents in memory** (see the module docstring). -/
theorem stdP_exec {M : CombMap D V F} {nD n : ℕ} (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιn : ∀ x, ιv x < n) (hDn : nD ≤ n) (hn : 1 ≤ n)
    {ℓ : D → ℤ} (hpos : ∀ d, 0 < ℓ d) {Lmax Inf : ℕ} (hL : ∀ d, (ℓ d).toNat ≤ Lmax)
    (hRL : Fintype.card V * Lmax < Inf) (hIW : Inf + Lmax ≤ W) {u : V}
    (hreach : ∀ x, MSSP.Reach (MSSP.pieceGraph M univ ℓ) u x)
    {NTb NHb Lb Ab : ℕ} (hNTA : NTb + nD ≤ Ab) (hNHA : NHb + nD ≤ Ab) (hLA : Lb + nD ≤ Ab)
    (hW : Ab + 10 * n + 1 + nD ≤ W) (c : Config) (hc : WordsBounded W c)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d)) (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (h60 : c.nreg 7860 = nD) (h61 : c.nreg 7861 = n) (h62 : c.nreg 7862 = NTb)
    (h63 : c.nreg 7863 = NHb) (h64 : c.nreg 7864 = Lb) (h65 : c.nreg 7865 = Ab)
    (h70 : c.nreg 7870 = Inf) (h71 : c.nreg 7871 = ιv u) :
    ∃ c' t, Exec P W stdP c c' t ∧ t ≤ stdCost n nD ∧
      (∀ x, c'.nmem (Ab + 5 * n + 1 + nD + ιv x) =
        (MSSP.dist (MSSP.pieceGraph M univ ℓ) u x).toNat) ∧
      (∀ x, x ≠ u → ∃ d, c'.nmem (Ab + 9 * n + 1 + nD + ιv x) = σ d ∧ M.head d = x ∧
        MSSP.dist (MSSP.pieceGraph M univ ℓ) u (M.tail d) + ℓ d =
          MSSP.dist (MSSP.pieceGraph M univ ℓ) u x) ∧
      (∀ a, a < Ab ∨ Ab + 10 * n + 1 + nD ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 1500 ∨ (1521 ≤ r ∧ r < 2300) ∨ (2322 ≤ r ∧ r < 2500) ∨
        (2548 ≤ r ∧ r < 7866) ∨ r = 7870 ∨ r = 7871 ∨ 7877 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hσs : ∀ i < nD, ∃ d, (σ d : ℕ) = i := fun i hi =>
    ⟨σ.symm ⟨i, hi⟩, by rw [Equiv.apply_symm_apply]⟩
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M univ ℓ).len a := fun a => (hpos a.1).le
  unfold stdP
  refine spec_seq ?_
  refine spec_use (stdA_exec (P := P) (M := M) σ hinj hιn hDn hNTA hW c hc hNT h60 h61 h62 h65) ?_
  intro c₁ k₁ hk₁ hw₁ hA
  obtain ⟨hOM, ⟨mm, hmm, hOBE, hdeg⟩, hemp, o1, m1, r67, r68, r69, r72, n1, rr1, rm1, ro1⟩ := hA
  have e1 : ∀ r, 7860 ≤ r → r ≤ 7865 ∨ r = 7870 ∨ r = 7871 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 => n1 r (by omega)
  refine spec_seq ?_
  refine spec_use (stdB_exec (P := P) (M := M) σ hinj hιn hDn hn hpos hL hRL hIW (u := u) hNHA hLA
    hW c₁ hw₁ hOM hmm hOBE hdeg hemp
    (fun d => by rw [m1 _ (Or.inl (by have := hσ d; omega))]; exact hNH d)
    (fun d => by rw [m1 _ (Or.inl (by have := hσ d; omega))]; exact hLv d)
    ((e1 _ (by omega) (by omega)).trans h61) ((e1 _ (by omega) (by omega)).trans h63)
    ((e1 _ (by omega) (by omega)).trans h64) r67 r68 r69
    ((e1 _ (by omega) (by omega)).trans h70) ((e1 _ (by omega) (by omega)).trans h71)) ?_
  intro c₂ k₂ hk₂ hw₂ hB
  obtain ⟨hD, m2, n2, rr2, rm2, ro2⟩ := hB
  have m2c : ∀ a, a < Ab → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (Or.inl (by omega)), m1 a (Or.inl ha)]
  have o2 : ∀ y < n, c₂.nmem (Ab + y) = 1 := fun y hy => by
    rw [m2 _ (Or.inl (by omega)), o1 y hy]
  have hD' : ∀ x, c₂.nmem (Ab + 5 * n + 1 + nD + ιv x) =
      (MSSP.dist (MSSP.pieceGraph M univ ℓ) u x).toNat := fun x => hD x (hreach x)
  have e2 : ∀ r, 7860 ≤ r → r ≤ 7865 ∨ r = 7870 ∨ r = 7871 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [n2 r (by omega), e1 r h1 h2]
  refine spec_use (stdC_exec (P := P) hDn hNTA hNHA hLA hW c₂ hw₂
    ((e2 _ le_rfl (by omega)).trans h60) ((e2 _ (by omega) (by omega)).trans h62)
    ((e2 _ (by omega) (by omega)).trans h63) ((e2 _ (by omega) (by omega)).trans h64)
    ((e2 _ (by omega) (by omega)).trans h65) (by rw [n2 _ (by omega)]; exact r68)
    (by rw [n2 _ (by omega)]; exact r72)
    (fun j hj => by
      obtain ⟨d, rfl⟩ := hσs j hj
      rw [m2c _ (by have := hσ d; omega), hNT]; exact hιn _)
    (fun j hj => by
      obtain ⟨d, rfl⟩ := hσs j hj
      rw [m2c _ (by have := hσ d; omega), hNH]; exact hιn _)) ?_
  intro c₃ k₃ hk₃ hw₃ hC
  obtain ⟨hP, m3, n3, rr3, rm3, ro3⟩ := hC
  refine ⟨by unfold stdCost; omega, fun x => ?_, fun x hx => ?_, fun a ha => ?_, fun r hr => ?_,
    by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [ro3, ro2, ro1]⟩
  · rw [m3 _ (Or.inl (by have := hιn x; omega))]; exact hD' x
  · -- a tight dart into `x` exists
    obtain ⟨a, ⟨-, ht⟩, hdst⟩ := MSSP.exists_tight hnn (hreach x) hx
    have hdst' : M.head a.1 = x := hdst
    have hT0 : TightI (fun j => c₂.nmem (Ab + j)) (fun j => c₂.nmem (NTb + j))
        (fun j => c₂.nmem (NHb + j)) (fun j => c₂.nmem (Lb + j)) (fun y => c₂.nmem (Ab + y))
        (fun y => c₂.nmem (Ab + 5 * n + 1 + nD + y)) (σ a.1) := by
      have h1 := hσ a.1
      refine ⟨?_, ?_, ?_⟩
      · show 0 < c₂.nmem (Ab + σ a.1)
        rw [o2 _ (by omega)]; omega
      · show 0 < c₂.nmem (Ab + c₂.nmem (NTb + σ a.1))
        rw [m2c (NTb + σ a.1) (by omega), hNT, o2 _ (hιn _)]; omega
      · show c₂.nmem (Ab + 5 * n + 1 + nD + c₂.nmem (NTb + σ a.1)) + c₂.nmem (Lb + σ a.1) =
          c₂.nmem (Ab + 5 * n + 1 + nD + c₂.nmem (NHb + σ a.1))
        rw [m2c (NTb + σ a.1) (by omega), m2c (NHb + σ a.1) (by omega),
          m2c (Lb + σ a.1) (by omega), hNT, hNH, hLv, hD', hD']
        have e3 : MSSP.dist (MSSP.pieceGraph M univ ℓ) u (M.tail a.1) + ℓ a.1 =
            MSSP.dist (MSSP.pieceGraph M univ ℓ) u (M.head a.1) := ht
        have p1 := MSSP.dist_nonneg hnn (hreach (M.tail a.1))
        have p2 := hpos a.1
        omega
    have hNH0 : c₂.nmem (NHb + σ a.1) = ιv x := by
      rw [m2c (NHb + σ a.1) (by have := hσ a.1; omega), hNH, hdst']
    obtain ⟨hj, hTj, hNj⟩ := tpW_tight (old := fun y => c₂.nmem (Ab + 9 * n + 1 + nD + y)) nD
      ⟨σ a.1, hσ a.1, hT0, hNH0⟩
    obtain ⟨d, hd⟩ := hσs _ hj
    rw [← hd] at hTj hNj
    have hNj' : c₂.nmem (NHb + σ d) = ιv x := hNj
    rw [m2c (NHb + σ d) (by have := hσ d; omega), hNH] at hNj'
    have hhd : M.head d = x := hinj hNj'
    refine ⟨d, ?_, hhd, ?_⟩
    · rw [hP _ (hιn x), hd]
    · obtain ⟨-, -, e⟩ := hTj
      change c₂.nmem (Ab + 5 * n + 1 + nD + c₂.nmem (NTb + σ d)) + c₂.nmem (Lb + σ d) =
        c₂.nmem (Ab + 5 * n + 1 + nD + c₂.nmem (NHb + σ d)) at e
      have := hσ d
      rw [m2c (NTb + σ d) (by omega), m2c (NHb + σ d) (by omega),
        m2c (Lb + σ d) (by omega), hNT, hNH, hLv, hD', hD', hhd] at e
      have p1 := MSSP.dist_nonneg hnn (hreach (M.tail d))
      have p2 := hpos d
      have p3 := MSSP.dist_nonneg hnn (hreach x)
      omega
  · rcases ha with ha | ha
    · rw [m3 a (Or.inl (by omega)), m2c a ha]
    · rw [m3 a (Or.inr (by omega)), m2 a (Or.inr (by omega)), m1 a (Or.inr (by omega))]
  · rw [n3 r (by omega), n2 r (by omega), n1 r (by omega)]

end Run

end NegSSSP

end PlanarFlow
