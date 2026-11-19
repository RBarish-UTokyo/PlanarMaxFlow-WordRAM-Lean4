module

public import PlanarFlow.NegSSSP.SplitProg
public import PlanarSeparator.Machine.MillerComp

/-!
# The components of a piece, on the machine

The split of the machine (`PlanarFlow.NegSSSP.splitM`) needs the components `pcomp N P x` of the
piece `P` (darts sharing an end), their sizes, and a dart of a component of more than three
quarters of the darts if there is one. Here they are computed in `O(m)` steps from a **plain
encoding of the piece carrying its own rotation**:

* the darts of `rcl N P` (the darts of `P` and their reverses) numbered `0, …, k - 1` by `δ`
  (`IsEnum k δ (rcl N P)`), the darts of `P` first (`IsEnum m δ P`);
* the reversal: at `bα + h` the number of `N.rev (δ h)`;
* the rotation of the piece: at `bσ + h` the number of `ret (rotPerm N) (rcl N P) (δ h)`, the
  first return of the rotation of `N` to the darts of the piece (the rotation of the piece map
  `kmap N K`, cut down from `N` in the same way).

Two darts of `P` sharing an end `v` have darts of `rcl N P` leaving `v`, in one cycle of the first
return (`sameCycle_ret_iff`, `N.RotTrans`); so the components of `P` are the classes of the
half-edges under the rotation and the reversal (`hstep_pcomp`).

* `compProg`: writes the adjacency array of the half-edges (three slots per half-edge: rotation
  forward, rotation backward, reversal; an involution, `AOk.revOk`), runs the depth-first
  labelling `PlanarSeparator.MillerProg.clab` on it, counts the darts of `P` per label and flags
  the darts of a component of more than three quarters of the darts, keeping one in `r857`
  (`compProg_exec`, `101 k + 24 m + 38` steps).
* `compProg_spec`: **the labels are the components** (`lb x = lb y ↔ δ y ∈ pcomp N P (δ x)`),
  the counts their sizes, the flags the test `3 #P / 4 < #pcomp` of `splitM`, and `r856` says
  whether a large component exists, `r857` then being a dart of it; `compProg_big`: the flags are
  then the membership in that component, as `joinProg_splitM` takes them.
* `natS`, `Exec.natS_frame`: programs without real instructions keep the real registers and
  memory.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset
open PlanarSeparator.MillerProg (clab clab_exec CR FA RevOk)

variable {P : Input} {W : ℕ}

/-! ### Programs on natural numbers keep the real part -/

/-- An instruction not touching the real registers or memory. -/
def natI : Instr → Bool
  | .constR .. | .copyR .. | .addR .. | .subR .. | .mulR .. | .divR .. | .loadR .. | .storeR .. =>
    false
  | _ => true

/-- A statement of instructions not touching the real registers or memory. -/
def natS : Stmt → Bool
  | .skip => true
  | .instr i => natI i
  | .seq s t => natS s && natS t
  | .ifLtN _ _ s t => natS s && natS t
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ s => natS s
  | .whileLtR _ _ _ => false

theorem natI_frame {i : Instr} {c c' : Config} (h : i.effect P c = some c') (hs : natI i = true) :
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  cases i <;> simp [Instr.effect, natI] at h hs <;> obtain ⟨-, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

/-- **A statement on natural numbers keeps the real registers and memory.** -/
theorem Exec.natS_frame {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : natS s = true) : c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  induction h with
  | skip _ => exact ⟨rfl, rfl⟩
  | instr _ he _ _ => exact natI_frame he hs
  | seq _ _ ih₁ ih₂ =>
    simp only [natS, Bool.and_eq_true] at hs
    exact ⟨(ih₂ hs.2).1.trans (ih₁ hs.1).1, (ih₂ hs.2).2.trans (ih₁ hs.1).2⟩
  | ifLtN_true _ _ ih => simp only [natS, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [natS, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ _ => simp [natS] at hs
  | ifLtR_false _ _ _ => simp [natS] at hs
  | whileLtN_false _ _ => exact ⟨rfl, rfl⟩
  | whileLtN_true _ _ _ ih₁ ih₂ => exact ⟨(ih₂ hs).1.trans (ih₁ hs).1, (ih₂ hs).2.trans (ih₁ hs).2⟩
  | whileLtR_false _ _ => exact ⟨rfl, rfl⟩
  | whileLtR_true _ _ _ _ _ => simp [natS] at hs

theorem natS_clab : natS clab = true := by decide

/-! ### The half-edges of the piece -/

/-- **One step between half-edges** `f, g < k`: along the rotation `σ` (either way) or the
reversal `α`. -/
def HeStep (k : ℕ) (α σ : ℕ → ℕ) (f g : ℕ) : Prop :=
  f < k ∧ g < k ∧ (g = σ f ∨ σ g = f ∨ g = α f)

/-- The reversal `α` is an involution and the rotation `σ` a permutation of `0, …, k - 1`. -/
structure HEnc (k : ℕ) (α σ : ℕ → ℕ) : Prop where
  α_lt : ∀ h < k, α h < k
  αα : ∀ h < k, α (α h) = h
  σ_lt : ∀ h < k, σ h < k
  σ_inj : ∀ h < k, ∀ h' < k, σ h = σ h' → h = h'
  σ_surj : ∀ g < k, ∃ h < k, σ h = g

/-- **The adjacency array** of the half-edges: three slots per half-edge `h`, slot `3 h` to the
slot `3 σ h + 1`, and slot `3 h + 2` to the slot `3 α h + 2`. -/
structure AOk (k : ℕ) (α σ A : ℕ → ℕ) : Prop where
  a0 : ∀ h < k, A (3 * h) = 3 * σ h + 1
  a1 : ∀ h < k, A (3 * σ h + 1) = 3 * h
  a2 : ∀ h < k, A (3 * h + 2) = 3 * α h + 2

variable {k : ℕ} {α σ A : ℕ → ℕ}

/-- The adjacency array is an involution of the slots. -/
theorem AOk.revOk (he : HEnc k α σ) (hA : AOk k α σ A) : RevOk k A := by
  intro x hx
  have h3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · have hq : x / 3 < k := by omega
    rw [show x = 3 * (x / 3) by omega, hA.a0 _ hq, hA.a1 _ hq]
    have := he.σ_lt _ hq
    omega
  · have hq : x / 3 < k := by omega
    obtain ⟨h, hh, e⟩ := he.σ_surj _ hq
    rw [show x = 3 * σ h + 1 by omega, hA.a1 _ hh, hA.a0 _ hh]
    omega
  · have hq : x / 3 < k := by omega
    rw [show x = 3 * (x / 3) + 2 by omega, hA.a2 _ hq, hA.a2 _ (he.α_lt _ hq), he.αα _ hq]
    have := he.α_lt _ hq
    omega

/-- The adjacency of the labelling program is the step between half-edges. -/
theorem AOk.fa_iff (he : HEnc k α σ) (hA : AOk k α σ A) (f g : ℕ) :
    FA k A (fun _ => 1) f g ↔ HeStep k α σ f g := by
  unfold FA HeStep
  constructor
  · rintro ⟨hf, -, -, j, hj, e⟩
    interval_cases j
    · rw [Nat.add_zero, hA.a0 _ hf] at e
      have := he.σ_lt _ hf
      exact ⟨hf, by omega, Or.inl (by omega)⟩
    · obtain ⟨h, hh, rfl⟩ := he.σ_surj _ hf
      rw [hA.a1 _ hh] at e
      exact ⟨he.σ_lt _ hh, by omega, Or.inr (Or.inl (by rw [← e]; congr 1; omega))⟩
    · rw [hA.a2 _ hf] at e
      have := he.α_lt _ hf
      exact ⟨hf, by omega, Or.inr (Or.inr (by omega))⟩
  · rintro ⟨hf, hg, h | h | h⟩
    · refine ⟨hf, one_pos, one_pos, 0, by omega, ?_⟩
      rw [Nat.add_zero, hA.a0 _ hf]; omega
    · refine ⟨hf, one_pos, one_pos, 1, by omega, ?_⟩
      rw [← h, hA.a1 _ hg]; omega
    · refine ⟨hf, one_pos, one_pos, 2, by omega, ?_⟩
      rw [hA.a2 _ hf]; omega

theorem AOk.rtg_iff (he : HEnc k α σ) (hA : AOk k α σ A) (f g : ℕ) :
    Relation.ReflTransGen (FA k A (fun _ => 1)) f g ↔ Relation.ReflTransGen (HeStep k α σ) f g := by
  have : FA k A (fun _ => 1) = HeStep k α σ := by
    funext f g; exact propext (hA.fa_iff he f g)
  rw [this]

/-- The number of `x < n` with label `ℓ`. -/
def cntL (lb : ℕ → ℕ) (n ℓ : ℕ) : ℕ := ((range n).filter fun y => lb y = ℓ).card

lemma cntL_succ (lb : ℕ → ℕ) (n ℓ : ℕ) :
    cntL lb (n + 1) ℓ = cntL lb n ℓ + if lb n = ℓ then 1 else 0 :=
  filter_range_succ_card _ n

lemma cntL_le (lb : ℕ → ℕ) (n ℓ : ℕ) : cntL lb n ℓ ≤ n :=
  (card_filter_le _ _).trans (card_range n).le

/-! ### The program -/

/-- Setup: the constants of `clab` (`r140 = 0`, `r141 = 1`, `r142 = 3`, `r143 = k`, `r144 = B + 3 k`
(the selections), `r145 = B + 4 k` (the labels), `r146 = B + 5 k` (the stack), `r147 = B` (the
adjacency array)), `r866 = B + 6 k` (the counts), `r867 = k + 1`, `r868 = 3 m`, `r856 = r857 = 0`,
`r870 = 0`. -/
def cpSetup : Stmt := block [.constN 140 0, .constN 141 1, .constN 142 3, .copyN 143 861,
  .copyN 147 864, .addN 871 861 861, .addN 871 871 861, .addN 144 864 871, .addN 145 144 861,
  .addN 146 145 861, .addN 866 146 861, .addN 867 861 10, .addN 868 860 860, .addN 868 868 860,
  .constN 856 0, .constN 857 0, .constN 870 0]

/-- The three slots of the half-edge `h = r870`: `A[3 h] = 3 σ h + 1`, `A[3 σ h + 1] = 3 h`,
`A[3 h + 2] = 3 α h + 2`; its selection `1` and its label `0`. -/
def cpAdj : Stmt := block [.addN 871 862 870, .loadN 872 871, .addN 871 863 870, .loadN 873 871,
  .addN 874 870 870, .addN 874 874 870, .addN 875 873 873, .addN 875 875 873, .addN 875 875 10,
  .addN 871 147 874, .storeN 871 875, .addN 871 147 875, .storeN 871 874,
  .addN 876 872 872, .addN 876 876 872, .addN 876 876 10, .addN 876 876 10,
  .addN 877 874 10, .addN 877 877 10, .addN 871 147 877, .storeN 871 876,
  .addN 871 144 870, .storeN 871 10, .addN 871 145 870, .storeN 871 140, .addN 870 870 10]

/-- Clearing the count `r870`. -/
def cpZero : Stmt := block [.addN 871 866 870, .storeN 871 140, .addN 870 870 10]

/-- Counting the dart `x = r870`: `C[lb x] += 1`. -/
def cpCount : Stmt := block [.addN 871 145 870, .loadN 872 871, .addN 871 866 872,
  .loadN 873 871, .addN 873 873 10, .storeN 871 873, .addN 870 870 10]

/-- The flag of the dart `x = r870`: `1` if `3 m < 4 C[lb x]` (then `r856 = 1`, `r857 = x`). -/
def cpFlag : Stmt :=
  .seq (block [.addN 871 145 870, .loadN 872 871, .addN 871 866 872, .loadN 873 871,
    .addN 874 873 873, .addN 874 874 874])
  (.seq (.ifLtN 868 874 (block [.constN 875 1, .constN 856 1, .copyN 857 870])
      (.instr (.constN 875 0)))
    (block [.addN 871 865 870, .storeN 871 875, .addN 870 870 10]))

/-- **The components of a piece** (`r860 = m`, `r861 = k`, `r862 = bα`, `r863 = bσ`, `r864 = B`,
`r865 = bF`, `r10 = 1`). -/
def compProg : Stmt :=
  .seq cpSetup <| .seq (.whileLtN 870 861 cpAdj) <| .seq clab <|
  .seq (.instr (.constN 870 0)) <| .seq (.whileLtN 870 867 cpZero) <|
  .seq (.instr (.constN 870 0)) <| .seq (.whileLtN 870 860 cpCount) <|
  .seq (.instr (.constN 870 0)) (.whileLtN 870 860 cpFlag)

theorem natS_compProg : natS compProg = true := by decide

/-- The registers of `compProg`. -/
structure CompIn (m k bα bσ B bF : ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r860 : c.nreg 860 = m
  r861 : c.nreg 861 = k
  r862 : c.nreg 862 = bα
  r863 : c.nreg 863 = bσ
  r864 : c.nreg 864 = B
  r865 : c.nreg 865 = bF

/-- The layout of `compProg`: the scratch `[B, B + 7 k + 1)` (adjacency `3 k`, selections,
labels, stack `k` each, counts `k + 1`) apart from the reversal and rotation `[bα, bα + k)`,
`[bσ, bσ + k)` and the flags `[bF, bF + m)`. -/
structure CompLay (m k bα bσ B bF W : ℕ) : Prop where
  mle : m ≤ k
  wB : B + 7 * k + 1 ≤ W
  wα : bα + k ≤ W
  wσ : bσ + k ≤ W
  wF : bF + m ≤ W
  wm : 4 * m + 3 ≤ W
  dα : bα + k ≤ B ∨ B + 7 * k + 1 ≤ bα
  dσ : bσ + k ≤ B ∨ B + 7 * k + 1 ≤ bσ
  dF : bF + m ≤ B ∨ B + 7 * k + 1 ≤ bF

/-! ### The steps -/

theorem cpAdj_exec {bα bσ B h a s : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e862 : c₁.nreg 862 = bα) (e863 : c₁.nreg 863 = bσ) (e147 : c₁.nreg 147 = B)
    (e144 : c₁.nreg 144 = B + 3 * k) (e145 : c₁.nreg 145 = B + 4 * k) (e140 : c₁.nreg 140 = 0)
    (e10 : c₁.nreg 10 = 1) (ha : c₁.nreg 870 = h) (hma : c₁.nmem (bα + h) = a)
    (hms : c₁.nmem (bσ + h) = s) (hh : h < k) (has : a < k) (hs : s < k)
    (wB : B + 7 * k + 1 ≤ W) (wα : bα + k ≤ W) (wσ : bσ + k ≤ W) :
    ∃ c' t, Exec P W cpAdj c₁ c' t ∧ t ≤ 26 ∧ c'.nreg 870 = h + 1 ∧
      (∀ r, r < 870 ∨ 877 < r → c'.nreg r = c₁.nreg r) ∧
      c'.nmem = upd (upd (upd (upd (upd c₁.nmem (B + (h + h + h)) (s + s + s + 1))
        (B + (s + s + s + 1)) (h + h + h)) (B + (h + h + h + 1 + 1)) (a + a + a + 1 + 1))
        (B + 3 * k + h) 1) (B + 4 * k + h) 0 ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold cpAdj
  exec_block
  all_goals try ((try config_simp); (try simp only [e862, e863, e147, e144, e145, e140, e10, ha,
    hma, hms]) <;> omega)
  refine ⟨by omega, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [e10, ha]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · config_simp; simp only [e862, e863, e147, e144, e145, e140, e10, ha, hma, hms]

/-- The frame of the loops of `compProg` (scratch registers `r870 … r877`). -/
structure CpFr (c c' : Config) : Prop where
  nreg : ∀ r, r < 870 ∨ 877 < r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem CpFr.trans {c c' c'' : Config} (h : CpFr c c') (h' : CpFr c' c'') : CpFr c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

/-- **The adjacency array**: the loop over the half-edges writes `AOk` at `B`, the selections `1`
at `B + 3 k` and the labels `0` at `B + 4 k`. -/
theorem cpAdjLoop_exec {bα bσ B : ℕ} (he : HEnc k α σ) (c₁ : Config) (hw : WordsBounded W c₁)
    (e861 : c₁.nreg 861 = k) (e862 : c₁.nreg 862 = bα) (e863 : c₁.nreg 863 = bσ)
    (e147 : c₁.nreg 147 = B) (e144 : c₁.nreg 144 = B + 3 * k) (e145 : c₁.nreg 145 = B + 4 * k)
    (e140 : c₁.nreg 140 = 0) (e10 : c₁.nreg 10 = 1) (e870 : c₁.nreg 870 = 0)
    (hα : ∀ h < k, c₁.nmem (bα + h) = α h) (hσ : ∀ h < k, c₁.nmem (bσ + h) = σ h)
    (wB : B + 7 * k + 1 ≤ W) (wα : bα + k ≤ W) (wσ : bσ + k ≤ W)
    (dα : bα + k ≤ B ∨ B + 7 * k + 1 ≤ bα) (dσ : bσ + k ≤ B ∨ B + 7 * k + 1 ≤ bσ) :
    ∃ c' t, Exec P W (.whileLtN 870 861 cpAdj) c₁ c' t ∧ t ≤ 28 * k + 2 ∧
      AOk k α σ (fun x => c'.nmem (B + x)) ∧ (∀ h < k, c'.nmem (B + 3 * k + h) = 1) ∧
      (∀ h < k, c'.nmem (B + 4 * k + h) = 0) ∧ CpFr c₁ c' ∧
      (∀ a, (a < B ∨ B + 5 * k ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    CpFr c₁ c' ∧ (∀ a, (a < B ∨ B + 5 * k ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ h < i, c'.nmem (B + 3 * h) = 3 * σ h + 1) ∧
      (∀ h < i, c'.nmem (B + (3 * σ h + 1)) = 3 * h) ∧
      (∀ h < i, c'.nmem (B + (3 * h + 2)) = 3 * α h + 2) ∧
      (∀ h < i, c'.nmem (B + 3 * k + h) = 1) ∧ (∀ h < i, c'.nmem (B + 4 * k + h) = 0)
  refine spec_use (forLoop_exec (P := P) (a := 870) (bR := 861) (body := cpAdj) J (K := 26)
    (n := k) _ hw e870 e861 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fm, f0, f1, f2, f3, f4⟩ => ?_)) ?_
  · exact ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  · have g : ∀ r, r < 870 → c₂.nreg r = c₁.nreg r := fun r hr => fr.nreg r (Or.inl hr)
    have hai := he.α_lt i hi
    have hsi := he.σ_lt i hi
    obtain ⟨c', t, hex, ht, h870, hreg, hmem, hrr, hrm, hout⟩ :=
      cpAdj_exec (P := P) (k := k) (bα := bα) (bσ := bσ) (B := B) (h := i) (a := α i) (s := σ i)
        c₂ hw₂ ((g _ (by omega)).trans e862) ((g _ (by omega)).trans e863)
        ((g _ (by omega)).trans e147) ((g _ (by omega)).trans e144)
        ((g _ (by omega)).trans e145) ((g _ (by omega)).trans e140) ((g _ (by omega)).trans e10)
        ha (by rw [fm _ (by omega)]; exact hα i hi) (by rw [fm _ (by omega)]; exact hσ i hi)
        hi hai hsi wB wα wσ
    refine ⟨c', t, hex, ht, h870, by rw [hreg 861 (by omega)]; exact hb,
      fr.trans ⟨hreg, hrr, hrm, hout⟩, fun a ha' => ?_, fun h hh => ?_, fun h hh => ?_,
      fun h hh => ?_, fun h hh => ?_, fun h hh => ?_⟩
    · rw [hmem]; simp only [upd_apply]
      split_ifs <;> first | omega | exact fm a ha'
    · have hsh := he.σ_lt h (by omega)
      rw [hmem]; simp only [upd_apply]
      rcases Nat.lt_or_ge h i with hlt | hge
      · split_ifs <;> first | omega | exact f0 h hlt
      · have : h = i := by omega
        subst this
        split_ifs <;> omega
    · have hsh := he.σ_lt h (by omega)
      rw [hmem]; simp only [upd_apply]
      rcases Nat.lt_or_ge h i with hlt | hge
      · have hne : σ h ≠ σ i := fun e => by have := he.σ_inj h (by omega) i hi e; omega
        split_ifs <;> first | omega | exact f1 h hlt
      · have : h = i := by omega
        subst this
        split_ifs <;> omega
    · have hah := he.α_lt h (by omega)
      rw [hmem]; simp only [upd_apply]
      rcases Nat.lt_or_ge h i with hlt | hge
      · split_ifs <;> first | omega | exact f2 h hlt
      · have : h = i := by omega
        subst this
        split_ifs <;> omega
    · rw [hmem]; simp only [upd_apply]
      rcases Nat.lt_or_ge h i with hlt | hge
      · split_ifs <;> first | omega | exact f3 h hlt
      · have : h = i := by omega
        subst this
        split_ifs <;> omega
    · rw [hmem]; simp only [upd_apply]
      rcases Nat.lt_or_ge h i with hlt | hge
      · split_ifs <;> first | omega | exact f4 h hlt
      · have : h = i := by omega
        subst this
        split_ifs <;> omega
  · intro c' t ht _ ⟨_, fr, fm, f0, f1, f2, f3, f4⟩
    exact ⟨by omega, ⟨f0, f1, f2⟩, f3, f4, fr, fm⟩

/-- **Clearing the counts** `[bC, bC + k + 1)`. -/
theorem cpZeroLoop_exec {bC : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e866 : c₁.nreg 866 = bC) (e867 : c₁.nreg 867 = k + 1) (e140 : c₁.nreg 140 = 0)
    (e10 : c₁.nreg 10 = 1) (e870 : c₁.nreg 870 = 0) (wC : bC + k + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 870 867 cpZero) c₁ c' t ∧ t ≤ 5 * k + 7 ∧
      (∀ ℓ < k + 1, c'.nmem (bC + ℓ) = 0) ∧ CpFr c₁ c' ∧
      (∀ a, (a < bC ∨ bC + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    CpFr c₁ c' ∧ (∀ a, (a < bC ∨ bC + i ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ ℓ < i, c'.nmem (bC + ℓ) = 0)
  refine spec_use (forLoop_exec (P := P) (a := 870) (bR := 867) (body := cpZero) J (K := 3)
    (n := k + 1) _ hw e870 e867 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fm, f0⟩ => ?_)) ?_
  · exact ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  · have g : ∀ r, r < 870 → c₂.nreg r = c₁.nreg r := fun r hr => fr.nreg r (Or.inl hr)
    have g866 := (g _ (by omega)).trans e866
    have g140 := (g _ (by omega)).trans e140
    have g10 := (g _ (by omega)).trans e10
    unfold cpZero
    exec_block
    all_goals try ((try config_simp); (try simp only [g866, g10, ha]) <;> omega)
    refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
      fr.trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun a ha' => ?_, fun ℓ hℓ => ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; simp only [upd_apply, g866, ha]
      split_ifs <;> first | omega | exact fm a (by omega)
    · config_simp; simp only [upd_apply, g866, ha, g140]
      split_ifs <;> first | omega | exact f0 ℓ (by omega)
  · intro c' t ht _ ⟨_, fr, fm, f0⟩
    exact ⟨by omega, f0, fr, fm⟩

/-- **The counts per label** of the darts `x < m` (labels `lb x ≤ k` at `bL + x`) at `bC + ℓ`. -/
theorem cpCountLoop_exec {m bL bC : ℕ} {lb : ℕ → ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e860 : c₁.nreg 860 = m) (e145 : c₁.nreg 145 = bL) (e866 : c₁.nreg 866 = bC)
    (e10 : c₁.nreg 10 = 1) (e870 : c₁.nreg 870 = 0) (hL : ∀ x < m, c₁.nmem (bL + x) = lb x)
    (hlb : ∀ x < m, lb x ≤ k) (hC : ∀ ℓ < k + 1, c₁.nmem (bC + ℓ) = 0)
    (dL : bL + m ≤ bC ∨ bC + k + 1 ≤ bL) (wC : bC + k + 1 ≤ W) (wL : bL + m ≤ W)
    (wm : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 870 860 cpCount) c₁ c' t ∧ t ≤ 9 * m + 2 ∧
      (∀ ℓ < k + 1, c'.nmem (bC + ℓ) = cntL lb m ℓ) ∧ CpFr c₁ c' ∧
      (∀ a, (a < bC ∨ bC + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    CpFr c₁ c' ∧ (∀ a, (a < bC ∨ bC + k + 1 ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ ℓ < k + 1, c'.nmem (bC + ℓ) = cntL lb i ℓ)
  refine spec_use (forLoop_exec (P := P) (a := 870) (bR := 860) (body := cpCount) J (K := 7)
    (n := m) _ hw e870 e860 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, fm, f0⟩ => ?_)) ?_
  · refine ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, fun ℓ hℓ => ?_⟩
    rw [hC ℓ hℓ]; simp [cntL]
  · have g : ∀ r, r < 870 → c₂.nreg r = c₁.nreg r := fun r hr => fr.nreg r (Or.inl hr)
    have g866 := (g _ (by omega)).trans e866
    have g145 := (g _ (by omega)).trans e145
    have g10 := (g _ (by omega)).trans e10
    have hLi : c₂.nmem (bL + i) = lb i := by rw [fm _ (by omega)]; exact hL i hi
    have hli := hlb i hi
    have hci : c₂.nmem (bC + lb i) = cntL lb i (lb i) := f0 _ (by omega)
    have := cntL_le lb i (lb i)
    unfold cpCount
    exec_block
    all_goals try ((try config_simp); (try simp only [g866, g145, g10, ha, hLi, hci]) <;> omega)
    refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
      fr.trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun a ha' => ?_, fun ℓ hℓ => ?_⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; simp only [upd_apply, g866, g145, ha, hLi]
      split_ifs <;> first | omega | exact fm a ha'
    · config_simp; simp only [upd_apply, g866, g145, ha, hLi, g10, hci, cntL_succ]
      split_ifs with h1 h2 h2 <;> first | omega | (rw [f0 ℓ hℓ]; omega) |
        (have e : ℓ = lb i := by omega
         subst e; omega)
  · intro c' t ht _ ⟨_, fr, fm, f0⟩
    exact ⟨by omega, f0, fr, fm⟩

/-- The test of a large component for the dart `y`. -/
def bigL (m : ℕ) (lb : ℕ → ℕ) (y : ℕ) : Prop := 3 * m < 4 * cntL lb m (lb y)

instance (m : ℕ) (lb : ℕ → ℕ) (y : ℕ) : Decidable (bigL m lb y) := by
  unfold bigL; infer_instance

/-- **The flags of the large component** at `bF + x`, and a dart of it in `r857` (`r856 = 1`) if
there is one. -/
theorem cpFlagLoop_exec {m bL bC bF : ℕ} {lb : ℕ → ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e860 : c₁.nreg 860 = m) (e145 : c₁.nreg 145 = bL) (e866 : c₁.nreg 866 = bC)
    (e865 : c₁.nreg 865 = bF) (e868 : c₁.nreg 868 = m + m + m) (e10 : c₁.nreg 10 = 1)
    (e870 : c₁.nreg 870 = 0) (e856 : c₁.nreg 856 = 0) (hL : ∀ x < m, c₁.nmem (bL + x) = lb x)
    (hlb : ∀ x < m, lb x ≤ k) (hC : ∀ ℓ < k + 1, c₁.nmem (bC + ℓ) = cntL lb m ℓ)
    (dL : bF + m ≤ bL ∨ bL + m ≤ bF) (dC : bF + m ≤ bC ∨ bC + k + 1 ≤ bF)
    (wC : bC + k + 1 ≤ W) (wL : bL + m ≤ W) (wF : bF + m ≤ W) (wm : 4 * m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 870 860 cpFlag) c₁ c' t ∧ t ≤ 15 * m + 2 ∧
      (∀ y < m, c'.nmem (bF + y) = if bigL m lb y then 1 else 0) ∧
      ((c'.nreg 856 = 0 ∧ ∀ y < m, ¬ bigL m lb y) ∨
        (c'.nreg 856 = 1 ∧ c'.nreg 857 < m ∧ bigL m lb (c'.nreg 857))) ∧
      (∀ r, r < 856 ∨ (857 < r ∧ r < 870) ∨ 877 < r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, (a < bF ∨ bF + m ≤ a) → c'.nmem a = c₁.nmem a) := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 856 ∨ (857 < r ∧ r < 870) ∨ 877 < r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, (a < bF ∨ bF + m ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ y < i, c'.nmem (bF + y) = if bigL m lb y then 1 else 0) ∧
      ((c'.nreg 856 = 0 ∧ ∀ y < i, ¬ bigL m lb y) ∨
        (c'.nreg 856 = 1 ∧ c'.nreg 857 < m ∧ bigL m lb (c'.nreg 857)))
  refine spec_use (forLoop_exec (P := P) (a := 870) (bR := 860) (body := cpFlag) J (K := 13)
    (n := m) _ hw e870 e860 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, frr, frm, fo, fm, fv, f6⟩ => ?_)) ?_
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega),
      Or.inl ⟨e856, fun _ h => absurd h (by omega)⟩⟩
  · have g : ∀ r, r < 856 → c₂.nreg r = c₁.nreg r := fun r hr => fr r (Or.inl hr)
    have g866 := (fr _ (by omega)).trans e866
    have g865 := (fr _ (by omega)).trans e865
    have g868 := (fr _ (by omega)).trans e868
    have g145 := (g _ (by omega)).trans e145
    have g10 := (g _ (by omega)).trans e10
    have hLi : c₂.nmem (bL + i) = lb i := by rw [fm _ (by omega)]; exact hL i hi
    have hli := hlb i hi
    have hci : c₂.nmem (bC + lb i) = cntL lb m (lb i) := by
      rw [fm _ (by omega)]; exact hC _ (by omega)
    have := cntL_le lb m (lb i)
    unfold cpFlag
    refine spec_seq ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [g866, g145, g10, ha, hb, hLi, hci]) <;> omega)
    refine spec_seq ?_
    by_cases hbig : bigL m lb i
    · have hb' : 3 * m < 4 * cntL lb m (lb i) := hbig
      refine spec_ifLtN_true (by config_simp; simp only [g868, g866, g145, ha, hLi, hci]; omega) ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [g865, g10, ha, hb]) <;> omega)
      refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
        fun r hr => ?_, frr, frm, fo, fun a ha' => ?_, fun y hy => ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
      · config_simp; (try simp only [upd_apply]); split_ifs <;> first | omega | exact fr r hr
      · config_simp; simp only [upd_apply, g865, ha]
        split_ifs <;> first | omega | exact fm a ha'
      · config_simp; simp only [upd_apply, g865, ha]
        rcases Nat.lt_or_ge y i with hlt | hge
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact fv y hlt
        · have : y = i := by omega
          subst this; simp [hbig]
      · config_simp
      · config_simp; simp only [ha]; omega
      · config_simp; simp only [ha]; exact hbig
    · have hb' : ¬ 3 * m < 4 * cntL lb m (lb i) := hbig
      refine spec_ifLtN_false (by config_simp; simp only [g868, g866, g145, ha, hLi, hci]; omega) ?_
      refine spec_instr (Exec.constN ‹_› 875 0 (by omega)) fun _ => ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [g865, g10, ha, hb]) <;> omega)
      refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
        fun r hr => ?_, frr, frm, fo, fun a ha' => ?_, fun y hy => ?_, ?_⟩
      · config_simp; (try simp only [upd_apply]); split_ifs <;> first | omega | exact fr r hr
      · config_simp; simp only [upd_apply, g865, ha]
        split_ifs <;> first | omega | exact fm a ha'
      · config_simp; simp only [upd_apply, g865, ha]
        rcases Nat.lt_or_ge y i with hlt | hge
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact fv y hlt
        · have : y = i := by omega
          subst this; simp [hbig]
      · config_simp
        rcases f6 with ⟨h0, hn⟩ | h1
        · refine Or.inl ⟨h0, fun y hy => ?_⟩
          rcases Nat.lt_or_ge y i with h | h
          · exact hn y h
          · have : y = i := by omega
            subst this; exact hbig
        · exact Or.inr h1
  · intro c' t ht _ ⟨_, fr, frr, frm, fo, fm, fv, f6⟩
    exact ⟨by omega, fv, f6, fr, frr, frm, fo, fm⟩

set_option maxHeartbeats 1000000 in
theorem cpSetup_exec {m B : ℕ} (c : Config) (hc : WordsBounded W c) (r10 : c.nreg 10 = 1)
    (r860 : c.nreg 860 = m) (r861 : c.nreg 861 = k) (r864 : c.nreg 864 = B)
    (wB : B + 7 * k + 1 ≤ W) (wm : 4 * m + 3 ≤ W) :
    ∃ c' t, Exec P W cpSetup c c' t ∧ t ≤ 17 ∧ c'.nreg 140 = 0 ∧ c'.nreg 141 = 1 ∧
      c'.nreg 142 = 3 ∧ c'.nreg 143 = k ∧ c'.nreg 147 = B ∧ c'.nreg 144 = B + 3 * k ∧
      c'.nreg 145 = B + 4 * k ∧ c'.nreg 146 = B + 5 * k ∧ c'.nreg 866 = B + 6 * k ∧
      c'.nreg 867 = k + 1 ∧ c'.nreg 868 = m + m + m ∧ c'.nreg 856 = 0 ∧ c'.nreg 870 = 0 ∧
      (∀ r, r < 140 ∨ (147 < r ∧ r < 856) ∨ (857 < r ∧ r < 866) ∨ 871 < r →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.output = c.output := by
  unfold cpSetup
  exec_block
  all_goals try ((try config_simp); (try simp only [r860, r861, r864, r10]) <;> omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  all_goals config_simp
  all_goals try ((try simp only [r860, r861, r864, r10]) <;> omega)
  repeat rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

set_option maxHeartbeats 1000000 in
/-- **The components of a piece on the machine.** From the reversal `α` and the rotation `σ` of
the half-edges `h < k` (at `bα + h`, `bσ + h`; `HEnc`), `compProg` ends within
`101 k + 24 m + 38` steps with labels `lb h ∈ [1, k]` at `B + 4 k + h`, equal exactly for
half-edges joined by steps along `σ` and `α`; at `B + 6 k + ℓ` the number of darts `x < m` with
label `ℓ`; at `bF + x` the flag `1` of the darts `x < m` whose label has more than three
quarters of the `m` darts (`bigL`); `r856 = 1` and `r857` such a dart if there is one,
`r856 = 0` otherwise. -/
theorem compProg_exec {m bα bσ B bF : ℕ} (he : HEnc k α σ) (c : Config) (hc : WordsBounded W c)
    (hI : CompIn m k bα bσ B bF c) (hL : CompLay m k bα bσ B bF W)
    (hα : ∀ h < k, c.nmem (bα + h) = α h) (hσ : ∀ h < k, c.nmem (bσ + h) = σ h) :
    ∃ c' t, Exec P W compProg c c' t ∧ t ≤ 101 * k + 24 * m + 38 ∧ ∃ lb : ℕ → ℕ,
      (∀ h < k, c'.nmem (B + 4 * k + h) = lb h) ∧ (∀ h < k, 1 ≤ lb h ∧ lb h ≤ k) ∧
      (∀ f < k, ∀ g < k, lb f = lb g ↔ Relation.ReflTransGen (HeStep k α σ) f g) ∧
      (∀ ℓ < k + 1, c'.nmem (B + 6 * k + ℓ) = cntL lb m ℓ) ∧
      (∀ y < m, c'.nmem (bF + y) = if bigL m lb y then 1 else 0) ∧
      ((c'.nreg 856 = 0 ∧ ∀ y < m, ¬ bigL m lb y) ∨
        (c'.nreg 856 = 1 ∧ c'.nreg 857 < m ∧ bigL m lb (c'.nreg 857))) ∧
      (∀ r, r < 140 ∨ (160 ≤ r ∧ r < 856) ∨ (857 < r ∧ r < 866) ∨ 880 ≤ r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 7 * k + 1 ≤ a) → (a < bF ∨ bF + m ≤ a) → c'.nmem a = c.nmem a) := by
  obtain ⟨r10, r860, r861, r862, r863, r864, r865⟩ := hI
  obtain ⟨hmk, wB, wα, wσ, wF, wm, dα, dσ, dF⟩ := hL
  suffices H : ∃ c' t, Exec P W compProg c c' t ∧ t ≤ 101 * k + 24 * m + 38 ∧ ∃ lb : ℕ → ℕ,
      (∀ h < k, c'.nmem (B + 4 * k + h) = lb h) ∧ (∀ h < k, 1 ≤ lb h ∧ lb h ≤ k) ∧
      (∀ f < k, ∀ g < k, lb f = lb g ↔ Relation.ReflTransGen (HeStep k α σ) f g) ∧
      (∀ ℓ < k + 1, c'.nmem (B + 6 * k + ℓ) = cntL lb m ℓ) ∧
      (∀ y < m, c'.nmem (bF + y) = if bigL m lb y then 1 else 0) ∧
      ((c'.nreg 856 = 0 ∧ ∀ y < m, ¬ bigL m lb y) ∨
        (c'.nreg 856 = 1 ∧ c'.nreg 857 < m ∧ bigL m lb (c'.nreg 857))) ∧
      (∀ r, r < 140 ∨ (160 ≤ r ∧ r < 856) ∨ (857 < r ∧ r < 866) ∨ 880 ≤ r →
        c'.nreg r = c.nreg r) ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 7 * k + 1 ≤ a) → (a < bF ∨ bF + m ≤ a) → c'.nmem a = c.nmem a) by
    obtain ⟨c', t, hex, ht, lb, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := H
    have hrr := Exec.natS_frame hex natS_compProg
    exact ⟨c', t, hex, ht, lb, h1, h2, h3, h4, h5, h6, h7, hrr.1, hrr.2, h8, h9⟩
  unfold compProg
  refine spec_seq ?_
  refine spec_use (cpSetup_exec (P := P) c hc r10 r860 r861 r864 wB wm) ?_
  intro c₁ t₁ ht₁ hw₁ ⟨s140, s141, s142, s143, s147, s144, s145, s146, s866, s867, s868, s856,
    s870, sfr, sm, so⟩
  have s10 : c₁.nreg 10 = 1 := (sfr 10 (by omega)).trans r10
  have s860 : c₁.nreg 860 = m := (sfr 860 (by omega)).trans r860
  have s861 : c₁.nreg 861 = k := (sfr 861 (by omega)).trans r861
  have s862 : c₁.nreg 862 = bα := (sfr 862 (by omega)).trans r862
  have s863 : c₁.nreg 863 = bσ := (sfr 863 (by omega)).trans r863
  have s865 : c₁.nreg 865 = bF := (sfr 865 (by omega)).trans r865
  -- the adjacency array
  refine spec_seq ?_
  refine spec_use (cpAdjLoop_exec (P := P) (bα := bα) (bσ := bσ) (B := B) he c₁ hw₁ s861 s862 s863
    s147 s144 s145 s140 s10 s870 (fun h hh => by rw [sm]; exact hα h hh)
    (fun h hh => by rw [sm]; exact hσ h hh) wB wα wσ dα dσ) ?_
  intro c₂ t₂ ht₂ hw₂ ⟨hA, hAv, hL0, fr₂, fm₂⟩
  have g₂ : ∀ r, r < 870 ∨ 877 < r → c₂.nreg r = c₁.nreg r := fr₂.nreg
  -- the labels
  refine spec_seq ?_
  refine spec_use (clab_exec (P := P) (W := W) (k := k) (A := fun x => c₂.nmem (B + x))
    (Av := fun _ => 1) (bA := B + 3 * k) (bL := B + 4 * k) (bS := B + 5 * k) (bR := B)
    (hA.revOk he) ⟨by omega, by omega, by omega⟩ (by omega) c₂ hw₂
    ⟨(g₂ _ (by omega)).trans s140, (g₂ _ (by omega)).trans s141, (g₂ _ (by omega)).trans s142,
      (g₂ _ (by omega)).trans s143, (g₂ _ (by omega)).trans s144, (g₂ _ (by omega)).trans s145,
      (g₂ _ (by omega)).trans s146, (g₂ _ (by omega)).trans s147⟩
    (fun x _ => rfl) hAv hL0) ?_
  intro c₃ t₃ ht₃ hw₃ ⟨lb, hlbm, h151, hlble, hlb0, hcomp, g₃, fm₃, fo₃⟩
  have hlbk : ∀ h < k, 1 ≤ lb h ∧ lb h ≤ k := fun h hh => by
    have := (hlb0 h hh).not.2 (by omega)
    have := hlble h hh
    omega
  have G : ∀ r, r < 140 ∨ (147 < r ∧ r < 150) ∨ (160 ≤ r ∧ r < 856) ∨ (857 < r ∧ r < 866) ∨
      877 < r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [g₃ r (by omega), g₂ r (by omega), sfr r (by omega)]
  have G' : ∀ r, (140 ≤ r ∧ r ≤ 147) ∨ (856 ≤ r ∧ r < 870) → c₃.nreg r = c₁.nreg r :=
    fun r hr => by rw [g₃ r (by omega), g₂ r (by omega)]
  -- clearing the counts
  refine spec_seq ?_
  refine spec_instr (Exec.constN ‹_› 870 0 (by omega)) fun hw₃' => ?_
  refine spec_seq ?_
  refine spec_use (cpZeroLoop_exec (P := P) (bC := B + 6 * k) _ hw₃'
    (by config_simp; rw [G' 866 (by omega), s866]) (by config_simp; rw [G' 867 (by omega), s867])
    (by config_simp; rw [G' 140 (by omega), s140]) (by config_simp; rw [G 10 (by omega), r10])
    (by config_simp) (by omega)) ?_
  intro c₄ t₄ ht₄ hw₄ ⟨hC0, fr₄, fm₄⟩
  -- the counts
  refine spec_seq ?_
  refine spec_instr (Exec.constN ‹_› 870 0 (by omega)) fun hw₄' => ?_
  refine spec_seq ?_
  have q : ∀ r, r < 870 → c₄.nreg r = c₃.nreg r := fun r hr => by
    rw [fr₄.nreg r (Or.inl hr)]; config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  refine spec_use (cpCountLoop_exec (P := P) (k := k) (m := m) (bL := B + 4 * k)
    (bC := B + 6 * k) (lb := lb) _ hw₄'
    (by config_simp; rw [q 860 (by omega), G 860 (by omega), r860])
    (by config_simp; rw [q 145 (by omega), G' 145 (by omega), s145])
    (by config_simp; rw [q 866 (by omega), G' 866 (by omega), s866])
    (by config_simp; rw [q 10 (by omega), G 10 (by omega), r10]) (by config_simp)
    (fun x hx => by config_simp; rw [fm₄ _ (by omega)]; config_simp; exact hlbm x (by omega))
    (fun x hx => (hlbk x (by omega)).2) (fun ℓ hℓ => by config_simp; exact hC0 ℓ hℓ)
    (by omega) (by omega) (by omega) (by omega)) ?_
  intro c₅ t₅ ht₅ hw₅ ⟨hC, fr₅, fm₅⟩
  -- the flags
  refine spec_seq ?_
  refine spec_instr (Exec.constN ‹_› 870 0 (by omega)) fun hw₅' => ?_
  have q' : ∀ r, r < 870 → c₅.nreg r = c₃.nreg r := fun r hr => by
    rw [fr₅.nreg r (Or.inl hr)]; config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact q r hr
  refine spec_use (cpFlagLoop_exec (P := P) (k := k) (m := m) (bL := B + 4 * k)
    (bC := B + 6 * k) (bF := bF) (lb := lb) _ hw₅'
    (by config_simp; rw [q' 860 (by omega), G 860 (by omega), r860])
    (by config_simp; rw [q' 145 (by omega), G' 145 (by omega), s145])
    (by config_simp; rw [q' 866 (by omega), G' 866 (by omega), s866])
    (by config_simp; rw [q' 865 (by omega), G 865 (by omega), r865])
    (by config_simp; rw [q' 868 (by omega), G' 868 (by omega), s868])
    (by config_simp; rw [q' 10 (by omega), G 10 (by omega), r10]) (by config_simp)
    (by config_simp; rw [q' 856 (by omega), G' 856 (by omega), s856])
    (fun x hx => by
      config_simp; rw [fm₅ _ (by omega)]; config_simp; rw [fm₄ _ (by omega)]; config_simp
      exact hlbm x (by omega))
    (fun x hx => (hlbk x (by omega)).2) (fun ℓ hℓ => by config_simp; exact hC ℓ hℓ)
    (by omega) (by omega) (by omega) (by omega) wF (by omega)) ?_
  intro c₆ t₆ ht₆ hw₆ ⟨hF, h856, fr₆, _, _, fo₆, fm₆⟩
  have hm6 : ∀ a, (a < B ∨ B + 7 * k + 1 ≤ a) → (a < bF ∨ bF + m ≤ a) → c₆.nmem a = c.nmem a :=
    fun a h₁ h₂ => by
      rw [fm₆ a h₂]; config_simp; rw [fm₅ a (by omega)]; config_simp; rw [fm₄ a (by omega)]
      config_simp; rw [fm₃ a (by omega), fm₂ a (by omega), sm]
  refine ⟨by omega, lb, fun h hh => ?_, hlbk, fun f hf g hg => ?_, fun ℓ hℓ => ?_, hF, h856,
    fun r hr => ?_, ?_, hm6⟩
  · rw [fm₆ _ (by omega)]; config_simp; rw [fm₅ _ (by omega)]; config_simp
    rw [fm₄ _ (by omega)]; config_simp; exact hlbm h hh
  · rw [hcomp f hf g hg (by omega) (by omega)]; exact hA.rtg_iff he f g
  · rw [fm₆ _ (by omega)]; config_simp; exact hC ℓ hℓ
  · rw [fr₆ r (by omega)]; config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fr₅.nreg r (by omega)]
    config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fr₄.nreg r (by omega)]
    config_simp
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), G r (by omega)]
  · rw [fo₆]; config_simp; rw [fr₅.out]; config_simp; rw [fr₄.out]; config_simp
    rw [fo₃, fr₂.out, so]

/-! ### The labels are the components of the piece -/

section Bridge

open Orbit CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The plain encoding of a piece carrying its own rotation**: the darts of `rcl N Pc` numbered
`0, …, k - 1` by `δ`, those of `Pc` first (`0, …, m - 1`), with the numbers `α h` of the
reverses and `σ h` of the first returns of the rotation of `N` to `rcl N Pc`. -/
structure PEnc (N : CombMap D V F) (Pc : Finset D) (m k : ℕ) (δ : ℕ → D) (α σ : ℕ → ℕ) :
    Prop where
  enum : IsEnum k δ (rcl N Pc)
  enumP : IsEnum m δ Pc
  mle : m ≤ k
  α_lt : ∀ h < k, α h < k
  α_eq : ∀ h < k, δ (α h) = N.rev (δ h)
  σ_lt : ∀ h < k, σ h < k
  σ_eq : ∀ h < k, δ (σ h) = ret (rotPerm N) (rcl N Pc) (δ h)

variable {Pc : Finset D} {m : ℕ} {δ : ℕ → D}

theorem PEnc.mem_iff (he : PEnc N Pc m k δ α σ) {x : ℕ} (hx : x < k) : δ x ∈ Pc ↔ x < m := by
  refine ⟨fun h => ?_, fun h => he.enumP.mem x h⟩
  obtain ⟨y, hy, e⟩ := he.enumP.surj _ h
  have := he.enum.inj y (by have := he.mle; omega) x hx e
  omega

theorem PEnc.hEnc (he : PEnc N Pc m k δ α σ) : HEnc k α σ where
  α_lt := he.α_lt
  αα h hh := he.enum.inj _ (he.α_lt _ (he.α_lt h hh)) h hh (by
    rw [he.α_eq _ (he.α_lt h hh), he.α_eq h hh, N.rev_rev])
  σ_lt := he.σ_lt
  σ_inj h hh h' hh' e := by
    have := congrArg δ e
    rw [he.σ_eq h hh, he.σ_eq h' hh'] at this
    exact he.enum.inj h hh h' hh' ((ret (rotPerm N) (rcl N Pc)).injective this)
  σ_surj g hg := by
    set y := (ret (rotPerm N) (rcl N Pc)).symm (δ g)
    have hy : y ∈ rcl N Pc := by
      rw [← ret_mem_iff (π := rotPerm N), Equiv.apply_symm_apply]; exact he.enum.mem g hg
    obtain ⟨h, hh, e⟩ := he.enum.surj y hy
    refine ⟨h, hh, he.enum.inj _ (he.σ_lt h hh) g hg ?_⟩
    rw [he.σ_eq h hh, e, Equiv.apply_symm_apply]

/-- The rotation of the piece keeps the tail. -/
theorem PEnc.tail_σ (hrot : N.RotTrans) (he : PEnc N Pc m k δ α σ) {h : ℕ} (hh : h < k) :
    N.tail (δ (σ h)) = N.tail (δ h) := by
  have h1 := he.enum.mem h hh
  rw [he.σ_eq h hh]
  exact ((sameCycle_ret_iff hrot h1 (ret_mem h1)).1
    (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))).symm

/-- The dart of `Pc` of the half-edge `h`: itself or its reverse. -/
def udart (m : ℕ) (α : ℕ → ℕ) (h : ℕ) : ℕ := if h < m then h else α h

theorem udart_of_lt {m h : ℕ} (hh : h < m) : udart m α h = h := by simp [udart, hh]

theorem PEnc.udart_lt (he : PEnc N Pc m k δ α σ) {h : ℕ} (hh : h < k) : udart m α h < m := by
  unfold udart
  split_ifs with h1
  · exact h1
  · have hr := he.enum.mem h hh
    rcases mem_union.1 hr with h2 | h2
    · exact absurd ((he.mem_iff hh).1 h2) h1
    · obtain ⟨q, hq, e⟩ := mem_image.1 h2
      refine (he.mem_iff (he.α_lt h hh)).1 ?_
      rw [he.α_eq h hh, ← e, N.rev_rev]; exact hq

theorem PEnc.ends (he : PEnc N Pc m k δ α σ) {h : ℕ} (hh : h < k) :
    (N.tail (δ (udart m α h)) = N.tail (δ h) ∨ N.head (δ (udart m α h)) = N.tail (δ h)) ∧
    (N.tail (δ (udart m α h)) = N.head (δ h) ∨ N.head (δ (udart m α h)) = N.head (δ h)) := by
  unfold udart
  split_ifs with h1
  · exact ⟨Or.inl rfl, Or.inr rfl⟩
  · rw [he.α_eq h hh, N.tail_rev, N.head_rev]
    exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- Half-edges with the same tail are joined along the rotation. -/
theorem PEnc.rtg_of_tail (hrot : N.RotTrans) (he : PEnc N Pc m k δ α σ) {f g : ℕ} (hf : f < k)
    (hg : g < k) (e : N.tail (δ f) = N.tail (δ g)) : Relation.ReflTransGen (HeStep k α σ) f g := by
  obtain ⟨n, hn⟩ := sameCycle_iff.1
    ((sameCycle_ret_iff hrot (he.enum.mem f hf) (he.enum.mem g hg)).2 e)
  have key : ∀ j, σ^[j] f < k ∧ δ (σ^[j] f) = (ret (rotPerm N) (rcl N Pc))^[j] (δ f) ∧
      Relation.ReflTransGen (HeStep k α σ) f (σ^[j] f) := by
    intro j
    induction j with
    | zero => exact ⟨hf, rfl, .refl⟩
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', he.σ_eq _ h1, h2]
      exact ⟨he.σ_lt _ h1, rfl, h3.tail ⟨h1, he.σ_lt _ h1, Or.inl rfl⟩⟩
  obtain ⟨h1, h2, h3⟩ := key n
  rw [hn] at h2
  rwa [← he.enum.inj _ h1 g hg h2]

/-- **Half-edges joined along the rotation and the reversal have their darts in one component of
the piece, and conversely.** -/
theorem hstep_pcomp (hrot : N.RotTrans) (he : PEnc N Pc m k δ α σ) {x y : ℕ} (hx : x < m)
    (hy : y < m) : Relation.ReflTransGen (HeStep k α σ) x y ↔ δ y ∈ pcomp N Pc (δ x) := by
  have hmk := he.mle
  constructor
  · intro hr
    have key : ∀ z, Relation.ReflTransGen (HeStep k α σ) x z →
        δ (udart m α z) ∈ pcomp N Pc (δ x) := by
      intro z hz
      induction hz with
      | refl =>
        rw [udart_of_lt hx]; exact self_mem_pcomp (he.enumP.mem x hx)
      | @tail z w _ hzw ih =>
        obtain ⟨hz, hw, hs⟩ := hzw
        refine mem_pcomp_of_share ih (he.enumP.mem _ (he.udart_lt hw)) ?_
        have ez := he.ends hz
        have ew := he.ends hw
        rcases hs with rfl | e | rfl
        · exact share_of ez.1 (by rw [he.tail_σ hrot hz] at ew; exact ew.1)
        · have : N.tail (δ z) = N.tail (δ w) := by rw [← e, he.tail_σ hrot hw]
          rw [this] at ez; exact share_of ez.1 ew.1
        · rw [he.α_eq _ hz, N.tail_rev] at ew; exact share_of ez.2 ew.1
    have := key y hr
    rwa [udart_of_lt hy] at this
  · intro hm
    obtain ⟨-, hr⟩ := mem_pcomp.1 hm
    have step : ∀ a < m, ∀ b < m, Share N (δ a) (δ b) →
        Relation.ReflTransGen (HeStep k α σ) a b := by
      intro a ha b hb hs
      have ha' : a < k := by omega
      have hb' : b < k := by omega
      have hαa := he.α_lt a ha'
      have hαb := he.α_lt b hb'
      have ra : Relation.ReflTransGen (HeStep k α σ) a (α a) :=
        .single ⟨ha', hαa, Or.inr (Or.inr rfl)⟩
      have rb : Relation.ReflTransGen (HeStep k α σ) (α b) b :=
        .single ⟨hαb, hb', Or.inr (Or.inr ((he.hEnc).αα b hb').symm)⟩
      have ta : N.tail (δ (α a)) = N.head (δ a) := by rw [he.α_eq _ ha', N.tail_rev]
      have tb : N.tail (δ (α b)) = N.head (δ b) := by rw [he.α_eq _ hb', N.tail_rev]
      unfold Share at hs
      rcases hs with e | e | e | e
      · exact he.rtg_of_tail hrot ha' hb' e
      · exact (he.rtg_of_tail hrot ha' hαb (by rw [tb, e])).trans rb
      · exact ra.trans (he.rtg_of_tail hrot hαa hb' (by rw [ta, e]))
      · exact ra.trans ((he.rtg_of_tail hrot hαa hαb (by rw [ta, tb, e])).trans rb)
    have key : ∀ b, Relation.ReflTransGen (fun a b => a ∈ Pc ∧ b ∈ Pc ∧ Share N a b) (δ x) b →
        ∀ z < m, δ z = b → Relation.ReflTransGen (HeStep k α σ) x z := by
      intro b hb
      induction hb with
      | refl =>
        intro z hz e
        rw [he.enumP.inj z hz x hx e]
      | @tail b c _ hbc ih =>
        intro z hz e
        obtain ⟨hbP, -, hs⟩ := hbc
        obtain ⟨w, hw, rfl⟩ := he.enumP.surj b hbP
        subst e
        exact (ih w hw rfl).trans (step w hw z hz hs)
    exact key _ hr y hy rfl

/-- The size of a component, from the labels. -/
theorem card_pcomp_cntL (hrot : N.RotTrans) (he : PEnc N Pc m k δ α σ) {lb : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, lb f = lb g ↔ Relation.ReflTransGen (HeStep k α σ) f g) {x : ℕ}
    (hx : x < m) : (pcomp N Pc (δ x)).card = cntL lb m (lb x) := by
  have hmk := he.mle
  exact image_filter_enum he.enumP (pcomp_subset Pc _) fun y hy => by
    rw [eq_comm, hlb x (by omega) y (by omega), hstep_pcomp hrot he hx hy]

/-- **The components of a piece on the machine**: on the plain encoding of the piece (the
reversal at `bα`, the rotation of the piece at `bσ`), `compProg` leaves at `B + 4 k + x` a label
`lb x ∈ [1, k]` per dart `x < m`, equal exactly for darts of one component `pcomp`; at
`B + 6 k + lb x` the size of the component of `δ x`; at `bF + x` a flag, nonzero exactly when
the component of `δ x` has more than three quarters of the darts (the test of `splitM`); and
`r856 = 1` with a dart `r857` of such a component if there is one, `r856 = 0` and every component
of at most three quarters of the darts otherwise. Within `101 k + 24 m + 38` steps. -/
theorem compProg_spec (hrot : N.RotTrans) (he : PEnc N Pc m k δ α σ) {bα bσ B bF : ℕ}
    (c : Config) (hc : WordsBounded W c) (hI : CompIn m k bα bσ B bF c)
    (hL : CompLay m k bα bσ B bF W) (hα : ∀ h < k, c.nmem (bα + h) = α h)
    (hσ : ∀ h < k, c.nmem (bσ + h) = σ h) :
    ∃ c' t, Exec P W compProg c c' t ∧ t ≤ 101 * k + 24 * m + 38 ∧
      (∀ x < m, 1 ≤ c'.nmem (B + 4 * k + x) ∧ c'.nmem (B + 4 * k + x) ≤ k) ∧
      (∀ x < m, ∀ y < m,
        c'.nmem (B + 4 * k + x) = c'.nmem (B + 4 * k + y) ↔ δ y ∈ pcomp N Pc (δ x)) ∧
      (∀ x < m, c'.nmem (B + 6 * k + c'.nmem (B + 4 * k + x)) = (pcomp N Pc (δ x)).card) ∧
      (∀ x < m, (c'.nmem (bF + x) ≠ 0 ↔ 3 * Pc.card / 4 < (pcomp N Pc (δ x)).card)) ∧
      ((c'.nreg 856 = 0 ∧ ∀ d ∈ Pc, (pcomp N Pc d).card ≤ 3 * Pc.card / 4) ∨
        (c'.nreg 856 = 1 ∧ c'.nreg 857 < m ∧
          3 * Pc.card / 4 < (pcomp N Pc (δ (c'.nreg 857))).card)) ∧
      (∀ r, r < 140 ∨ (160 ≤ r ∧ r < 856) ∨ (857 < r ∧ r < 866) ∨ 880 ≤ r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < B ∨ B + 7 * k + 1 ≤ a) → (a < bF ∨ bF + m ≤ a) → c'.nmem a = c.nmem a) := by
  have hmk := he.mle
  have hcard := he.enumP.card
  obtain ⟨c', t, hex, ht, lb, hl, hlk, hlb, hC, hF, h856, hr, hrr, hrm, ho, hm⟩ :=
    compProg_exec (P := P) he.hEnc c hc hI hL hα hσ
  have hcp : ∀ x < m, (pcomp N Pc (δ x)).card = cntL lb m (lb x) := fun x hx =>
    card_pcomp_cntL hrot he hlb hx
  have hbig : ∀ x < m, bigL m lb x ↔ 3 * Pc.card / 4 < (pcomp N Pc (δ x)).card := fun x hx => by
    unfold bigL; rw [hcp x hx]; omega
  refine ⟨c', t, hex, ht, fun x hx => by rw [hl x (by omega)]; exact hlk x (by omega),
    fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_, ?_, hr, hrr, hrm, ho, hm⟩
  · rw [hl x (by omega), hl y (by omega), hlb x (by omega) y (by omega), hstep_pcomp hrot he hx hy]
  · rw [hl x (by omega), hC _ (by have := hlk x (by omega); omega), hcp x hx]
  · rw [hF x hx, ← hbig x hx]; split_ifs <;> simp_all
  · rcases h856 with ⟨h0, hn⟩ | ⟨h1, hlt, hb⟩
    · refine Or.inl ⟨h0, fun d hd => ?_⟩
      obtain ⟨x, hx, rfl⟩ := he.enumP.surj d hd
      have := (hbig x hx).not.1 (hn x hx)
      omega
    · exact Or.inr ⟨h1, hlt, (hbig _ hlt).1 hb⟩

/-- **The flags of the large component**: when `compProg` finds a large component (`r856 = 1`),
the flags are the membership in the component of the dart `r857` found, as `joinProg_splitM`
takes them (`Kb = bF`, `x₀ = δ r857`). -/
theorem flags_big {x₀ : D} (hb : 3 * Pc.card / 4 < (pcomp N Pc x₀).card)
    {flag : ℕ → ℕ} (hF : ∀ x < m, (flag x ≠ 0 ↔ 3 * Pc.card / 4 < (pcomp N Pc (δ x)).card))
    (hP : ∀ x < m, δ x ∈ Pc) : ∀ x < m, (flag x ≠ 0 ↔ δ x ∈ pcomp N Pc x₀) := by
  intro x hx
  rw [hF x hx]
  constructor
  · intro h
    rw [← pcomp_eq_of_big h hb]; exact self_mem_pcomp (hP x hx)
  · intro h
    rw [pcomp_eq h]; exact hb

/-- A part `K` of `Pc` closed under sharing an end within `Pc` (a union of components). -/
def ShareClosed (N : CombMap D V F) (Pc K : Finset D) : Prop :=
  K ⊆ Pc ∧ ∀ a ∈ K, ∀ b ∈ Pc, Share N a b → b ∈ K

theorem shareClosed_pcomp (Pc : Finset D) (x : D) : ShareClosed N Pc (pcomp N Pc x) :=
  ⟨pcomp_subset Pc x, fun _ ha _ hb hs => mem_pcomp_of_share ha hb hs⟩

lemma tail_iterate_rotPerm (d : D) (j : ℕ) : N.tail ((rotPerm N)^[j] d) = N.tail d := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', rotPerm_apply, N.tail_rot, ih]

/-- **The rotation of the piece map of a component is the rotation of the piece cut down**: for a
part `K` of `Pc` closed under sharing an end (a component `pcomp N Pc x`), the first return of the
rotation of `N` to `rcl N K` is, on `rcl N K`, its first return to `rcl N Pc`. So the rotation of
`kmap N K` is read off the plain encoding of the piece (`PEnc`), restricted to the half-edges of
`K` (`PEnc.σ_eq_comp`). -/
theorem ret_rcl_closed {K : Finset D} (hK : ShareClosed N Pc K) {d : D} (hd : d ∈ rcl N K) :
    ret (rotPerm N) (rcl N K) d = ret (rotPerm N) (rcl N Pc) d := by
  have hsub : rcl N K ⊆ rcl N Pc := fun e he => by
    rcases mem_rcl.1 he with h | h
    · exact mem_rcl.2 (Or.inl (hK.1 h))
    · exact mem_rcl.2 (Or.inr (hK.1 h))
  have hdP := hsub hd
  set n := retIdx (rotPerm N) (rcl N Pc) d
  have hn := iterate_retIdx_mem (π := rotPerm N) hdP
  have hy : (rotPerm N)^[n] d ∈ rcl N K := by
    set y := (rotPerm N)^[n] d
    have ht : N.tail y = N.tail d := tail_iterate_rotPerm d n
    -- the darts of `Pc` under `d` and `y` share the vertex `tail d`
    have key : ∀ a ∈ K, (N.tail a = N.tail d ∨ N.head a = N.tail d) → ∀ b ∈ Pc,
        (N.tail b = N.tail d ∨ N.head b = N.tail d) → b ∈ K := fun a ha h1 b hb h2 =>
      hK.2 a ha b hb (share_of h1 h2)
    rcases mem_rcl.1 hd with ha | ha
    · rcases mem_rcl.1 hn with hb | hb
      · exact mem_rcl.2 (Or.inl (key d ha (Or.inl rfl) y hb (Or.inl ht)))
      · exact mem_rcl.2 (Or.inr (key d ha (Or.inl rfl) _ hb (Or.inr (by rw [N.head_rev, ht]))))
    · rcases mem_rcl.1 hn with hb | hb
      · exact mem_rcl.2 (Or.inl (key _ ha (Or.inr (by rw [N.head_rev])) y hb (Or.inl ht)))
      · exact mem_rcl.2 (Or.inr (key _ ha (Or.inr (by rw [N.head_rev])) _ hb
          (Or.inr (by rw [N.head_rev, ht]))))
  rw [ret_apply_of_mem hdP]
  exact ret_eq_of hd (retIdx_pos _) hy fun j h0 h1 h => not_mem_of_lt_retIdx hdP h0 h1 (hsub h)

/-- On the half-edges of a component, the rotation of the plain encoding of the piece is the
rotation of the piece map of the component. -/
theorem PEnc.σ_eq_comp (he : PEnc N Pc m k δ α σ) {K : Finset D} (hK : ShareClosed N Pc K)
    {h : ℕ} (hh : h < k) (hK' : δ h ∈ rcl N K) :
    δ (σ h) = ret (rotPerm N) (rcl N K) (δ h) := by
  rw [he.σ_eq h hh, ret_rcl_closed hK hK']

end Bridge

end NegSSSP

end PlanarFlow
