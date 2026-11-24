module

public import PlanarFlow.Klein.ProgTrip
public import Mathlib.Data.List.GetD

/-!
# Klein's algorithm on the machine: the preconditions can be met

`klein_exec_pre`: **for every map, boundary, piece and lengths meeting the hypotheses of the
trip** (`Hyp`, `SameReach`) **and `t` target vertices, none of them a root**, there are a layout
of the nodes, a numbering of the darts, an input (`KInput`, `KBnd`, `KOut`, `KInit`, `KTgt`,
built here as a list of words by regions, `lay`: `kInput`, then the targets, `kInputT`), initial
trees, a word bound and a starting configuration (its real memory holding `WT`, `PH` and the
constants) meeting all the hypotheses of `klein_exec`; `klein_exec_exists`: hence the end-to-end
statement, an execution of `kleinProg` within `36500000 (N lg N + k t lg N)` steps ending with
the answers at the targets in its output.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

/-! ### Lists of words by regions -/

/-- The word `a` of the concatenation of regions, each of a length and a function. -/
def lay : List (ℕ × (ℕ → ℕ)) → ℕ → ℕ
  | [], _ => 0
  | r :: rs, a => if a < r.1 then r.2 a else lay rs (a - r.1)

lemma lay_off : ∀ (pre : List (ℕ × (ℕ → ℕ))) (r : ℕ × (ℕ → ℕ)) (post : List (ℕ × (ℕ → ℕ)))
    {i : ℕ}, i < r.1 → lay (pre ++ r :: post) ((pre.map Prod.fst).sum + i) = r.2 i
  | [], r, post, i, hi => by simp [lay, hi]
  | p :: pre, r, post, i, hi => by
    simp only [List.cons_append, lay, List.map_cons, List.sum_cons]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      show p.1 + (pre.map Prod.fst).sum + i - p.1 = (pre.map Prod.fst).sum + i by omega]
    exact lay_off pre r post hi

lemma lay_get (rs : List (ℕ × (ℕ → ℕ))) (j : ℕ) (hj : j < rs.length) {i : ℕ}
    (hi : i < rs[j].1) : lay rs (((rs.take j).map Prod.fst).sum + i) = rs[j].2 i := by
  have e : rs.take j ++ rs[j] :: rs.drop (j + 1) = rs := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have := lay_off (rs.take j) rs[j] (rs.drop (j + 1)) hi
  rwa [e] at this

/-- The list of the words of the regions. -/
@[irreducible] def layList (rs : List (ℕ × (ℕ → ℕ))) : List ℕ :=
  List.ofFn fun a : Fin (rs.map Prod.fst).sum => lay rs a

lemma layList_getD (rs : List (ℕ × (ℕ → ℕ))) (j : ℕ) (hj : j < rs.length) {i : ℕ}
    (hi : i < rs[j].1) :
    (layList rs).getD (((rs.take j).map Prod.fst).sum + i) 0 = rs[j].2 i := by
  have hlt : ((rs.take j).map Prod.fst).sum + i < (rs.map Prod.fst).sum := by
    have e : rs = rs.take j ++ rs[j] :: rs.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    conv_rhs => rw [e]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  unfold layList
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt]
  exact lay_get rs j hj hi

lemma layList_le (rs : List (ℕ × (ℕ → ℕ))) (a : ℕ) :
    (layList rs).getD a 0 ≤ (layList rs).sum := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (layList rs)[a]? with _ | x
  · simp
  · exact List.le_sum_of_mem (List.mem_of_getElem? h)

lemma lay_append (rs rs' : List (ℕ × (ℕ → ℕ))) {a : ℕ} (ha : a < (rs.map Prod.fst).sum) :
    lay (rs ++ rs') a = lay rs a := by
  induction rs generalizing a with
  | nil => simp at ha
  | cons r rs ih =>
    simp only [List.cons_append, lay]
    split_ifs with h
    · rfl
    · exact ih (by simp only [List.map_cons, List.sum_cons] at ha; omega)

/-- The words of the first regions are kept when regions are appended. -/
lemma layList_append_getD (rs rs' : List (ℕ × (ℕ → ℕ))) {a : ℕ}
    (ha : a < (rs.map Prod.fst).sum) :
    (layList (rs ++ rs')).getD a 0 = (layList rs).getD a 0 := by
  have ha' : a < ((rs ++ rs').map Prod.fst).sum := by
    simp only [List.map_append, List.sum_append]; omega
  unfold layList
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, ha, ha']
  exact lay_append rs rs' ha

/-! ### The input -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- A region of `nD` words indexed by the numbers of the darts. -/
def dReg {nD : ℕ} (σ : D ≃ Fin nD) (f : D → ℕ) : ℕ × (ℕ → ℕ) :=
  (nD, fun j => if h : j < nD then f (σ.symm ⟨j, h⟩) else 0)

lemma dReg_apply {nD : ℕ} (σ : D ≃ Fin nD) (f : D → ℕ) (d : D) : (dReg σ f).2 (σ d) = f d := by
  simp [dReg]

/-- The out-darts of the piece of a vertex. -/
def outL (M : CombMap D V F) (S : Finset D) (x : V) : List D :=
  (S.filter fun d => M.tail d = x).toList

/-- The out-darts of the piece, vertex after vertex. -/
def allOut (M : CombMap D V F) (S : Finset D) : List D :=
  (univ : Finset V).toList.flatMap (outL M S)

/-- The position of the first out-dart of a vertex in `allOut`. -/
def outB (M : CombMap D V F) (S : Finset D) (x : V) : ℕ :=
  (((univ : Finset V).toList.take ((univ : Finset V).toList.idxOf x)).flatMap (outL M S)).length

lemma allOut_split (M : CombMap D V F) (S : Finset D) (x : V) :
    allOut M S = (((univ : Finset V).toList.take ((univ : Finset V).toList.idxOf x)).flatMap
      (outL M S) ++ outL M S x) ++ ((univ : Finset V).toList.drop
        ((univ : Finset V).toList.idxOf x + 1)).flatMap (outL M S) := by
  have hx : (univ : Finset V).toList.idxOf x < (univ : Finset V).toList.length :=
    List.idxOf_lt_length_iff.2 (by simp)
  have e : (univ : Finset V).toList = (univ : Finset V).toList.take
      ((univ : Finset V).toList.idxOf x) ++ x :: (univ : Finset V).toList.drop
        ((univ : Finset V).toList.idxOf x + 1) := by
    conv_lhs => rw [← List.take_append_drop ((univ : Finset V).toList.idxOf x)
      (univ : Finset V).toList]
    rw [List.drop_eq_getElem_cons hx, List.getElem_idxOf hx]
  unfold allOut
  conv_lhs => rw [e]
  simp [List.flatMap_append, List.append_assoc]

lemma allOut_length (M : CombMap D V F) (S : Finset D) : (allOut M S).length = S.card := by
  classical
  unfold allOut outL
  rw [List.length_flatMap, ← List.sum_toFinset _ (nodup_toList _)]
  simp only [length_toList, Finset.toList_toFinset]
  exact (card_eq_sum_card_fiberwise fun d _ => mem_univ (M.tail d)).symm

variable (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ} (σ : D ≃ Fin nD)
  (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (n k : ℕ) (g : ℕ → D)
  (T : DTree M.dual) (C : DTree M) (vs ts : List V) (fs cs : List F)

open Classical in
/-- **The regions of the input**: `KInput` (eight arrays by darts, `ED` by nodes), `KBnd`,
`KOut` (`OB`, `OE` by nodes, `OL` padded to `nD` words), `KInit`. -/
def kRegs : List (ℕ × (ℕ → ℕ)) :=
  [dReg σ (fun d => σ (M.rev d)), dReg σ (fun d => ιf (M.face d)), dReg σ ιe, dReg σ ιg,
    dReg σ (fun d => ιv (M.tail d)), dReg σ (fun d => ιv (M.head d)),
    dReg σ (fun d => if d ∈ S then 1 else 0), dReg σ (fun d => (ℓ d).toNat),
    (n, fun u => if h : ∃ d, ιe d = u then σ (Classical.choose h) else 0),
    (k, fun i => σ (g i)),
    (n, fun u => if h : ∃ x, ιv x = u then outB M S (Classical.choose h) else 0),
    (n, fun u => if h : ∃ x, ιv x = u then
      outB M S (Classical.choose h) + (outL M S (Classical.choose h)).length else 0),
    (nD, fun j => ((allOut M S).map fun d => (σ d : ℕ)).getD j 0),
    (n, fun j => (vs.map ιv).getD j 0),
    (n, fun j => (ts.map fun x => (σ (T.par x) : ℕ)).getD j 0),
    (n, fun j => (fs.map ιf).getD j 0),
    (n, fun j => (cs.map fun y => (σ (C.par y) : ℕ)).getD j 0),
    (4, fun j => [vs.length, ts.length, fs.length, cs.length].getD j 0)]

/-- **The input.** -/
def kInput : Input := ⟨layList (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs), fun _ => 0⟩

open Classical in
/-- **The regions of the targets** (`KTgt`): the nodes `XN` of the `t` targets `X i`, then their
reach bits `XR` from the first root. -/
def kRegsX (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) (ιv : V → ℕ)
    (t : ℕ) (X : ℕ → V) : List (ℕ × (ℕ → ℕ)) :=
  [(t, fun i => ιv (X i)),
    (t, fun i => if Reach (pieceGraph M S ℓ) (M.tail (g 0)) (X i) then 1 else 0)]

/-- **The input with the targets**: the regions of `kInput`, then those of the targets. -/
def kInputT (t : ℕ) (X : ℕ → V) : Input :=
  ⟨layList (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs ++ kRegsX M k g S ℓ ιv t X),
    fun _ => 0⟩

variable {M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs}


lemma kInput_data : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data = layList (kRegs M S ℓ
    σ ιv ιg ιf ιe n k g T C vs ts fs cs) := rfl

lemma kInput_rv (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iRV nD + σ
    d) 0 = σ (M.rev d) := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 0 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iRV]

lemma kInput_nh (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iNH nD + σ
    d) 0 = ιv (M.head d) := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 5 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iNH]; ring

lemma kInput_nf (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iNF nD + σ
    d) 0 = ιf (M.face d) := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 1 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iNF] <;> ring

lemma kInput_ne (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iNE nD + σ
    d) 0 = ιe d := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 2 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iNE] <;> ring

lemma kInput_ng (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iNG nD + σ
    d) 0 = ιg d := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 3 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iNG] <;> ring

lemma kInput_nt (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iNT nD + σ
    d) 0 = ιv (M.tail d) := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 4 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iNT] <;> ring

lemma kInput_is (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iIS nD + σ
    d) 0 = if d ∈ S then 1 else 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 6 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iIS] <;> ring

lemma kInput_ln (d : D) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iLN nD + σ
    d) 0 = (ℓ d).toNat := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 7 (by simp [kRegs]) (i
      := σ d) (by simp [kRegs, dReg])
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iLN] <;> ring

lemma kInput_ed (hN : Nodes n M ιf ιe) (d : D) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iED nD + ιe d) 0 = σ d ∨ (kInput
        M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iED nD + ιe d) 0 = σ (M.rev d) := by
  classical
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 8 (by simp [kRegs]) (i
      := ιe d) (by simp [kRegs]; exact hN.e_lt d)
  have e : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iED nD + ιe d) 0 = σ
      (Classical.choose (⟨d, rfl⟩ : ∃ d', ιe d' = ιe d)) := by
    rw [kInput_data]
    convert h using 2
    · simp [kRegs, dReg, iED]; ring
    · simp [kRegs]
  rw [e]
  rcases hN.e_eq _ _ (Classical.choose_spec (⟨d, rfl⟩ : ∃ d', ιe d' = ιe d)) with h' | h'
  · exact Or.inl (congrArg (fun x => ((σ x : Fin nD) : ℕ)) h'.symm)
  · refine Or.inr (congrArg (fun x => ((σ x : Fin nD) : ℕ)) ?_)
    calc _ = M.rev (M.rev (Classical.choose (⟨d, rfl⟩ : ∃ d', ιe d' = ιe d))) :=
          (M.rev_rev _).symm
      _ = M.rev d := by rw [← h']

lemma kInput_gb {i : ℕ} (hi : i < k) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs
    cs).data.getD (iGB nD n + i) 0 = σ (g i) := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 9 (by simp [kRegs]) (i
      := i) (by simp [kRegs]; exact hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iGB] <;> ring

lemma kInput_ob (hinj : Function.Injective ιv) (hlt : ∀ x, ιv x < n) (x : V) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iOB nD n k + ιv x) 0 = outB M S
        x := by
  classical
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 10 (by simp [kRegs]) (i
      := ιv x) (by simp [kRegs]; exact hlt x)
  rw [kInput_data]
  convert h using 2
  · simp [kRegs, dReg, iOB]; ring
  · simp only [kRegs, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [dif_pos ⟨x, rfl⟩, hinj (Classical.choose_spec (⟨x, rfl⟩ : ∃ x', ιv x' = ιv x))]

lemma kInput_oe (hinj : Function.Injective ιv) (hlt : ∀ x, ιv x < n) (x : V) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iOE nD n k + ιv x) 0 = outB M S
        x + (outL M S x).length := by
  classical
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 11 (by simp [kRegs]) (i
      := ιv x) (by simp [kRegs]; exact hlt x)
  rw [kInput_data]
  convert h using 2
  · simp [kRegs, dReg, iOE]; ring
  · simp only [kRegs, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [dif_pos ⟨x, rfl⟩, hinj (Classical.choose_spec (⟨x, rfl⟩ : ∃ x', ιv x' = ιv x))]

lemma kInput_ol {j : ℕ} (hj : j < nD) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iOL nD n k + j) 0 = ((allOut M
        S).map fun d => (σ d : ℕ)).getD j 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 12 (by simp [kRegs]) (i
      := j) (by simp [kRegs]; exact hj)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iOL] <;> ring

lemma kInput_iv {i : ℕ} (hi : i < n) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD (iIV nD n k + i) 0 = (vs.map
        ιv).getD i 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 13 (by simp [kRegs]) (i
      := i) (by simpa [kRegs] using hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iIV] <;> ring

lemma kInput_it {i : ℕ} (hi : i < n) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD ((iIV nD n k + 1 * n) + i) 0 =
        (ts.map fun x => (σ (T.par x) : ℕ)).getD i 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 14 (by simp [kRegs]) (i
      := i) (by simpa [kRegs] using hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iIV] <;> ring

lemma kInput_if {i : ℕ} (hi : i < n) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD ((iIV nD n k + 2 * n) + i) 0 =
        (fs.map ιf).getD i 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 15 (by simp [kRegs]) (i
      := i) (by simpa [kRegs] using hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iIV] <;> ring

lemma kInput_ic {i : ℕ} (hi : i < n) :
    (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs).data.getD ((iIV nD n k + 3 * n) + i) 0 =
        (cs.map fun y => (σ (C.par y) : ℕ)).getD i 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 16 (by simp [kRegs]) (i
      := i) (by simpa [kRegs] using hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iIV] <;> ring

lemma kInput_hd {i : ℕ} (hi : i < 4) : (kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs
    cs).data.getD (iHD nD n k + i) 0 =
    [vs.length, ts.length, fs.length, cs.length].getD i 0 := by
  have h := layList_getD (kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs) 17 (by simp [kRegs]) (i
      := i) (by simp [kRegs]; exact hi)
  rw [kInput_data]
  convert h using 2 <;> simp [kRegs, dReg, iHD, iIV] <;> ring

/-- The input, in the lemmas below. -/
local notation "KI" => kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs
/-- Its regions, in the lemmas below. -/
local notation "KR" => kRegs M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs

lemma kRegs_len : ((KR).map Prod.fst).sum = iXT nD n k := by
  simp [kRegs, dReg, iXT]; ring

/-- **The input with the targets agrees with `kInput`** below the targets. -/
lemma kInputT_getD {t : ℕ} {X : ℕ → V} {a : ℕ} (ha : a < iXT nD n k) :
    (kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X).data.getD a 0 = (KI).data.getD a 0 :=
  layList_append_getD _ _ (by rw [kRegs_len]; exact ha)

lemma kInputT_xn {t : ℕ} {X : ℕ → V} {i : ℕ} (hi : i < t) :
    (kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X).data.getD (iXT nD n k + i) 0 =
      ιv (X i) := by
  have h := layList_getD (KR ++ kRegsX M k g S ℓ ιv t X) 18 (by simp [kRegs, kRegsX]) (i := i)
    (by simp [kRegs, kRegsX]; exact hi)
  convert h using 2 <;> simp [kInputT, kRegs, kRegsX, dReg, iXT] <;> ring

open Classical in
lemma kInputT_xr {t : ℕ} {X : ℕ → V} {i : ℕ} (hi : i < t) :
    (kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X).data.getD (iXT nD n k + t + i) 0 =
      if Reach (pieceGraph M S ℓ) (M.tail (g 0)) (X i) then 1 else 0 := by
  have h := layList_getD (KR ++ kRegsX M k g S ℓ ιv t X) 19 (by simp [kRegs, kRegsX]) (i := i)
    (by simp [kRegs, kRegsX]; exact hi)
  convert h using 2 <;> simp [kInputT, kRegs, kRegsX, dReg, iXT] <;> ring

/-! ### The preconditions are met -/

variable {k : ℕ} {g : ℕ → D} {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- The real memory of the starting configuration: `WT`, `PH` and the constants. -/
def kReal (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ}
    (σ : D ≃ Fin nD) (a : ℕ) : ℝ :=
  if h : a < nD then (tripWt M k g S ℓ 0 (σ.symm ⟨a, h⟩) : ℝ)
  else if h' : a - nD < nD then (tripφ S ℓ (σ.symm ⟨a - nD, h'⟩) : ℝ)
  else if a = 3 * nD then (tripL V S ℓ : ℝ)
  else if a = 3 * nD + 1 then (tripTh V S ℓ : ℝ)
  else if a = 3 * nD + 2 then (tripH0 V S ℓ k : ℝ) else 0

/-- **The preconditions of `klein_exec` can be met**: for every map, boundary, piece and
lengths meeting the hypotheses of the trip, a layout on `2 (#V + #F + #D)` nodes, the numbering
`Fintype.equivFin` of the darts, the input `kInputT` (`kInput`, then the `t` targets `X i`, none
of them a root, and their reach bits), the initial trees of `klein_init_exists`, a word bound and
a configuration with the real memory `kReal`. -/
theorem klein_exec_pre (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ) (X : ℕ → V)
    (hX : ∀ i < t, ¬ IsRoot M k g (X i)) :
    ∃ (n : ℕ) (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ)
      (σ : D ≃ Fin (Fintype.card D)) (P : Input) (B : ℕ) (T : DTree M.dual) (C : DTree M)
      (vs ts : List V) (fs cs : List F) (c₀ : Config),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      9 * Fintype.card D + 7 * n + k + 4 + 2 * t ≤ B ∧ n + 2 * Fintype.card D ≤ B ∧
      aOUT (Fintype.card D) + k * t ≤ B ∧ aRB n + k * t ≤ B ∧
      (∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) ∧
      Layout M n ιv ιg ιf ιe ∧ KInput M S ℓ σ ιv ιg ιf ιe P ∧ KBnd k g σ n P ∧
      KOut M S σ ιv n k P ∧ KTgt M k g S ℓ (Fintype.card D) n ιv t X P ∧
      KInit M σ ιv ιf n k T C vs ts fs cs P ∧
      (∀ x, x ≠ C.root → ¬ T.InT (C.par x)) ∧ C.root = M.face (g 0) ∧
      Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k)) (tpar 𝒢 (tripSrc M k g 0)) ∧
      WordsBounded (B + 16 * (n + 1)) c₀ ∧
      (∀ d, c₀.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d) ∧
      (∀ d, c₀.rmem (aPH (Fintype.card D) + σ d) = tripφ S ℓ d) ∧
      c₀.rmem (aTL (Fintype.card D)) = tripL V S ℓ ∧
      c₀.rmem (aTH (Fintype.card D)) = tripTh V S ℓ ∧
      c₀.rmem (aH0 (Fintype.card D)) = tripH0 V S ℓ k ∧
      (∀ r, c₀.rreg r = 0) ∧ (∀ a, ∃ z : ℤ, c₀.rmem a = z) := by
  classical
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := exists_layout M
  obtain ⟨T, C, vs, ts, fs, cs, hOT, hOC, hoff, hCr, hT⟩ := klein_init_exists H hR
  set nD := Fintype.card D with hnD
  set n := 2 * (Fintype.card V + Fintype.card F + Fintype.card D) with hn
  set σ : D ≃ Fin nD := Fintype.equivFin D with hσdef
  set P₀ := kInput M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs with hP₀
  set P := kInputT M S ℓ σ ιv ιg ιf ιe n k g T C vs ts fs cs t X with hP
  have hTr : ∀ a, a < iXT nD n k → P.data.getD a 0 = P₀.data.getD a 0 := fun a ha =>
    kInputT_getD ha
  set B := P.data.sum + 9 * nD + 7 * n + k + 4 + 2 * t + aOUT nD + k * t + n + 2 * nD with hB
  have hk := H.two_le_k
  have hnD1 : 1 ≤ nD := Fintype.card_pos_iff.2 ⟨g 0⟩
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hvl := hOT.flen
  have htl := hOT.ylen
  have hfl := hOC.flen
  have hcl := hOC.ylen
  have hVn : 2 * Fintype.card V ≤ n := hL.hv
  have hFn : 2 * Fintype.card F ≤ n := hL.hf
  have hSn : S.card ≤ nD := card_le_univ S
  refine ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs,
    { initConfig with rmem := kReal M k g S ℓ σ }, rfl, by omega, by omega, by omega,
    by unfold aRB; omega, fun i => ?_, hL,
    ⟨fun d => (hTr _ (by unfold iRV iXT; have := hσ d; omega)).trans (kInput_rv d),
      fun d => (hTr _ (by unfold iNF iXT; have := hσ d; omega)).trans (kInput_nf d),
      fun d => (hTr _ (by unfold iNE iXT; have := hσ d; omega)).trans (kInput_ne d),
      fun d => (hTr _ (by unfold iNG iXT; have := hσ d; omega)).trans (kInput_ng d),
      fun d => (hTr _ (by unfold iNT iXT; have := hσ d; omega)).trans (kInput_nt d),
      fun d => (hTr _ (by unfold iNH iXT; have := hσ d; omega)).trans (kInput_nh d),
      fun d => (hTr _ (by unfold iIS iXT; have := hσ d; omega)).trans (kInput_is d),
      fun d _ => (hTr _ (by unfold iLN iXT; have := hσ d; omega)).trans (kInput_ln d),
      fun d => by
        rw [hTr _ (by unfold iED iXT; have := hL.dual.e_lt d; omega)]
        exact kInput_ed hL.dual d⟩,
    fun i hi => (hTr _ (by unfold iGB iXT; omega)).trans (kInput_gb hi), fun x => ?_,
    ⟨hX, fun i hi => kInputT_xn hi, fun i hi => kInputT_xr hi⟩,
    ⟨hOT, hOC, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩,
    hoff, hCr, hT, wordsBounded_initConfig _, fun d => ?_, fun d => ?_, ?_, ?_, ?_,
    fun _ => rfl, fun a => ?_⟩
  · have h1 : P.data.getD i 0 ≤ P.data.sum := layList_le _ i
    omega
  · -- the out-darts
    have hx := hL.prim.f_lt x
    have hsplit := allOut_split M S x
    have hlen : outB M S x + (outL M S x).length ≤ nD := by
      have := congrArg List.length hsplit
      rw [allOut_length] at this
      simp only [List.length_append] at this
      unfold outB; omega
    have bOB : iOB nD n k + ιv x < iXT nD n k := by unfold iOB iXT; omega
    have bOE : iOE nD n k + ιv x < iXT nD n k := by unfold iOE iXT; omega
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
  · rw [show iIT nD n k = iIV nD n k + 1 * n by unfold iIT; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_it (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [show iIF nD n k = iIV nD n k + 2 * n by unfold iIF; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_if (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [show iIC nD n k = iIV nD n k + 3 * n by unfold iIC; ring,
      hTr _ (by unfold iIV iXT; omega), kInput_ic (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    have := kInput_hd (M := M) (S := S) (ℓ := ℓ) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 0) (by norm_num)
    simpa using this
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := ℓ) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 1) (by norm_num)
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := ℓ) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 2) (by norm_num)
  · rw [hTr _ (by unfold iHD iIV iXT; omega)]
    simpa using kInput_hd (M := M) (S := S) (ℓ := ℓ) (σ := σ) (ιv := ιv) (ιg := ιg) (ιf := ιf)
      (ιe := ιe) (n := n) (k := k) (g := g) (T := T) (C := C) (vs := vs) (ts := ts) (fs := fs)
      (cs := cs) (i := 3) (by norm_num)
  · show kReal M k g S ℓ σ (aWT + σ d) = _
    simp [kReal, aWT, hσ d]
  · show kReal M k g S ℓ σ (aPH nD + σ d) = _
    have h1 : ¬ nD + (σ d : ℕ) < nD := by omega
    have h2 : nD + (σ d : ℕ) - nD < nD := by have := hσ d; omega
    simp only [kReal, aPH, h1, h2, ↓reduceDIte]
    congr
    apply σ.symm_apply_eq.2
    ext; simp
  · show kReal M k g S ℓ σ (aTL nD) = _
    have h1 : ¬ 3 * nD < nD := by omega
    have h2 : ¬ 3 * nD - nD < nD := by omega
    simp [kReal, aTL, h1, h2]
  · show kReal M k g S ℓ σ (aTH nD) = _
    have h1 : ¬ 3 * nD + 1 < nD := by omega
    have h2 : ¬ 3 * nD + 1 - nD < nD := by omega
    simp [kReal, aTH, h1, h2]
  · show kReal M k g S ℓ σ (aH0 nD) = _
    have h1 : ¬ 3 * nD + 2 < nD := by omega
    have h2 : ¬ 3 * nD + 2 - nD < nD := by omega
    simp [kReal, aH0, h1, h2]
  · show ∃ z : ℤ, kReal M k g S ℓ σ a = z
    unfold kReal
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨0, by simp⟩

/-- **Klein's algorithm on the machine, end to end** (`klein_exec` with the preconditions of
`klein_exec_pre`): for every map, boundary, piece and lengths meeting the hypotheses of the trip,
with `N = #V + #F + #D`, there are an input and a starting configuration (as in
`klein_exec_pre`: the map, the boundary, the out-darts and the initial trees in the input, the
weights of the first move and the constants in the real memory, the `t` targets `X i` with
their reach bits in the input) from which `kleinProg` runs within
`36500000 (N lg N + k t lg N)` steps, makes the `k` moves of a trip, prints nothing and ends with
the answers in its output: `kOut j i` (the real word `OUT[j t + i]` where the natural word
`RB[j t + i]` is `1`) is the distance in the piece from `tail (g j)` to `X i`, none when `X i` is
not reached (`odist`). -/
theorem klein_exec_exists (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ) (X : ℕ → V)
    (hX : ∀ i < t, ¬ IsRoot M k g (X i)) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (kleinProg B (Fintype.card D) n k t) c₀ c' steps ∧
      steps ≤ 36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) ∧
      (∃ R : ℕ → MoveData M S, IsTripUpTo M k g S ℓ k R) ∧
      (∀ j < k, ∀ i < t, kOut (Fintype.card D) n t c' j i =
        (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
      c'.output = c₀.output := by
  obtain ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs, c₀, hn, hWa, hB, hOUT, hRB, hP, hL,
    hK, hG, hO, hXT, hI, hoff, hCr, hT, hc₀, hwt, hph, htl, hth, hh0, -⟩ :=
    klein_exec_pre H hR t X hX
  obtain ⟨c', steps, e, hsteps, htrip, hd, hout⟩ := klein_exec hWa hB hOUT hRB hP H hR hL hK hG
    hO hXT hI hoff hCr hT hc₀ hwt hph htl hth hh0
  refine ⟨n, B, P, c₀, c', steps, hn, e, hsteps.trans ?_, htrip, hd, hout⟩
  have hk := H.k_le_card
  have h2 := H.face.two_le
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  rw [hn]
  exact klein_steps_le (by omega) hS hk

end Klein

end PlanarFlow
