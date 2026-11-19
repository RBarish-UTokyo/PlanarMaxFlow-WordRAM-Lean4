module

public import NestedDissection.MachineSparse
public import NestedDissection.MachineGram

/-!
# The input of sparse elimination, assembled from listed entries, an order and a pattern

`SparseMod.ndIn p σ H E = [n, p, #E] ++ rkWords σ ++ words E ++ nbWords H` is the input of
`SparseMod.sparseMod` built from

* a list `E` of triples `(i, j, g)` (for instance the output of `GramMod.gram`),
* the order `σ`, as the ranks `σ⁻¹ u` (`SparseMod.rkWords`),
* the pattern `H`, as the blocks `[d_k, w₀, …]` of the later neighbours of every `k` in increasing
  order (`SparseMod.nbWords`, the natural encoder of the fill graph).

Its fields are read off by `SparseMod.rk_ndIn`, `SparseMod.eu_ndIn`, …, `SparseMod.nb_ndIn`; when
the entries of `E` are inside the matrix, with residues `< p`, and the word bound is large
enough, it is well formed (`SparseMod.sEnc_ndIn`); its neighbour sets are the later neighbours in
`H` (`SparseMod.nbSet_ndIn`); and when the triples of `E` agree on every position the listed
matrix holds their value at every listed position and `0` elsewhere (`SparseMod.rmem_ndIn`).
-/

@[expose] public section

namespace NestedDissection

namespace SparseMod

open WordRAM Finset
open DetMod (dim prm)
open GramMod (words)

/-! ### Reading lists -/

theorem getD_append_left' {l l' : List ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l l' : List ℕ) (i : ℕ) :
    (l ++ l').getD (l.length + i) 0 = l'.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem length_words (E : List (ℕ × ℕ × ℕ)) : (words E).length = 3 * E.length := by
  induction E with
  | nil => rfl
  | cons x E ih => simp [words] at ih ⊢; omega

theorem getD_words (E : List (ℕ × ℕ × ℕ)) {t : ℕ} (ht : t < E.length) :
    (words E).getD (3 * t) 0 = E[t].1 ∧ (words E).getD (3 * t + 1) 0 = E[t].2.1 ∧
      (words E).getD (3 * t + 2) 0 = E[t].2.2 := by
  induction E generalizing t with
  | nil => simp at ht
  | cons x E ih =>
    cases t with
    | zero => simp [words]
    | succ t =>
      have h := ih (t := t) (by simpa using ht)
      have e : words (x :: E) = [x.1, x.2.1, x.2.2] ++ words E := by simp [words]
      rw [e, show 3 * (t + 1) = [x.1, x.2.1, x.2.2].length + 3 * t by simp; ring,
        getD_append_right', show [x.1, x.2.1, x.2.2].length + 3 * t + 1 =
          [x.1, x.2.1, x.2.2].length + (3 * t + 1) by ring, getD_append_right',
        show [x.1, x.2.1, x.2.2].length + 3 * t + 2 = [x.1, x.2.1, x.2.2].length + (3 * t + 2) by
          ring, getD_append_right']
      simpa using h

/-- Reading a block of a concatenation of blocks. -/
theorem getD_flatMap_range (blk : ℕ → List ℕ) {k N i : ℕ} (hk : k < N) (hi : i < (blk k).length) :
    ((List.range N).flatMap blk).getD (((List.range k).flatMap blk).length + i) 0 =
      (blk k).getD i 0 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have hle : ((List.range (k + 1)).flatMap blk).length ≤
          ((List.range N).flatMap blk).length := by
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ N by omega)
        rw [List.range_add (n := k + 1) (m := r), List.flatMap_append, List.length_append]; omega
      have hlt : ((List.range k).flatMap blk).length + i <
          ((List.range N).flatMap blk).length := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
          List.length_append] at hle
        omega
      rw [getD_append_left' hlt, ih hk]
    · rw [getD_append_right']

/-! ### The neighbour blocks -/

variable {n : ℕ}

/-- The later neighbours of `k` in `H`, in increasing order. -/
noncomputable def later (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℕ) : List ℕ :=
  if h : k < n then ((laterNbrs Fin.val H ⟨k, h⟩).image Fin.val).sort (· ≤ ·) else []

/-- The block of `k`: the number of later neighbours, then the later neighbours. -/
noncomputable def nbBlk (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℕ) : List ℕ :=
  (later H k).length :: later H k

/-- **The natural encoding of the pattern**: the blocks of `0, …, n - 1`. -/
noncomputable def nbWords (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : List ℕ :=
  (List.range n).flatMap (nbBlk H)

/-- The ranks `σ⁻¹ u`. -/
def rkWords (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun u => (σ.symm u : ℕ)

/-- **The assembled input of `sparseMod`.** -/
noncomputable def ndIn (p : ℕ) (σ : Equiv.Perm (Fin n)) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (E : List (ℕ × ℕ × ℕ)) : List ℕ :=
  [n, p, E.length] ++ rkWords σ ++ words E ++ nbWords H

variable {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]

theorem mem_later {k x : ℕ} (hk : k < n) :
    x ∈ later H k ↔ ∃ hx : x < n, H.Adj ⟨k, hk⟩ ⟨x, hx⟩ ∧ k < x := by
  simp only [later, hk, ↓reduceDIte, mem_sort, mem_image, mem_laterNbrs]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨i.2, h1, h2⟩
  · rintro ⟨hx, h1, h2⟩; exact ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩

theorem nodup_later (k : ℕ) : (later H k).Nodup := by
  unfold later; split_ifs
  · exact sort_nodup _ _
  · exact List.nodup_nil

theorem length_later_le (k : ℕ) : (later H k).length ≤ n := by
  unfold later; split_ifs
  · rw [length_sort]
    exact (card_image_le).trans ((card_le_univ _).trans_eq (Fintype.card_fin n))
  · exact Nat.zero_le _

theorem length_later (k : ℕ) (hk : k < n) :
    (later H k).length = (laterNbrs Fin.val H ⟨k, hk⟩).card := by
  simp only [later, hk, ↓reduceDIte, length_sort]
  exact card_image_of_injective _ Fin.val_injective

theorem length_nbWords : (nbWords H).length ≤ n + n * n := by
  unfold nbWords
  rw [List.length_flatMap]
  have : ∀ k ∈ List.range n, (nbBlk H k).length ≤ n + 1 := fun k _ => by
    simp only [nbBlk, List.length_cons]; have := length_later_le (H := H) k; omega
  calc (List.map (fun k => (nbBlk H k).length) (List.range n)).sum
      ≤ (List.map (fun _ => n + 1) (List.range n)).sum :=
        List.sum_le_sum (by simpa using this)
    _ = n + n * n := by simp; ring

/-! ### The fields of the assembled input -/

variable {p : ℕ} {σ : Equiv.Perm (Fin n)} {E : List (ℕ × ℕ × ℕ)}

theorem ndIn_eq : ndIn p σ H E = [n, p, E.length] ++ (rkWords σ ++ (words E ++ nbWords H)) := by
  simp [ndIn]

@[simp] theorem dim_ndIn : dim (ndIn p σ H E) = n := rfl
@[simp] theorem prm_ndIn : prm (ndIn p σ H E) = p := rfl
@[simp] theorem em_ndIn : em (ndIn p σ H E) = E.length := rfl

theorem length_rkWords : (rkWords σ).length = n := List.length_ofFn

theorem rk_ndIn {u : ℕ} (hu : u < n) : rk (ndIn p σ H E) u = (σ.symm ⟨u, hu⟩ : ℕ) := by
  rw [rk, ndIn_eq, show 3 + u = [n, p, E.length].length + u by simp, getD_append_right',
    getD_append_left' (by rw [length_rkWords]; exact hu)]
  simp [rkWords, List.getD_eq_getElem?_getD, hu]

theorem entry_ndIn {t : ℕ} (ht : t < E.length) :
    eu (ndIn p σ H E) t = E[t].1 ∧ ev (ndIn p σ H E) t = E[t].2.1 ∧
      ea (ndIn p σ H E) t = E[t].2.2 := by
  have hw := getD_words E ht
  have hl : ∀ r < 3, 3 * t + r < (words E).length := fun r hr => by
    rw [length_words]; omega
  have key : ∀ r < 3, (ndIn p σ H E).getD (3 + n + 3 * t + r) 0 = (words E).getD (3 * t + r) 0 :=
    fun r hr => by
      rw [ndIn_eq, show 3 + n + 3 * t + r = [n, p, E.length].length + ((rkWords σ).length +
        (3 * t + r)) by simp [length_rkWords]; ring, getD_append_right', getD_append_right',
        getD_append_left' (hl r hr)]
  refine ⟨?_, ?_, ?_⟩
  · have := key 0 (by omega); simp only [Nat.add_zero] at this
    rw [eu, dim_ndIn, this, hw.1]
  · have := key 1 (by omega)
    rw [ev, dim_ndIn, show 4 + n + 3 * t = 3 + n + 3 * t + 1 by ring, this, hw.2.1]
  · have := key 2 (by omega)
    rw [ea, dim_ndIn, show 5 + n + 3 * t = 3 + n + 3 * t + 2 by ring, this, hw.2.2]

theorem getD_ndIn_nb (i : ℕ) :
    (ndIn p σ H E).getD (3 + n + 3 * E.length + i) 0 = (nbWords H).getD i 0 := by
  rw [ndIn_eq, show 3 + n + 3 * E.length + i = [n, p, E.length].length + ((rkWords σ).length +
    ((words E).length + i)) by simp [length_rkWords, length_words]; ring, getD_append_right',
    getD_append_right', getD_append_right']

theorem lpos_ndIn {k : ℕ} (hk : k ≤ n) :
    lpos (ndIn p σ H E) k = 3 + n + 3 * E.length + ((List.range k).flatMap (nbBlk H)).length := by
  induction k with
  | zero => simp [lpos]
  | succ k ih =>
    rw [lpos_succ, ih (by omega), deg, ih (by omega), getD_ndIn_nb,
      show ((List.range k).flatMap (nbBlk H)).length = ((List.range k).flatMap (nbBlk H)).length
        + 0 from rfl, nbWords, getD_flatMap_range _ (by omega) (by simp [nbBlk]),
      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
    simp [nbBlk]; ring

theorem deg_ndIn {k : ℕ} (hk : k < n) : deg (ndIn p σ H E) k = (later H k).length := by
  rw [deg, lpos_ndIn hk.le, getD_ndIn_nb, nbWords,
    show ((List.range k).flatMap (nbBlk H)).length = ((List.range k).flatMap (nbBlk H)).length
      + 0 from rfl, getD_flatMap_range _ hk (by simp [nbBlk])]
  simp [nbBlk]

theorem nb_ndIn {k t : ℕ} (hk : k < n) (ht : t < (later H k).length) :
    nb (ndIn p σ H E) k t = (later H k)[t] := by
  rw [nb, lpos_ndIn hk.le, show 3 + n + 3 * E.length +
    ((List.range k).flatMap (nbBlk H)).length + 1 + t = 3 + n + 3 * E.length +
      (((List.range k).flatMap (nbBlk H)).length + (t + 1)) by ring, getD_ndIn_nb, nbWords,
    getD_flatMap_range _ hk (by simp [nbBlk]; omega)]
  simp [nbBlk, List.getD_eq_getElem?_getD, ht]

theorem lpos_ndIn_le : lpos (ndIn p σ H E) n ≤ 3 + n + 3 * E.length + (n + n * n) := by
  rw [lpos_ndIn le_rfl]
  have := length_nbWords (H := H)
  unfold nbWords at this
  omega

/-- The neighbour sets of the assembled input are the later neighbours in `H`. -/
theorem nbSet_ndIn {k : ℕ} (hk : k < n) :
    (∀ i (hi : i < n), (∃ t < deg (ndIn p σ H E) k, nb (ndIn p σ H E) k t = i) ↔
      H.Adj ⟨k, hk⟩ ⟨i, hi⟩ ∧ k < i) := by
  intro i hi
  rw [deg_ndIn hk]
  constructor
  · rintro ⟨t, ht, e⟩
    rw [nb_ndIn hk ht] at e
    obtain ⟨_, h1, h2⟩ := (mem_later hk).1 (List.getElem_mem ht)
    subst e
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem ((mem_later hk).2 ⟨hi, h1, h2⟩)
    exact ⟨t, ht, by rw [nb_ndIn hk ht, e]⟩

/-- **The assembled input is well formed** when the triples are inside the matrix with residues
below the prime and the word bound is large enough. -/
theorem sEnc_ndIn {W : ℕ} (hp : p.Prime) (hE : ∀ x ∈ E, x.1 < n ∧ x.2.1 < n ∧ x.2.2 < p)
    (hW : p * p + p + n * n + 3 * E.length + 4 * n + 8 ≤ W) : SEnc (ndIn p σ H E) W := by
  have hp2 := hp.two_le
  have hpos := lpos_ndIn_le (p := p) (σ := σ) (H := H) (E := E)
  refine ⟨hp, fun i => ?_, by simp; omega, by simp; omega, by simp; omega, fun t ht => ?_,
    fun u hu => ?_, fun k hk t ht => ?_, fun k hk t ht t' ht' e => ?_⟩
  · -- every word
    rw [ndIn_eq]
    have hlen : ∀ (l : List ℕ) (B : ℕ), (∀ x ∈ l, x ≤ B) → l.getD i 0 ≤ B := fun l B hB => by
      rw [List.getD_eq_getElem?_getD]
      cases h : l[i]? with
      | none => simp
      | some x => exact hB x (List.mem_of_getElem? h)
    refine hlen _ W fun x hx => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | hx | hx | hx
    · omega
    · omega
    · omega
    · simp only [rkWords, List.mem_ofFn] at hx
      obtain ⟨u, rfl⟩ := hx; have := (σ.symm u).2; omega
    · simp only [words, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨y, hy, hx⟩ := hx
      obtain ⟨h1, h2, h3⟩ := hE y hy
      rcases hx with rfl | rfl | rfl <;> omega
    · simp only [nbWords, List.mem_flatMap, List.mem_range, nbBlk, List.mem_cons] at hx
      obtain ⟨k, hk, hx | hx⟩ := hx
      · have := length_later_le (H := H) k; rw [hx]; omega
      · obtain ⟨hx', -⟩ := (mem_later hk).1 hx; omega
  · simp only [em_ndIn] at ht
    obtain ⟨h1, h2, -⟩ := entry_ndIn (p := p) (σ := σ) (H := H) ht
    simp only [dim_ndIn, h1, h2]
    exact ⟨(hE _ (List.getElem_mem ht)).1, (hE _ (List.getElem_mem ht)).2.1⟩
  · simp only [dim_ndIn] at hu ⊢; rw [rk_ndIn hu]; exact (σ.symm _).2
  · simp only [dim_ndIn] at hk ⊢
    rw [deg_ndIn hk] at ht
    rw [nb_ndIn hk ht]
    obtain ⟨hx, -, h2⟩ := (mem_later hk).1 (List.getElem_mem ht)
    exact ⟨h2, hx⟩
  · simp only [dim_ndIn] at hk
    rw [deg_ndIn hk] at ht ht'
    rw [nb_ndIn hk ht, nb_ndIn hk ht'] at e
    exact (nodup_later k).getElem_inj_iff.1 e

/-- **The listed matrix of the assembled input**: if all triples at a position carry the same
value `g a`, the stored value at `a` is `g a mod p` if `a` is listed and `0` otherwise. -/
theorem rmem_consistent (d : List ℕ) (g : ℕ → ℕ)
    (hg : ∀ t < em d, ea d t = g (eu d t * dim d + ev d t)) {t : ℕ} (ht : t ≤ em d) (a : ℕ) :
    rmem d t a = if ∃ t' < t, eu d t' * dim d + ev d t' = a then g a % prm d else 0 := by
  induction t with
  | zero => simp [rmem]
  | succ t ih =>
    simp only [rmem, Machine.upd_apply]
    by_cases ha : a = eu d t * dim d + ev d t
    · have hex : ∃ t' < t + 1, eu d t' * dim d + ev d t' = a := ⟨t, by omega, ha.symm⟩
      simp only [ha, ↓reduceIte, hg t (by omega)]
      rw [← ha]; simp only [hex, ↓reduceIte]
    · simp only [ha, ↓reduceIte]
      rw [ih (by omega)]
      congr 1
      apply propext
      constructor
      · rintro ⟨t', ht', e⟩; exact ⟨t', by omega, e⟩
      · rintro ⟨t', ht', e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
        · exact ⟨t', ht', e⟩
        · exact absurd e.symm ha

end SparseMod

end NestedDissection
