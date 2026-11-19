module

public import PlanarFlow.BKMNW.PpSl
public import PlanarSeparator.Machine.RadixProg

/-!
# The sort of the slots: the mathematics

The slots `s < G` (`G = 7 n`) are sorted by one stable counting-sort pass (`csPass`) of the items
`itF s = kap s · G + s` on the key `x / G mod (KM + 1)`, where `kap s ≤ KM` is the key of a valid
slot and `KM` for the others. The output `csS` lists the valid slots first (sorted by key), then
the others. With `srtF p = csS[p] mod G`:

* `srtF_lt`, `srtF_inj` (a permutation of `[0, G)`);
* `nV` (the number of valid slots, `= ∑ fl V`), `srtF_valid` (`p < nV` gives a valid slot),
  `srtF_all` (every valid slot is listed before `nV`), `srtF_sorted` (keys nondecreasing).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset PlanarSeparator.Piece

section SortMath

variable (G KM : ℕ) (kap : ℕ → ℕ)

/-- The sort item of a slot. -/
def itF (s : ℕ) : ℕ := kap s * G + s

/-- The items of the slots `< G`. -/
def Lit : List ℕ := (List.range G).map (itF G kap)

/-- The sort key. -/
def κF (x : ℕ) : ℕ := x / G % (KM + 1)

/-- The sorted items. -/
def soF : List ℕ := csS (κF G KM) (Lit G kap) (KM + 1)

/-- The sorted slots. -/
def srtF (p : ℕ) : ℕ := (soF G KM kap).getD p 0 % G

/-- The number of valid slots: the items of key `< KM`. -/
def nV : ℕ := (csS (κF G KM) (Lit G kap) KM).length

variable {G KM kap}
variable (hG : 0 < G) (hk : ∀ s < G, kap s ≤ KM)
include hG

lemma itF_mod {s : ℕ} (hs : s < G) : itF G kap s % G = s := by
  unfold itF; rw [Nat.mul_add_mod_of_lt hs]

lemma itF_div {s : ℕ} (hs : s < G) : itF G kap s / G = kap s := by
  unfold itF; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hs, Nat.zero_add]

include hk

lemma κF_itF {s : ℕ} (hs : s < G) : κF G KM (itF G kap s) = kap s := by
  unfold κF; rw [itF_div hG hs, Nat.mod_eq_of_lt (by have := hk s hs; omega)]

omit hk in
lemma mem_Lit {x : ℕ} : x ∈ Lit G kap ↔ ∃ s < G, itF G kap s = x := by
  simp [Lit]

omit hk in
lemma Lit_nodup : (Lit G kap).Nodup := by
  unfold Lit
  refine (List.nodup_range).map_on fun a ha b hb e => ?_
  rw [List.mem_range] at ha hb
  rw [← itF_mod hG ha, e, itF_mod hG hb]

lemma κF_lt {x : ℕ} (hx : x ∈ Lit G kap) : κF G KM x < KM + 1 := by
  unfold κF; exact Nat.mod_lt _ (by omega)

lemma soF_perm : (soF G KM kap).Perm (Lit G kap) :=
  perm_csS _ _ (Lit_nodup hG) fun x hx => κF_lt hG hk hx

lemma soF_length : (soF G KM kap).length = G := by
  rw [(soF_perm hG hk).length_eq]; simp [Lit]

omit hk in
lemma soF_nodup : (soF G KM kap).Nodup := nodup_csS _ _ (Lit_nodup hG) _

lemma soF_eq : soF G KM kap = csS (κF G KM) (Lit G kap) KM ++ csBlk (κF G KM) (Lit G kap) KM :=
  csS_succ _ _ _

lemma mem_soF_lit {x : ℕ} (hx : x ∈ soF G KM kap) : ∃ s < G, itF G kap s = x :=
  (mem_Lit hG).1 ((soF_perm hG hk).subset hx)

lemma srtF_lt (p : ℕ) : srtF G KM kap p < G := Nat.mod_lt _ hG

lemma getD_soF {p : ℕ} (hp : p < G) :
    (soF G KM kap).getD p 0 = (soF G KM kap)[p]'(by rw [soF_length hG hk]; exact hp) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl

lemma srtF_inj {p q : ℕ} (hp : p < G) (hq : q < G) (e : srtF G KM kap p = srtF G KM kap q) :
    p = q := by
  unfold srtF at e
  rw [getD_soF hG hk hp, getD_soF hG hk hq] at e
  obtain ⟨s, hs, es⟩ := mem_soF_lit hG hk (List.getElem_mem (l := soF G KM kap)
    (n := p) (by rw [soF_length hG hk]; exact hp))
  obtain ⟨t, ht, et⟩ := mem_soF_lit hG hk (List.getElem_mem (l := soF G KM kap)
    (n := q) (by rw [soF_length hG hk]; exact hq))
  rw [← es, ← et, itF_mod hG hs, itF_mod hG ht] at e
  subst e
  have := (soF_nodup hG).getElem_inj_iff.1 (es.symm.trans et)
  exact this

lemma nV_le : nV G KM kap ≤ G := by
  have := congrArg List.length (soF_eq hG hk)
  rw [List.length_append, soF_length hG hk] at this
  unfold nV; omega

lemma getD_lt_nV {p : ℕ} (hp : p < nV G KM kap) :
    (soF G KM kap).getD p 0 = (csS (κF G KM) (Lit G kap) KM).getD p 0 := by
  rw [soF_eq hG hk, List.getD_append _ _ _ _ hp]

variable (V : ℕ → Prop) (hV : ∀ s < G, V s ↔ kap s < KM)
include hV

lemma srtF_valid {p : ℕ} (hp : p < nV G KM kap) : V (srtF G KM kap p) := by
  unfold srtF
  rw [getD_lt_nV hG hk hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
    Option.getD_some]
  have hm := List.getElem_mem (l := csS (κF G KM) (Lit G kap) KM) hp
  obtain ⟨hL, hκ⟩ := (mem_csS _ _).1 hm
  obtain ⟨s, hs, es⟩ := (mem_Lit hG).1 hL
  rw [← es, itF_mod hG hs]
  rw [← es, κF_itF hG hk hs] at hκ
  exact (hV s hs).2 hκ

lemma srtF_all {s : ℕ} (hs : s < G) (hv : V s) : ∃ p < nV G KM kap, srtF G KM kap p = s := by
  have hm : itF G kap s ∈ csS (κF G KM) (Lit G kap) KM :=
    (mem_csS _ _).2 ⟨(mem_Lit hG).2 ⟨s, hs, rfl⟩, by rw [κF_itF hG hk hs]; exact (hV s hs).1 hv⟩
  obtain ⟨p, hp, e⟩ := List.mem_iff_getElem.1 hm
  refine ⟨p, hp, ?_⟩
  unfold srtF
  rw [getD_lt_nV hG hk hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
    Option.getD_some, e, itF_mod hG hs]

lemma kap_srtF {p : ℕ} (hp : p < G) :
    kap (srtF G KM kap p) = κF G KM ((soF G KM kap).getD p 0) := by
  rw [getD_soF hG hk hp]
  obtain ⟨s, hs, es⟩ := mem_soF_lit hG hk (List.getElem_mem (l := soF G KM kap)
    (n := p) (by rw [soF_length hG hk]; exact hp))
  unfold srtF; rw [getD_soF hG hk hp, ← es, itF_mod hG hs, κF_itF hG hk hs]

lemma srtF_sorted {p q : ℕ} (hpq : p < q) (hq : q < G) :
    kap (srtF G KM kap p) ≤ kap (srtF G KM kap q) := by
  rw [kap_srtF hG hk V hV (by omega), kap_srtF hG hk V hV hq, getD_soF hG hk (by omega),
    getD_soF hG hk hq]
  have hpw := csS_pairwise_key (κF G KM) (Lit G kap) (KM + 1)
  exact List.pairwise_iff_getElem.1 hpw p q _ _ hpq

lemma nV_eq : nV G KM kap = ∑ s ∈ range G, fl (V s) := by
  classical
  have hnd : (csS (κF G KM) (Lit G kap) KM).Nodup := nodup_csS _ _ (Lit_nodup hG) _
  unfold nV
  rw [← List.toFinset_card_of_nodup hnd]
  have e : (csS (κF G KM) (Lit G kap) KM).toFinset =
      ((range G).filter V).image (itF G kap) := by
    ext x
    simp only [List.mem_toFinset, mem_csS, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨hL, hκ⟩
      obtain ⟨s, hs, rfl⟩ := (mem_Lit hG).1 hL
      rw [κF_itF hG hk hs] at hκ
      exact ⟨s, ⟨hs, (hV s hs).2 hκ⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hv⟩, rfl⟩
      exact ⟨(mem_Lit hG).2 ⟨s, hs, rfl⟩, by rw [κF_itF hG hk hs]; exact (hV s hs).1 hv⟩
  rw [e, card_image_of_injOn (fun a ha b hb h => by
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at ha hb
    rw [← itF_mod hG ha.1, h, itF_mod hG hb.1])]
  rw [card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun s _ => ?_
  unfold fl; split_ifs <;> rfl

end SortMath

end Pp

end BKMNW

end PlanarFlow
