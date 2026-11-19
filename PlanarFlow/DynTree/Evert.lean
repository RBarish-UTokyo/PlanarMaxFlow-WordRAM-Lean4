module

public import PlanarFlow.DynTree.Ops

/-!
# Dynamic trees: evert, and the parent read from the access

After the access of `v`, its auxiliary tree `T = node l v leaf dv` is the path from the root of
its tree down to `v`. **Evert** (`evertM v = flipM v`) reverses this path lazily: it toggles the
reversal bit of `v` and mirrors its record. The virtual forest becomes `mirT T :: G`, whose
auxiliary tree is the reversed path, and it represents `evert F n v` (`evert_okE`): the path is
reversed, and the two values of its nodes are exchanged. The potential is unchanged.

Evert does not keep the forest-parent field `fpar`; the parent of `v` is then read from the
access instead (`parent_top`): it is the rightmost node of the left subtree of `v`.
-/

@[expose] public noncomputable section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine VT

variable (B n : ℕ)

/-- Evert after the access of `v`. -/
def evertM (v : ℕ) (M : Mem) : Mem := flipM B v M

lemma revPar_of_chain : ∀ {L : List ℕ} {q u p : ℕ}, L.Nodup → (u, p) ∈ VT.chain q L →
    revPar q L u = some p
  | [], _, _, _, _, h => by simp at h
  | x :: L, q, u, p, hnd, h => by
    simp only [VT.chain_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [revPar]
    · have hu : u ∈ L := chain_fst h
      have hux : u ≠ x := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hu)
      simp only [revPar, hux, ↓reduceIte]
      exact revPar_of_chain (List.nodup_cons.mp hnd).2 h

lemma revPar_of_not_mem : ∀ {L : List ℕ} {q u : ℕ}, u ∉ L → revPar q L u = none
  | [], _, _, _ => rfl
  | x :: L, q, u, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [revPar, h.1, ↓reduceIte]
    exact revPar_of_not_mem h.2

mutual
lemma dE_fst_hN : ∀ (t : VT) {u q : ℕ}, (u, q) ∈ dE t → u ∈ hN t
  | leaf, _, _, h => by simp at h
  | node l x r ds, u, q, h => by
    simp only [dE_node, List.mem_append] at h
    simp only [hN, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (dE_fst_hN l h))
    · exact Or.inl (Or.inr (dE_fst_hN r h))
    · exact Or.inr (dEL_fst x ds h)
end

/-- **Evert.** After the access of `v`, flipping `v` reverses the path from the root of its tree
down to `v`. -/
theorem evert_okE {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv) :
    Inv B n (evertM B v M) (mirT T :: G) ∧ RepE B n (evertM B v M) (mirT T :: G) (evert F n v) ∧
      MemFrame B n M (evertM B v M) ∧ potL (mirT T :: G) = potL (T :: G) := by
  have hvT : v ∈ nodes T := by rw [hT]; simp
  have hvn : v < n := (hI.cover v).mp (by simp [hvT])
  have hnd := hI.nodup
  simp only [nodesL_cons, List.nodup_append] at hnd
  have hvG : ∀ u ∈ nodesL G, u ≠ v := fun u hu e => hnd.2.2 v hvT u hu e.symm
  have hrt : rt n T = v := by rw [hT]; rfl
  have hTne : T ≠ VT.leaf := by rw [hT]; simp
  obtain ⟨E1, E2⟩ := enc_flip B n hI.nil (hI.enc T (by simp)) hnd.1 hTne
  rw [hrt] at E1 E2
  have hN' : NilOK B n (evertM B v M) := flipM_nil hI.nil
  have hE' : Enc B n (evertM B v M) (mirT T) n false := (enc_mirror_iff B n).mpr E1
  have hseq : seq T = seq l ++ [v] := by rw [hT]; simp
  have hrp := rootPath_top B n hI hR (gb := []) (ga := G) rfl hseq
  rw [← hseq] at hrp
  have hperm : (nodesL (mirT T :: G)).Perm (nodesL (T :: G)) := by
    simp only [nodesL_cons]; exact (nodes_mirT T).append_right _
  have hagG : ∀ u ∈ nodesL G, Agr B M (evertM B v M) u := fun u hu => flipM_agr (hvG u hu)
  have hagT : ∀ u ∈ nodes T, u ≠ rt n T → Agr B M (evertM B v M) u := fun u _ hne =>
    flipM_agr (by rwa [hrt] at hne)
  have ndseq : (seq T).Nodup := (seq_sublist_nodes T).nodup hnd.1
  have hnotP : ∀ u, u ∈ hN T → u ∉ seq T := by
    intro u hu hs
    have := (nodes_perm_hN T).nodup_iff.mp hnd.1
    exact List.disjoint_of_nodup_append this hs hu
  have hnotPG : ∀ u, u ∈ nodesL G → u ∉ seq T := fun u hu hs =>
    hnd.2.2 u ((seq_sublist_nodes T).subset hs) u hu rfl
  refine ⟨⟨fun T' hT' => ?_, hperm.nodup_iff.mpr hI.nodup,
      fun u => hperm.mem_iff.trans (hI.cover u), hN'⟩, ⟨fun u p h => ?_, fun u w h => ?_,
      fun u w h => ?_⟩, flipM_frame hvn.le, by simp [pot_mirT]⟩
  · rcases List.mem_cons.mp hT' with rfl | hT'
    · exact hE'
    · exact enc_frame_all B n hI.nil hN' (hI.enc T' (by simp [hT']))
        (nodup_of_mem_nodesL hnd.2.1 hT') (fun u hu => hagG u (mem_nodesL_of hT' hu))
  · -- the edges
    simp only [dEL_cons, List.mem_append, seq_mirT] at h
    simp only [evert, hrp]
    rcases h with (h | h) | h
    · rw [revPar_of_chain (by simpa using ndseq) h]; rfl
    · rw [dE_mirT] at h
      have hu := hnotP u (dE_fst_hN T h)
      rw [revPar_of_not_mem (by simpa using hu)]
      exact hR.par u p (by simp [h])
    · have hu := hnotPG u (dEL_fst n G h)
      rw [revPar_of_not_mem (by simpa using hu)]
      exact hR.par u p (by simp [h])
  all_goals
    simp only [dVL_cons, List.mem_append] at h
    rw [dVL_frame B G (fun u hu => (hagG u hu).agrV B)] at h
    have hdV : ∀ k e, e ∈ dV B (evertM B v M) (mirT T) k ↔ e ∈ dV B M T k := by
      intro k e
      rw [dV_mirT, dV_frame_root B n (fun u hu hne => (hagT u hu hne).agrV B) hnd.1]
    rw [hdV] at h
    simp only [evert, hrp, List.mem_reverse]
    rcases h with (h | h) | h
    · rw [rs_mirT, evertM, E2] at h
      rw [List.mem_reverse] at h
      try simp only [Bool.not_false, Bool.not_true] at h
      have hu : u ∈ seq T := rs_fst_mem B h
      simp only [hu, ↓reduceIte]
      first
      | exact hR.val2 u w (by simp [h])
      | exact hR.val u w (by simp [h])
    · have hu := hnotP u (dV_fst B T h)
      simp only [hu, ↓reduceIte]
      first
      | exact hR.val u w (by simp [h])
      | exact hR.val2 u w (by simp [h])
    · have hu := hnotPG u (dVL_fst B G h)
      simp only [hu, ↓reduceIte]
      first
      | exact hR.val u w (by simp [h])
      | exact hR.val2 u w (by simp [h])

/-- **The parent from the access.** After the access of `v` (whose reversal bit is clear), the
parent of `v` in the forest is the rightmost node of its left subtree (`n` if there is none). -/
theorem parent_top {M : Mem} {G : List VT} {F : Forest} {T : VT} (hI : Inv B n M (T :: G))
    (hR : RepE B n M (T :: G) F) {l : VT} {v : ℕ} {dv : List VT} (hT : T = node l v leaf dv)
    (hv : rv B M v = false) :
    F.par v = if lc B M v < n then rtm B M (lc B M v) else n := by
  have hE := hI.enc T (by simp)
  rw [hT, enc_node_iff_clean B n hv] at hE
  obtain ⟨-, hlv, -, -, hlE, -⟩ := hE
  have hlt : ∀ u ∈ nodes l, u < n := fun u hu => (hI.cover u).mp (by simp [hT, hu])
  have hA := hlE.agg B n hI.nil hlt
  rw [Ag.mirIf_false] at hA
  have hedge : (v, (seq l).getLastD n) ∈ dEL n (T :: G) := by
    rw [hT]; simp only [dEL_cons, seq_node, seq_leaf, List.mem_append]
    left; left
    rw [VT.chain_append]; simp
  rw [hR.par v _ hedge, hlv]
  by_cases hl : l = VT.leaf
  · subst hl; simp
  · have hrl : rt n l < n := hlt _ (rt_mem_nodes hl n)
    rw [ite_of_pos hrl]
    have := congrArg Ag.rm (hA.2 hrl)
    simp only [rd, own, Ag.addTags, tAg] at this
    exact this.symm

end DynTree

end PlanarFlow
