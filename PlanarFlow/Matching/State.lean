module

public import PlanarFlow.Matching.Prog

/-!
# Maximum bipartite matching: transitions of the search state

Pure lemmas on the memory: visiting a black vertex (free: the search stops; matched: its mate is
queued), finishing a white vertex, and König's certificate at the end of a search that found no
free black vertex.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open WordRAM WordRAM.Machine Finset

variable {d : List ℕ} {W : ℕ}

lemma BS.tail_lt {μ : ℕ → ℕ} {D : ℕ → Prop} {m : ℕ → ℕ} {tail t found : ℕ}
    (h : BS d μ D m tail t found) {x : ℕ} (hx : x < nn d) (hnot : vs d m x = 0) :
    tail < nn d := by
  classical
  have hn : ∀ k < tail, qu d m k ≠ x := fun k hk e => by
    have := (h.q k hk).2.2; rw [e] at this; omega
  have := Finset.card_le_card_of_injOn (qu d m) (s := range tail) (t := (range (nn d)).erase x)
    (fun k hk => by
      simp only [coe_range, Set.mem_Iio] at hk
      simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨(h.q k hk).1, hn k hk⟩)
    (fun k hk l hl e => h.qinj k (by simpa using hk) l (by simpa using hl) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hx), card_range] at this
  omega

lemma Valid.mate_lt {μ : ℕ → ℕ} (hμ : Valid d μ) {x : ℕ} (hx : x < nn d) (h : μ x ≠ 0) :
    μ x - 1 < nn d := (hμ x hx h).1

/-- The memory after visiting `b` from `w` at time `t`. -/
def visitMem (d : List ℕ) (m : ℕ → ℕ) (w b t : ℕ) : ℕ → ℕ :=
  upd (upd (upd m (nn d + b) 1) (2 * nn d + b) w) (3 * nn d + b) t

section visit
variable {μ : ℕ → ℕ} {D : ℕ → Prop} {m : ℕ → ℕ} {tail t : ℕ} {w b : ℕ}

lemma vs_visit (hb : b < nn d) (v : ℕ) (hv : v < nn d) :
    vs d (visitMem d m w b t) v = if v = b then 1 else vs d m v := by
  simp only [vs, visitMem, upd_apply]; split_ifs <;> first | omega | rfl

lemma pa_visit (hb : b < nn d) (v : ℕ) (hv : v < nn d) :
    pa d (visitMem d m w b t) v = if v = b then w else pa d m v := by
  simp only [pa, visitMem, upd_apply]; split_ifs <;> first | omega | rfl

lemma tm_visit (hb : b < nn d) (v : ℕ) (hv : v < nn d) :
    tmv d (visitMem d m w b t) v = if v = b then t else tmv d m v := by
  simp only [tmv, visitMem, upd_apply]; split_ifs <;> first | omega | rfl

lemma qu_visit (hb : b < nn d) (k : ℕ) : qu d (visitMem d m w b t) k = qu d m k := by
  simp only [qu, visitMem, upd_apply]; split_ifs <;> first | omega | rfl

lemma mate_visit (hb : b < nn d) (v : ℕ) (hv : v < nn d) : visitMem d m w b t v = m v := by
  simp only [visitMem, upd_apply]; split_ifs <;> first | omega | rfl

/-- The common part of a visit: everything but the found flag and the new mate. -/
theorem BS.visit (hw : Wf d) (hμ : Valid d μ) (h : BS d μ D m tail t 0) (hwn : w < nn d)
    (hvw : vs d m w = 1) (harc : Arc d w b) (hb0 : vs d m b = 0) :
    let m' := visitMem d m w b t
    (∀ v < nn d, m' v = μ v) ∧ (∀ v < nn d, vs d m' v = 0 ∨ vs d m' v = 1) ∧
    (∀ v < nn d, vs d m v = 1 → vs d m' v = 1) ∧ (∀ k, qu d m' k = qu d m k) ∧
    vs d m' b = 1 ∧ pa d m' b = w ∧ tmv d m' b = t ∧
    (∀ v < nn d, v ≠ b → vs d m' v = vs d m v ∧ pa d m' v = pa d m v ∧ tmv d m' v = tmv d m v) ∧
    nvis d m' = t + 1 := by
  have hbn := hw.arc_lt _ _ harc
  refine ⟨fun v hv => (mate_visit hbn v hv).trans (h.mate v hv), fun v hv => ?_, fun v hv h1 => ?_,
    fun k => qu_visit hbn k, by rw [vs_visit hbn b hbn]; simp, by rw [pa_visit hbn b hbn]; simp,
    by rw [tm_visit hbn b hbn]; simp, fun v hv hvb => ?_, ?_⟩
  · rw [vs_visit hbn v hv]; split_ifs; exacts [Or.inr rfl, h.vis01 v hv]
  · rw [vs_visit hbn v hv]; split_ifs <;> simp [h1]
  · rw [vs_visit hbn v hv, pa_visit hbn v hv, tm_visit hbn v hv]; simp [hvb]
  · rw [h.tcnt]
    exact nvis_mark hbn hb0 (by rw [vs_visit hbn b hbn]; simp) fun v hv hvb => by
      rw [vs_visit hbn v hv]; simp [hvb]

end visit

/-- The vertex `w` visits the free black vertex `b`: the search stops with `found = b + 1`. -/
theorem BS.visit_free (hw : Wf d) {μ : ℕ → ℕ} (hμ : Valid d μ) {D : ℕ → Prop} {m : ℕ → ℕ}
    {tail t : ℕ} (h : BS d μ D m tail t 0) {w b : ℕ} (hwn : w < nn d) (hvw : vs d m w = 1)
    (harc : Arc d w b) (hb0 : vs d m b = 0) (hfree : μ b = 0) :
    BS d μ D (visitMem d m w b t) tail (t + 1) (b + 1) := by
  have hbn := hw.arc_lt _ _ harc
  have hcb := (hw.arc_col _ _ harc).2
  obtain ⟨hmate, h01, hge, hqu, hvb, hpb, htb, hsame, hcnt⟩ := h.visit hw hμ hwn hvw harc hb0
  have hwb : w ≠ b := fun e => by rw [e] at hvw; omega
  refine ⟨hmate, h01, h.tl, fun k hk => ?_, fun k hk l hl e => h.qinj k hk l hl
    (by rwa [hqu, hqu] at e), fun x hx hcx hvx => ?_, fun x hx hcx hμx => hge x hx
    (h.free x hx hcx hμx), fun h0 => by omega, fun x hx hcx hvx => ?_,
    fun x hx hcx hvx hμx => ?_, fun v hv hvv => ?_, hcnt.symm,
    fun _ => ⟨by simpa using hbn, by simpa using hcb, by simpa using hvb, by simpa using hfree⟩⟩
  · obtain ⟨h1, h2, h3⟩ := h.q k hk
    rw [hqu]; exact ⟨h1, h2, hge _ h1 h3⟩
  · have hxb : x ≠ b := fun e => by rw [e] at hcx; omega
    rw [(hsame x hx hxb).1] at hvx
    obtain ⟨k, hk, e⟩ := h.wvis x hx hcx hvx
    exact ⟨k, hk, by rw [hqu]; exact e⟩
  · by_cases hxb : x = b
    · rw [hxb, hpb, htb, (hsame w hwn hwb).2.2]
      exact ⟨hwn, hge w hwn hvw, harc, h.tmlt w hwn hvw, fun _ => rfl, fun h' => absurd hfree h'⟩
    · obtain ⟨e1, e2, e3⟩ := hsame x hx hxb
      rw [e1] at hvx
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.bvis x hx hcx hvx
      have hpb' : pa d m x ≠ b := fun e => by rw [e] at a2; omega
      rw [e2, e3, (hsame _ a1 hpb').2.2]
      refine ⟨a1, hge _ a1 a2, a3, a4, fun h' => absurd (a5 h') (by omega), fun h' =>
        hge _ (hμ.mate_lt hx h') (a6 h')⟩
  · have hxb : x ≠ b := fun e => by rw [e] at hcx; omega
    obtain ⟨e1, -, e3⟩ := hsame x hx hxb
    rw [e1] at hvx
    obtain ⟨a1, a2⟩ := h.wmat x hx hcx hvx hμx
    have hlt := hμ.mate_lt hx hμx
    have hyb : μ x - 1 ≠ b := fun e => by rw [e] at a1; omega
    rw [e3, (hsame _ hlt hyb).2.2]
    exact ⟨hge _ hlt a1, a2⟩
  · by_cases hvb' : v = b
    · rw [hvb', htb]; omega
    · obtain ⟨e1, -, e3⟩ := hsame v hv hvb'
      rw [e1] at hvv; rw [e3]; have := h.tmlt v hv hvv; omega

/-- The memory after queueing `w'` at the tail `tail` at time `t`. -/
def enqMem (d : List ℕ) (m : ℕ → ℕ) (w' tail t : ℕ) : ℕ → ℕ :=
  upd (upd (upd m (nn d + w') 1) (4 * nn d + tail) w') (3 * nn d + w') t

/-- The vertex `w` visits the matched black vertex `b`; its mate `w'` is queued. -/
theorem BS.visit_matched (hw : Wf d) {μ : ℕ → ℕ} (hμ : Valid d μ) {D : ℕ → Prop} {m : ℕ → ℕ}
    {tail t : ℕ} (h : BS d μ D m tail t 0) {w b : ℕ} (hwn : w < nn d) (hvw : vs d m w = 1)
    (harc : Arc d w b) (hb0 : vs d m b = 0) (hmb : μ b ≠ 0) :
    vs d m (μ b - 1) = 0 ∧
    BS d μ D (enqMem d (visitMem d m w b t) (μ b - 1) tail (t + 1)) (tail + 1) (t + 2) 0 := by
  have hbn := hw.arc_lt _ _ harc
  have hcb := (hw.arc_col _ _ harc).2
  obtain ⟨hmate, h01, hge, hqu, hvb, hpb, htb, hsame, hcnt⟩ := h.visit hw hμ hwn hvw harc hb0
  have hwb : w ≠ b := fun e => by rw [e] at hvw; omega
  obtain ⟨hw'n, hback, -, harc'⟩ := hμ b hbn hmb
  generalize hw' : μ b - 1 = w' at hw'n hback harc'
  have hcw' : col d w' = 1 := (hw.arc_col _ _ (harc' hcb)).1
  have hw'b : w' ≠ b := fun e => by rw [e] at hcw'; omega
  -- the mate of `b` was not visited
  have hw'0 : vs d m w' = 0 := by
    rcases h.vis01 w' hw'n with h0 | h1
    · exact h0
    · have := (h.wmat w' hw'n hcw' h1 (by rw [hback]; omega)).1
      rw [hback, Nat.add_sub_cancel] at this; omega
  refine ⟨hw'0, ?_⟩
  have htl := h.tail_lt hw'n hw'0
  set m₁ := visitMem d m w b t with hm₁
  have hvs₁ : vs d m₁ w' = 0 := by rw [(hsame w' hw'n hw'b).1]; exact hw'0
  have hvs : ∀ v < nn d, vs d (enqMem d m₁ w' tail (t + 1)) v = if v = w' then 1 else vs d m₁ v := by
    intro v hv; simp only [vs, enqMem, upd_apply]; split_ifs <;> first | omega | rfl
  have hpa : ∀ v < nn d, pa d (enqMem d m₁ w' tail (t + 1)) v = pa d m₁ v := by
    intro v hv; simp only [pa, enqMem, upd_apply]; split_ifs <;> first | omega | rfl
  have htm : ∀ v < nn d, tmv d (enqMem d m₁ w' tail (t + 1)) v =
      if v = w' then t + 1 else tmv d m₁ v := by
    intro v hv; simp only [tmv, enqMem, upd_apply]; split_ifs <;> first | omega | rfl
  have hq : ∀ k, qu d (enqMem d m₁ w' tail (t + 1)) k = if k = tail then w' else qu d m₁ k := by
    intro k; simp only [qu, enqMem, upd_apply]; split_ifs <;> first | omega | rfl
  have hge' : ∀ v < nn d, vs d m₁ v = 1 → vs d (enqMem d m₁ w' tail (t + 1)) v = 1 := by
    intro v hv h1; rw [hvs v hv]; split_ifs <;> simp [h1]
  have hgeall : ∀ v < nn d, vs d m v = 1 → vs d (enqMem d m₁ w' tail (t + 1)) v = 1 :=
    fun v hv h1 => hge' v hv (hge v hv h1)
  have hqold : ∀ k < tail, qu d m k ≠ w' := fun k hk e => by
    have := (h.q k hk).2.2; rw [e] at this; omega
  refine ⟨fun v hv => ?_, fun v hv => ?_, htl, fun k hk => ?_, fun k hk l hl e => ?_,
    fun x hx hcx hvx => ?_, fun x hx hcx hμx => hgeall x hx (h.free x hx hcx hμx),
    fun _ y z hy harc'' => hgeall z (hw.arc_lt _ _ harc'') (h.cl rfl y z hy harc''),
    fun x hx hcx hvx => ?_, fun x hx hcx hvx hμx => ?_, fun v hv hvv => ?_, ?_,
    fun h0 => absurd rfl h0⟩
  · simp only [enqMem, upd_apply]; split_ifs <;> first | omega | exact hmate v hv
  · rw [hvs v hv]; split_ifs; exacts [Or.inr rfl, h01 v hv]
  · rw [hq]
    split_ifs with hkt
    · exact ⟨hw'n, hcw', by rw [hvs w' hw'n]; simp⟩
    · obtain ⟨h1, h2, h3⟩ := h.q k (by omega)
      rw [hqu]; exact ⟨h1, h2, hgeall _ h1 h3⟩
  · rw [hq, hq] at e
    split_ifs at e with h1 h2 h2
    · omega
    · rw [hqu] at e; exact absurd e.symm (hqold l (by omega))
    · rw [hqu] at e; exact absurd e (hqold k (by omega))
    · rw [hqu, hqu] at e; exact h.qinj k (by omega) l (by omega) e
  · rw [hvs x hx] at hvx
    by_cases hxw : x = w'
    · exact ⟨tail, by omega, by rw [hq]; simp [hxw]⟩
    · simp only [hxw, ite_false] at hvx
      have hxb : x ≠ b := fun e => by rw [e] at hcx; omega
      rw [(hsame x hx hxb).1] at hvx
      obtain ⟨k, hk, e⟩ := h.wvis x hx hcx hvx
      exact ⟨k, by omega, by rw [hq]; simp [show k ≠ tail by omega, hqu, e]⟩
  · have hxw : x ≠ w' := fun e => by rw [e] at hcx; omega
    rw [hvs x hx] at hvx; simp only [hxw, ite_false] at hvx
    rw [hpa x hx, htm x hx]; simp only [hxw, ite_false]
    by_cases hxb : x = b
    · rw [hxb, hpb, htb]
      have hww' : w ≠ w' := fun e => by rw [e] at hvw; omega
      rw [htm w hwn]; simp only [hww', ite_false]
      rw [(hsame w hwn hwb).2.2]
      refine ⟨hwn, hgeall w hwn hvw, harc, h.tmlt w hwn hvw, fun h' => absurd h' hmb,
        fun _ => by rw [hw', hvs w' hw'n]; simp⟩
    · obtain ⟨e1, e2, e3⟩ := hsame x hx hxb
      rw [e1] at hvx
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.bvis x hx hcx hvx
      have hpb' : pa d m x ≠ b := fun e => by rw [e] at a2; omega
      have hpw' : pa d m x ≠ w' := fun e => by rw [e] at a2; omega
      rw [e2, e3, htm _ a1]; simp only [hpw', ite_false]
      rw [(hsame _ a1 hpb').2.2]
      refine ⟨a1, hgeall _ a1 a2, a3, a4, fun h' => absurd (a5 h') (by omega), fun h' =>
        hgeall _ (hμ.mate_lt hx h') (a6 h')⟩
  · rw [hvs x hx] at hvx
    by_cases hxw : x = w'
    · subst hxw
      rw [hback, Nat.add_sub_cancel, htm _ hbn, htm _ hx]
      simp only [hw'b.symm, ite_false, ite_true]
      refine ⟨hge' _ hbn hvb, by rw [htb]; omega⟩
    · simp only [hxw, ite_false] at hvx
      have hxb : x ≠ b := fun e => by rw [e] at hcx; omega
      obtain ⟨e1, -, e3⟩ := hsame x hx hxb
      rw [e1] at hvx
      obtain ⟨a1, a2⟩ := h.wmat x hx hcx hvx hμx
      have hlt := hμ.mate_lt hx hμx
      have hyb : μ x - 1 ≠ b := fun e => by rw [e] at a1; omega
      have hyw : μ x - 1 ≠ w' := fun e => by rw [e] at a1; omega
      rw [htm _ hlt, htm _ hx]; simp only [hyw, hxw, ite_false]
      rw [e3, (hsame _ hlt hyb).2.2]
      exact ⟨hgeall _ hlt a1, a2⟩
  · rw [hvs v hv] at hvv
    rw [htm v hv]
    by_cases hvw' : v = w'
    · simp [hvw']
    · simp only [hvw', ite_false] at hvv ⊢
      by_cases hvb' : v = b
      · rw [hvb', htb]; omega
      · obtain ⟨e1, -, e3⟩ := hsame v hv hvb'
        rw [e1] at hvv; rw [e3]; have := h.tmlt v hv hvv; omega
  · rw [h.tcnt] at hcnt
    have := nvis_mark (m := m₁) (m' := enqMem d m₁ w' tail (t + 1)) hw'n hvs₁
      (by rw [hvs w' hw'n]; simp) fun v hv hvw => by rw [hvs v hv]; simp [hvw]
    rw [this, hcnt, h.tcnt]

/-- All the arcs of `w` have been scanned. -/
theorem BS.done {μ : ℕ → ℕ} {D : ℕ → Prop} {m : ℕ → ℕ} {tail t found : ℕ}
    (h : BS d μ D m tail t found) {w : ℕ}
    (hall : found = 0 → ∀ b, Arc d w b → vs d m b = 1) :
    BS d μ (fun x => D x ∨ x = w) m tail t found := by
  refine { h with cl := ?_ }
  intro h0 x b hx harc
  rcases hx with hx | rfl
  · exact h.cl h0 x b hx harc
  · exact hall h0 b harc

/-- **The certificate.** A search that has scanned every queued vertex and found no free black
vertex proves the matching maximum. -/
theorem BS.maximal (hw : Wf d) {μ : ℕ → ℕ} (hμ : Valid d μ) {D : ℕ → Prop} {m : ℕ → ℕ}
    {tail t : ℕ} (h : BS d μ D m tail t 0) (hD : ∀ k < tail, D (qu d m k)) {M : Finset (ℕ × ℕ)}
    (hM : IsMatching d M) : M.card ≤ size d μ := by
  classical
  refine card_le_size hw hμ (fun v => vs d m v = 1) (fun w hw' hc h0 => h.free w hw' hc h0)
    (fun w b harc hvw => ?_) (fun b hb hc hvb => ?_) hM
  · obtain ⟨k, hk, rfl⟩ := h.wvis w harc.1 (hw.arc_col _ _ harc).1 hvw
    exact h.cl rfl _ b (hD k hk) harc
  · obtain ⟨-, -, -, -, a5, a6⟩ := h.bvis b hb hc hvb
    have hm : μ b ≠ 0 := fun h0 => by have := a5 h0; omega
    exact ⟨hm, a6 hm⟩

end BM

end PlanarFlow
