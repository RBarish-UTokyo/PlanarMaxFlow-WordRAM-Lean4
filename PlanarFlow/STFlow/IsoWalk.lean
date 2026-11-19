module

public import PlanarFlow.STFlow.IsoCycle
public import PlanarFlow.NegSSSP.Spec

/-!
# Unique shortest walks for lengths with a positive-curl perturbation

The isolation argument of Bourke, Tewari and Vinodchandran (*Directed planar reachability is in
unambiguous log-space*, ACM TOCT 1 (2009)): in a plane map, give the dart `d` the length
`N c d + L + w d`, with `c` arbitrary integers, `w` antisymmetric of positive curl at every face
but one (`PlanarFlow/STFlow/IsoCycle.lean`), `L` above the total positive curl and `N` at least
`L` times the number of vertices. Then **a shortest walk between two vertices is unique**, among
the walks using darts of any given set on which the lengths are positive. Two distinct shortest
walks would contain two internally disjoint shortest paths from a vertex `u` to a vertex `v`
(after the last common prefix, up to the first common vertex), of the same length; together they
form a simple cycle, along which the sum of `w` is nonzero and below `L`, which the three scales
`N`, `L`, `1` of the lengths cannot compensate.

* `IsMinW G Q x y l`: `l` is a walk from `x` to `y` with darts in `Q`, of least length among them.
* `IsMinW.nodup`: with positive lengths, a least walk visits every vertex once.
* `minW_unique`: **two least walks with the same ends are equal**, as soon as no two internally
  disjoint simple paths with distinct first arcs between the same vertices have the same length
  (`hsep`);
* `curl_sep`: this condition for the lengths `N c + L + w` in a plane map with transitive
  rotations;
* `curl_unique`: hence **unique least walks** for these lengths.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset BKMNW

section Generic

variable {X A : Type*} {G : Digraph X A} {Q : A → Prop}

variable (G Q) in
/-- `l` is a walk from `x` to `y` with darts in `Q`, of least length among those walks. -/
def IsMinW (x y : X) (l : List A) : Prop :=
  IsWalk G x l y ∧ (∀ a ∈ l, Q a) ∧
    ∀ l', IsWalk G x l' y → (∀ a ∈ l', Q a) → wlen G l ≤ wlen G l'

lemma isWalk_end {x y y' : X} {l : List A} (h : IsWalk G x l y) (h' : IsWalk G x l y') :
    y = y' := by
  induction l generalizing x with
  | nil => exact h.symm.trans h'
  | cons a l ih => exact ih h.2 h'.2

lemma isWalk_concat_end {x z : X} {p : List A} {a : A} (h : IsWalk G x (p ++ [a]) z) :
    z = G.dst a := by
  obtain ⟨y, -, h2⟩ := isWalk_append_iff.1 h
  exact (isWalk_singleton.1 h2).2.symm

lemma mem_dst_of_walk {x y : X} {l : List A} (h : IsWalk G x l y) (hl : l ≠ []) :
    y ∈ l.map G.dst := by
  induction l generalizing x with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · have := h.2; simp only [isWalk_nil] at this; simp [this]
    · exact List.mem_cons_of_mem _ (ih h.2 (by simp))

lemma wlen_pos (hpos : ∀ a, Q a → 0 < G.len a) {l : List A} (hQ : ∀ a ∈ l, Q a) (hl : l ≠ []) :
    0 < wlen G l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rw [wlen_cons]
    have h1 := hpos a (hQ a (by simp))
    rcases l with _ | ⟨b, l⟩
    · simp [wlen]; exact h1
    · have := ih (fun a' ha' => hQ a' (List.mem_cons_of_mem _ ha')) (by simp); omega

lemma IsMinW.tail' {x y : X} {a : A} {l : List A} (h : IsMinW G Q x y (a :: l)) :
    IsMinW G Q (G.dst a) y l := by
  obtain ⟨⟨h1, h2⟩, hQ, hmin⟩ := h
  refine ⟨h2, fun a' ha' => hQ a' (List.mem_cons_of_mem _ ha'), fun l' hl' hQ' => ?_⟩
  have := hmin (a :: l') ⟨h1, hl'⟩ (fun b hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hQ _ (by simp)
    · exact hQ' b hb)
  simp only [wlen_cons] at this
  omega

lemma IsMinW.prefix {x y z : X} {p q : List A} (h : IsMinW G Q x y (p ++ q))
    (hp : IsWalk G x p z) : IsMinW G Q x z p := by
  obtain ⟨hw, hQ, hmin⟩ := h
  obtain ⟨z', hp', hq⟩ := isWalk_append_iff.1 hw
  obtain rfl := isWalk_end hp hp'
  refine ⟨hp, fun a ha => hQ a (List.mem_append_left _ ha), fun l' hl' hQ' => ?_⟩
  have := hmin (l' ++ q) (hl'.append hq) (fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · exact hQ' a ha
    · exact hQ a (List.mem_append_right _ ha))
  rw [wlen_append, wlen_append] at this
  omega

/-- **A least walk with positive lengths visits every vertex once.** -/
theorem IsMinW.nodup [DecidableEq X] (hpos : ∀ a, Q a → 0 < G.len a) {x y : X} {l : List A}
    (h : IsMinW G Q x y l) : (x :: l.map G.dst).Nodup := by
  induction l generalizing x with
  | nil => simp
  | cons a r ih =>
    have ih' := ih h.tail'
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hx => ?_, ih'⟩
    rw [← List.map_cons] at hx
    obtain ⟨b, hb, hbx⟩ := List.mem_map.1 hx
    obtain ⟨p, q, hpq⟩ := List.append_of_mem hb
    obtain ⟨hw, hQ, hmin⟩ := h
    rw [hpq, show p ++ b :: q = (p ++ [b]) ++ q by simp] at hw hQ
    obtain ⟨z, h1, h2⟩ := isWalk_append_iff.1 hw
    have hz := isWalk_concat_end h1
    rw [hz, hbx] at h2
    have hle := hmin q h2 (fun a ha => hQ a (List.mem_append_right _ ha))
    rw [hpq, show p ++ b :: q = (p ++ [b]) ++ q by simp, wlen_append] at hle
    have := wlen_pos hpos (l := p ++ [b]) (fun a ha => hQ a (List.mem_append_left _ ha))
      (by simp)
    omega

lemma exists_first (P : A → Prop) [DecidablePred P] {l : List A} (h : ∃ a ∈ l, P a) :
    ∃ p a q, l = p ++ a :: q ∧ P a ∧ ∀ a' ∈ p, ¬ P a' := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : P b
    · exact ⟨[], b, l, rfl, hb, by simp⟩
    · obtain ⟨a, ha, hPa⟩ := h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact absurd hPa hb
      obtain ⟨p, a', q, rfl, h1, h2⟩ := ih ⟨a, ha, hPa⟩
      refine ⟨b :: p, a', q, rfl, h1, fun a'' ha'' => ?_⟩
      rcases List.mem_cons.1 ha'' with rfl | ha''
      · exact hb
      · exact h2 a'' ha''

lemma head?_concat_eq {p q : List A} {a : A} : (p ++ [a]).head? = (p ++ a :: q).head? := by
  cases p <;> rfl

/-- **Two least walks with the same ends are equal**, when no two internally disjoint simple
paths between the same vertices, with darts in `Q` and distinct first arcs, have the same
length. -/
theorem minW_unique [DecidableEq X] (hpos : ∀ a, Q a → 0 < G.len a)
    (hsep : ∀ (u v : X) (p₁ p₂ : List A), IsWalk G u p₁ v → IsWalk G u p₂ v →
      (∀ a ∈ p₁, Q a) → (∀ a ∈ p₂, Q a) → p₁ ≠ [] → p₂ ≠ [] → p₁.head? ≠ p₂.head? →
      (u :: p₁.map G.dst).Nodup → (u :: p₂.map G.dst).Nodup →
      (∀ z ∈ p₁.map G.dst, z ∈ p₂.map G.dst → z = v) → wlen G p₁ ≠ wlen G p₂)
    {x y : X} {l₁ l₂ : List A} (h₁ : IsMinW G Q x y l₁) (h₂ : IsMinW G Q x y l₂) : l₁ = l₂ := by
  classical
  induction l₁ generalizing x l₂ with
  | nil =>
    have hxy : x = y := h₁.1
    rcases l₂ with _ | ⟨b, r⟩
    · rfl
    · exfalso
      have := h₂.2.2 [] hxy (by simp)
      have := wlen_pos hpos h₂.2.1 (by simp)
      simp [wlen] at *; omega
  | cons a r₁ ih =>
    rcases l₂ with _ | ⟨b, r₂⟩
    · exfalso
      have hxy : x = y := h₂.1
      have := h₁.2.2 [] hxy (by simp)
      have := wlen_pos hpos h₁.2.1 (by simp)
      simp [wlen] at *; omega
    by_cases hab : a = b
    · subst hab
      rw [ih h₁.tail' (by rw [show G.dst a = G.dst a from rfl]; exact h₂.tail')]
    exfalso
    -- the first vertex of `l₁` (after `x`) on `l₂`
    have hy₁ := mem_dst_of_walk h₁.1 (by simp)
    have hy₂ := mem_dst_of_walk h₂.1 (by simp)
    obtain ⟨a₀, ha₀, hya⟩ := List.mem_map.1 hy₁
    obtain ⟨p₁', a₁, q₁, hl₁, hP₁, hfirst⟩ :=
      exists_first (fun a' => G.dst a' ∈ (b :: r₂).map G.dst) ⟨a₀, ha₀, by rw [hya]; exact hy₂⟩
    obtain ⟨b₁, hb₁, hba⟩ := List.mem_map.1 hP₁
    obtain ⟨p₂', q₂, hl₂⟩ := List.append_of_mem hb₁
    set v := G.dst a₁
    have hw₁ := h₁.1
    have hw₂ := h₂.1
    rw [hl₁, show p₁' ++ a₁ :: q₁ = (p₁' ++ [a₁]) ++ q₁ by simp] at hw₁
    rw [hl₂, show p₂' ++ b₁ :: q₂ = (p₂' ++ [b₁]) ++ q₂ by simp] at hw₂
    obtain ⟨z₁, hp₁, -⟩ := isWalk_append_iff.1 hw₁
    obtain ⟨z₂, hp₂, -⟩ := isWalk_append_iff.1 hw₂
    have hz₁ := isWalk_concat_end hp₁
    have hz₂ := isWalk_concat_end hp₂
    rw [hz₁] at hp₁
    rw [hz₂, hba] at hp₂
    have hm₁ : IsMinW G Q x v (p₁' ++ [a₁]) := by
      have := h₁; rw [hl₁, show p₁' ++ a₁ :: q₁ = (p₁' ++ [a₁]) ++ q₁ by simp] at this
      exact this.prefix hp₁
    have hm₂ : IsMinW G Q x v (p₂' ++ [b₁]) := by
      have := h₂; rw [hl₂, show p₂' ++ b₁ :: q₂ = (p₂' ++ [b₁]) ++ q₂ by simp] at this
      exact this.prefix hp₂
    have heq : wlen G (p₁' ++ [a₁]) = wlen G (p₂' ++ [b₁]) :=
      le_antisymm (hm₁.2.2 _ hm₂.1 hm₂.2.1) (hm₂.2.2 _ hm₁.1 hm₁.2.1)
    refine hsep x v _ _ hp₁ hp₂ hm₁.2.1 hm₂.2.1 (by simp) (by simp) ?_ (hm₁.nodup hpos)
      (hm₂.nodup hpos) ?_ heq
    · rw [head?_concat_eq (q := q₁), ← hl₁, head?_concat_eq (q := q₂), ← hl₂]
      simpa using hab
    · intro z hz1 hz2
      rw [List.map_append, List.mem_append] at hz1
      rcases hz1 with hz1 | hz1
      · exfalso
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hz1
        apply hfirst a' ha'
        rw [hl₂]
        have : (p₂' ++ [b₁]).map G.dst ⊆ (p₂' ++ b₁ :: q₂).map G.dst := by
          intro x hx; simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
            List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
          tauto
        exact this hz2
      · simpa using hz1

end Generic

/-! ### Plane maps -/

section Plane

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {N : CombMap D V F}

lemma walk_step {ℓ : D → ℤ} {x y : V} {l : List D} (h : IsWalk (N.graph ℓ) x l y) :
    ∀ t (ht : t + 1 < l.length), N.head l[t] = N.tail l[t + 1] := by
  induction l generalizing x with
  | nil => intro t ht; simp at ht
  | cons a l ih =>
    intro t ht
    rcases t with _ | t
    · rcases l with _ | ⟨b, l⟩
      · simp at ht
      · exact h.2.1.symm
    · exact ih h.2 t (by simpa using ht)

lemma walk_first {ℓ : D → ℤ} {x y : V} {l : List D} (h : IsWalk (N.graph ℓ) x l y)
    (hl : 0 < l.length) : N.tail (l[0]'hl) = x := by
  rcases l with _ | ⟨a, l⟩
  · simp at hl
  · exact h.1

lemma walk_last {ℓ : D → ℤ} {x y : V} {l : List D} (h : IsWalk (N.graph ℓ) x l y)
    (hl : 0 < l.length) : N.head (l[l.length - 1]'(by omega)) = y := by
  induction l generalizing x with
  | nil => simp at hl
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · have := h.2; simp only [isWalk_nil] at this; exact this
    · have := ih h.2 (by simp)
      simpa using this

lemma walk_tails {ℓ : D → ℤ} {x y : V} {l : List D} (h : IsWalk (N.graph ℓ) x l y) :
    l.map N.tail ++ [y] = x :: l.map N.head := by
  induction l generalizing x with
  | nil => simpa using h.symm
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.cons_append, ih h.2]
    rw [show N.tail a = x from h.1]
    rfl

lemma walk_rev {ℓ ℓ' : D → ℤ} {x y : V} {l : List D} (h : IsWalk (N.graph ℓ) x l y) :
    IsWalk (N.graph ℓ') y (l.map N.rev).reverse x := by
  induction l generalizing x with
  | nil => exact h.symm
  | cons a l ih =>
    rw [List.map_cons, List.reverse_cons]
    refine (ih h.2).append ?_
    rw [isWalk_singleton]
    exact ⟨by simp [CombMap.graph], by simpa [CombMap.graph] using h.1⟩

lemma sum_range_getD {β : Type*} [AddCommMonoid β] (f : D → β) (d₀ : D) (l : List D) :
    ∑ t ∈ range l.length, f (l.getD t d₀) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
    exact add_comm _ _

lemma wlen_split (Nc L : ℤ) (cap w : D → ℤ) (l : List D) :
    wlen (N.graph fun d => Nc * cap d + L + w d) l =
      Nc * (l.map cap).sum + L * l.length + (l.map w).sum := by
  induction l with
  | nil => simp [wlen]
  | cons a l ih =>
    rw [wlen_cons, ih]
    simp only [CombMap.graph, List.map_cons, List.sum_cons, List.length_cons]
    push_cast; ring

/-- **The separation condition of `minW_unique` for the lengths `N c + L + w`**: two internally
disjoint simple paths with distinct first arcs between the same vertices have different
lengths, when `w` is antisymmetric with positive curl off the face `f₀`, `L` is above the total
curl off `f₀`, and `N ≥ L · #V`. -/
theorem curl_sep (hM : N.IsPlane) (hrot : N.RotTrans) {w : D → ℤ} (hw : N.IsAntisymm w)
    {f₀ : F} (hcurl : ∀ f, f ≠ f₀ → 0 < N.curl w f) {L Nc : ℤ}
    (hL : ∑ f ∈ univ.erase f₀, N.curl w f < L) (hN : L * Fintype.card V ≤ Nc) (cap : D → ℤ)
    (u v : V) (p₁ p₂ : List D) (hp₁ : IsWalk (N.graph fun d => Nc * cap d + L + w d) u p₁ v)
    (hp₂ : IsWalk (N.graph fun d => Nc * cap d + L + w d) u p₂ v) (hn₁ : p₁ ≠ []) (hn₂ : p₂ ≠ [])
    (hhead : p₁.head? ≠ p₂.head?) (hnd₁ : (u :: p₁.map N.head).Nodup)
    (hnd₂ : (u :: p₂.map N.head).Nodup) (hdis : ∀ z ∈ p₁.map N.head, z ∈ p₂.map N.head → z = v) :
    wlen (N.graph fun d => Nc * cap d + L + w d) p₁ ≠
      wlen (N.graph fun d => Nc * cap d + L + w d) p₂ := by
  set G := N.graph fun d => Nc * cap d + L + w d
  set cl := p₁ ++ (p₂.map N.rev).reverse with hcl
  obtain ⟨a₁, r₁, rfl⟩ := List.exists_cons_of_ne_nil hn₁
  obtain ⟨b₁, r₂, rfl⟩ := List.exists_cons_of_ne_nil hn₂
  have hab : a₁ ≠ b₁ := fun h => hhead (by simp [h])
  have hwc : IsWalk G u cl u := hp₁.append (walk_rev hp₂)
  have hlen : cl.length = (a₁ :: r₁).length + (b₁ :: r₂).length := by simp [cl]; omega
  have h2 : 2 ≤ cl.length := by rw [hlen]; simp; omega
  -- the tails of the cycle are distinct
  have ht₁ := walk_tails hp₁
  have hnd : (cl.map N.tail).Nodup := by
    have e : cl.map N.tail = (a₁ :: r₁).map N.tail ++ ((b₁ :: r₂).map N.head).reverse := by
      simp [cl, List.map_reverse, Function.comp_def]
    rw [e, List.nodup_append]
    have hn1 : ((a₁ :: r₁).map N.tail).Nodup := by
      have := hnd₁; rw [← ht₁] at this; exact (List.nodup_append.1 this).1
    have hvn : v ∉ (a₁ :: r₁).map N.tail := by
      have := hnd₁; rw [← ht₁] at this
      have := (List.nodup_append.1 this).2.2
      intro hv; exact this _ hv _ (by simp) rfl
    refine ⟨hn1, List.nodup_reverse.2 (List.nodup_cons.1 hnd₂).2, fun z hz z' hz' hzz => ?_⟩
    subst hzz
    rw [List.mem_reverse] at hz'
    have hz0 : z ∈ u :: (a₁ :: r₁).map N.head := by
      rw [← ht₁]; exact List.mem_append_left _ hz
    rcases List.mem_cons.1 hz0 with rfl | hz0
    · exact (List.nodup_cons.1 hnd₂).1 hz'
    · exact hvn (by rw [← hdis z hz0 hz']; exact hz)
  have hC : N.IsSCycle cl.length (fun t => cl.getD t a₁) := by
    refine CombMap.isSCycle_of_list a₁ h2 (walk_step hwc) ?_ hnd ?_
    · rw [walk_last hwc (by omega), walk_first hwc (by omega)]
    · intro h
      have hr1 : r₁ = [] := by
        rw [hlen] at h; simp at h; exact List.eq_nil_of_length_eq_zero (by omega)
      have hr2 : r₂ = [] := by
        rw [hlen] at h; simp at h; exact List.eq_nil_of_length_eq_zero (by omega)
      subst hr1 hr2
      simp only [cl, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
      intro he
      exact hab (N.rev_injective he).symm
  obtain ⟨hS0, hSle⟩ := CombMap.cycle_curl hM hrot hC hw hcurl
  rw [sum_range_getD] at hS0 hSle
  have hS : (cl.map w).sum = ((a₁ :: r₁).map w).sum - ((b₁ :: r₂).map w).sum := by
    have hw' : ∀ d, w (N.rev d) = - w d := hw
    simp only [cl, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
      List.map_map]
    have : ((b₁ :: r₂).map (w ∘ N.rev)).sum = - ((b₁ :: r₂).map w).sum := by
      rw [show (w ∘ N.rev) = fun d => - w d from funext hw']
      generalize b₁ :: r₂ = l
      induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [this]; ring
  rw [hS] at hS0 hSle
  -- the lengths of the two paths are below the number of vertices
  have hl₁ := hnd₁.length_le_card
  have hl₂ := hnd₂.length_le_card
  simp only [List.length_cons, List.length_map] at hl₁ hl₂
  intro heq
  rw [wlen_split, wlen_split] at heq
  set S := ((a₁ :: r₁).map w).sum - ((b₁ :: r₂).map w).sum
  set Δc := ((a₁ :: r₁).map cap).sum - ((b₁ :: r₂).map cap).sum
  set k₁ := (a₁ :: r₁).length
  set k₂ := (b₁ :: r₂).length
  have hk₁ : (k₁ : ℤ) + 1 ≤ Fintype.card V := by
    simp only [k₁, List.length_cons]; exact_mod_cast hl₁
  have hk₂ : (k₂ : ℤ) + 1 ≤ Fintype.card V := by
    simp only [k₂, List.length_cons]; exact_mod_cast hl₂
  have hk₁0 : (1 : ℤ) ≤ k₁ := by simp [k₁]
  have hk₂0 : (1 : ℤ) ≤ k₂ := by simp [k₂]
  have hX : Nc * Δc + (L * ((k₁ : ℤ) - k₂) + S) = 0 := by
    simp only [Δc, S]; linarith
  have hLpos : 0 < L := lt_of_le_of_lt (abs_nonneg _) (lt_of_le_of_lt hSle hL)
  have hSL : |S| < L := lt_of_le_of_lt hSle hL
  rw [abs_lt] at hSL
  have hb1 : L * ((k₁ : ℤ) - k₂) ≤ L * (Fintype.card V - 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hLpos.le
  have hb2 : L * (2 - Fintype.card V) ≤ L * ((k₁ : ℤ) - k₂) :=
    mul_le_mul_of_nonneg_left (by linarith) hLpos.le
  have hXlt : |L * ((k₁ : ℤ) - k₂) + S| < Nc := by
    rw [abs_lt]; constructor <;> nlinarith
  rw [abs_lt] at hXlt
  have hΔc : Δc = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : Nc * Δc ≤ - Nc := by nlinarith
      linarith
    · have : Nc ≤ Nc * Δc := by nlinarith
      linarith
  rw [hΔc, mul_zero, zero_add] at hX
  have hk : (k₁ : ℤ) - k₂ = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : L * ((k₁ : ℤ) - k₂) ≤ - L := by nlinarith
      linarith
    · have : L ≤ L * ((k₁ : ℤ) - k₂) := by nlinarith
      linarith
  rw [hk, mul_zero, zero_add] at hX
  exact hS0 hX

/-- **Unique least walks for the lengths `N c + L + w`** in a plane map with transitive
rotations: among the walks with darts in `Q` (on which the lengths are positive), two least
walks with the same ends are equal. -/
theorem curl_unique (hM : N.IsPlane) (hrot : N.RotTrans) {w : D → ℤ} (hw : N.IsAntisymm w)
    {f₀ : F} (hcurl : ∀ f, f ≠ f₀ → 0 < N.curl w f) {L Nc : ℤ}
    (hL : ∑ f ∈ univ.erase f₀, N.curl w f < L) (hN : L * Fintype.card V ≤ Nc) (cap : D → ℤ)
    {Q : D → Prop} (hpos : ∀ d, Q d → 0 < Nc * cap d + L + w d) {x y : V} {l₁ l₂ : List D}
    (h₁ : IsMinW (N.graph fun d => Nc * cap d + L + w d) Q x y l₁)
    (h₂ : IsMinW (N.graph fun d => Nc * cap d + L + w d) Q x y l₂) : l₁ = l₂ :=
  minW_unique hpos (fun u v p₁ p₂ hp₁ hp₂ _ _ hn₁ hn₂ hh hnd₁ hnd₂ hdis =>
    curl_sep hM hrot hw hcurl hL hN cap u v p₁ p₂ hp₁ hp₂ hn₁ hn₂ hh hnd₁ hnd₂ hdis) h₁ h₂

end Plane

end STFlow

end PlanarFlow
