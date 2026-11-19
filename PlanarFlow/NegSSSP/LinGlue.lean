module

public import PlanarFlow.Monge.RowMin

/-!
# The linear bookkeeping of a node of the negative-length recursion, on the machine

Machine programs for the glue between the subroutine calls of a node (`NegCosts.lin`), on a
plain encoding of the node: the darts numbered `0, …, m - 1` with their tails, heads and sides
(natural memory) and lengths (real memory), the vertices numbered `0, …, w - 1` with the
potentials `δ₀`, `δ₁` of the two parts (real memory).

* `forLoop_exec`: a counted loop with a per-iteration invariant (the common pattern).
* `redProg`: the reduced lengths `ℓ d + δ (tail d) - δ (head d)` (`redProg_exec`, `17 m + 3`
  steps).
* `bdryProg`: the vertices `v < w` that are an end of a dart of each side, listed in increasing
  order (`bList`), by marks cleared, set and scanned (`bdryProg_exec`, `15 m + 23 w + 12` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-- **A counted loop** `while r_a < r_bR do body`, the body advancing `r_a` by one and keeping
`r_bR = n`, with an invariant `J i` after `i` iterations and a body cost at most `K`. -/
theorem forLoop_exec {a bR : ℕ} {body : Stmt} (J : ℕ → Config → Prop) {n K : ℕ} (c : Config)
    (hc : WordsBounded W c) (ha : c.nreg a = 0) (hb : c.nreg bR = n) (hJ : J 0 c)
    (hbody : ∀ i c, i < n → WordsBounded W c → c.nreg a = i → c.nreg bR = n → J i c →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ K ∧ c'.nreg a = i + 1 ∧ c'.nreg bR = n ∧ J (i + 1) c') :
    ∃ c' k, Exec P W (.whileLtN a bR body) c c' k ∧ k ≤ (K + 2) * n + 2 ∧
      WordsBounded W c' ∧ J n c' := by
  refine spec_while (fun c => WordsBounded W c ∧ c.nreg a ≤ n ∧ c.nreg bR = n ∧ J (c.nreg a) c)
    (fun c => (K + 2) * (n - c.nreg a)) (fun c h => h.1) ?_ ⟨hc, by omega, hb, by rw [ha]; exact hJ⟩
    ?_
  · intro c₁ ⟨hw₁, hle, hb₁, hJ₁⟩ hlt
    rw [hb₁] at hlt
    obtain ⟨c₂, k, hex, hk, ha₂, hb₂, hJ₂⟩ := hbody _ c₁ hlt hw₁ rfl hb₁ hJ₁
    refine ⟨c₂, k, hex, ⟨hex.wb_right, by omega, hb₂, by rw [ha₂]; exact hJ₂⟩, ?_⟩
    rw [ha₂]
    have := mul_pred_add (a := K + 2) (x := n - c₁.nreg a) (by omega)
    rw [show n - c₁.nreg a - 1 = n - (c₁.nreg a + 1) by omega] at this
    omega
  · intro c₂ k₂ ⟨hw₂, hle, hb₂, hJ₂⟩ hn hk₂
    rw [hb₂] at hn
    have e : c₂.nreg a = n := by omega
    rw [e] at hJ₂
    refine ⟨?_, hw₂, hJ₂⟩
    rw [ha] at hk₂; simpa using hk₂

/-! ### The reduced lengths -/

/-- The body of `redProg` at the dart `r210`: `R[d] := ℓ[d] + δ[T[d]] - δ[H[d]]`. The bases:
`r201` tails, `r202` heads (natural), `r203` lengths, `r204` potentials, `r205` output (real);
`r10 = 1`. -/
def redBody : Stmt :=
  block [.addN 211 201 210, .loadN 212 211, .addN 211 202 210, .loadN 213 211,
    .addN 211 203 210, .loadR 200 211, .addN 211 204 212, .loadR 201 211,
    .addN 211 204 213, .loadR 202 211, .addR 200 200 201, .subR 200 200 202,
    .addN 211 205 210, .storeR 211 200, .addN 210 210 10]

/-- **The reduced lengths** of the darts `0, …, r200 - 1`. -/
def redProg : Stmt := .seq (.instr (.constN 210 0)) (.whileLtN 210 200 redBody)

/-- The data of `redProg`: the registers, and the arrays read. -/
structure RedIn (m w Tb Hb Lb δb Rb : ℕ) (T H : ℕ → ℕ) (L δ : ℕ → ℝ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r200 : c.nreg 200 = m
  r201 : c.nreg 201 = Tb
  r202 : c.nreg 202 = Hb
  r203 : c.nreg 203 = Lb
  r204 : c.nreg 204 = δb
  r205 : c.nreg 205 = Rb
  tl : ∀ d < m, c.nmem (Tb + d) = T d
  hd : ∀ d < m, c.nmem (Hb + d) = H d
  ln : ∀ d < m, c.rmem (Lb + d) = L d
  pt : ∀ v < w, c.rmem (δb + v) = δ v

/-- The layout of `redProg`: the output region `[Rb, Rb + m)` apart from the lengths and the
potentials, the ends below `w`, the addresses below the word bound. -/
structure RedLay (m w Tb Hb Lb δb Rb W : ℕ) (T H : ℕ → ℕ) : Prop where
  rl : Rb + m ≤ Lb ∨ Lb + m ≤ Rb
  rp : Rb + m ≤ δb ∨ δb + w ≤ Rb
  ends : ∀ d < m, T d < w ∧ H d < w
  wT : Tb + m ≤ W
  wH : Hb + m ≤ W
  wL : Lb + m ≤ W
  wP : δb + w ≤ W
  wR : Rb + m ≤ W

theorem redBody_exec {m w Tb Hb Lb δb Rb : ℕ} {T H : ℕ → ℕ} {L δ : ℕ → ℝ}
    (hL : RedLay m w Tb Hb Lb δb Rb W T H) (c : Config) (hc : WordsBounded W c)
    (hI : RedIn m w Tb Hb Lb δb Rb T H L δ c) {d : ℕ} (hd : d < m) (h210 : c.nreg 210 = d) :
    ∃ c' k, Exec P W redBody c c' k ∧ k ≤ 15 ∧
      (c'.nreg 210 = d + 1 ∧ (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r < 200 ∨ 202 < r → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        c'.rmem = (fun a => if a = Rb + d then L d + δ (T d) - δ (H d) else c.rmem a) ∧
        c'.output = c.output) := by
  have hw := hL.wR
  obtain ⟨e1, e2⟩ := hL.ends d hd
  unfold redBody
  have ht := hI.tl d hd
  have hh := hI.hd d hd
  have := hL.wT; have := hL.wH; have := hL.wL; have := hL.wP
  exec_block
  all_goals try ((try config_simp); simp only [hI.r10, hI.r201, hI.r202, hI.r203, hI.r204,
    hI.r205, h210, ht, hh]; omega)
  config_simp
  and_intros
  all_goals first
    | omega
    | rfl
    | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | (rw [h210, hI.r10])
    | (funext a
       simp only [upd_apply, hI.r203, hI.r204, hI.r205, h210, hI.r201, hI.r202, ht, hh,
         hI.ln d hd, hI.pt _ e1, hI.pt _ e2])

/-- **The reduced lengths.** From `RedIn` (with `r200 = m`), `redProg` writes
`L d + δ (T d) - δ (H d)` at `Rb + d` for every `d < m`, within `17 m + 3` steps, changing only
the real memory in `[Rb, Rb + m)`, the natural registers `210, …, 213` and the real registers
`200, 201, 202`. -/
theorem redProg_exec {m w Tb Hb Lb δb Rb : ℕ} {T H : ℕ → ℕ} {L δ : ℕ → ℝ}
    (hL : RedLay m w Tb Hb Lb δb Rb W T H) (c : Config) (hc : WordsBounded W c)
    (hI : RedIn m w Tb Hb Lb δb Rb T H L δ c) :
    ∃ c' k, Exec P W redProg c c' k ∧ k ≤ 17 * m + 3 ∧
      ((∀ d < m, c'.rmem (Rb + d) = L d + δ (T d) - δ (H d)) ∧
        (∀ a, (a < Rb ∨ Rb + m ≤ a) → c'.rmem a = c.rmem a) ∧ c'.nmem = c.nmem ∧
        (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) ∧
        (∀ r, r < 200 ∨ 202 < r → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have hw := hL.wR
  have hrl := hL.rl; have hrp := hL.rp
  unfold redProg
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 210 0 (by omega)) fun hw₁ => ?_
  set c₁ : Config := { c with nreg := upd c.nreg 210 0 }
  have hn₁ : ∀ r, r ≠ 210 → c₁.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) ∧
    (∀ r, r < 200 ∨ 202 < r → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
    (∀ a, c'.rmem a = if Rb ≤ a ∧ a < Rb + i then L (a - Rb) + δ (T (a - Rb)) - δ (H (a - Rb))
      else c.rmem a) ∧ c'.output = c.output
  have hJ0 : J 0 c₁ := ⟨fun r hr => hn₁ r (by omega), fun _ _ => rfl, rfl,
    fun a => by simp only [c₁]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))], rfl⟩
  obtain ⟨c₂, k, hex, hk, -, hJ⟩ := forLoop_exec (P := P) (a := 210) (bR := 200)
    (body := redBody) J c₁ hw₁
    (by simp [c₁]) (by rw [hn₁ 200 (by omega)]; exact hI.r200) hJ0 (K := 15) (n := m)
    (fun i c' hi hw' ha hb ⟨fn, fr, fnm, frm, fo⟩ => by
      have hI' : RedIn m w Tb Hb Lb δb Rb T H L δ c' :=
        ⟨by rw [fn 10 (by omega)]; exact hI.r10, by rw [fn 200 (by omega)]; exact hI.r200,
          by rw [fn 201 (by omega)]; exact hI.r201, by rw [fn 202 (by omega)]; exact hI.r202,
          by rw [fn 203 (by omega)]; exact hI.r203, by rw [fn 204 (by omega)]; exact hI.r204,
          by rw [fn 205 (by omega)]; exact hI.r205, fun d hd => by rw [fnm]; exact hI.tl d hd,
          fun d hd => by rw [fnm]; exact hI.hd d hd,
          fun d hd => by
            rw [frm, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact hI.ln d hd,
          fun v hv => by
            rw [frm, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact hI.pt v hv⟩
      obtain ⟨c'', k', hex', hk', h210, gn, gr, gnm, grm, go⟩ :=
        redBody_exec (P := P) hL c' hw' hI' hi ha
      refine ⟨c'', k', hex', hk', h210, by rw [gn 200 (by omega), hb], fun r hr => ?_,
        fun r hr => ?_, by rw [gnm, fnm], fun a => ?_, by rw [go, fo]⟩
      · rw [gn r hr, fn r hr]
      · rw [gr r hr, fr r hr]
      · rw [grm]
        simp only
        rw [frm]
        split_ifs with h1 h2 h3 <;> first | omega | (subst h1; simp) | rfl)
  refine ⟨_, _, hex, by omega, fun d hd => ?_, fun a ha => ?_, hJ.2.2.1, hJ.1, hJ.2.1, hJ.2.2.2.2⟩
  · rw [hJ.2.2.2.1, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; simp
  · rw [hJ.2.2.2.1, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-! ### The boundary and its enumeration -/

/-- Phase 1 of `bdryProg`: `M[a] := 0` for `a < 2w` (`r208` the base of the marks, `r214 = 2w`). -/
def bzBody : Stmt := block [.addN 211 208 210, .storeN 211 216, .addN 210 210 10]

/-- Phase 2: the dart `r210` marks its tail and head in the marks of its side `S[d]`
(`M[S[d] w + v] := 1`; `r206` the base of the sides, `r207 = w`). -/
def bmBody : Stmt :=
  block [.addN 211 206 210, .loadN 212 211, .mulN 212 212 207, .addN 212 212 208,
    .addN 211 201 210, .loadN 213 211, .addN 213 213 212, .storeN 213 10,
    .addN 211 202 210, .loadN 213 211, .addN 213 213 212, .storeN 213 10, .addN 210 210 10]

/-- Phase 3: the vertex `r210` is appended to the list at `r209` (length `r217`) when it is
marked on both sides. -/
def bsRead : Stmt :=
  block [.addN 211 208 210, .loadN 212 211, .addN 211 211 207, .loadN 213 211, .mulN 218 212 213]

/-- Phase 3 at the vertex `r210`. -/
def bsBody : Stmt :=
  .seq bsRead <|
  .seq (.ifLtN 218 10 .skip (block [.addN 219 209 217, .storeN 219 210, .addN 217 217 10])) <|
  .instr (.addN 210 210 10)

/-- **The boundary**: the vertices `v < w` that are an end of a dart of each side, listed in
increasing order at `r209`, their number in `r217`. -/
def bdryProg : Stmt :=
  .seq (block [.constN 216 0, .addN 214 207 207, .constN 210 0]) <|
  .seq (.whileLtN 210 214 bzBody) <|
  .seq (.instr (.constN 210 0)) <|
  .seq (.whileLtN 210 200 bmBody) <|
  .seq (.instr (.constN 210 0)) <| .seq (.instr (.constN 217 0)) <|
  .whileLtN 210 207 bsBody

/-- `v` is an end of a dart of side `s` among the first `i` darts. -/
def InSide (T H S : ℕ → ℕ) (i s v : ℕ) : Prop := ∃ d < i, S d = s ∧ (T d = v ∨ H d = v)

/-- The boundary vertices below `v`, in increasing order. -/
noncomputable def bList (T H S : ℕ → ℕ) (m v : ℕ) : List ℕ := by
  classical
  exact (List.range v).filter fun u => InSide T H S m 0 u ∧ InSide T H S m 1 u

/-- The data of `bdryProg`. -/
structure BdIn (m w Tb Hb Sb Mb Bb : ℕ) (T H S : ℕ → ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r200 : c.nreg 200 = m
  r201 : c.nreg 201 = Tb
  r202 : c.nreg 202 = Hb
  r206 : c.nreg 206 = Sb
  r207 : c.nreg 207 = w
  r208 : c.nreg 208 = Mb
  r209 : c.nreg 209 = Bb
  tl : ∀ d < m, c.nmem (Tb + d) = T d
  hd : ∀ d < m, c.nmem (Hb + d) = H d
  sd : ∀ d < m, c.nmem (Sb + d) = S d

/-- The layout of `bdryProg`: the marks `[Mb, Mb + 2w)` and the list `[Bb, Bb + w)` apart from
each other and from the arrays read; sides `0` or `1`, ends below `w`. -/
structure BdLay (m w Tb Hb Sb Mb Bb W : ℕ) (T H S : ℕ → ℕ) : Prop where
  ends : ∀ d < m, T d < w ∧ H d < w ∧ S d ≤ 1
  mT : Mb + 2 * w ≤ Tb ∨ Tb + m ≤ Mb
  mH : Mb + 2 * w ≤ Hb ∨ Hb + m ≤ Mb
  mS : Mb + 2 * w ≤ Sb ∨ Sb + m ≤ Mb
  bT : Bb + w ≤ Tb ∨ Tb + m ≤ Bb
  bH : Bb + w ≤ Hb ∨ Hb + m ≤ Bb
  bS : Bb + w ≤ Sb ∨ Sb + m ≤ Bb
  bM : Bb + w ≤ Mb ∨ Mb + 2 * w ≤ Bb
  wT : Tb + m ≤ W
  wH : Hb + m ≤ W
  wS : Sb + m ≤ W
  wM : Mb + 2 * w ≤ W
  wB : Bb + w ≤ W
  wm : m + 1 ≤ W
  ww : 2 * w + 1 ≤ W

/-- The common frame of the phases: the registers outside `210, …, 219`, the real state and the
output kept. -/
structure BFr (c c' : Config) : Prop where
  nreg : ∀ r, r < 210 ∨ 219 < r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem BFr.refl (c : Config) : BFr c c := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem BFr.trans {c c' c'' : Config} (h : BFr c c') (h' : BFr c' c'') : BFr c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

/-- **Phase 1**: the marks cleared. -/
theorem bz_exec {w Mb : ℕ} (hww : 2 * w + 1 ≤ W) (hwM : Mb + 2 * w ≤ W) (c : Config)
    (hc : WordsBounded W c) (h10 : c.nreg 10 = 1) (h208 : c.nreg 208 = Mb)
    (h214 : c.nreg 214 = 2 * w) (h216 : c.nreg 216 = 0) (h210 : c.nreg 210 = 0) :
    ∃ c' k, Exec P W (.whileLtN 210 214 bzBody) c c' k ∧ k ≤ 5 * (2 * w) + 2 ∧
      ((∀ a < 2 * w, c'.nmem (Mb + a) = 0) ∧
        (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 210 → r ≠ 211 → c'.nreg r = c.nreg r) ∧ BFr c c') := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r ≠ 210 → r ≠ 211 → c'.nreg r = c.nreg r) ∧ BFr c c' ∧
    (∀ a, c'.nmem a = if Mb ≤ a ∧ a < Mb + i then 0 else c.nmem a)
  obtain ⟨c', k, hex, hk, -, hJ⟩ := forLoop_exec (P := P) (a := 210) (bR := 214)
    (body := bzBody) J (K := 3) (n := 2 * w) c hc h210 h214
    ⟨fun _ _ _ => rfl, BFr.refl c,
      fun a => by rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]⟩
    (fun i c₁ hi hw₁ ha hb ⟨fn, fr, fm⟩ => by
      have e208 := fn 208 (by omega) (by omega)
      have e10 := fn 10 (by omega) (by omega)
      have e216 := fn 216 (by omega) (by omega)
      unfold bzBody
      exec_block
      all_goals try ((try config_simp); simp only [e208, e10, e216, h208, h10, h216, ha]; omega)
      dsimp only [J]
      config_simp
      and_intros
      · omega
      · rw [ha, e10, h10]
      · rw [hb]
      · intro r h1 h2; simp only [upd_apply]; split_ifs; exact fn r h1 h2
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
            exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro a
        simp only [upd_apply, e208, h208, ha, e216, h216, fm a]
        split_ifs <;> omega)
  refine ⟨c', k, hex, by omega, fun a ha => ?_, fun a ha => ?_, hJ.1, hJ.2.1⟩
  · rw [hJ.2.2, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  · rw [hJ.2.2, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

lemma inSide_zero (T H S : ℕ → ℕ) (s v : ℕ) : ¬ InSide T H S 0 s v := fun ⟨d, hd, _⟩ => by omega

lemma inSide_succ (T H S : ℕ → ℕ) (i s v : ℕ) :
    InSide T H S (i + 1) s v ↔ InSide T H S i s v ∨ (S i = s ∧ (T i = v ∨ H i = v)) := by
  constructor
  · rintro ⟨d, hd, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
    · exact Or.inl ⟨d, hd, h⟩
    · exact Or.inr h
  · rintro (⟨d, hd, h⟩ | h)
    · exact ⟨d, by omega, h⟩
    · exact ⟨i, by omega, h⟩

/-- The cell of the mark `(s, v)`. -/
lemma mark_cell {w s v s' v' : ℕ} (hs : s ≤ 1) (hv : v < w) (hs' : s' ≤ 1) (hv' : v' < w) :
    s * w + v = s' * w + v' ↔ s = s' ∧ v = v' := by
  constructor
  · intro h
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;>
      rcases (by omega : s' = 0 ∨ s' = 1) with rfl | rfl <;> simp at h ⊢ <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

lemma sw_le {s w : ℕ} (hs : s ≤ 1) : s * w ≤ w := by
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp

/-- **Phase 2**: the marks of the ends of the darts of each side. -/
theorem bm_exec {m w Tb Hb Sb Mb Bb : ℕ} {T H S : ℕ → ℕ}
    (hL : BdLay m w Tb Hb Sb Mb Bb W T H S) (c : Config) (hc : WordsBounded W c)
    (hI : BdIn m w Tb Hb Sb Mb Bb T H S c) (h210 : c.nreg 210 = 0)
    (hz : ∀ a < 2 * w, c.nmem (Mb + a) = 0) :
    ∃ c' k, Exec P W (.whileLtN 210 200 bmBody) c c' k ∧ k ≤ 15 * m + 2 ∧
      ((∀ s ≤ 1, ∀ v < w, c'.nmem (Mb + (s * w + v)) = if InSide T H S m s v then 1 else 0) ∧
        (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) ∧ BFr c c') := by
  have := hL.wT; have := hL.wH; have := hL.wS; have := hL.wM; have := hL.wm
  have := hL.mT; have := hL.mH; have := hL.mS
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 210 ∨ 213 < r → c'.nreg r = c.nreg r) ∧ BFr c c' ∧
    (∀ s ≤ 1, ∀ v < w, c'.nmem (Mb + (s * w + v)) = if InSide T H S i s v then 1 else 0) ∧
    (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → c'.nmem a = c.nmem a)
  have hJ0 : J 0 c := ⟨fun _ _ => rfl, BFr.refl c, fun s hs v hv => by
    rw [ite_eq_right_of_eq_false _ _ (eq_false (inSide_zero T H S s v))]
    exact hz _ (by have := sw_le (w := w) hs; omega), fun _ _ => rfl⟩
  obtain ⟨c', k, hex, hk, -, hJ⟩ := forLoop_exec (P := P) (a := 210) (bR := 200)
    (body := bmBody) J (K := 13) (n := m) c hc h210 hI.r200 hJ0
    (fun i c₁ hi hw₁ ha hb ⟨fn, fr, fm, fo⟩ => by
      obtain ⟨t1, t2, t3⟩ := hL.ends i hi
      have g : ∀ r, r < 210 → c₁.nreg r = c.nreg r := fun r hr => fn r (by omega)
      have e201 := (g 201 (by omega)).trans hI.r201
      have e202 := (g 202 (by omega)).trans hI.r202
      have e206 := (g 206 (by omega)).trans hI.r206
      have e207 := (g 207 (by omega)).trans hI.r207
      have e208 := (g 208 (by omega)).trans hI.r208
      have e10 := (g 10 (by omega)).trans hI.r10
      have xT : c₁.nmem (Tb + i) = T i := by rw [fo _ (by omega)]; exact hI.tl i hi
      have xH : c₁.nmem (Hb + i) = H i := by rw [fo _ (by omega)]; exact hI.hd i hi
      have xS : c₁.nmem (Sb + i) = S i := by rw [fo _ (by omega)]; exact hI.sd i hi
      have hsw : S i * w ≤ w := sw_le t3
      have xH' : upd c₁.nmem (T i + (S i * w + Mb)) 1 (Hb + i) = H i := by
        rw [upd_other _ _ _ (by omega)]; exact xH
      unfold bmBody
      exec_block
      all_goals try
        ((try config_simp); simp only [e201, e202, e206, e207, e208, e10, ha, xT, xS, xH']
         omega)
      dsimp only [J]
      config_simp
      simp only [e201, e202, e206, e207, e208, e10, ha, xT, xS, xH']
      and_intros
      · omega
      · trivial
      · rw [hb]
      · intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact fn r hr
      · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
            exact fr.nreg r hr, fr.rreg, fr.rmem, fr.out⟩
      · intro s' hs' v hv
        have c1 := mark_cell (w := w) hs' hv t3 t1
        have c2 := mark_cell (w := w) hs' hv t3 t2
        simp only [upd_apply, fm s' hs' v hv, inSide_succ]
        by_cases q2 : s' = S i ∧ v = H i
        · obtain ⟨rfl, rfl⟩ := q2
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
            ite_eq_left_of_eq_true _ _ (eq_true (Or.inr ⟨rfl, Or.inr rfl⟩))]
        · have n2 : s' * w + v ≠ S i * w + H i := fun h => q2 (c2.1 h)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          by_cases q1 : s' = S i ∧ v = T i
          · obtain ⟨rfl, rfl⟩ := q1
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true (Or.inr ⟨rfl, Or.inl rfl⟩))]
          · have n1 : s' * w + v ≠ S i * w + T i := fun h => q1 (c1.1 h)
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
            by_cases q0 : InSide T H S i s' v
            · rw [ite_eq_left_of_eq_true _ _ (eq_true q0),
                ite_eq_left_of_eq_true _ _ (eq_true (Or.inl q0))]
            · have q : ¬ (InSide T H S i s' v ∨ (S i = s' ∧ (T i = v ∨ H i = v))) := by
                rintro (h | ⟨h1, h2 | h2⟩)
                · exact q0 h
                · exact q1 ⟨h1.symm, h2.symm⟩
                · exact q2 ⟨h1.symm, h2.symm⟩
              rw [ite_eq_right_of_eq_false _ _ (eq_false q0),
                ite_eq_right_of_eq_false _ _ (eq_false q)]
      · intro a ha'
        simp only [upd_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a ha'])
  exact ⟨c', k, hex, by omega, hJ.2.2.1, hJ.2.2.2, hJ.1, hJ.2.1⟩

/-- `v` is a boundary vertex (an end of a dart of each side). -/
def IsBd (T H S : ℕ → ℕ) (m v : ℕ) : Prop := InSide T H S m 0 v ∧ InSide T H S m 1 v

lemma bList_succ (T H S : ℕ → ℕ) (m v : ℕ) :
    bList T H S m (v + 1) = bList T H S m v ++ (if IsBd T H S m v then [v] else []) := by
  unfold bList IsBd
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : InSide T H S m 0 v ∧ InSide T H S m 1 v
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; simp [h]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; simp [h]

lemma bList_length_le (T H S : ℕ → ℕ) (m v : ℕ) : (bList T H S m v).length ≤ v := by
  unfold bList
  exact (List.length_filter_le _ _).trans (by simp)

/-- The marks read at the vertex `v`. -/
theorem bsRead_exec {m w Mb : ℕ} {T H S : ℕ → ℕ} (hwM : Mb + 2 * w ≤ W) (c : Config)
    (hc : WordsBounded W c) (h207 : c.nreg 207 = w) (h208 : c.nreg 208 = Mb) {v : ℕ}
    (hv : v < w) (h210 : c.nreg 210 = v)
    (hM : ∀ s ≤ 1, ∀ v < w, c.nmem (Mb + (s * w + v)) = if InSide T H S m s v then 1 else 0) :
    ∃ c' k, Exec P W bsRead c c' k ∧ k ≤ 5 ∧
      (c'.nreg 218 = (if IsBd T H S m v then 1 else 0) ∧
        (∀ r, r ≠ 211 → r ≠ 212 → r ≠ 213 → r ≠ 218 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ BFr c c') := by
  have m0 := hM 0 (by omega) v hv
  have m1 := hM 1 (by omega) v hv
  rw [show Mb + (0 * w + v) = Mb + v by ring] at m0
  rw [show Mb + (1 * w + v) = Mb + v + w by ring] at m1
  have hx : WordsBounded W c := hc
  unfold bsRead
  exec_block
  all_goals try ((try config_simp); simp only [h207, h208, h210, m0, m1]; (try split_ifs) <;> omega)
  config_simp
  and_intros
  · omega
  · simp only [h207, h208, h210, m0, m1]
    unfold IsBd
    by_cases a : InSide T H S m 0 v <;> by_cases b : InSide T H S m 1 v <;> simp [a, b]
  · intro r h1 h2 h3 h4; simp only [upd_apply]; split_ifs; rfl
  · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> omega, rfl, rfl, rfl⟩

/-- **Phase 3**: the boundary vertices listed. -/
theorem bs_exec {m w Mb Bb : ℕ} {T H S : ℕ → ℕ} (hwM : Mb + 2 * w ≤ W) (hwB : Bb + w ≤ W)
    (hBM : Bb + w ≤ Mb ∨ Mb + 2 * w ≤ Bb) (c : Config)
    (hc : WordsBounded W c) (h10 : c.nreg 10 = 1) (h207 : c.nreg 207 = w)
    (h208 : c.nreg 208 = Mb) (h209 : c.nreg 209 = Bb) (h210 : c.nreg 210 = 0)
    (h217 : c.nreg 217 = 0)
    (hM : ∀ s ≤ 1, ∀ v < w, c.nmem (Mb + (s * w + v)) = if InSide T H S m s v then 1 else 0) :
    ∃ c' k, Exec P W (.whileLtN 210 207 bsBody) c c' k ∧ k ≤ 13 * w + 2 ∧
      (c'.nreg 217 = (bList T H S m w).length ∧
        (∀ j < (bList T H S m w).length, c'.nmem (Bb + j) = (bList T H S m w).getD j 0) ∧
        (∀ a, (a < Bb ∨ Bb + w ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 210 ∨ 219 < r → c'.nreg r = c.nreg r) ∧ BFr c c') := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 210 ∨ 219 < r → c'.nreg r = c.nreg r) ∧ BFr c c' ∧
    c'.nreg 217 = (bList T H S m i).length ∧
    (∀ j < (bList T H S m i).length, c'.nmem (Bb + j) = (bList T H S m i).getD j 0) ∧
    (∀ a, (a < Bb ∨ Bb + w ≤ a) → c'.nmem a = c.nmem a)
  have hJ0 : J 0 c := ⟨fun _ _ => rfl, BFr.refl c, by rw [h217]; simp [bList],
    fun j hj => by simp [bList] at hj, fun _ _ => rfl⟩
  obtain ⟨c', k, hex, hk, -, hJ⟩ := forLoop_exec (P := P) (a := 210) (bR := 207)
    (body := bsBody) J (K := 11) (n := w) c hc h210 h207 hJ0
    (fun i c₁ hi hw₁ ha hb ⟨fn, fr, f217, fl, fo⟩ => by
      have g : ∀ r, r < 210 → c₁.nreg r = c.nreg r := fun r hr => fn r (by omega)
      have e207 := (g 207 (by omega)).trans h207
      have e208 := (g 208 (by omega)).trans h208
      have e209 := (g 209 (by omega)).trans h209
      have e10 := (g 10 (by omega)).trans h10
      have hM₁ : ∀ s ≤ 1, ∀ v < w, c₁.nmem (Mb + (s * w + v)) =
          if InSide T H S m s v then 1 else 0 := fun s hs v hv => by
        rw [fo _ (by have := sw_le (w := w) hs; omega)]; exact hM s hs v hv
      have hlen := bList_length_le T H S m i
      unfold bsBody
      refine spec_seq ?_
      refine spec_use (bsRead_exec (P := P) (m := m) hwM c₁ hw₁ e207 e208 hi ha hM₁) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨q218, qn, qm, qf⟩
      have d : ∀ r, r ≠ 211 → r ≠ 212 → r ≠ 213 → r ≠ 218 → c₂.nreg r = c₁.nreg r := qn
      have k10 : c₂.nreg 10 = 1 := (d 10 (by omega) (by omega) (by omega) (by omega)).trans e10
      have k209 : c₂.nreg 209 = Bb :=
        (d 209 (by omega) (by omega) (by omega) (by omega)).trans e209
      have k217 : c₂.nreg 217 = (bList T H S m i).length :=
        (d 217 (by omega) (by omega) (by omega) (by omega)).trans f217
      have k210 : c₂.nreg 210 = i := (d 210 (by omega) (by omega) (by omega) (by omega)).trans ha
      have k207 : c₂.nreg 207 = w := (d 207 (by omega) (by omega) (by omega) (by omega)).trans hb
      have kg : ∀ r, r < 210 ∨ 219 < r → c₂.nreg r = c.nreg r := fun r hr =>
        (d r (by omega) (by omega) (by omega) (by omega)).trans (fn r hr)
      refine spec_seq ?_
      by_cases hB : IsBd T H S m i
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hB)] at q218
        have ht : ¬ c₂.nreg 218 < c₂.nreg 10 := by rw [q218, k10]; omega
        refine spec_ifLtN_false ht ?_
        exec_block
        all_goals try ((try config_simp); simp only [k209, k217, k210, k10]; omega)
        refine spec_instr (Exec.addN ‹_› 210 210 10 (by config_simp; rw [k210, k10]; omega))
          fun hw₃ => ?_
        dsimp only [J]
        config_simp
        rw [bList_succ, ite_eq_left_of_eq_true _ _ (eq_true hB)]
        simp only [List.length_append, List.length_singleton, k209, k217, k210, k10, k207]
        and_intros
        all_goals try trivial
        · omega
        · intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact kg r hr
        · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
            exact (qf.nreg r hr).trans (fr.nreg r hr), qf.rreg.trans fr.rreg,
            qf.rmem.trans fr.rmem, qf.out.trans fr.out⟩
        · intro j hj
          simp only [upd_apply, qm]
          by_cases hj' : j < (bList T H S m i).length
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fl j hj',
              List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hj']
          · have : j = (bList T H S m i).length := by omega
            subst this
            rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), List.getD_eq_getElem?_getD]
            simp
        · intro a ha'
          simp only [upd_apply, qm]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a ha']
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hB)] at q218
        have ht : c₂.nreg 218 < c₂.nreg 10 := by rw [q218, k10]; omega
        refine spec_ifLtN_true ht ?_
        refine spec_skip hw₂ ?_
        refine spec_instr (Exec.addN hw₂ 210 210 10 (by rw [k210, k10]; omega)) fun hw₃ => ?_
        dsimp only [J]
        config_simp
        rw [bList_succ, ite_eq_right_of_eq_false _ _ (eq_false hB)]
        simp only [List.append_nil, k217, k210, k10, k207]
        and_intros
        all_goals try trivial
        · omega
        · intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact kg r hr
        · exact ⟨fun r hr => by simp only [upd_apply]; split_ifs <;> first | omega |
            exact (qf.nreg r hr).trans (fr.nreg r hr), qf.rreg.trans fr.rreg,
            qf.rmem.trans fr.rmem, qf.out.trans fr.out⟩
        · intro j hj; rw [qm]; exact fl j hj
        · intro a ha'; rw [qm]; exact fo a ha')
  exact ⟨c', k, hex, by omega, hJ.2.2.1, hJ.2.2.2.1, hJ.2.2.2.2, hJ.1, hJ.2.1⟩

/-- **The boundary on the machine.** From `BdIn` (the tails, heads and sides of the darts
`0, …, m - 1`), `bdryProg` lists at `Bb` the vertices `v < w` that are an end of a dart of each
side, in increasing order (`bList`), their number in `r217`, within `15 m + 23 w + 12` steps. -/
theorem bdryProg_exec {m w Tb Hb Sb Mb Bb : ℕ} {T H S : ℕ → ℕ}
    (hL : BdLay m w Tb Hb Sb Mb Bb W T H S) (c : Config) (hc : WordsBounded W c)
    (hI : BdIn m w Tb Hb Sb Mb Bb T H S c) :
    ∃ c' k, Exec P W bdryProg c c' k ∧ k ≤ 15 * m + 23 * w + 12 ∧
      (c'.nreg 217 = (bList T H S m w).length ∧
        (∀ j < (bList T H S m w).length, c'.nmem (Bb + j) = (bList T H S m w).getD j 0) ∧
        (∀ a, (a < Mb ∨ Mb + 2 * w ≤ a) → (a < Bb ∨ Bb + w ≤ a) → c'.nmem a = c.nmem a) ∧
        BFr c c') := by
  have := hL.wM; have := hL.ww; have := hL.wB; have := hL.wm
  unfold bdryProg
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r207]); omega)
  refine spec_seq ?_
  refine spec_use (bz_exec (P := P) (w := w) (Mb := Mb) (by omega) (by omega) _ ‹_›
    (by config_simp; exact hI.r10) (by config_simp; exact hI.r208)
    (by config_simp; rw [hI.r207]; ring) (by config_simp) (by config_simp)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨z₁, m₁, n₁, f₁⟩
  have g₁ : ∀ r, r < 210 → c₁.nreg r = c.nreg r := fun r hr => by
    rw [n₁ r (by omega) (by omega)]; config_simp
    simp only [upd_apply]; split_ifs <;> omega
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 210 0 (by omega)) fun hw₂ => ?_
  have hI₂ : BdIn m w Tb Hb Sb Mb Bb T H S { c₁ with nreg := upd c₁.nreg 210 0 } := by
    have g : ∀ r, r < 210 → (upd c₁.nreg 210 0) r = c.nreg r := fun r hr => by
      rw [upd_other _ _ _ (by omega), g₁ r hr]
    refine ⟨(g 10 (by omega)).trans hI.r10, (g 200 (by omega)).trans hI.r200,
      (g 201 (by omega)).trans hI.r201, (g 202 (by omega)).trans hI.r202,
      (g 206 (by omega)).trans hI.r206, (g 207 (by omega)).trans hI.r207,
      (g 208 (by omega)).trans hI.r208, (g 209 (by omega)).trans hI.r209,
      fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
    · show c₁.nmem _ = _; rw [m₁ _ (by have := hL.mT; omega)]; config_simp; exact hI.tl d hd
    · show c₁.nmem _ = _; rw [m₁ _ (by have := hL.mH; omega)]; config_simp; exact hI.hd d hd
    · show c₁.nmem _ = _; rw [m₁ _ (by have := hL.mS; omega)]; config_simp; exact hI.sd d hd
  refine spec_seq ?_
  refine spec_use (bm_exec (P := P) hL _ hw₂ hI₂ (by config_simp) z₁) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨mk₃, m₃, n₃, f₃⟩
  have g₃ : ∀ r, r < 210 → c₃.nreg r = c.nreg r := fun r hr => by
    rw [n₃ r (by omega)]; show (upd c₁.nreg 210 0) r = _; rw [upd_other _ _ _ (by omega), g₁ r hr]
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₃ 210 0 (by omega)) fun hw₅ => ?_
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₅ 217 0 (by omega)) fun hw₆ => ?_
  refine spec_use (bs_exec (P := P) (m := m) (T := T) (H := H) (S := S) (w := w) (Mb := Mb)
    (Bb := Bb) (by omega) (by omega) hL.bM _ hw₆ (by config_simp; rw [g₃ 10 (by omega), hI.r10])
    (by config_simp; rw [g₃ 207 (by omega), hI.r207]) (by config_simp; rw [g₃ 208 (by omega),
      hI.r208]) (by config_simp; rw [g₃ 209 (by omega), hI.r209]) (by config_simp)
    (by config_simp) (fun s hs v hv => by config_simp; exact mk₃ s hs v hv)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨l₄, e₄, m₄, n₄, f₄⟩
  refine ⟨by omega, l₄, e₄, fun a ha hb => ?_, ?_⟩
  · rw [m₄ a hb]; config_simp; rw [m₃ a ha]; show c₁.nmem a = _; rw [m₁ a ha]
  · refine ⟨fun r hr => ?_, f₄.rreg.trans (f₃.rreg.trans f₁.rreg),
      f₄.rmem.trans (f₃.rmem.trans f₁.rmem), f₄.out.trans (f₃.out.trans f₁.out)⟩
    rw [n₄ r hr]
    show (upd (upd c₃.nreg 210 0) 217 0) r = _
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), n₃ r (by omega)]
    show (upd c₁.nreg 210 0) r = _
    rw [upd_other _ _ _ (by omega)]
    rcases hr with hr | hr
    · exact g₁ r hr
    · rw [n₁ r (by omega) (by omega)]
      show (upd (upd (upd c.nreg 216 0) 214 (c.nreg 207 + c.nreg 207)) 210 0) r = _
      rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]

end NegSSSP

end PlanarFlow
