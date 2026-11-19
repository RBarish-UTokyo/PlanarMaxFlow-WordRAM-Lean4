module

public import PlanarFlow.DynTree.CodeSplay
public import WordRAM.Machine.RealsModNat

/-!
# Dynamic trees: bounded real comparisons in the recomputation and the rotation

The only real tests of the link-cut tree are the conditional moves `cmov1`, `cmov2` of
`recompS` (and the comparison bit of the queries `min`/`min2`, `PlanarFlow/DynTree/CmpOK.lean`).
`recompS` at `u` compares the stored values of `u` with the minima of its children as `u` reads
them (`minA`, `minA2`). For the simulation of the reals modulo a word
(`WordRAM.Machine.ModNat.CmpOK`) the compared differences must be bounded.

* `ModNat.CmpOK.seq_ex`: the rule of a sequence whose first part has a known execution (the
  big-step semantics is deterministic, `Machine.Exec.det`).
* `NearAt V M u O1 O2`: the values compared at `u` (both channels), shifted by `O1`, `O2`, are at
  most `V` in absolute value; `RecNear V M u` for some shifts. **`recompS_cmpOK`**: then every
  run of `recompS` at `u` compares numbers at distance at most `2 V`.
* `RotNear V M x`: the recomputations of the rotation of `x` (at its parent `y` on `rotP x M`,
  then at `x`) are near; **`rotS_cmpOK`**. **`rotNear_of_L`**, **`rotNear_of_R`**: they are when
  the values around `x`, `y` (`x` a left, resp. right child of `y`), shifted by the tags along
  the path, are bounded (`NearRot`): the rotation moves the tags as in the delta representation,
  so the compared numbers stay shifted values of the same nodes.
* `NearAt.cmb`: the minima recomputed from near values are near.
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs VT

/-! ### Generic rules -/

section generic
variable {P : Input} {W H : ℕ}

theorem ModNat.CmpOK.seq_ex {s t : Stmt} {c : Config} (hs : ModNat.CmpOK P W H s c)
    (h : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ ModNat.CmpOK P W H t c₁) :
    ModNat.CmpOK P W H (.seq s t) c := by
  refine ModNat.CmpOK.seq hs fun c₁ k₁ e => ?_
  obtain ⟨c₂, k₂, e₂, h₂⟩ := h
  obtain ⟨rfl, -⟩ := Exec.det e e₂
  exact h₂

theorem ModNat.CmpOK.mono {s : Stmt} {c : Config} {H' : ℕ} (h : ModNat.CmpOK P W H s c)
    (hH : H ≤ H') : ModNat.CmpOK P W H' s c :=
  fun c' k e => (h c' k e).mono_H hH

/-- Every execution ends where a known one ends. -/
theorem exec_post {s : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (e₁ : Exec P W s c c₁ k₁)
    (e₂ : Exec P W s c c₂ k₂) : c₂ = c₁ := (Exec.det e₂ e₁).1

theorem cmov1_cmpOK {c : Config} {a b x y rr sr nr sn : ℕ}
    (h : c.nreg a < c.nreg b → |c.rreg x - c.rreg y| ≤ H) :
    ModNat.CmpOK P W H (cmov1 a b x y rr sr nr sn) c :=
  ModNat.CmpOK.ifLtN (fun h1 => ModNat.CmpOK.ifLtR (h h1)
    (fun _ => ModNat.cmpOK_of_noTestR rfl _) (fun _ => ModNat.cmpOK_of_noTestR rfl _))
    (fun _ => ModNat.cmpOK_of_noTestR rfl _)

theorem cmov2_cmpOK {c : Config} {a b x y rr sr nr sn : ℕ}
    (h : c.nreg a < c.nreg b → |c.rreg x - c.rreg y| ≤ H) :
    ModNat.CmpOK P W H (cmov2 a b x y rr sr nr sn) c :=
  ModNat.CmpOK.ifLtN (fun h1 => ModNat.CmpOK.ifLtR (h h1)
    (fun _ => ModNat.cmpOK_of_noTestR rfl _) (fun _ => ModNat.cmpOK_of_noTestR rfl _))
    (fun _ => ModNat.cmpOK_of_noTestR rfl _)

/-- What a conditional move changes. -/
structure MovPost (rr sr nr : ℕ) (c c' : Config) : Prop where
  nreg : ∀ r, r ≠ nr → c'.nreg r = c.nreg r
  rreg : ∀ r, r ≠ rr → c'.rreg r = c.rreg r
  mv : c'.rreg rr = c.rreg rr ∨ c'.rreg rr = c.rreg sr
  mem : mem c' = mem c

theorem cmov1_post {c c' : Config} {k : ℕ} (hc : WordsBounded W c) {a b x y rr sr nr sn : ℕ}
    (e : Exec P W (cmov1 a b x y rr sr nr sn) c c' k) : MovPost rr sr nr c c' := by
  obtain ⟨k₁, e₁, -⟩ := cmov1_exec (P := P) hc a b x y rr sr nr sn
  have := exec_post e₁ e; subst this
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, rfl⟩
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_apply, ↓reduceIte]; split_ifs <;> simp

theorem cmov2_post {c c' : Config} {k : ℕ} (hc : WordsBounded W c) {a b x y rr sr nr sn : ℕ}
    (e : Exec P W (cmov2 a b x y rr sr nr sn) c c' k) : MovPost rr sr nr c c' := by
  obtain ⟨k₁, e₁, -⟩ := cmov2_exec (P := P) hc a b x y rr sr nr sn
  have := exec_post e₁ e; subst this
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, rfl⟩
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_apply, ↓reduceIte]; split_ifs <;> simp

end generic

/-! ### Near values -/

lemma abs_sub_le_two {p q O V : ℝ} (hp : |p + O| ≤ V) (hq : |q + O| ≤ V) : |p - q| ≤ 2 * V := by
  rw [abs_le] at hp hq ⊢; constructor <;> linarith

section near
variable (B n : ℕ)

/-- The values compared by `recompS` at `u`, shifted by `O1` (first values) and `O2` (second
values), are at most `V` in absolute value. -/
structure NearAt (V : ℝ) (M : Mem) (u : ℕ) (O1 O2 : ℝ) : Prop where
  v1 : |vl B M u + O1| ≤ V
  v2 : |vl2 B M u + O2| ≤ V
  l1 : lc B M u < n → |minA B M (lc B M u) + O1| ≤ V
  l2 : lc B M u < n → |minA2 B M (lc B M u) + O2| ≤ V
  r1 : rc B M u < n → |minA B M (rc B M u) + O1| ≤ V
  r2 : rc B M u < n → |minA2 B M (rc B M u) + O2| ≤ V

/-- The values compared by `recompS` at `u` are near: shifted values of absolute value at most
`V`. -/
def RecNear (V : ℝ) (M : Mem) (u : ℕ) : Prop := ∃ O1 O2, NearAt B n V M u O1 O2

end near

/-! ### The recomputation -/

section rec
variable {P : Input} {W H : ℕ}

/-- The conditional moves of `recompS`, from the values read by its first block. -/
def recTail (B : ℕ) : Stmt :=
  .seq (cmov1 171 151 170 192 196 192 174 161) <|
  .seq (cmov2 172 151 194 196 196 194 174 162) <|
  .seq (block [.copyR 197 170, .copyN 175 170]) <|
  .seq (cmov1 172 151 170 194 197 194 175 164) <|
  .seq (cmov2 171 151 192 197 197 192 175 163) <|
  .seq (block [.copyR 198 171, .copyN 176 170]) <|
  .seq (cmov1 171 151 171 193 198 193 176 165) <|
  .seq (cmov2 172 151 195 198 198 195 176 166) <|
  .seq (block [.copyR 199 171, .copyN 177 170]) <|
  .seq (cmov1 172 151 171 195 199 195 177 168) <|
  .seq (cmov2 171 151 193 199 199 193 177 167) <|
  .seq (block [.copyN 161 170]) <|
  .seq (.ifLtN 171 151 (.instr (.copyN 161 169)) .skip) <|
  .seq (block [.copyN 162 170]) <|
  .seq (.ifLtN 172 151 (.instr (.copyN 162 173)) .skip) <|
  block (st B 170 3 174 ++ st B 170 5 161 ++ st B 170 6 162 ++ st B 170 7 175 ++
    st B 170 8 176 ++ st B 170 9 177 ++ stR B 170 2 196 ++ stR B 170 3 190 ++ stR B 170 4 187 ++
    stR B 170 7 198 ++ stR B 170 8 191)

/-- The registers after the first block of `recompS`, near. -/
structure TailNear (n : ℕ) (V O1 O2 : ℝ) (c : Config) : Prop where
  hn : c.nreg 151 = n
  v1 : |c.rreg 170 + O1| ≤ V
  v2 : |c.rreg 171 + O2| ≤ V
  a1 : c.nreg 171 < n → |c.rreg 192 + O1| ≤ V
  a2 : c.nreg 171 < n → |c.rreg 193 + O2| ≤ V
  b1 : c.nreg 172 < n → |c.rreg 194 + O1| ≤ V
  b2 : c.nreg 172 < n → |c.rreg 195 + O2| ≤ V
  m : c.rreg 196 = c.rreg 170

lemma copy_post {c c' : Config} {k : ℕ} (hc : WordsBounded W c) {rr sr nr sn : ℕ}
    (e : Exec P W (block [.copyR rr sr, .copyN nr sn]) c c' k) :
    (∀ r, r ≠ nr → c'.nreg r = c.nreg r) ∧ (∀ r, r ≠ rr → c'.rreg r = c.rreg r) ∧
      c'.rreg rr = c.rreg sr := by
  have e1 := Exec.copyR (P := P) hc rr sr
  have e2 := Exec.copyN (P := P) e1.wb_right nr sn
  have := exec_post (Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_nil e2.wb_right))) e
  subst this
  refine ⟨fun r hr => ?_, fun r hr => ?_, ?_⟩
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_ne_of _ _ _ hr]
  · simp only [upd_apply, ↓reduceIte]

theorem recTail_cmpOK (B : ℕ) {n : ℕ} {V O1 O2 : ℝ} (hH : 2 * V ≤ H) {c : Config}
    (hc : WordsBounded W c) (h : TailNear n V O1 O2 c) :
    ModNat.CmpOK P W H (recTail B) c := by
  obtain ⟨hn, v1, v2, a1, a2, b1, b2, m⟩ := h
  have hd : ∀ {p q O : ℝ}, |p + O| ≤ V → |q + O| ≤ V → |p - q| ≤ H :=
    fun hp hq => (abs_sub_le_two hp hq).trans hH
  unfold recTail
  -- first channel, left argmin
  refine ModNat.CmpOK.seq (cmov1_cmpOK fun h1 => hd v1 (a1 (hn ▸ h1))) fun c1 k1 e1 => ?_
  have p1 := cmov1_post hc e1
  have w1 := e1.wb_right
  refine ModNat.CmpOK.seq (cmov2_cmpOK fun h1 => ?_) fun c2 k2 e2 => ?_
  · rw [p1.nreg 172 (by omega), p1.nreg 151 (by omega)] at h1
    rw [p1.rreg 194 (by omega)]
    rcases p1.mv with h | h
    · rw [h, m]; exact hd (b1 (hn ▸ h1)) v1
    · by_cases ha : c.nreg 171 < n
      · rw [h]; exact hd (b1 (hn ▸ h1)) (a1 ha)
      · have e' : c1.rreg 196 = c.rreg 196 := by
          obtain ⟨k₁, e₁, -⟩ := cmov1_exec (P := P) hc 171 151 170 192 196 192 174 161
          rw [exec_post e₁ e1]; simp [hn, ha]
        rw [e', m]; exact hd (b1 (hn ▸ h1)) v1
  have p2 := cmov2_post w1 e2
  have w2 := e2.wb_right
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR rfl _) fun c3 k3 e3 => ?_
  have p3 := copy_post w2 e3
  have w3 := e3.wb_right
  -- registers kept so far
  have k171 : c3.nreg 171 = c.nreg 171 := by
    rw [p3.1 171 (by omega), p2.nreg 171 (by omega), p1.nreg 171 (by omega)]
  have k172 : c3.nreg 172 = c.nreg 172 := by
    rw [p3.1 172 (by omega), p2.nreg 172 (by omega), p1.nreg 172 (by omega)]
  have k151 : c3.nreg 151 = c.nreg 151 := by
    rw [p3.1 151 (by omega), p2.nreg 151 (by omega), p1.nreg 151 (by omega)]
  have kR : ∀ r, r < 196 → c3.rreg r = c.rreg r := by
    intro r h1
    rw [p3.2.1 r (by omega), p2.rreg r (by omega), p1.rreg r (by omega)]
  have q3 : c3.rreg 197 = c.rreg 170 := by
    rw [p3.2.2, p2.rreg 170 (by omega), p1.rreg 170 (by omega)]
  -- first channel, right argmin
  refine ModNat.CmpOK.seq (cmov1_cmpOK fun h1 => ?_) fun c4 k4 e4 => ?_
  · rw [k172, k151] at h1
    rw [kR 170 (by omega), kR 194 (by omega)]
    exact hd v1 (b1 (hn ▸ h1))
  have p4 := cmov1_post w3 e4
  have w4 := e4.wb_right
  refine ModNat.CmpOK.seq (cmov2_cmpOK fun h1 => ?_) fun c5 k5 e5 => ?_
  · rw [p4.nreg 171 (by omega), p4.nreg 151 (by omega), k171, k151] at h1
    rw [p4.rreg 192 (by omega), kR 192 (by omega)]
    rcases p4.mv with h | h
    · rw [h, q3]; exact hd (a1 (hn ▸ h1)) v1
    · by_cases hb : c.nreg 172 < n
      · rw [h, kR 194 (by omega)]; exact hd (a1 (hn ▸ h1)) (b1 hb)
      · have e' : c4.rreg 197 = c3.rreg 197 := by
          obtain ⟨k₁, e₁, -⟩ := cmov1_exec (P := P) w3 172 151 170 194 197 194 175 164
          rw [exec_post e₁ e4]; simp [k172, k151, hn, hb]
        rw [e', q3]; exact hd (a1 (hn ▸ h1)) v1
  have p5 := cmov2_post w4 e5
  have w5 := e5.wb_right
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR rfl _) fun c6 k6 e6 => ?_
  have p6 := copy_post w5 e6
  have w6 := e6.wb_right
  have k171' : c6.nreg 171 = c.nreg 171 := by
    rw [p6.1 171 (by omega), p5.nreg 171 (by omega), p4.nreg 171 (by omega), k171]
  have k172' : c6.nreg 172 = c.nreg 172 := by
    rw [p6.1 172 (by omega), p5.nreg 172 (by omega), p4.nreg 172 (by omega), k172]
  have k151' : c6.nreg 151 = c.nreg 151 := by
    rw [p6.1 151 (by omega), p5.nreg 151 (by omega), p4.nreg 151 (by omega), k151]
  have kR' : ∀ r, r < 196 → c6.rreg r = c.rreg r := by
    intro r h1
    rw [p6.2.1 r (by omega), p5.rreg r (by omega), p4.rreg r (by omega), kR r h1]
  have q6 : c6.rreg 198 = c.rreg 171 := by
    rw [p6.2.2, p5.rreg 171 (by omega), p4.rreg 171 (by omega), kR 171 (by omega)]
  -- second channel, left argmin
  refine ModNat.CmpOK.seq (cmov1_cmpOK fun h1 => ?_) fun c7 k7 e7 => ?_
  · rw [k171', k151'] at h1
    rw [kR' 171 (by omega), kR' 193 (by omega)]
    exact hd v2 (a2 (hn ▸ h1))
  have p7 := cmov1_post w6 e7
  have w7 := e7.wb_right
  refine ModNat.CmpOK.seq (cmov2_cmpOK fun h1 => ?_) fun c8 k8 e8 => ?_
  · rw [p7.nreg 172 (by omega), p7.nreg 151 (by omega), k172', k151'] at h1
    rw [p7.rreg 195 (by omega), kR' 195 (by omega)]
    rcases p7.mv with h | h
    · rw [h, q6]; exact hd (b2 (hn ▸ h1)) v2
    · by_cases ha : c.nreg 171 < n
      · rw [h, kR' 193 (by omega)]; exact hd (b2 (hn ▸ h1)) (a2 ha)
      · have e' : c7.rreg 198 = c6.rreg 198 := by
          obtain ⟨k₁, e₁, -⟩ := cmov1_exec (P := P) w6 171 151 171 193 198 193 176 165
          rw [exec_post e₁ e7]; simp [k171', k151', hn, ha]
        rw [e', q6]; exact hd (b2 (hn ▸ h1)) v2
  have p8 := cmov2_post w7 e8
  have w8 := e8.wb_right
  refine ModNat.CmpOK.seq (ModNat.cmpOK_of_noTestR rfl _) fun c9 k9 e9 => ?_
  have p9 := copy_post w8 e9
  have w9 := e9.wb_right
  have k171'' : c9.nreg 171 = c.nreg 171 := by
    rw [p9.1 171 (by omega), p8.nreg 171 (by omega), p7.nreg 171 (by omega), k171']
  have k172'' : c9.nreg 172 = c.nreg 172 := by
    rw [p9.1 172 (by omega), p8.nreg 172 (by omega), p7.nreg 172 (by omega), k172']
  have k151'' : c9.nreg 151 = c.nreg 151 := by
    rw [p9.1 151 (by omega), p8.nreg 151 (by omega), p7.nreg 151 (by omega), k151']
  have kR'' : ∀ r, r < 196 → c9.rreg r = c.rreg r := by
    intro r h1
    rw [p9.2.1 r (by omega), p8.rreg r (by omega), p7.rreg r (by omega), kR' r h1]
  have q9 : c9.rreg 199 = c.rreg 171 := by
    rw [p9.2.2, p8.rreg 171 (by omega), p7.rreg 171 (by omega), kR' 171 (by omega)]
  -- second channel, right argmin
  refine ModNat.CmpOK.seq (cmov1_cmpOK fun h1 => ?_) fun c10 k10 e10 => ?_
  · rw [k172'', k151''] at h1
    rw [kR'' 171 (by omega), kR'' 195 (by omega)]
    exact hd v2 (b2 (hn ▸ h1))
  have p10 := cmov1_post w9 e10
  refine ModNat.CmpOK.seq (cmov2_cmpOK fun h1 => ?_) fun _ _ _ => ModNat.cmpOK_of_noTestR rfl _
  rw [p10.nreg 171 (by omega), p10.nreg 151 (by omega), k171'', k151''] at h1
  rw [p10.rreg 193 (by omega), kR'' 193 (by omega)]
  rcases p10.mv with h | h
  · rw [h, q9]; exact hd (a2 (hn ▸ h1)) v2
  · by_cases hb : c.nreg 172 < n
    · rw [h, kR'' 195 (by omega)]; exact hd (a2 (hn ▸ h1)) (b2 hb)
    · have e' : c10.rreg 199 = c9.rreg 199 := by
        obtain ⟨k₁, e₁, -⟩ := cmov1_exec (P := P) w9 172 151 171 195 199 195 177 168
        rw [exec_post e₁ e10]; simp [k172'', k151'', hn, hb]
      rw [e', q9]; exact hd (a2 (hn ▸ h1)) v2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- **The recomputation compares near values.** -/
theorem recompS_cmpOK (B n : ℕ) {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    {u : ℕ} (hu : c.nreg 170 = u) (hn : c.nreg 151 = n) (hun : u ≤ n)
    (ha : lc B (mem c) u ≤ n) (hb : rc B (mem c) u ≤ n) {V : ℝ} (hH : 2 * V ≤ H)
    (hN : RecNear B n V (mem c) u) : ModNat.CmpOK P W H (recompS B) c := by
  obtain ⟨O1, O2, N⟩ := hN
  obtain ⟨v1, v2, l1, l2, r1, r2⟩ := N
  simp only [lc, rc, mem, adr] at ha hb
  simp only [vl, vl2, minA, minA2, mn, mn2, tg, tg2, lc, rc, mem, adr] at v1 v2 l1 l2 r1 r2
  unfold recompS
  refine ModNat.CmpOK.seq_ex ?_ ?_
  · exact ModNat.cmpOK_of_noTestR (noTestR_block _) _
  simp only [ld, ldR, ad, List.cons_append, List.nil_append]
  exec_block
  any_goals (config_simp; (try simp only [hu]); omega)
  refine recTail_cmpOK B (n := n) (O1 := O1) (O2 := O2) hH ‹WordsBounded W _›
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals config_simp
  all_goals (try simp only [hu]); (first | exact hn | assumption)

end rec

/-! ### The rotation -/

section rot
variable (B n : ℕ)

/-- The recomputations of the rotation of `x` (at its parent on `rotP x M`, then at `x`) compare
near values. -/
def RotNear (V : ℝ) (M : Mem) (x : ℕ) : Prop :=
  RecNear B n V (rotP B x M) (par B M x) ∧ RecNear B n V (recomp B n (par B M x) (rotP B x M)) x

variable {P : Input} {W H : ℕ}

lemma rotPS_noTestR : (rotPS B).noTestR = true := by
  simp [rotPS, rotRead, rotBranch, rotTail, eqS, noTestR]

/-- **The rotation compares near values.** -/
theorem rotS_cmpOK {c : Config} (hc : WordsBounded W c) (hW : B + 16 * (n + 1) ≤ W)
    (hn : c.nreg 151 = n) (hb : Bnd B n (mem c)) {x : ℕ} (hx : c.nreg 160 = x) (hxn : x ≤ n)
    {V : ℝ} (hH : 2 * V ≤ H) (hR : RotNear B n V (mem c) x) :
    ModNat.CmpOK P W H (rotS B) c := by
  obtain ⟨py, lx, rx, -, -, -⟩ := hb.get hxn
  obtain ⟨pz, -, -, -, -, -⟩ := hb.get py
  obtain ⟨c1, k1, e1, hk1, m1, f1, s160, s161⟩ := rotPS_exec (P := P) B n hc hW hx hxn py pz lx rx
  have hb1 : Bnd B n (mem c1) := m1 ▸ hb.rotP hxn
  have hw1 := e1.wb_right
  unfold rotS
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR (rotPS_noTestR B) _) ⟨c1, k1, e1, ?_⟩
  have e2 := Exec.copyN (P := P) hw1 170 161
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e2, ?_⟩
  have hw2 := e2.wb_right
  have hb2 : Bnd B n (mem { c1 with nreg := upd c1.nreg 170 (c1.nreg 161) }) := hb1
  obtain ⟨-, l2, r2, -, -, -⟩ := hb2.get py
  have h151 : c1.nreg 151 = n := by rw [(f1.1 151 (by omega)).1]; exact hn
  obtain ⟨c3, k3, e3, hk3, m3, f3, s170, t160⟩ := recompS_exec (P := P) B n hw2 hW
    (u := par B (mem c) x) (by config_simp; exact s161) (by config_simp; exact h151) py l2 r2
  refine ModNat.CmpOK.seq (recompS_cmpOK (P := P) B n hw2 hW (u := par B (mem c) x)
    (by config_simp; exact s161) (by config_simp; exact h151) py l2 r2 hH ?_) fun c3' k3' e3' => ?_
  · change RecNear B n V (mem c1) _
    rw [m1]; exact hR.1
  obtain rfl : c3' = c3 := exec_post e3 e3'
  have hw3 := e3.wb_right
  have e4 := Exec.copyN (P := P) hw3 170 160
  refine ModNat.CmpOK.seq_ex (ModNat.cmpOK_of_noTestR rfl _) ⟨_, _, e4, ?_⟩
  have hw4 := e4.wb_right
  have hb3 : Bnd B n (mem c3') := m3 ▸ hb2.recomp py
  have hb4 : Bnd B n (mem { c3' with nreg := upd c3'.nreg 170 (c3'.nreg 160) }) := hb3
  obtain ⟨-, l4, r4, -, -, -⟩ := hb4.get hxn
  have h160 : c3'.nreg 160 = x := by
    rw [t160]; config_simp; exact s160
  have h151' : c3'.nreg 151 = n := by
    rw [(f3.1 151 (by omega)).1]; config_simp; exact h151
  refine recompS_cmpOK (P := P) B n hw4 hW (u := x) (by config_simp; exact h160)
    (by config_simp; exact h151') hxn l4 r4 hH ?_
  change RecNear B n V (mem c3') x
  rw [m3]
  change RecNear B n V (recomp B n (par B (mem c) x) (mem c1)) x
  rw [m1]; exact hR.2

end rot

/-! ### Near values around a rotation -/

section rotlocal
variable {B n : ℕ}

lemma abs_le_of_eq' {p q V : ℝ} (h : |p| ≤ V) (e : p = q) : |q| ≤ V := e ▸ h

/-- The minimum recomputed by `lmn` is one of its arguments. -/
lemma lmn_fst_mem {Q : ℝ → Prop} {a : ℕ} {A : ℝ × ℕ} {v : ℝ} {u b : ℕ} {Bq : ℝ × ℕ}
    (hv : Q v) (ha : a < n → Q A.1) (hb : b < n → Q Bq.1) : Q (lmn n a A v u b Bq).1 := by
  rw [lmn_fst]
  have hx : Q (if a < n ∧ ¬ v < A.1 then A.1 else v) := by
    by_cases h : a < n ∧ ¬ v < A.1
    · rw [ite_of_pos h]; exact ha h.1
    · rw [ite_of_neg h]; exact hv
  by_cases h : b < n ∧ Bq.1 < (if a < n ∧ ¬ v < A.1 then A.1 else v)
  · rw [ite_of_pos h]; exact hb h.1
  · rw [ite_of_neg h]; exact hx

/-- The minima recomputed from near values are near. -/
lemma NearAt.cmb {V : ℝ} {M : Mem} {u : ℕ} {O1 O2 : ℝ} (h : NearAt B n V M u O1 O2) :
    |(cmb B n M u).m1 + O1| ≤ V ∧ |(cmb B n M u).m2 + O2| ≤ V :=
  ⟨lmn_fst_mem (Q := fun r => |r + O1| ≤ V) h.v1 h.l1 h.r1,
    lmn_fst_mem (Q := fun r => |r + O2| ≤ V) h.v2 h.l2 h.r2⟩

lemma mn_recomp {M : Mem} {u : ℕ} :
    mn B (recomp B n u M) u = (cmb B n M u).m1 ∧ mn2 B (recomp B n u M) u = (cmb B n M u).m2 :=
  ⟨congrArg Ag.m1 (own_setOwn B (M := M) (u := u) (cmb B n M u)),
    congrArg Ag.m2 (own_setOwn B (M := M) (u := u) (cmb B n M u))⟩

lemma rotP_tg_other {M : Mem} {x u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x)
    (h3 : u ≠ (if lc B M (par B M x) = x then rc B M x else lc B M x)) :
    tg B (rotP B x M) u = tg B M u ∧ tg2 B (rotP B x M) u = tg2 B M u := by
  constructor <;> simp only [tg, tg2, rotP] <;>
    simp [upd_adr _ _ (show (1 : ℕ) < 16 by omega), upd_adr _ _ (show (6 : ℕ) < 16 by omega),
      h1, h2, h3]

lemma rotP_minA_other {M : Mem} {x u : ℕ} (h1 : u ≠ x) (h2 : u ≠ par B M x)
    (h3 : u ≠ (if lc B M (par B M x) = x then rc B M x else lc B M x)) :
    minA B (rotP B x M) u = minA B M u ∧ minA2 B (rotP B x M) u = minA2 B M u := by
  obtain ⟨t1, t2⟩ := rotP_tg_other h1 h2 h3
  simp only [minA, minA2, t1, t2, mn, mn2]
  rw [rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)]
  exact ⟨rfl, rfl⟩

/-- The values around a rotation of `x`, a child of `y` (with `aa`, `bb` the children of `x`,
`bb` the one changing sides, and `cc` the other child of `y`), shifted by the tags along the path
and by `O1`, `O2` (the tags above `y`), are at most `V`. -/
structure NearRot (V : ℝ) (M : Mem) (x y aa bb cc : ℕ) (O1 O2 : ℝ) : Prop where
  y1 : |vl B M y + tg B M y + O1| ≤ V
  y2 : |vl2 B M y + tg2 B M y + O2| ≤ V
  x1 : |vl B M x + tg B M x + tg B M y + O1| ≤ V
  x2 : |vl2 B M x + tg2 B M x + tg2 B M y + O2| ≤ V
  a1 : aa < n → |minA B M aa + tg B M x + tg B M y + O1| ≤ V
  a2 : aa < n → |minA2 B M aa + tg2 B M x + tg2 B M y + O2| ≤ V
  b1 : bb < n → |minA B M bb + tg B M x + tg B M y + O1| ≤ V
  b2 : bb < n → |minA2 B M bb + tg2 B M x + tg2 B M y + O2| ≤ V
  c1 : cc < n → |minA B M cc + tg B M y + O1| ≤ V
  c2 : cc < n → |minA2 B M cc + tg2 B M y + O2| ≤ V

/-- The second recomputation of a rotation, from the first. -/
lemma nearAt_x {V : ℝ} {M M1 : Mem} {x y aa : ℕ} {O1 O2 : ℝ}
    (N1 : NearAt B n V M1 y (O1 + tg B M y) (O2 + tg2 B M y))
    (hvx : vl B M1 x = vl B M x ∧ vl2 B M1 x = vl2 B M x)
    (hty : tg B M1 y = - tg B M x ∧ tg2 B M1 y = - tg2 B M x)
    (hay : aa < n → aa ≠ y)
    (hma : aa < n → minA B M1 aa = minA B M aa ∧ minA2 B M1 aa = minA2 B M aa)
    (x1 : |vl B M x + tg B M x + tg B M y + O1| ≤ V)
    (x2 : |vl2 B M x + tg2 B M x + tg2 B M y + O2| ≤ V)
    (a1 : aa < n → |minA B M aa + tg B M x + tg B M y + O1| ≤ V)
    (a2 : aa < n → |minA2 B M aa + tg2 B M x + tg2 B M y + O2| ≤ V)
    (hl : lc B M1 x = aa ∧ rc B M1 x = y ∨ lc B M1 x = y ∧ rc B M1 x = aa) :
    NearAt B n V (recomp B n y M1) x (O1 + tg B M x + tg B M y) (O2 + tg2 B M x + tg2 B M y) := by
  obtain ⟨-, el, er, -, ev, -, ev2, -, -⟩ := recomp_agrS_par B n (M := M1) (u := y) (v := x)
  obtain ⟨m1, m2⟩ := mn_recomp (B := B) (n := n) (M := M1) (u := y)
  obtain ⟨-, -, -, -, -, ty, -, ty2, -⟩ := recomp_agrS_par B n (M := M1) (u := y) (v := y)
  obtain ⟨k1, k2⟩ := N1.cmb
  have hY1 : |minA B (recomp B n y M1) y + (O1 + tg B M x + tg B M y)| ≤ V :=
    abs_le_of_eq' k1 (by simp only [minA, m1, ty, hty.1]; ring)
  have hY2 : |minA2 B (recomp B n y M1) y + (O2 + tg2 B M x + tg2 B M y)| ≤ V :=
    abs_le_of_eq' k2 (by simp only [minA2, m2, ty2, hty.2]; ring)
  have hA : aa < n → |minA B (recomp B n y M1) aa + (O1 + tg B M x + tg B M y)| ≤ V ∧
      |minA2 B (recomp B n y M1) aa + (O2 + tg2 B M x + tg2 B M y)| ≤ V := by
    intro ha
    have ag := recomp_agr B n (M := M1) (u := y) (hay ha)
    have e1 : minA B (recomp B n y M1) aa = minA B M1 aa := by
      simp only [minA, mn, tg]; rw [(ag 2 (by omega)).2, (ag 1 (by omega)).2]
    have e2 : minA2 B (recomp B n y M1) aa = minA2 B M1 aa := by
      simp only [minA2, mn2, tg2]; rw [(ag 7 (by omega)).2, (ag 6 (by omega)).2]
    exact ⟨abs_le_of_eq' (a1 ha) (by rw [e1, (hma ha).1]; ring),
      abs_le_of_eq' (a2 ha) (by rw [e2, (hma ha).2]; ring)⟩
  refine ⟨abs_le_of_eq' x1 (by rw [ev, hvx.1]; ring), abs_le_of_eq' x2 (by rw [ev2, hvx.2]; ring),
    ?_, ?_, ?_, ?_⟩ <;> simp only [el, er] <;>
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2] <;> intro hlt
  all_goals first
    | exact hY1 | exact hY2 | exact (hA hlt).1 | exact (hA hlt).2

/-- **Near values around the rotation of a left child.** -/
theorem rotNear_of_L {V : ℝ} {M : Mem} {x y aa bb cc : ℕ} {O1 O2 : ℝ}
    (N : NearRot (B := B) (n := n) V M x y aa bb cc O1 O2) (hyx : par B M x = y)
    (hlc : lc B M y = x) (hla : lc B M x = aa) (hrx : rc B M x = bb) (hrc : rc B M y = cc)
    (hxy : x ≠ y) (hxz : x ≠ par B M y) (hyz : y ≠ par B M y) (hbx : bb ≠ x) (hby : bb ≠ y)
    (ha : aa < n → aa ≠ x ∧ aa ≠ y ∧ aa ≠ bb) (hc : cc < n → cc ≠ x ∧ cc ≠ y ∧ cc ≠ bb) :
    RotNear B n V M x := by
  obtain ⟨-, lx, rx, -, ly, ry, -, tx, ty, tb, -, -, tx2, ty2, tb2⟩ :=
    rotP_L hyx rfl hlc hrx hxy hxz hyz hbx hby
  have hbb : (if lc B M (par B M x) = x then rc B M x else lc B M x) = bb := by
    rw [hyx, hlc, ite_of_pos rfl, hrx]
  have other : ∀ u, u ≠ x → u ≠ y → u ≠ bb →
      minA B (rotP B x M) u = minA B M u ∧ minA2 B (rotP B x M) u = minA2 B M u :=
    fun u h1 h2 h3 => rotP_minA_other h1 (hyx ▸ h2) (hbb ▸ h3)
  have vx : vl B (rotP B x M) x = vl B M x ∧ vl2 B (rotP B x M) x = vl2 B M x :=
    ⟨rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)⟩
  have vy : vl B (rotP B x M) y = vl B M y ∧ vl2 B (rotP B x M) y = vl2 B M y :=
    ⟨rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)⟩
  have mb : minA B (rotP B x M) bb = minA B M bb + tg B M x ∧
      minA2 B (rotP B x M) bb = minA2 B M bb + tg2 B M x := by
    simp only [minA, minA2, tb, tb2, mn, mn2]
    rw [rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)]
    constructor <;> ring
  have N1 : NearAt B n V (rotP B x M) y (O1 + tg B M y) (O2 + tg2 B M y) := by
    refine ⟨abs_le_of_eq' N.y1 (by rw [vy.1]; ring), abs_le_of_eq' N.y2 (by rw [vy.2]; ring),
      ?_, ?_, ?_, ?_⟩ <;> intro h
    · rw [ly] at h ⊢; exact abs_le_of_eq' (N.b1 h) (by rw [mb.1]; ring)
    · rw [ly] at h ⊢; exact abs_le_of_eq' (N.b2 h) (by rw [mb.2]; ring)
    · rw [ry, hrc] at h ⊢
      obtain ⟨c1, c2, c3⟩ := hc h
      exact abs_le_of_eq' (N.c1 h) (by rw [(other cc c1 c2 c3).1]; ring)
    · rw [ry, hrc] at h ⊢
      obtain ⟨c1, c2, c3⟩ := hc h
      exact abs_le_of_eq' (N.c2 h) (by rw [(other cc c1 c2 c3).2]; ring)
  refine ⟨hyx ▸ ⟨_, _, N1⟩, ⟨O1 + tg B M x + tg B M y, O2 + tg2 B M x + tg2 B M y, ?_⟩⟩
  rw [hyx]
  exact nearAt_x N1 vx ⟨ty, ty2⟩ (fun h => (ha h).2.1)
    (fun h => other aa (ha h).1 (ha h).2.1 (ha h).2.2) N.x1 N.x2 N.a1 N.a2
    (Or.inl ⟨lx.trans hla, rx⟩)

/-- **Near values around the rotation of a right child.** -/
theorem rotNear_of_R {V : ℝ} {M : Mem} {x y aa bb cc : ℕ} {O1 O2 : ℝ}
    (N : NearRot (B := B) (n := n) V M x y aa bb cc O1 O2) (hyx : par B M x = y)
    (hlc : lc B M y = cc) (hcx : cc ≠ x) (hla : rc B M x = aa) (hlx : lc B M x = bb)
    (hxy : x ≠ y) (hxz : x ≠ par B M y) (hyz : y ≠ par B M y) (hbx : bb ≠ x) (hby : bb ≠ y)
    (ha : aa < n → aa ≠ x ∧ aa ≠ y ∧ aa ≠ bb) (hc : cc < n → cc ≠ x ∧ cc ≠ y ∧ cc ≠ bb) :
    RotNear B n V M x := by
  have hlc' : lc B M y ≠ x := hlc ▸ hcx
  obtain ⟨-, lx, rx, -, ly, ry, -, tx, ty, tb, -, -, tx2, ty2, tb2⟩ :=
    rotP_R hyx rfl hlc' hlx hxy hxz hyz hbx hby
  have hbb : (if lc B M (par B M x) = x then rc B M x else lc B M x) = bb := by
    rw [hyx, ite_of_neg hlc', hlx]
  have other : ∀ u, u ≠ x → u ≠ y → u ≠ bb →
      minA B (rotP B x M) u = minA B M u ∧ minA2 B (rotP B x M) u = minA2 B M u :=
    fun u h1 h2 h3 => rotP_minA_other h1 (hyx ▸ h2) (hbb ▸ h3)
  have vx : vl B (rotP B x M) x = vl B M x ∧ vl2 B (rotP B x M) x = vl2 B M x :=
    ⟨rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)⟩
  have vy : vl B (rotP B x M) y = vl B M y ∧ vl2 B (rotP B x M) y = vl2 B M y :=
    ⟨rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)⟩
  have mb : minA B (rotP B x M) bb = minA B M bb + tg B M x ∧
      minA2 B (rotP B x M) bb = minA2 B M bb + tg2 B M x := by
    simp only [minA, minA2, tb, tb2, mn, mn2]
    rw [rotP_rm (by omega) (by omega), rotP_rm (by omega) (by omega)]
    constructor <;> ring
  have N1 : NearAt B n V (rotP B x M) y (O1 + tg B M y) (O2 + tg2 B M y) := by
    refine ⟨abs_le_of_eq' N.y1 (by rw [vy.1]; ring), abs_le_of_eq' N.y2 (by rw [vy.2]; ring),
      ?_, ?_, ?_, ?_⟩ <;> intro h
    · rw [ly, hlc] at h ⊢
      obtain ⟨c1, c2, c3⟩ := hc h
      exact abs_le_of_eq' (N.c1 h) (by rw [(other cc c1 c2 c3).1]; ring)
    · rw [ly, hlc] at h ⊢
      obtain ⟨c1, c2, c3⟩ := hc h
      exact abs_le_of_eq' (N.c2 h) (by rw [(other cc c1 c2 c3).2]; ring)
    · rw [ry] at h ⊢; exact abs_le_of_eq' (N.b1 h) (by rw [mb.1]; ring)
    · rw [ry] at h ⊢; exact abs_le_of_eq' (N.b2 h) (by rw [mb.2]; ring)
  refine ⟨hyx ▸ ⟨_, _, N1⟩, ⟨O1 + tg B M x + tg B M y, O2 + tg2 B M x + tg2 B M y, ?_⟩⟩
  rw [hyx]
  exact nearAt_x N1 vx ⟨ty, ty2⟩ (fun h => (ha h).2.1)
    (fun h => other aa (ha h).1 (ha h).2.1 (ha h).2.2) N.x1 N.x2 N.a1 N.a2
    (Or.inr ⟨lx, rx.trans hla⟩)

end rotlocal

end DynTree

end PlanarFlow
