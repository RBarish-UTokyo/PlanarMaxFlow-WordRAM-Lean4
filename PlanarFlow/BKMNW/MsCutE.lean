module

public import PlanarFlow.BKMNW.MsCutD

/-!
# The cut map of the path on the machine, part E: the preparation

**`cutPre`**: from the index arrays `RV`, `RT` of `M`, the path flags `LF` and the tour array
`TA` (as written by `fcProg`), in the scratch `[Z, Z + 6m)`:

* `VL[i] = olab RT i + 1` (vertex labels, `olProg`), `VP'` (the marks of the labels of the vertices
  of the path, `vpMk`), `TF[i] = VP'[VL[i]]` (the darts leaving the path, `lgProg`);
* the ranks `RE`, `RK` and the totals `nE`, `nT` (`rkLoop`);
* `TI[TA[i]] = i` (the inverse tour, `lsProg`);
* the registers of the value blocks (`VRegs`) and of the write loops.

Input registers `8250 … 8257` (`m`, `RVb`, `RTb`, `LFb`, `TAb`, `Z`, `RVo`, `RTo`).
**`cutPre_exec`** (on arrays).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab

variable {P : Input} {W : ℕ}

def cpA : Stmt :=
  block [.copyN 8236 8250, .copyN 8233 8253, .copyN 8234 8255, .addN 8240 8255 8250,
    .constN 8241 1, .subN 8235 8240 8241]

def cpB : Stmt :=
  block [.addN 8242 8240 8250, .addN 8243 8242 8250, .addN 8244 8243 8250,
    .addN 8247 8244 8250, .addN 5030 8250 8250, .copyN 5031 8255]

def cpC : Stmt := block [.copyN 7350 8252, .copyN 7351 8255, .copyN 7352 8250]

def cpD : Stmt := block [.copyN 6210 8250, .copyN 6211 8255, .copyN 6212 8235, .copyN 6213 8242]

def cpE : Stmt :=
  block [.copyN 6220 8250, .copyN 6221 8254, .copyN 6222 8254, .copyN 6223 8250,
    .copyN 6224 8247]

def cpF : Stmt :=
  block [.copyN 8220 8253, .copyN 8221 8242, .copyN 8222 8243, .copyN 8223 8244,
    .copyN 8224 8254, .copyN 8225 8247]

def cpG : Stmt :=
  block [.copyN 8226 8251, .copyN 8227 8252, .copyN 8228 8245, .addN 8230 8245 8246,
    .addN 8231 8230 8246, .addN 8232 8231 8246]

def cpH : Stmt := block [.copyN 8200 8250, .copyN 8201 8256, .copyN 8202 8257]

/-- **The preparation of the cut arrays.** -/
def cutPre : Stmt :=
  .seq cpA (.seq cpB (.seq mzFill (.seq cpC (.seq olProg (.seq vpMk (.seq cpD (.seq lgProg
    (.seq rkLoop (.seq cpE (.seq lsProg (.seq cpF (.seq cpG cpH))))))))))))

/-- The input registers. -/
structure CpIn (c : Config) (m RVb RTb LFb TAb Z RVo RTo : ℕ) : Prop where
  r50 : c.nreg 8250 = m
  r51 : c.nreg 8251 = RVb
  r52 : c.nreg 8252 = RTb
  r53 : c.nreg 8253 = LFb
  r54 : c.nreg 8254 = TAb
  r55 : c.nreg 8255 = Z
  r56 : c.nreg 8256 = RVo
  r57 : c.nreg 8257 = RTo

lemma CpIn.of {c d : Config} {m RVb RTb LFb TAb Z RVo RTo : ℕ}
    (h : CpIn c m RVb RTb LFb TAb Z RVo RTo)
    (hr : ∀ r, 8250 ≤ r → r ≤ 8257 → d.nreg r = c.nreg r) : CpIn d m RVb RTb LFb TAb Z RVo RTo :=
  ⟨by rw [hr _ (by omega) (by omega), h.r50], by rw [hr _ (by omega) (by omega), h.r51],
    by rw [hr _ (by omega) (by omega), h.r52], by rw [hr _ (by omega) (by omega), h.r53],
    by rw [hr _ (by omega) (by omega), h.r54], by rw [hr _ (by omega) (by omega), h.r55],
    by rw [hr _ (by omega) (by omega), h.r56], by rw [hr _ (by omega) (by omega), h.r57]⟩

/-- The scratch registers of `cutPre`. -/
def CpScr (r : ℕ) : Prop :=
  (5030 ≤ r ∧ r ≤ 5035) ∨ (6210 ≤ r ∧ r ≤ 6228) ∨ (7350 ≤ r ∧ r ≤ 7352) ∨
    (7400 ≤ r ∧ r ≤ 7405) ∨ (8200 ≤ r ∧ r ≤ 8249)

theorem cpA_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb LFb TAb Z RVo RTo : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) (hw : Z + 6 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cpA c c' t ∧ t = 6 ∧ c'.nreg 8236 = m ∧ c'.nreg 8233 = LFb ∧
      c'.nreg 8234 = Z ∧ c'.nreg 8240 = Z + m ∧ c'.nreg 8235 = Z + m - 1 ∧
      (∀ r, r ≠ 8233 → r ≠ 8234 → r ≠ 8235 → r ≠ 8236 → r ≠ 8240 → r ≠ 8241 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hI
  unfold cpA
  exec_block
  all_goals try ((try config_simp); (try simp only [h0, h3, h5]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a b d e f g => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [h0, h3, h5]; done)
    | (simp only [h0, h3, h5]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

theorem cpB_exec (c : Config) (hc : WordsBounded W c) {m Z : ℕ}
    (r50 : c.nreg 8250 = m) (r55 : c.nreg 8255 = Z) (r40 : c.nreg 8240 = Z + m)
    (hw : Z + 6 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cpB c c' t ∧ t = 6 ∧ c'.nreg 8242 = Z + 2 * m ∧
      c'.nreg 8243 = Z + 3 * m ∧ c'.nreg 8244 = Z + 4 * m ∧ c'.nreg 8247 = Z + 5 * m ∧
      c'.nreg 5030 = 2 * m ∧ c'.nreg 5031 = Z ∧
      (∀ r, r ≠ 8242 → r ≠ 8243 → r ≠ 8244 → r ≠ 8247 → r ≠ 5030 → r ≠ 5031 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpB
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r55, r40]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d e f g => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r55, r40]; done)
    | (simp only [r50, r55, r40]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

/-- A block of copies `rᵢ := sᵢ` (distinct targets): the values and the frame. -/
theorem copies_exec (c : Config) (hc : WordsBounded W c) (l : List (ℕ × ℕ))
    (hnd : (l.map Prod.fst).Nodup) (hsrc : ∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1) :
    ∃ c' t, Exec P W (block (l.map fun p => .copyN p.1 p.2)) c c' t ∧ t = l.length ∧
      (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧
      (∀ r, r ∉ l.map Prod.fst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, 0, .block_nil hc, rfl, fun p hp => absurd hp (by simp),
      fun r _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    obtain ⟨r, s⟩ := p
    have hnd' : (l.map Prod.fst).Nodup := (List.nodup_cons.1 hnd).2
    have hr : r ∉ l.map Prod.fst := (List.nodup_cons.1 hnd).1
    have e1 := Exec.copyN (P := P) hc r s
    obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := ih _ e1.wb_right hnd'
      (fun p hp q hq => hsrc p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq))
    refine ⟨c', t + 1, .block_cons e1 ex, by simp [ht], fun q hq => ?_, fun x hx => ?_,
      by rw [hm], by rw [hrr], by rw [hrm], by rw [ho]⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · rw [hfr _ hr]
        simp only [Config.nreg_mk, upd_same]
      · rw [hv q hq]
        have : q.2 ≠ r := hsrc q (List.mem_cons_of_mem _ hq) (r, s) (List.mem_cons_self) |>.symm
          |> fun h => fun e => h e.symm
        simp only [Config.nreg_mk, upd_other _ _ _ this]
    · simp only [List.map_cons, List.mem_cons, not_or] at hx
      rw [hfr x hx.2]
      simp only [Config.nreg_mk, upd_other _ _ _ hx.1]

/-! ### The copy blocks -/

theorem cpC_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cpC c c' t ∧ t = 3 ∧ c'.nreg 7350 = c.nreg 8252 ∧
      c'.nreg 7351 = c.nreg 8255 ∧ c'.nreg 7352 = c.nreg 8250 ∧
      (∀ r, (r < 7350 ∨ 7352 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := copies_exec (P := P) c hc
    [(7350, 8252), (7351, 8255), (7352, 8250)] (by decide) (by decide)
  exact ⟨c', t, ex, ht, hv (7350, 8252) (by simp), hv (7351, 8255) (by simp), hv (7352, 8250) (by simp),
    fun r hr => hfr r (by simp; omega), hm, hrr, hrm, ho⟩

theorem cpD_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cpD c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 8250 ∧
      c'.nreg 6211 = c.nreg 8255 ∧ c'.nreg 6212 = c.nreg 8235 ∧ c'.nreg 6213 = c.nreg 8242 ∧
      (∀ r, (r < 6210 ∨ 6213 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := copies_exec (P := P) c hc
    [(6210, 8250), (6211, 8255), (6212, 8235), (6213, 8242)] (by decide) (by decide)
  exact ⟨c', t, ex, ht, hv (6210, 8250) (by simp), hv (6211, 8255) (by simp), hv (6212, 8235) (by simp), hv (6213, 8242) (by simp),
    fun r hr => hfr r (by simp; omega), hm, hrr, hrm, ho⟩

theorem cpE_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cpE c c' t ∧ t = 5 ∧ c'.nreg 6220 = c.nreg 8250 ∧
      c'.nreg 6221 = c.nreg 8254 ∧ c'.nreg 6222 = c.nreg 8254 ∧ c'.nreg 6223 = c.nreg 8250 ∧
      c'.nreg 6224 = c.nreg 8247 ∧
      (∀ r, (r < 6220 ∨ 6224 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := copies_exec (P := P) c hc
    [(6220, 8250), (6221, 8254), (6222, 8254), (6223, 8250), (6224, 8247)] (by decide)
    (by decide)
  exact ⟨c', t, ex, ht, hv (6220, 8250) (by simp), hv (6221, 8254) (by simp), hv (6222, 8254) (by simp), hv (6223, 8250) (by simp),
    hv (6224, 8247) (by simp), fun r hr => hfr r (by simp; omega), hm, hrr, hrm, ho⟩

theorem cpF_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cpF c c' t ∧ t = 6 ∧ c'.nreg 8220 = c.nreg 8253 ∧
      c'.nreg 8221 = c.nreg 8242 ∧ c'.nreg 8222 = c.nreg 8243 ∧ c'.nreg 8223 = c.nreg 8244 ∧
      c'.nreg 8224 = c.nreg 8254 ∧ c'.nreg 8225 = c.nreg 8247 ∧
      (∀ r, (r < 8220 ∨ 8225 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := copies_exec (P := P) c hc
    [(8220, 8253), (8221, 8242), (8222, 8243), (8223, 8244), (8224, 8254), (8225, 8247)]
    (by decide) (by decide)
  exact ⟨c', t, ex, ht, hv (8220, 8253) (by simp), hv (8221, 8242) (by simp), hv (8222, 8243) (by simp), hv (8223, 8244) (by simp),
    hv (8224, 8254) (by simp), hv (8225, 8247) (by simp), fun r hr => hfr r (by simp; omega), hm, hrr, hrm, ho⟩

theorem cpH_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W cpH c c' t ∧ t = 3 ∧ c'.nreg 8200 = c.nreg 8250 ∧
      c'.nreg 8201 = c.nreg 8256 ∧ c'.nreg 8202 = c.nreg 8257 ∧
      (∀ r, (r < 8200 ∨ 8202 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, hv, hfr, hm, hrr, hrm, ho⟩ := copies_exec (P := P) c hc
    [(8200, 8250), (8201, 8256), (8202, 8257)] (by decide) (by decide)
  exact ⟨c', t, ex, ht, hv (8200, 8250) (by simp), hv (8201, 8256) (by simp), hv (8202, 8257) (by simp),
    fun r hr => hfr r (by simp; omega), hm, hrr, hrm, ho⟩

theorem cpG_exec (c : Config) (hc : WordsBounded W c) {nE nT : ℕ}
    (r45 : c.nreg 8245 = nE) (r46 : c.nreg 8246 = nT) (hw : nE + 3 * nT ≤ W) :
    ∃ c' t, Exec P W cpG c c' t ∧ t = 6 ∧ c'.nreg 8226 = c.nreg 8251 ∧
      c'.nreg 8227 = c.nreg 8252 ∧ c'.nreg 8228 = nE ∧ c'.nreg 8230 = nE + nT ∧
      c'.nreg 8231 = nE + 2 * nT ∧ c'.nreg 8232 = nE + 3 * nT ∧
      (∀ r, (r < 8226 ∨ 8232 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cpG
  exec_block
  all_goals try ((try config_simp); (try simp only [r45, r46]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r45, r46]; done)
    | (simp only [r45, r46]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

end MsEnc

end BKMNW

end PlanarFlow
