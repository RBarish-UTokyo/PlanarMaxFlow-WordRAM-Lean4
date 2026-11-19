module

public import PlanarFlow.DynTree.CmpOK

/-!
# Dynamic trees: adaptive runs whose real comparisons are bounded

`ORunC P W H B n s c F G c' os G' m g` is an `ORun` (an amortised run performing the operations
`os`, `PlanarFlow/DynTree/Adaptive.lean`) together with `ModNat.CmpOK P W H s c`: every run of
`s` from `c` compares reals at distance at most `H`, the condition of the simulation of the reals
modulo a word (`WordRAM/Machine/RealsModNat.lean`). The rules mirror those of `ORun`, so that a
proof of an `ORun` replays as a proof of an `ORunC`:

* `ORunC.seq`, `ORunC.mono`, `ORunC.of_noTestR` (code without real tests, for example the glue
  `ORunC.glue`), `ORunC.ifLtN_true`, `…_false`, `ORunC.ifLtR_true`, `…_false` (with the bound of
  the compared registers), `ORunC.whileLtN`, `ORunC.whileLtN_abs` (the loop rules; the
  compare-boundedness of the loop follows from that of the body, `ModNat.CmpOK.whileLtN`);
* the register-operand blocks, `regLink_orunC`, …, `regSet_orunC`, `ropsS_orunC`: those of
  `Adaptive.lean`, when the forest has values at most `V` (`VBnd V n F`) and `2 V ≤ H` (for
  `min`, `min2`, the minimum on the root path within `H` of the threshold).
-/

@[expose] public section

namespace PlanarFlow

namespace DynTree

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt VT

/-- An `ORun` whose real comparisons are bounded by `H`. -/
def ORunC (P : Input) (W H B n : ℕ) (s : Stmt) (c : Config) (F : Forest) (G : List VT)
    (c' : Config) (os : List EOp) (G' : List VT) (m g : ℕ) : Prop :=
  ORun P W B n s c F G c' os G' m g ∧ ModNat.CmpOK P W H s c

section rules
variable {P : Input} {W H B n : ℕ}

lemma ORunC.seq {s t : Stmt} {c c₁ c₂ : Config} {F : Forest} {G G₁ G₂ : List VT}
    {os₁ os₂ : List EOp} {m₁ g₁ m₂ g₂ : ℕ} (h₁ : ORunC P W H B n s c F G c₁ os₁ G₁ m₁ g₁)
    (h₂ : ORunC P W H B n t c₁ (runOpsE n F os₁).1 G₁ c₂ os₂ G₂ m₂ g₂) :
    ORunC P W H B n (.seq s t) c F G c₂ (os₁ ++ os₂) G₂ (m₁ + m₂) (g₁ + g₂) := by
  refine ⟨h₁.1.seq h₂.1, ModNat.CmpOK.seq h₁.2 fun c₁' k e => ?_⟩
  obtain ⟨k₁, e₁, -, -⟩ := h₁.1.2
  obtain rfl : c₁' = c₁ := exec_post e₁ e
  exact h₂.2

/-- Sequencing with a rewrite of the forest in between (as `STFlow.ORun.seq'`). -/
lemma ORunC.seq' {s t : Stmt} {c c₁ c₂ : Config} {F F₁ : Forest} {G G₁ G₂ : List VT}
    {os₁ os₂ : List EOp} {m₁ g₁ m₂ g₂ : ℕ} (h₁ : ORunC P W H B n s c F G c₁ os₁ G₁ m₁ g₁)
    (hF : (runOpsE n F os₁).1 = F₁) (h₂ : ORunC P W H B n t c₁ F₁ G₁ c₂ os₂ G₂ m₂ g₂) :
    ORunC P W H B n (.seq s t) c F G c₂ (os₁ ++ os₂) G₂ (m₁ + m₂) (g₁ + g₂) := by
  subst hF; exact h₁.seq h₂

lemma ORunC.mono {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT} {os : List EOp}
    {m g m' g' : ℕ} (h : ORunC P W H B n s c F G c' os G' m g) (hm : m ≤ m') (hg : g ≤ g') :
    ORunC P W H B n s c F G c' os G' m' g' := ⟨h.1.mono hm hg, h.2⟩

lemma ORunC.mono_H {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT} {os : List EOp}
    {m g H' : ℕ} (h : ORunC P W H B n s c F G c' os G' m g) (hH : H ≤ H') :
    ORunC P W H' B n s c F G c' os G' m g := ⟨h.1, ModNat.CmpOK.mono h.2 hH⟩

/-- An `ORun` of code without real tests. -/
lemma ORunC.of_noTestR {s : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (h : ORun P W B n s c F G c' os G' m g) (hs : s.noTestR = true) :
    ORunC P W H B n s c F G c' os G' m g := ⟨h, ModNat.cmpOK_of_noTestR hs c⟩

/-- Glue code without real tests (`ORun.glue`). -/
lemma ORunC.glue {s : Stmt} {c c' : Config} {F : Forest} {G : List VT} {k : ℕ}
    (e : Exec P W s c c' k) (hS : LCTE B n F G c)
    (hm : ∀ a, B ≤ a → a < B + 16 * (n + 1) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a)
    (h151 : c'.nreg 151 = c.nreg 151) (hs : s.noTestR = true) :
    ORunC P W H B n s c F G c' [] G 0 k :=
  ORunC.of_noTestR (ORun.glue e hS hm h151) hs

lemma ORunC.skip {c : Config} {F : Forest} {G : List VT} (hc : WordsBounded W c)
    (hS : LCTE B n F G c) : ORunC P W H B n .skip c F G c [] G 0 0 :=
  ⟨⟨trivial, LRun.skip hc hS⟩, ModNat.cmpOK_of_noTestR rfl c⟩

lemma ORunC.ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : c.nreg a < c.nreg b)
    (h : ORunC P W H B n t c F G c' os G' m g) :
    ORunC P W H B n (.ifLtN a b t e) c F G c' os G' m (g + 1) :=
  ⟨h.1.ifLtN_true ht, ModNat.CmpOK.ifLtN (fun _ => h.2) (fun h' => absurd ht h')⟩

lemma ORunC.ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (ht : ¬ c.nreg a < c.nreg b)
    (h : ORunC P W H B n e c F G c' os G' m g) :
    ORunC P W H B n (.ifLtN a b t e) c F G c' os G' m (g + 2) :=
  ⟨h.1.ifLtN_false ht, ModNat.CmpOK.ifLtN (fun h' => absurd h' ht) (fun _ => h.2)⟩

lemma ORunC.ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (hb : |c.rreg a - c.rreg b| ≤ H) (ht : c.rreg a < c.rreg b)
    (h : ORunC P W H B n t c F G c' os G' m g) :
    ORunC P W H B n (.ifLtR a b t e) c F G c' os G' m (g + 1) :=
  ⟨h.1.ifLtR_true ht, ModNat.CmpOK.ifLtR hb (fun _ => h.2) (fun h' => absurd ht h')⟩

lemma ORunC.ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {F : Forest} {G G' : List VT}
    {os : List EOp} {m g : ℕ} (hb : |c.rreg a - c.rreg b| ≤ H) (ht : ¬ c.rreg a < c.rreg b)
    (h : ORunC P W H B n e c F G c' os G' m g) :
    ORunC P W H B n (.ifLtR a b t e) c F G c' os G' m (g + 2) :=
  ⟨h.1.ifLtR_false ht, ModNat.CmpOK.ifLtR hb (fun h' => absurd h' ht) (fun _ => h.2)⟩

/-- **The loop rule** (`ORun.whileLtN`) with bounded comparisons in every iteration. -/
theorem ORunC.whileLtN {α : Type*} {a b : ℕ} {body : Stmt} (F₀ : Forest)
    (I : α → List EOp → List VT → Config → Prop) (cnt ext : α → ℕ)
    (hI : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs →
      LCTE B n (runOpsE n F₀ hs).1 G c ∧ WordsBounded W c)
    (hbody : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs → c.nreg a < c.nreg b →
      ∃ x' c' os G' j h, ORunC P W H B n body c (runOpsE n F₀ hs).1 G c' os G' j h ∧
        I x' (hs ++ os) G' c' ∧ cnt x' = cnt x + j ∧ ext x' + h + 2 ≤ ext x)
    {x : α} {hs : List EOp} {G : List VT} {c : Config} (hc : I x hs G c)
    (hv : ValidOpsE n F₀ hs) :
    ∃ x' os c' G', ORunC P W H B n (.whileLtN a b body) c (runOpsE n F₀ hs).1 G c' os G'
        (cnt x' - cnt x) (ext x + 2 - ext x') ∧ I x' (hs ++ os) G' c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ cnt x ≤ cnt x' ∧ ext x' ≤ ext x := by
  obtain ⟨x', os, c', G', hrun, rest⟩ := ORun.whileLtN (P := P) (W := W) (B := B) (n := n)
    (a := a) (b := b) (body := body) F₀ I cnt ext hI
    (fun x hs G c h1 h2 h3 => by
      obtain ⟨x', c', os, G', j, h, o, r⟩ := hbody x hs G c h1 h2 h3
      exact ⟨x', c', os, G', j, h, o.1, r⟩) hc hv
  refine ⟨x', os, c', G', ⟨hrun, ?_⟩, rest⟩
  refine ModNat.CmpOK.whileLtN (fun d => ∃ x hs G, I x hs G d ∧ ValidOpsE n F₀ hs)
    (fun d ⟨x, hs, G, h1, h2⟩ ht => ?_) ⟨x, hs, G, hc, hv⟩
  obtain ⟨x₁, c₁, os₁, G₁, j, h, o, hI₁, -, -⟩ := hbody x hs G d h1 h2 ht
  refine ⟨o.2, fun d₁ k₁ e => ?_⟩
  obtain ⟨k₀, e₀, -, -⟩ := o.1.2
  obtain rfl : d₁ = c₁ := exec_post e₀ e
  exact ⟨x₁, hs ++ os₁, G₁, hI₁, (validOpsE_append_iff n F₀ hs os₁).2 ⟨h2, o.1.1⟩⟩

/-- **The loop rule paying the further steps by the operations** (`ORun.whileLtN_abs`). -/
theorem ORunC.whileLtN_abs {α : Type*} {a b : ℕ} {body : Stmt}
    (F₀ : Forest) (I : α → List EOp → List VT → Config → Prop) (cnt μ : α → ℕ)
    (hI : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs →
      LCTE B n (runOpsE n F₀ hs).1 G c ∧ WordsBounded W c)
    (hbody : ∀ x hs G c, I x hs G c → ValidOpsE n F₀ hs → c.nreg a < c.nreg b →
      ∃ x' c' os G' j h, ORunC P W H B n body c (runOpsE n F₀ hs).1 G c' os G' j h ∧
        I x' (hs ++ os) G' c' ∧ cnt x' = cnt x + j ∧ 1 ≤ j ∧ h + 2 ≤ opCostE n ∧ μ x' < μ x)
    {x : α} {hs : List EOp} {G : List VT} {c : Config} (hc : I x hs G c)
    (hv : ValidOpsE n F₀ hs) :
    ∃ x' os c' G', ORunC P W H B n (.whileLtN a b body) c (runOpsE n F₀ hs).1 G c' os G'
        (2 * (cnt x' - cnt x)) 2 ∧ I x' (hs ++ os) G' c' ∧
      ¬ c'.nreg a < c'.nreg b ∧ cnt x ≤ cnt x' := by
  obtain ⟨x', os, c', G', hrun, rest⟩ := ORun.whileLtN_abs (P := P) (W := W) (B := B) (n := n)
    (a := a) (b := b) (body := body) F₀ I cnt μ hI
    (fun x hs G c h1 h2 h3 => by
      obtain ⟨x', c', os, G', j, h, o, r⟩ := hbody x hs G c h1 h2 h3
      exact ⟨x', c', os, G', j, h, o.1, r⟩) hc hv
  refine ⟨x', os, c', G', ⟨hrun, ?_⟩, rest⟩
  refine ModNat.CmpOK.whileLtN (fun d => ∃ x hs G, I x hs G d ∧ ValidOpsE n F₀ hs)
    (fun d ⟨x, hs, G, h1, h2⟩ ht => ?_) ⟨x, hs, G, hc, hv⟩
  obtain ⟨x₁, c₁, os₁, G₁, j, h, o, hI₁, -, -⟩ := hbody x hs G d h1 h2 ht
  refine ⟨o.2, fun d₁ k₁ e => ?_⟩
  obtain ⟨k₀, e₀, -, -⟩ := o.1.2
  obtain rfl : d₁ = c₁ := exec_post e₀ e
  exact ⟨x₁, hs ++ os₁, G₁, hI₁, (validOpsE_append_iff n F₀ hs os₁).2 ⟨h2, o.1.1⟩⟩

end rules

/-! ### The register-operand blocks -/

section leaves
variable {P : Input} {W H B n : ℕ} (hW : B + 16 * (n + 1) ≤ W) {c : Config}
  (hc : WordsBounded W c) {F : Forest} {G : List VT} (hS : LCTE B n F G c) {V : ℝ}
  (hV : VBnd V n F) (hH : 2 * V ≤ H)
include hW hc hS hV hH

theorem regLink_orunC {ra rb v w : ℕ} (hrb : rb ≠ 193)
    (hv : c.nreg ra = v) (hw : c.nreg rb = w) (hvn : v < n) (hwn : w < n) (hp : F.par v = n)
    (hroot : findRoot F n w ≠ v) :
    ∃ c' G', ORunC P W H B n (regLinkS B ra rb) c F G c' [.link v w] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regLink_orun (P := P) hW hc hS hrb hv hw hvn hwn hp hroot
  exact ⟨c', G', ⟨o, regLink_cmpOK B n hc hW hS hV hH hrb hv hw hvn hwn⟩, h⟩

theorem regCut_orunC {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) (hp : F.par v < n) :
    ∃ c' G', ORunC P W H B n (regCutS B ra) c F G c' [.cut v] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regCut_orun (P := P) hW hc hS hv hvn hp
  exact ⟨c', G', ⟨o, regCut_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regAdd_orunC {ra rz v : ℕ} {z : ℤ} (hv : c.nreg ra = v) (hz : c.rreg rz = (z : ℝ))
    (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regAddS B ra rz) c F G c' [.add v z] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regAdd_orun (P := P) hW hc hS hv hz hvn
  exact ⟨c', G', ⟨o, regAdd_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regAdd2_orunC {ra rz v : ℕ} {z : ℤ} (hv : c.nreg ra = v) (hz : c.rreg rz = (z : ℝ))
    (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regAdd2S B ra rz) c F G c' [.add2 v z] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regAdd2_orun (P := P) hW hc hS hv hz hvn
  exact ⟨c', G', ⟨o, regAdd2_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regEvert_orunC {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regEvertS B ra) c F G c' [.evert v] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regEvert_orun (P := P) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regEvert_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regQuery_orunC {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regQueryS B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 195 = findRoot F n v ∧ c'.nreg 196 = (pathMin F n v).2 ∧
      c'.rreg 195 = (pathMin F n v).1 ∧ c'.rreg 196 = pathSum F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regQuery_orun (P := P) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regQuery_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regQuery2_orunC {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regQuery2S B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.rreg 196 = pathSum2 F n v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regQuery2_orun (P := P) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regQuery2_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regMin_orunC {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n)
    (hz : |(pathMin F n v).1 - c.rreg rz| ≤ H) :
    ∃ c' G', ORunC P W H B n (regMinS B ra rz) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin F n v).2 ∧ c'.rreg 195 = (pathMin F n v).1 ∧
      c'.nreg 198 = (if (pathMin F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.nreg 195 = findRoot F n v ∧ c'.rreg 196 = pathSum F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regMin_orun (P := P) (rz := rz) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regMin_cmpOK B n hc hW hS hV hH hv hvn hz⟩, h⟩

theorem regMin2_orunC {ra rz v : ℕ} (hv : c.nreg ra = v) (hvn : v < n)
    (hz : |(pathMin2 F n v).1 - c.rreg rz| ≤ H) :
    ∃ c' G', ORunC P W H B n (regMin2S B ra rz) c F G c' [] G' 1 0 ∧
      c'.nreg 196 = (pathMin2 F n v).2 ∧ c'.rreg 195 = (pathMin2 F n v).1 ∧
      c'.nreg 198 = (if (pathMin2 F n v).1 < c.rreg rz then 1 else 0) ∧
      c'.rreg 196 = pathSum2 F n v ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regMin2_orun (P := P) (rz := rz) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regMin2_cmpOK B n hc hW hS hV hH hv hvn hz⟩, h⟩

theorem regParent_orunC {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regParentS B ra) c F G c' [] G' 1 0 ∧
      c'.nreg 195 = F.par v ∧
      c'.rreg 200 = c.rreg 200 ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regParent_orun (P := P) hW hc hS hv hvn
  exact ⟨c', G', ⟨o, regParent_cmpOK B n hc hW hS hV hH hv hvn⟩, h⟩

theorem regVal_orunC (k : Bool) {ra v : ℕ} (hv : c.nreg ra = v) (hvn : v < n) :
    ∃ c' G', ORunC P W H B n (regValS B k ra) c F G c' [] G' 2 0 ∧
      c'.rreg 195 = F.valc k v ∧ MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regVal_orun (P := P) hW k hc hS hv hvn
  exact ⟨c', G', ⟨o, regVal_cmpOK B n hc hW hS hV hH k hv hvn⟩, h⟩

theorem regSet_orunC (k : Bool) {ra rz v : ℕ} {q : ℤ} (hv : c.nreg ra = v) (hvn : v < n)
    (hp : F.par v = n) (hq : c.rreg rz - F.valc k v = (q : ℝ)) :
    ∃ c' G', ORunC P W H B n (regSetS B k ra rz) c F G c'
        [if k then .add2 v q else .add v q] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', o, h⟩ := regSet_orun (P := P) hW k hc hS hv hvn hp hq
  exact ⟨c', G', ⟨o, regSet_cmpOK B n hc hW hS hV hH k hv hvn⟩, h⟩

theorem rop_orunC (zr : ℕ → ℤ) (o : ROp) (hok : o.Ok c zr) (hv : (o.eop c zr).Valid n F) :
    ∃ c' G', ORunC P W H B n (o.stmt B) c F G c' [o.eop c zr] G' 1 0 ∧
      MemFrame B n (mem c) (mem c') ∧ RegFr c c' := by
  obtain ⟨c', G', r, h⟩ := rop_orun (P := P) hW hc hS zr o hok hv
  exact ⟨c', G', ⟨r, rop_cmpOK B n hc hW hS hV hH o zr hok hv⟩, h⟩

end leaves

/-- The values of the forests along a list of operations are at most `V`. -/
def AllV (V : ℝ) (n : ℕ) : Forest → List EOp → Prop
  | F, [] => VBnd V n F
  | F, o :: os => VBnd V n F ∧ AllV V n (o.apply n F) os

lemma AllV.vbnd {V : ℝ} {n : ℕ} {F : Forest} {os : List EOp} (h : AllV V n F os) :
    VBnd V n F := by
  cases os with
  | nil => exact h
  | cons o os => exact h.1

/-- **A list of register-operand operations** (`ropsS_orun`), the forests along it having values
at most `V`. -/
theorem ropsS_orunC {P : Input} {W H B n : ℕ} (hW : B + 16 * (n + 1) ≤ W) (zr : ℕ → ℤ) {V : ℝ}
    (hH : 2 * V ≤ H) :
    ∀ (os : List ROp) {c : Config}, WordsBounded W c → ∀ {F : Forest} {G : List VT},
      LCTE B n F G c → (∀ o ∈ os, o.Ok c zr) → ValidOpsE n F (os.map (ROp.eop c zr)) →
      AllV V n F (os.map (ROp.eop c zr)) →
      ∃ c' G', ORunC P W H B n (ropsS B os) c F G c' (os.map (ROp.eop c zr)) G' os.length 0 ∧
        MemFrame B n (mem c) (mem c') ∧ RegFr c c'
  | [], c, hc, F, G, hS, _, _, _ =>
    ⟨c, G, ORunC.skip hc hS, MemFrame.refl B n _, RegFr.refl c⟩
  | o :: os, c, hc, F, G, hS, hok, hv, hA => by
    obtain ⟨c₁, G₁, h₁, hm₁, hf₁⟩ := rop_orunC (P := P) hW hc hS hA.1 hH zr o (hok o (by simp))
      hv.1
    have hok₁ : ∀ o' ∈ os, o'.Ok c₁ zr := fun o' ho' =>
      ROp.ok_congr hf₁ zr (hok o' (by simp [ho']))
    have hmap : os.map (ROp.eop c₁ zr) = os.map (ROp.eop c zr) :=
      List.map_congr_left fun o' ho' => ROp.eop_congr hf₁ zr (hok o' (by simp [ho']))
    have hv₁ : ValidOpsE n ((o.eop c zr).apply n F) (os.map (ROp.eop c₁ zr)) := by
      rw [hmap]; exact hv.2
    have hA₁ : AllV V n ((o.eop c zr).apply n F) (os.map (ROp.eop c₁ zr)) := by
      rw [hmap]; exact hA.2
    obtain ⟨c₂, G₂, h₂, hm₂, hf₂⟩ := ropsS_orunC hW zr hH os h₁.1.2.wb h₁.1.2.lcte hok₁ hv₁ hA₁
    refine ⟨c₂, G₂, ?_, MemFrame.trans B n hm₁ hm₂, hf₁.trans hf₂⟩
    have h := ORunC.seq h₁ (by rw [hmap] at h₂; exact h₂)
    simpa [ropsS, Nat.add_comm] using h

end DynTree

end PlanarFlow
