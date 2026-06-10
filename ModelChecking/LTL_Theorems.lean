import Mathlib.Data.Set.Insert
import Cslib.Computability.Languages.OmegaLanguage
import Mathlib.Order.Lattice
import Mathlib.Topology.Closure

import ModelChecking.LTL_NBW_Statement

open Cslib

def LTL.true {AP} [Inhabited AP] : LTL AP :=
  (LTL.atom default).or (LTL.atom default).not
def LTL.future {AP} [Inhabited AP] (φ : LTL AP) : LTL AP :=
  true.until φ
def LTL.global {AP} [Inhabited AP] (φ : LTL AP) : LTL AP :=
  φ.not.future.not
def LTL.implies {AP} (φ₁ φ₂ : LTL AP) : LTL AP :=
  φ₁.not.or φ₂
def LTL.and {AP} (φ₁ φ₂ : LTL AP) : LTL AP :=
  (φ₁.not.or φ₂.not).not

def LTL.lang {AP} (φ : LTL AP) : ωLanguage (Letter AP) := ⟨{ t | φ.language t }⟩

namespace ltl_not
scoped prefix:50 " G " => LTL.global
scoped prefix:50 " F " => LTL.future
scoped infixr:50 " → " => LTL.implies
scoped infixr:35 " ∧ " => LTL.and
scoped infixr:30 " ∨ " => LTL.or
scoped notation:max "¬" p:40 => LTL.not p
end ltl_not

open ltl_not in
example {AP} [Inhabited AP] (a b : LTL AP)
  : (G (a → F b)).lang ≤ (G F (a → b)).lang
    := by
  simp [LTL.lang, LTL.language, LTL.global, LTL.implies, LTL.future, LTL.true]
  intros t H n
  specialize H n
  by_cases all_a : ∀ i, a.language (fun j => t (j + i + n))
  · have := all_a 0
    simp at this
    specialize H this
    obtain ⟨n_b, Hb⟩ := H
    exists n_b
    intros _
    exact Hb
  · simp at all_a
    obtain ⟨n_not_a, Ha⟩ := all_a
    exists n_not_a
    intros _
    contradiction

open ltl_not in
example {AP} (a b : LTL AP)
  : (a.lang ≤ b.lang) ↔ ((a → b).lang = ⊤)
    := by
  simp [LTL.lang, LTL.language, LTL.implies, ωLanguage.le_def, ωLanguage.top_def, Set.eq_univ_iff_forall]
  grind

open ltl_not in
example {AP} [Inhabited AP] (a b : LTL AP)
  : (G F (a ∧ b)).lang ≤ (G F a ∧ G F b).lang
    := by
  simp [LTL.lang, LTL.language, LTL.global, LTL.and, LTL.future, LTL.true]
  intros t H
  constructor
  · intros n
    obtain ⟨n', H⟩ := H n
    exists n'
    exact H.left
  · intros n
    obtain ⟨n', H⟩ := H n
    exists n'
    exact H.right

open ltl_not in
example {AP} [Inhabited AP] (a b x : LTL AP)
  : ((G F x) → G (a → F b)).lang ≤ (G (a → F (b ∨ ¬x))).lang
    := by
  simp [LTL.lang, LTL.language, LTL.global, LTL.future, LTL.implies, LTL.true]
  intros t H n Ha
  rcases H with ⟨i, H⟩|H
  · specialize H n
    exists i
    grind
  · specialize H n Ha
    obtain ⟨i, H⟩ := H
    exists i
    grind

abbrev InfWord S := ℕ → S
-- abbrev FinWord S := List S

/-- Linear time property. -/
-- abbrev LTProp T := Set (InfWord T)

-- abbrev LTProp.Sat {T} (M P : LTProp T) := M ⊆ P

class HasSat (α β : Type u) where
  sat : α → β → Prop
infixl:25 " ⊨ " => HasSat.sat

-- instance {S} : HasSat (LTProp S) (LTProp S) := ⟨LTProp.Sat⟩

-- def LTL.ltp {AP} (φ : LTL AP) : LTProp (Letter AP) := { t | φ.language t }

open ltl_not in
example {AP} (M : ωLanguage (Letter AP)) (A P : LTL AP)
  : (M ⊓ A.lang ≤ P.lang) ↔ (M ≤ (A → P).lang)
    := by
  simp [LTL.language, LTL.lang, LTL.implies, ωLanguage.le_def, ωLanguage.inf_def, Set.setOf_or, ←Set.compl_setOf]
  grind

def LTProp.stable {T} : ωLanguage T := ⟨{ t | ∃ x, ∀ i, t i = x }⟩
def LTProp.const {S} (val : S) : ωLanguage S := ⟨{ t | ∀ i, t i = val }⟩

structure LTS (S : Type) where
  /-- The type of states. -/
  Q : Type
  /-- The set of starting states. -/
  q₀ : Set Q
  /-- The transition relation. -/
  δ : Q → S → Q → Prop

-- def LTS.finrun {S} (A : LTS S) (w : FinWord S) (p : Vector A.Q (w.length + 1)) :=
--   p[0] ∈ A.q₀ ∧ ∀ i, (_ : i < w.length) → A.δ p[i] w[i] p[i + 1]

def LTS.infrun {S} (A : LTS S) (w : InfWord S) (p : ℕ → A.Q) :=
  p 0 ∈ A.q₀ ∧ ∀ i, A.δ (p i) (w i) (p (i + 1))

def LTS.lang {S} (A : LTS S) : ωLanguage S := ⟨{ w | ∃ p, A.infrun w p }⟩
def NBW.lang {S} (A : NBW S) : ωLanguage S := ⟨{ w | A.language w }⟩

-- structure NFA (S : Type) extends LTS S where
--   F : Set Q

-- def NFA.accepts {S} (A : NFA S) (w : FinWord S) :=
--   ∃ p, A.finrun w p ∧ p[w.length] ∈ A.F

-- def NFA.lang {S} (A : NFA S) := { w | A.accepts w }

def LTS.stable {S} : LTS S := {
  Q := Option S
  q₀ := {none}
  δ q s q' :=
    match q with
    | none => q' = some s
    | some v => q = q' ∧ s = v
}

theorem LTS.stable_lang {S}
    : LTS.stable (S := S).lang = LTProp.stable := by
  unfold LTS.stable
  simp [LTS.lang, LTS.infrun, LTProp.stable]
  apply Set.ext; intros w
  constructor
  · rintro ⟨p, p0, hp⟩
    have H : p = (fun i => if i = 0 then none else some (w 0)) := by
      funext i; induction i <;> grind
    exists w 0
    intros i
    specialize hp i
    grind
  · rintro ⟨v⟩
    exists (fun i => if i = 0 then none else some v)
    grind

def LTS.const {S} (val : S) : LTS S := {
  Q := Unit
  q₀ := Set.univ
  δ _ s _ := s = val
}

theorem LTS.const_const
  {S} (val : S)
    : (LTS.const val).lang = LTProp.const val := by
  unfold LTS.const
  simp [LTProp.const, LTS.lang, LTS.lang, LTS.infrun]

def LTS.toNBW {S} (M : LTS S) : NBW S := { M with F := Set.univ }

theorem LTS.toNBW_lang {S} (M : LTS S) : M.lang = M.toNBW.lang := by
  unfold LTS.lang LTS.toNBW NBW.lang NBW.language NBW.run LTS.infrun
  ext; simp; intros; exists ?_; rfl

def LTS.prod {S} (A B : LTS S) : LTS S := {
  Q := A.Q × B.Q
  q₀ := A.q₀ ×ˢ B.q₀
  δ := fun (a, b) s (a', b') => A.δ a s a' ∧ B.δ b s b'
}

def NBW.prod {S} (A B : NBW S) : NBW S := {
  Q := A.Q × B.Q × Bool
  q₀ := A.q₀ ×ˢ B.q₀ ×ˢ {false}
  δ := fun (qa, qb, x) s (qa', qb', x') =>
    A.δ qa s qa' ∧
    B.δ qb s qb' ∧
    match x, x' with
    | false, false => qa ∉ A.F
    | false, true => qa ∈ A.F
    | true, false => qb ∈ B.F
    | true, true => qb ∉ B.F
  F := { (_, qb, x) : _ | qb ∈ B.F ∧ x = true }
}

noncomputable def NBW.prod_lang.phase {α β} (pa : ℕ → α) (pb : ℕ → β) (AF : Set α) (BF : Set β) (i : ℕ) : Bool :=
  match i with
  | 0 => false
  | i' + 1 =>
    let : DecidablePred (· ∈ AF) := by classical infer_instance
    let : DecidablePred (· ∈ BF) := by classical infer_instance
    match phase pa pb AF BF i' with
    | false => if pa i' ∈ AF then true else false
    | true => if pb i' ∈ BF then false else true

theorem NBW.prod_lang {S} (A B : NBW S) : (A.prod B).lang = A.lang ⊓ B.lang := by
  unfold NBW.lang NBW.language NBW.prod NBW.run
  simp [ωLanguage.inf_def]
  apply Set.ext; intros w
  repeat rw [Set.mem_setOf]
  simp
  constructor
  · rintro ⟨p, ⟨⟨p0, ⟨p1, p2⟩⟩, p3⟩, p4⟩
    constructor
    · exists Prod.fst ∘ p
      simp
      refine ⟨⟨p0, ?_⟩, ?_⟩
      · grind
      · intros i
        obtain ⟨j, jle, ⟨hj1, hj2⟩⟩ := p4 i
        have hpj1 : (p (j + 1)).2.2 = false := by grind
        by_contra
        simp at this
        have false_inf : ∀ i > j, (p i).2.2 = false := by
          intros i; induction i <;> grind
        have := p4 (j + 1)
        grind
    · exists Prod.fst ∘ Prod.snd ∘ p
      simp
      refine ⟨⟨p1, ?_⟩, ?_⟩
      · grind
      · intros i
        obtain ⟨j, jle, _⟩ := p4 i
        exists j, jle
        grind
  · rintro ⟨⟨pa, pa1, pa2⟩, ⟨pb, pb1, pb2⟩⟩
    exists fun i => (pa i, pb i, NBW.prod_lang.phase pa pb A.F B.F i)
    simp
    refine ⟨?_, ?_⟩
    · grind [prod_lang.phase]
    · by_contra
      simp at this
      obtain ⟨x, H⟩ := this
      obtain ⟨j, lj, Ha⟩ := pa2 x
      have : ∃ k > j, pb k ∈ B.F ∧ ∀ i, j < i → i < k → pb i ∉ B.F := by
        by_contra
        simp at this
        obtain ⟨upper, le_upper, H_upper⟩ := pb2 (j + 1)
        have : ∀ i, ∃ n, pb n ∈ B.F ∧ j < n ∧ n < upper - i := by
          intros i; induction i <;> grind
        specialize this upper
        grind
      obtain ⟨k, Hnext⟩ := this
      have : ∀ i, j < i → i ≤ k → prod_lang.phase pa pb A.F B.F i = true := by
        intros i; induction i <;> grind [prod_lang.phase]
      specialize H k (by omega) (by grind)
      specialize this k (by omega) (by omega)
      grind

theorem LTS.prod_lang
  {S} (A B : LTS S)
    : (A.prod B).lang = A.lang ⊓ B.lang := by
  unfold LTS.prod
  simp [LTS.lang, LTS.infrun, ωLanguage.inf_def]
  apply Set.ext; intros w
  constructor
  · rintro ⟨p⟩
    constructor
    · exists (fun x => (p x).fst); grind
    · exists (fun x => (p x).snd); grind
  · rintro ⟨⟨f⟩, ⟨g⟩⟩
    exists (fun x => (f x, g x))
    grind

def LTS.lift_left {α β} (A : LTS β) : LTS (α × β) := {
  Q := A.Q
  q₀ := A.q₀
  δ q s q' := A.δ q s.snd q'
}
def LTS.lift_right {α β} (A : LTS α) : LTS (α × β) := {
  Q := A.Q
  q₀ := A.q₀
  δ q s q' := A.δ q s.fst q'
}

def LTS.erase_right {α β} (A : LTS (α × β)) : LTS α := {
  Q := A.Q
  q₀ := A.q₀
  δ q a q' := ∃ b, A.δ q (a, b) q'
}

def LTS.tie_right {α β} (A : LTS (α × β)) (b : β) : LTS α := {
  Q := A.Q
  q₀ := A.q₀
  δ q a q' := A.δ q (a, b) q'
}

def Cslib.ωLanguage.lift_left {α β} (P : ωLanguage β) : ωLanguage (α × β) := ⟨{ w | ⟨Prod.snd ∘ w⟩ ∈ P }⟩
theorem LTS.lift_left_lang
  {α β} (A : LTS β) : A.lift_left (α := α).lang = A.lang.lift_left := by rfl

def Cslib.ωLanguage.lift_right {α β} (P : ωLanguage α) : ωLanguage (α × β) := ⟨{ w | ⟨Prod.fst ∘ w⟩ ∈ P }⟩
theorem LTS.lift_right_lang
  {α β} (A : LTS α) : A.lift_right (β := β).lang = A.lang.lift_right := by rfl

def LTProp.tie_right {α β} (P : ωLanguage (α × β)) (b : β) : ωLanguage α :=
  ⟨{ w | ⟨fun i => (w i, b)⟩ ∈ P }⟩
theorem LTS.tie_right_lang
  {α β} (A : LTS (α × β)) (b : β)
    : (A.tie_right b).lang = LTProp.tie_right (A.lang) b := by
  rfl

def NBW.tie_right {α β} (A : NBW (α × β)) (b : β) : NBW α := {
  Q := A.Q
  q₀ := A.q₀
  δ q a q' := A.δ q (a, b) q'
  F := A.F
}
theorem NBW.tie_right_lang
  {α β} (A : NBW (α × β)) (b : β)
    : (A.tie_right b).lang = LTProp.tie_right (A.lang) b := by
  rfl

theorem LTS.tie_eq_const_erase
  {α β} (A : LTS (α × β)) (b : β)
    : (A.prod (LTS.const b).lift_left).erase_right.lang = (A.tie_right b).lang := by
  unfold LTS.prod LTS.lift_left LTS.const LTS.erase_right
  simp [LTS.lang, LTS.tie_right, LTS.infrun]
  apply Set.ext; intros w
  repeat rw [Set.mem_setOf]
  constructor
  · rintro ⟨p, p0, Hp⟩
    exists fun i => (p i).fst
  · rintro ⟨p, p0, Hp⟩
    exists fun i => (p i, ())

def add_symvar {α β} (A : LTS β) : LTS (α × β) := LTS.prod (LTS.stable).lift_right A.lift_left

def LTS.SatNBW {S} (M : LTS S) (P : NBW S) := M.lang ≤ P.lang
instance {S} : HasSat (LTS S) (NBW S) := ⟨LTS.SatNBW⟩

theorem symvar_thm
  {C S} (M : ωLanguage S) (P : ωLanguage (S × C))
    : ((M.lift_right ⊓ (LTProp.stable (T := C)).lift_left) ≤ P) ↔ (∀ c : C, M ≤ LTProp.tie_right P c) := by
  simp [LTProp.stable, ωLanguage.lift_left, ωLanguage.lift_right, LTProp.tie_right]
  constructor
  · simp [Set.inter_def, Set.subset_def, ωLanguage.le_def, ωLanguage.inf_def, ωLanguage.mem_def]
    intros H c w Hw
    apply H (w ·, c) Hw c (by intro; rfl)
  · simp [Set.inter_def, Set.subset_def, ωLanguage.le_def, ωLanguage.inf_def, ωLanguage.mem_def]
    intros H w Hw c
    specialize H c (Prod.fst ∘ w) Hw
    intros h
    simp at H
    rw [show w = (fun i => ((w i).fst, (w i).snd)) by rfl]
    grind

theorem symvar_thm_automata
  {C S} (M : LTS S) (P : NBW (S × C))
    : (M.lift_right.prod (LTS.stable (S := C).lift_left) ⊨ P) ↔ (∀ c : C, M ⊨ P.tie_right c) := by
  simp [HasSat.sat, LTS.SatNBW]
  rw [LTS.prod_lang]
  simp [NBW.tie_right_lang]
  rw [LTS.lift_right_lang]
  rw [LTS.lift_left_lang]
  rw [LTS.stable_lang]
  apply symvar_thm

theorem agt_interp
  {S} [SemilatticeInf S] (A M P : S)
    : A ⊓ M ≤ P ↔ (∀ E, E ⊓ M ≤ A → E ⊓ M ≤ P) := by
  constructor
  · intro h E hEA
    exact le_trans (le_inf hEA inf_le_right) h
  · intro h
    exact h A inf_le_left

example
  {S₁ S₂ α}
  (M₁ : ωLanguage (S₁ × α)) (M₂ : ωLanguage (α × S₂))
  (I : ωLanguage α) (P : ωLanguage (α × S₂))
    : M₁ ≤ I.lift_left ∧ I.lift_right ⊓ M₂ ≤ P →
      ((M₁.lift_right (β := S₂)).map (fun ((a, b), c) => (a, b, c))) ⊓
      (M₂.lift_left (α := S₁)) ≤ P.lift_left := by
  open ωLanguage in simp [mem_def, map_def, inf_def, lift_right, lift_left, le_def, Set.subset_def]
  intros h1 h2 w h4 h5
  specialize h1 _ h4
  apply h2 _ (by exact h1)
  grind

notation "⟨" A "|" M "|" P "⟩" => A ⊓ M ≤ P

theorem agt_trans
  {S} [SemilatticeInf S] (A M P Q : S)
    : ⟨A|M|P⟩ → ⟨P|M|Q⟩ → ⟨A|M|Q⟩ := by
  grind [agt_interp]

theorem agt_trans_2 {S} [SemilatticeInf S] (A M₁ M₂ P Q : S)
  : ⟨A|M₁|P⟩ → ⟨P|M₂|Q⟩ → ⟨A|M₁ ⊓ M₂|Q⟩ := by
  repeat rw [agt_interp]
  intros T1 T2 E HA
  specialize T2 (E ⊓ M₁)
  rw [←inf_assoc]
  apply T2; clear T2
  specialize T1 (E ⊓ M₂)
  rw [inf_assoc]
  rw [inf_comm M₁]
  rw [←inf_assoc]
  apply T1; clear T1
  rw [inf_assoc]
  rw [inf_comm M₂]
  assumption

theorem rule_asym {S} [SemilatticeInf S] (A M₁ M₂ P X : S)
  : ⟨A|M₁|P⟩ → ⟨X|M₂|A⟩ → ⟨X|M₁ ⊓ M₂|P⟩ := by
  repeat rw [agt_interp]
  intros T1 T2 E _
  specialize T1 (E ⊓ M₂)
  rw [inf_comm M₁]
  rw [←inf_assoc]
  apply T1
  specialize T2 (E ⊓ M₁)
  rw [inf_assoc]
  rw [inf_comm M₂]
  rw [←inf_assoc]
  apply T2
  rw [inf_assoc]
  assumption

theorem rule_circ
  {S} [SemilatticeInf S] [OrderTop S] (A₁ A₂ M₁ M₂ P : S)
    : ⟨A₁|M₁|P⟩ → ⟨A₂|M₂|A₁⟩ → ⟨⊤|M₁|A₂⟩ → M₁ ⊓ M₂ ≤ P := by
  rw [agt_interp]
  rw [agt_interp]
  rw [agt_interp]
  intros T1 T2 T3
  rw [inf_comm]
  apply T1 M₂
  rw [inf_comm]
  apply T2 M₁
  rw [inf_comm]
  apply T3 M₂
  exact le_top
