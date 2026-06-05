import ModelChecking.LTL_NBW_Statement

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

def LTL.lang {AP} (φ : LTL AP) : Set (ℕ → Letter AP) := { t | φ.language t }

prefix:50 " G " => LTL.global
prefix:50 " F " => LTL.future
infixr:50 " => " => LTL.implies
infixr:35 " ∧ " => LTL.and
infixr:30 " ∨ " => LTL.or
notation:max "¬" p:40 => LTL.not p

example {AP} [Inhabited AP] (a b : LTL AP)
  : (G (a => F b)).lang ⊆ (G F (a => b)).lang
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

example {AP} (a b : LTL AP)
  : (a.lang ⊆ b.lang) ↔ (∀ t, (a => b).language t)
    := by
  simp [LTL.lang, LTL.language, LTL.implies]; grind

example {AP} [Inhabited AP] (a b : LTL AP)
  : (G F (a ∧ b)).lang ⊆ (G F a ∧ G F b).lang
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

example {AP} [Inhabited AP] (a b x : LTL AP)
  : ((G F x) => G (a => F b)).lang ⊆ (G (a => F (b ∨ ¬x))).lang
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

abbrev InfWord T := ℕ → T

/-- Linear time property. -/
abbrev LTProp T := Set (InfWord T)

def LTL.ltp {AP} (φ : LTL AP) : LTProp (Letter AP) := { t | φ.language t }

-- class HasSatisfies (α : Type u) where
--   satisfies : α → α → Prop

-- infixl:25 " ⊨ " => HasSatisfies.satisfies

-- instance {T} : HasSatisfies (LTProp T) where
--   satisfies M P := M ⊆ P

example {AP} (M : LTProp (Letter AP)) (A P : LTL AP) : (M ∩ A.ltp ⊆ P.ltp) ↔ (M ⊆ (A => P).ltp) := by
  simp only [LTL.language, LTL.ltp, LTL.implies]
  rw [Set.setOf_or]
  grind
