import Mathlib.Topology.Order
import Cslib.Computability.Languages.OmegaLanguage

open Cslib (ωLanguage ωSequence)

namespace AmlaEtAl

def Word T := ωSequence T ⊕ List T
def Word.prefix {T} (a b : Word T) :=
  match a, b with
  | .inl a, .inl b => a = b
  | .inl a, .inr b => False
  | .inr a, .inl b => ∀ i (_ : i < a.length), a[i] = b i
  | .inr a, .inr b => ∃ (_ : a.length ≤ b.length), ∀ i (_ : i < a.length), a[i] = b[i]

instance {T} : PartialOrder (Word T) where
  le := Word.prefix
  le_refl a := by cases a <;> simp [Word.prefix]
  le_trans := by rintro (a|a) (b|b) (c|c) <;> grind [Word.prefix]
  le_antisymm := by
    rintro (a|a) (b|b) <;> simp [Word.prefix]
    · grind
    · intros; congr; ext; grind

def Word.infs {T} : Set (Word T) := { w | w.isLeft }
def Word.fins {T} : Set (Word T) := { w | w.isRight }

theorem Word.infs_downward_closed {T} (p w : Word T) :
    w ∈ Word.fins → p ≤ w → p ∈ Word.fins := by
  cases p <;> cases w <;> simp [Word.fins]
  simp [LE.le, Word.prefix]

instance wf_fins {T} : WellFoundedLT { w // w ∈ Word.fins (T := T) } where
  wf := by
    refine Subrelation.wf ?_ (measure (fun ⟨w, pw⟩ => match w with | .inl w => (by exfalso; simp [Word.fins] at pw) | .inr w => w.length)).wf
    simp [WellFoundedRelation.rel, Word.fins]
    rintro (u|u) (v|v) h <;> try contradiction
    simp [InvImage]
    simp [LT.lt] at h
    simp [Word.prefix] at h
    grind

abbrev Lang T := Set (Word T)

instance {T} : TopologicalSpace (Word T) :=
  TopologicalSpace.generateFrom
    { U | ∃ p ∈ Word.fins, U = Set.Ici p }

abbrev FinWord T := List T
instance {T} : PartialOrder (FinWord T) where
  le := List.IsPrefix
  le_refl a := by simp
  le_trans := by grind
  le_antisymm := by simp [List.IsPrefix]
instance wf_finword {T} : WellFoundedLT (FinWord T) where
  wf := by
    refine Subrelation.wf ?_ (measure List.length).wf
    simp [WellFoundedRelation.rel]
    rintro (u|⟨u, ut⟩) (v|⟨v, vt⟩) h <;> simp [InvImage] <;> simp [LT.lt] at h
    simp [List.IsPrefix] at h
    rcases h with ⟨⟨rfl, ⟨w, rfl⟩⟩, h2⟩
    simp
    grind

lemma dropLast_lt {T} {w : List T} (h : w ≠ []) : w.dropLast < w := by
  simp [LT.lt, List.IsPrefix]
  constructor
  · exists [w.getLast h]
    apply List.dropLast_concat_getLast
  · intros t H
    have : (w ++ t).length = w.dropLast.length := by rw [H]
    simp at this
    have : w.length > 0 := by grind
    omega

def DoesNotBlock {S} (Q P : Set (FinWord S)) :=
  ([] ∈ P → [] ∈ P ∩ Q) ∧
  ∀ x y, x ∈ P → y < x → y ∈ P ∩ Q → x ∈ P ∩ Q

def DownwardClosed {S} (Q : Set (FinWord S)) :=
  ∀ x y, x ∈ Q → y ≤ x → y ∈ Q

lemma lemma1
  {S}
  {P₁ P₂ Q₁ Q₂ : Set (FinWord S)}
  (hdc : DownwardClosed P₁ ∧ DownwardClosed P₂)
  -- (ha : DoesNotBlock Q₂ P₁ ∧ DoesNotBlock Q₁ P₂)
  (ha : DoesNotBlock Q₂ P₁)
  (hb : P₁ ∩ Q₂ ⊆ Q₁)
  -- (hc : Q₁ ∩ P₂ ⊆ Q₂)
    : P₁ ∩ P₂ ⊆ Q₁ ∩ Q₂ := by
  rw [Set.subset_def]
  simp only [DoesNotBlock] at ha
  -- rcases ha with ⟨⟨ha11, ha12⟩, ⟨ha21, ha22⟩⟩
  rcases ha with ⟨ha21, ha22⟩
  intros w
  apply wf_finword.induction w
  simp
  intros w ih h1 h2
  by_cases w_nil : w = []
  · grind
  · specialize ih w.dropLast
    specialize ih (dropLast_lt w_nil)
    have tp1 : w.dropLast ∈ P₁ := hdc.left w w.dropLast h1 (dropLast_lt w_nil).le
    have tp2 : w.dropLast ∈ P₂ := hdc.right w w.dropLast h2 (dropLast_lt w_nil).le
    specialize ih tp1 tp2
    -- specialize ha12 w w.dropLast h1 (dropLast_lt w_nil) (by grind)
    specialize ha22 w w.dropLast h1 (dropLast_lt w_nil) (by grind)

    grind

theorem rule_circ_2
  {S}
  (E P₁ P₂ Q₁ Q₂ T : Set (FinWord S))
  (hdc : DownwardClosed P₁ ∧ DownwardClosed P₂)
  (ha : DoesNotBlock Q₂ P₁)
  (hb : P₁ ∩ Q₂ ⊆ Q₁)
  -- (hc : Q₁ ∩ P₂ ⊆ Q₂)
  (hd : E ∩ Q₁ ∩ Q₂ ⊆ T)
  -- (h_safety : IsClosed T)
  -- (he : E ⊓ P₁ ⊓ (closure T) ≤ T ⊔ Q₁ ⊔ Q₂)
    : E ∩ P₁ ∩ P₂ ⊆ T := by
  have := lemma1 hdc ha (Q₁ := Q₁)
  rw [Set.inter_assoc] at hd ⊢
  grind

end AmlaEtAl
