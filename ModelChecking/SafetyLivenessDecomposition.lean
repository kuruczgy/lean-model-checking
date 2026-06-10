import Mathlib.Data.Set.Basic
import Mathlib.Data.List.OfFn
import Cslib.Computability.Languages.OmegaLanguage
import Mathlib.Topology.Constructions

open Cslib (ωLanguage ωSequence)

namespace SafetyLivenessDecomposition

abbrev FinWord T := List T

def FinWord.append {T} (a : FinWord T) (b : ωSequence T) : ωSequence T :=
  fun i =>
    if _ : i < a.length then a[i]
    else b (i - a.length)

def _root_.Cslib.ωSequence.slice {T} (w : ωSequence T) (k : ℕ) : FinWord T :=
  List.ofFn (fun (i : Fin k) => w i)

-- Definitions based on:
-- Alpern, Bowen; Schneider, Fred B. Recognizing safety and liveness
-- https://doi.org/10.1016/0020-0190(85)90056-0
def EveryCEXFinite {T} (P : ωLanguage T) :=
  ∀ (σ : ωSequence T),
  σ ∉ P →
  ∃ (i : ℕ),
  ∀ (β : ωSequence T),
  (σ.slice i).append β ∉ P
def NoFiniteCEX {T} (P : ωLanguage T) :=
  ∀ (α : FinWord T),
  ∃ (β : ωSequence T),
  α.append β ∈ P

instance {S} [TopologicalSpace S] : TopologicalSpace (ωSequence S) :=
  TopologicalSpace.induced ωSequence.get Pi.topologicalSpace

/-- Safety property is a closed set. -/
def SafetyProp {S} [TopologicalSpace S] (L : ωLanguage S) := IsClosed L.toSet
/-- Liveness property is a dense set. -/
def LivenessProp {S} [TopologicalSpace S] (L : ωLanguage S) := Dense L.toSet

def safetyPart {S} [TopologicalSpace S] (P : ωLanguage S) : ωLanguage S :=
  ⟨closure P.toSet⟩
def livenessPart {S} [TopologicalSpace S] (P : ωLanguage S) : ωLanguage S :=
  ⟨P.toSet ∪ (closure P.toSet)ᶜ⟩

theorem safetyPart_isSafety {S} [TopologicalSpace S] (P : ωLanguage S) :
    SafetyProp (safetyPart P) := by
  dsimp [SafetyProp, safetyPart]
  exact isClosed_closure

theorem livenessPart_isLiveness {S} [TopologicalSpace S] (P : ωLanguage S) :
    LivenessProp (livenessPart P) := by
  dsimp [LivenessProp, livenessPart, Dense]
  intros x
  rw [closure_union]
  have := subset_closure (s := (closure P.toSet)ᶜ)
  grind

theorem safetyPart_inf_livenessPart {S} [TopologicalSpace S] (P : ωLanguage S) :
    safetyPart P ⊓ livenessPart P = P := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hcl, hp_or⟩
    rcases hp_or with hp | hnot
    · exact hp
    · exact False.elim (hnot hcl)
  · intro hw
    constructor
    · exact subset_closure hw
    · exact Or.inl hw

@[simp] lemma slice_length {T} (σ : ωSequence T) (n : ℕ) : (σ.slice n).length = n := by
  simp [ωSequence.slice]

@[simp] lemma slice_get {T} (σ : ωSequence T) (n k : ℕ)
    (hk : k < (σ.slice n).length) :
    (σ.slice n)[k] = σ k := by
  simp [ωSequence.slice]

lemma slice_append {T} (α : FinWord T) (β : ωSequence T) :
    (α.append β).slice α.length = α := by
  have hfun : (fun i : Fin α.length => (α.append β) i)
      = fun i : Fin α.length => α[i] := by
    funext i
    simp [FinWord.append, i.2]
  simp [ωSequence.slice, hfun]

lemma append_slice_eq_self {T} (σ : ωSequence T) (n : ℕ) :
    (σ.slice n).append (fun k => σ (k + n)) = σ := by
  rcases σ with ⟨σ⟩
  simp [FinWord.append]
  funext k
  by_cases hk : k < n
  · simp [hk]
  · have hle : n ≤ k := Nat.le_of_not_lt hk
    simp [hk, Nat.sub_add_cancel hle]

lemma slice_append_get_lt {T} (σ : ωSequence T) (k : ℕ) (β : ωSequence T) (i : ℕ) (_ : i < k) :
    (σ.slice k).append β i = σ i := by
  simp [FinWord.append]
  grind

lemma slice_append_get_ge {T} (σ : ωSequence T) (k : ℕ) (β : ωSequence T) (i : ℕ) (hi : k ≤ i) :
    (σ.slice k).append β i = β (i - k) := by
  simp only [FinWord.append, ωSequence.slice, List.length_ofFn]
  exact dif_neg (not_lt.mpr hi)

def cylinder {S} (x : ωSequence S) (n : ℕ) : ωLanguage S :=
  ⟨{ y | ∀ i, i < n → y i = x i }⟩

theorem cylinder_clopen {S} [TopologicalSpace S] [DiscreteTopology S] (σ : ωSequence S) (n : ℕ) :
    IsClopen (cylinder σ n).toSet := by
  have eq : (cylinder σ n).toSet = ⋂ i : Fin n, {τ : ωSequence S | τ i = σ i} := by
    ext τ
    simp [cylinder]
    constructor
    · rintro H ⟨i, ih⟩; exact H i ih
    · rintro H i ih; exact H ⟨i, ih⟩
  have hcont : ∀ i : Fin n, Continuous (fun τ : ωSequence S => τ i.val) := fun i => by
    simpa using
      (continuous_apply i.val).comp
        (continuous_induced_dom : Continuous (ωSequence.get : ωSequence S → ℕ → S))
  rw [eq]
  exact ⟨isClosed_iInter fun i => by simpa using (isClosed_discrete {σ i.val}).preimage (hcont i),
         isOpen_iInter_of_finite fun i => by simpa using (isOpen_discrete {σ i.val}).preimage (hcont i)⟩

lemma mem_cylinder_iff_exists_append {T} (σ τ : ωSequence T) (k : ℕ) :
    τ ∈ cylinder σ k ↔ ∃ β, (σ.slice k).append β = τ := by
  simp [cylinder, ωLanguage.mem_def]
  constructor
  · intro h
    refine ⟨fun i => τ (i + k), ?_⟩
    rcases τ with ⟨τ⟩
    simp [FinWord.append]
    funext i
    split_ifs with hi
    · simp at h
      exact (h _ hi).symm
    · congr 1; omega
  · rintro ⟨β, rfl⟩ i hi
    apply slice_append_get_lt σ
    exact hi

theorem LivenessProp_iff_NoFiniteCEX
  {S} (L : ωLanguage S) [TopologicalSpace S] [DiscreteTopology S] [Nonempty S]
    : LivenessProp L ↔ NoFiniteCEX L := by
  -- Lemma: every open set containing x also contains some cylinder around x.
  -- This holds because the topology on ωSequence S is the product topology
  -- (via ωSequence.get), and with discrete factors every Pi-basic open set
  -- determined by finitely many coordinates i₁,...,iₙ contains the cylinder
  -- of depth (max {i₁,...,iₙ} + 1).
  have nhd_has_cyl : ∀ (x : ωSequence S) (U : Set (ωSequence S)),
      IsOpen U → x ∈ U → ∃ n : ℕ, (cylinder x n).toSet ⊆ U := by
    intro x U hU hxU
    -- Unfold the induced topology to get an open V in Pi(ℕ → S)
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    -- V open in Pi topology: around x.get there is a Pi-basic open set
    rw [isOpen_pi_iff] at hV
    obtain ⟨I, f, hIf, hIsub⟩ := hV _ hxU
    -- Use depth = (max coordinate in I) + 1
    refine ⟨(I.sup id) + 1, fun τ hτ => hIsub ?_⟩
    -- Show τ.get ∈ Set.pi ↑I f, i.e. for all i ∈ I, τ i ∈ f i
    intro i hi
    simp only [cylinder, Set.mem_setOf_eq] at hτ
    have hin : i < (I.sup id) + 1 :=
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    -- τ ∈ cylinder x n means τ agrees with x on positions 0..n-1
    rw [show τ.get i = τ i by rfl]
    rw [hτ i hin]
    -- x i ∈ f i because x.get ∈ Set.pi ↑I f
    exact (hIf i hi).2
  constructor
  · -- (→) Dense L implies LivenessPropSpec L
    intro hdense α
    -- Extend α arbitrarily to get σ : ωSequence S
    let σ : ωSequence S := α.append ⟨fun _ => Classical.arbitrary S⟩
    -- cylinder σ α.length is an open neighbourhood of σ (it's actually clopen)
    -- Dense L meets every non-empty open set, in particular this cylinder
    obtain ⟨τ, hτcyl, hτL⟩ := hdense.inter_open_nonempty _ (cylinder_clopen σ α.length).2 ⟨σ, by simp [cylinder]⟩
    -- τ ∈ cylinder σ α.length means τ = (σ.slice α.length).append β for some β
    rw [←ωLanguage.mem_def] at hτcyl
    rw [mem_cylinder_iff_exists_append] at hτcyl
    obtain ⟨β, hβ⟩ := hτcyl
    -- σ.slice α.length = α  (the first α.length elements of α.append _ are α)
    exact ⟨β, slice_append α _ ▸ hβ ▸ hτL⟩
  · -- (←) LivenessPropSpec L implies Dense L
    intro hspec
    unfold LivenessProp
    rw [dense_iff_inter_open]
    -- For any non-empty open U, we must find a point of L in U
    intro U hU ⟨x, hxU⟩
    -- Find a cylinder of depth n around x inside U
    obtain ⟨n, hn⟩ := nhd_has_cyl x U hU hxU
    -- By liveness, the finite prefix x.slice n extends to some β with the full
    -- sequence (x.slice n).append β ∈ L
    obtain ⟨β, hβ⟩ := hspec (x.slice n)
    -- This sequence is in cylinder x n (it matches x on positions 0..n-1)
    -- hence in U ⊆ U, and it's in L
    exact ⟨(x.slice n).append β, hn ((mem_cylinder_iff_exists_append x _ n).mpr ⟨β, rfl⟩), hβ⟩

theorem SafetyProp_iff_EveryCEXFinite
  {S} (L : ωLanguage S) [TopologicalSpace S] [DiscreteTopology S]
    : SafetyProp L ↔ EveryCEXFinite L := by
  simp only [SafetyProp, EveryCEXFinite]
  rw [← isOpen_compl_iff]
  -- Work in the induced topology: open sets are preimages of open sets in the Pi topology
  rw [isOpen_induced_iff]
  constructor
  · -- (→) Safety (closed) implies finite-witness spec
    rintro ⟨V, hV_open, hV_eq⟩ σ hσ
    -- σ lies in the open complement, so ωSequence.get σ ∈ V
    have hσV : ωSequence.get σ ∈ V := by
      have : σ ∈ (L.toSet)ᶜ := hσ
      rwa [← hV_eq, Set.mem_preimage] at this
    -- By openness of V in the Pi topology, get a cylinder neighborhood
    rw [isOpen_pi_iff] at hV_open
    obtain ⟨I, U, hU_open, hU_sub⟩ := hV_open (ωSequence.get σ) hσV
    -- Let k be one past the maximum index in I
    refine ⟨if h : I.Nonempty then I.sup' h id + 1 else 0, fun β => ?_⟩
    -- (σ.slice k).append β lies in Lᶜ: show its `get` is in V
    -- Convert `∉ L` to `ωSequence.get _ ∉ V's preimage complement`
    intro hmem
    -- hmem : (σ.slice k).append β ∈ L
    -- We'll show ωSequence.get ((σ.slice k).append β) ∈ V and derive a contradiction
    -- via hV_eq: ωSequence.get ⁻¹' V = Lᶜ, so membership in V means ∉ L
    have hget_in_V : ωSequence.get ((σ.slice (if h : I.Nonempty then I.sup' h id + 1 else 0)).append β) ∈ V := by
      apply hU_sub
      intro i hi
      -- i ∈ I, so i < k
      have hi_lt : i < (if h : I.Nonempty then I.sup' h id + 1 else 0) := by
        have hne : I.Nonempty := ⟨i, hi⟩
        simp only [hne, dite_true]
        exact Nat.lt_succ_of_le (Finset.le_sup' id hi)
      -- (σ.slice k).append β at position i equals σ i
      have heq : ωSequence.get ((σ.slice (if h : I.Nonempty then I.sup' h id + 1 else 0)).append β) i = σ i := by
        show (σ.slice _).append β i = σ i
        exact slice_append_get_lt σ _ β i hi_lt
      rw [heq]
      exact (hU_open i hi).2
    -- Now use hV_eq to transfer: get ∈ V means the sequence is in Lᶜ
    have hcompl : (σ.slice (if h : I.Nonempty then I.sup' h id + 1 else 0)).append β ∈ (L.toSet)ᶜ := by
      rw [← hV_eq]; exact hget_in_V
    exact hcompl hmem
  · -- (←) Finite-witness spec implies safety (closed)
    intro hSpec
    -- We exhibit V = (L.toSet)ᶜ itself (as a subset of ℕ → S); the induced preimage is Lᶜ
    refine ⟨
      (ωSequence.get '' L.toSet)ᶜ,
      ?_,
      by
        simp; apply Function.Injective.preimage_image
        simp [Function.Injective]
        rintro ⟨a⟩ ⟨b⟩
        simp
    ⟩
    -- Show (L.toSet)ᶜ is open in the Pi topology on ℕ → S
    rw [isOpen_pi_iff]
    intro σ hσ
    obtain ⟨k, hk⟩ := hSpec σ (by
      simp at hσ
      intros H
      specialize hσ ⟨σ⟩ H
      contradiction
    )
    -- Cylinder: match σ on {0, …, k-1}, use singletons (open in discrete topology)
    -- Pi.isOpen_iff shape: ∃ I U, (∀ i ∈ I, IsOpen (U i) ∧ σ i ∈ U i) ∧ (↑I).pi U ⊆ V
    refine ⟨Finset.range k, fun i => {σ i}, fun i hi => ?_, fun τ hτ => ?_⟩
    · -- openness of {σ i} and membership σ i ∈ {σ i}
      exact ⟨isOpen_discrete _, Set.mem_singleton _⟩
    · -- τ agrees with σ on range k → τ ∉ L (i.e., τ ∈ (L.toSet)ᶜ)
      simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range,
                 Set.mem_singleton_iff] at hτ
      obtain ⟨β, eq⟩ := (mem_cylinder_iff_exists_append ⟨σ⟩ ⟨τ⟩ k).mp (fun i hi => hτ i hi)
      specialize hk β
      rw [eq] at hk
      simp
      intros x h1 h2
      rw [←h2] at hk
      contradiction

-- Theorem statement written by hand
theorem safety_liveness_decomposition_explicit {T} [Nonempty T] (P : ωLanguage T)
    : ∃ (A B : ωLanguage T), EveryCEXFinite A ∧ NoFiniteCEX B ∧ (A ⊓ B = P) := by
  let : TopologicalSpace T := ⊥
  have : DiscreteTopology T := ⟨rfl⟩
  exists (safetyPart P), (livenessPart P)
  refine ⟨?_, ?_, safetyPart_inf_livenessPart P⟩
  · rw [←SafetyProp_iff_EveryCEXFinite]
    apply safetyPart_isSafety
  · rw [←LivenessProp_iff_NoFiniteCEX]
    apply livenessPart_isLiveness

end SafetyLivenessDecomposition
