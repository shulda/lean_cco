import CCO.TransitionClosure.OriginalTerminalUniqueCoverReadout
import CCO.TransitionClosure.OriginalNamedHiddenCoordinates

/-!
# Source11 T02: finite STRONG fork intersections retain an external atom

The original named hidden coordinate carries proper meet-irreducibility
in the FULL old invariant lattice. The accepted original full order
isomorphism converts this to the exact `InfIrred` input of source07's
STRONG exact prime-intersection theorem.

Finite intersections below contain only actual diversity atoms. Their
nonemptiness is explicit; the source-specific two-copy SAP construction
must discharge it for the full old one-point type. The empty family is
the actual diversity palette, and properness of J handles this case
without an artificial STRONG identity atom or a nonempty-base premise.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice
open CCO.TransitionClosure CCO.QuotientTransport

universe u v w t

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

/-- A genuinely named proper FULL MI has the exact lattice-theoretic
meet-irreducibility used in the source STRONG-prime theorem. This is
transport through the actual FULL old order isomorphism, without any
claim about meet-irreducibility in a restricted represented sublattice. -/
theorem original_named_hidden_full_infIrred
    (H : HomogeneousSource S G) {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i) :
    letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
    InfIrred J.val := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  let e : ColourEq S i ≃o InvEq G (X i) :=
    originalFullColourEqInvEqOrderIso S H
  have hProper := J.property.2.1
  refine ⟨?_, ?_⟩
  · intro hMax
    apply hProper.1
    change e J.val = ⊤
    rw [hMax.eq_top]
    exact e.map_top
  · intro A B hAB
    have hMapped : e J.val = e A ⊓ e B := by
      rw [← e.map_inf, hAB]
    rcases hProper.2 (e A) (e B) hMapped with hA | hB
    · exact Or.inl (e.injective hA).symm
    · exact Or.inr (e.injective hB).symm

/-- Named hidden coordinates are proper in the FULL original
`ColourEq` order itself, as well as in the equivalent invariant order.
This supplies the strict old top inequality for source atom selection. -/
theorem original_named_hidden_full_proper
    (H : HomogeneousSource S G) {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i) : J.val ≠ ⊤ := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  have hMI : InfIrred J.val := original_named_hidden_full_infIrred S H J
  intro hTop
  apply hMI.1
  rw [hTop]
  exact isMax_top

/-- A proper original equivalence cannot contain ALL actual same-sort
diversity atoms. Actual unequal pairs have one of those colours, while
the remaining true diagonal is already covered by reflexivity. -/
theorem original_proper_equivalence_diversity_top_exits
    {i : ι} (J : ColourEq S i) (hProper : J ≠ ⊤) :
    ¬ (Set.univ : S.Menu i i) ⊆ originalEquivDiversityPalette S J := by
  intro hInside
  apply hProper
  apply ColourEq.ext S i
  intro x y
  constructor
  · intro _
    trivial
  · intro _
    by_cases hxy : x = y
    · subst y
      exact J.val.refl x
    · have hTagged : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
        intro h
        exact hxy (eq_of_heq (Sigma.mk.inj h).2)
      obtain ⟨a,hColour⟩ := S.some_colour_of_ne x y hTagged
      obtain ⟨u,v,hJ,hColourUV⟩ := hInside (Set.mem_univ a)
      exact (J.property u v x y (hColourUV.trans hColour.symm)).mp hJ

/-- Literal diversity intersection of a finite LIST of old menus.
The empty restriction list imposes no diversity-colour condition. -/
def originalStrongMenuIntersection {i : ι}
    (menus : List (S.Menu i i)) : S.Menu i i :=
  {a | ∀ A ∈ menus, a ∈ A}

@[simp] theorem original_strong_menu_intersection_nil {i : ι} :
    originalStrongMenuIntersection S ([] : List (S.Menu i i)) = Set.univ := by
  ext a
  simp [originalStrongMenuIntersection]

@[simp] theorem original_strong_menu_intersection_cons {i : ι}
    (A : S.Menu i i) (menus : List (S.Menu i i)) :
    originalStrongMenuIntersection S (A :: menus) =
      A ∩ originalStrongMenuIntersection S menus := by
  ext a
  simp [originalStrongMenuIntersection]

/-- Actual nonempty finite STRONG exact intersections remain STRONG
exact, including the empty restriction list. Nonempty partial meets
are obtained from the SAME witness of the whole intersection. -/
theorem original_strong_menu_intersection_exact
    {i : ι} (menus : List (S.Menu i i)) :
    (∀ A ∈ menus, StrongExact.Exact S A) →
    (originalStrongMenuIntersection S menus).Nonempty →
      StrongExact.Exact S (originalStrongMenuIntersection S menus) := by
  induction menus with
  | nil =>
      intro _ hNonempty
      rw [original_strong_menu_intersection_nil] at hNonempty ⊢
      exact StrongExact.exact_top S hNonempty
  | cons A menus ih =>
      intro hExact hNonempty
      have hA : StrongExact.Exact S A := hExact A (by simp)
      have hTail : (originalStrongMenuIntersection S menus).Nonempty := by
        obtain ⟨a,ha⟩ := hNonempty
        refine ⟨a,?_⟩
        intro B hB
        exact ha B (List.mem_cons_of_mem A hB)
      have hTailExact : StrongExact.Exact S
          (originalStrongMenuIntersection S menus) :=
        ih (fun B hB => hExact B (List.mem_cons_of_mem A hB)) hTail
      rw [original_strong_menu_intersection_cons] at hNonempty ⊢
      exact StrongExact.exact_inter S hA hTailExact hNonempty

/-- Source11 finite repeated STRONG prime intersection. EVERY original
exact factor exits the actual named proper MI, so its NONEMPTY total
intersection also exits. All canonical-domain and full-cover inputs
of source07 are discharged by the accepted original source theorems.

The nonempty total intersection is the separate literal two-copy SAP
duty in the orbit proof; it is not inferred from a fake diagonal. -/
theorem original_named_hidden_finite_strong_intersection_exits
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : OriginalNamedHiddenCoordinate S H i)
    (menus : List (S.Menu i i)) :
    (∀ A ∈ menus, StrongExact.Exact S A) →
    (∀ A ∈ menus, ¬ A ⊆ originalEquivDiversityPalette S J.val) →
    (originalStrongMenuIntersection S menus).Nonempty →
    ¬ originalStrongMenuIntersection S menus ⊆
      originalEquivDiversityPalette S J.val := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  have hMI : InfIrred J.val := original_named_hidden_full_infIrred S H J
  induction menus with
  | nil =>
      intro _ _ _ hInside
      have hProper : J.val ≠ ⊤ := by
        intro hTop
        apply hMI.1
        rw [hTop]
        exact isMax_top
      apply original_proper_equivalence_diversity_top_exits S J.val hProper
      simpa only [original_strong_menu_intersection_nil] using hInside
  | cons A menus ih =>
      intro hExact hExits hNonempty hInside
      have hTail : (originalStrongMenuIntersection S menus).Nonempty := by
        obtain ⟨a,ha⟩ := hNonempty
        refine ⟨a,?_⟩
        intro B hB
        exact ha B (List.mem_cons_of_mem A hB)
      have hAExact : StrongExact.Exact S A := hExact A (by simp)
      have hTailExact : StrongExact.Exact S
          (originalStrongMenuIntersection S menus) :=
        original_strong_menu_intersection_exact S menus
          (fun B hB => hExact B (List.mem_cons_of_mem A hB)) hTail
      have hANamed : StrongExact.CanonicalThetaDomain S A :=
        (original_typed_PC_fixed_domain_iff_exact S H sap cco A).mpr hAExact
      have hTailNamed : StrongExact.CanonicalThetaDomain S
          (originalStrongMenuIntersection S menus) :=
        (original_typed_PC_fixed_domain_iff_exact
          S H sap cco (originalStrongMenuIntersection S menus)).mpr hTailExact
      have hMeet : (A ∩ originalStrongMenuIntersection S menus).Nonempty := by
        simpa only [original_strong_menu_intersection_cons] using hNonempty
      have hContained : (A ∩ originalStrongMenuIntersection S menus) ⊆
          originalEquivDiversityPalette S J.val := by
        simpa only [original_strong_menu_intersection_cons] using hInside
      rcases original_terminal_represented_prime_intersection_no_cover
          S H sap cco nr2 J.val hMI A
          (originalStrongMenuIntersection S menus)
          hANamed hTailNamed hMeet hContained with hA | hRest
      · exact hExits A (by simp) hA
      · exact ih
          (fun B hB => hExact B (List.mem_cons_of_mem A hB))
          (fun B hB => hExits B (List.mem_cons_of_mem A hB)) hTail hRest

end CCO.TypedOrbitFrames
