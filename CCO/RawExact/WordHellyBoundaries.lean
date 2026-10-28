import CCO.RawExact.Convolution

/-!
# B002 C07: precise empty, singleton, pair and identity-profile Helly cases

The general three-or-more positive-word case requires the private theta
graph and actual SemanticCCO; it is NOT inferred from these easy cases.
An identity-only reduced RAW word must be handled as real equality,
not a fictitious diversity edge.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem word_helly_empty {i j : ι} :
    TRel.Nonempty (evaluate S ([] : Presentation S i j)) :=
  (NonemptyExact.top S i j).nonempty

theorem word_helly_single {i j : ι}
    (word : RawWord S i j)
    (h : TRel.Nonempty (RawWord.relation S word)) :
    TRel.Nonempty (evaluate S [word]) := by
  obtain ⟨x, z, hxz⟩ := h
  refine ⟨x, z, ?_⟩
  intro w hw
  have hEq : w = word := by
    simpa only [List.mem_singleton] using hw
  subst w
  exact hxz

theorem word_helly_two {i j : ι}
    (p q : RawWord S i j)
    (h : TRel.Nonempty
      (fun x z => RawWord.relation S p x z ∧
        RawWord.relation S q x z)) :
    TRel.Nonempty (evaluate S [p, q]) := by
  obtain ⟨x, z, hp, hq⟩ := h
  refine ⟨x, z, ?_⟩
  intro w hw
  have hw' : w = p ∨ w = q := by simpa using hw
  rcases hw' with hwp | hwq
  · subst w
    exact hp
  · subst w
    exact hq

/-- The nontrivial identity-profile part of word Helly: when ONE
profile is literally real identity, pairwise intersection with it
gives some diagonal point in every other word profile. ORIGINAL
one-sort transitivity and word invariance transport ALL these loops
to the SAME actual target point, with no CCO assumption. -/
theorem word_helly_with_identity_profile
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {i : ι} (P : Presentation S i i)
    (identityWord : RawWord S i i)
    (hIdentity : RawWord.relation S identityWord = TRel.ident X i)
    (hPair : ∀ w, w ∈ P →
      TRel.Nonempty (fun x z =>
        RawWord.relation S identityWord x z ∧
          RawWord.relation S w x z)) :
    TRel.Nonempty (evaluate S P) := by
  obtain ⟨target⟩ := S.nonemptySort i
  refine ⟨target, target, ?_⟩
  intro w hw
  obtain ⟨x, z, hId, hWalk⟩ := hPair w hw
  rw [hIdentity] at hId
  change x = z at hId
  subst z
  obtain ⟨g, hg⟩ :=
    S.original_sort_transitive_of_homogeneous H i x target
  have hTranslated :=
    (word_invariant_of_homogeneous S H w) g x x hWalk
  simpa only [hg] using hTranslated

/-- The full source-style pairwise assumption implies the identity case,
including a word with several (erasable) logical-identity letters. -/
theorem word_helly_if_identity_member
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {i : ι} (P : Presentation S i i)
    (identityWord : RawWord S i i)
    (hMember : identityWord ∈ P)
    (hIdentity : RawWord.relation S identityWord = TRel.ident X i)
    (hPairwise : ∀ p, p ∈ P → ∀ q, q ∈ P →
      TRel.Nonempty (fun x z =>
        RawWord.relation S p x z ∧ RawWord.relation S q x z)) :
    TRel.Nonempty (evaluate S P) :=
  word_helly_with_identity_profile S H P identityWord hIdentity
    (fun w hw => hPairwise identityWord hMember w hw)

end CCO.RawExact
