import CCO.RigidGroupoid.Geometry.Basic
import CCO.RigidGroupoid.Geometry.Quotient.OrbitalConvolution
import CCO.ExactCRT.CanonicalTypedQuotients

/-!
# The actual simultaneous quotient full-exact calculus

Original support Helly transfers through the safe full-exact word pullback.
Quotient convolution is then proved by the two support-Helly/Peirce argument,
not inferred from the old exactness of its pullback. The final canonical
instance uses the literal quotient carriers and constructed original action.
-/

universe u v w q r t

namespace CCO.RigidGroupoid.Geometry.Quotient

open RawExact

section General
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include H cco π surjπ equivπ E hE hT

/-- C05: quotient WORD support Helly comes from original FULL EXACT support
Helly. No different-centre ball theorem or quotient homogeneous-source theorem
is consumed after the original exact word pullback has been proved.
-/
theorem quotientWordHelly : WordProfileHelly T := by
  intro i j P _ hPair
  let lift : RawWord T i j → NonemptyExact S i j :=
    ExactCRT.liftQuotientWord S T H cco π surjπ equivπ E hE hT
  let L := P.map lift
  have hp : ∀ d ∈ L, ∀ e ∈ L, d ≠ e → TRel.Nonempty
      (fun x y => evaluate S d.words x y ∧ evaluate S e.words x y) := by
    intro d hd e he _
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hd
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp he
    obtain ⟨x',y',hp',hq'⟩ := hPair p hp q hq
    obtain ⟨x,rfl⟩ := surjπ i x'
    obtain ⟨y,rfl⟩ := surjπ j y'
    refine ⟨x,y,?_,?_⟩
    · rw [ExactCRT.liftQuotientWord_relation]
      exact hp'
    · rw [ExactCRT.liftQuotientWord_relation]
      exact hq'
  obtain ⟨x,y,hxy⟩ := exactMenuHelly_of_CCO S H cco L hp
  refine ⟨π i x,π j y,?_⟩
  intro word hw
  have hh := hxy (lift word) (List.mem_map.mpr ⟨word,hw,rfl⟩)
  rw [ExactCRT.liftQuotientWord_relation] at hh
  exact hh

theorem quotientMenuHelly {i j : ι} (D : List (NonemptyExact T i j))
    (hPair : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → TRel.Nonempty
      (fun x y => evaluate T d.words x y ∧ evaluate T e.words x y)) :
    TRel.Nonempty (fun x y => ∀ d ∈ D, evaluate T d.words x y) :=
  exact_menu_helly_of_word_helly T (quotientWordHelly S T H cco π surjπ equivπ E hE hT) D hPair

/-- C05 convolution uses the quotient's proved WORD support Helly twice and
its actual ambient pair orbitals. No reverse old-to-quotient exact descent.
-/
theorem quotientConvolution {i j k : ι} (D : NonemptyExact T i j) (F : NonemptyExact T j k) :
    TRel.comp (evaluate T D.words) (evaluate T F.words) =
      evaluate T (pairWords T D.words F.words) :=
  convolution_of_wordHelly T hT
    (quotientWordHelly S T H cco π surjπ equivπ E hE hT) D F

theorem quotientExactCalculus : ExactCalculus T where
  comp := by
    intro i j k R U hR hU
    obtain ⟨D,rfl⟩ := hR
    obtain ⟨F,rfl⟩ := hU
    have hn : TRel.Nonempty (TRel.comp (evaluate T D.words) (evaluate T F.words)) :=
      TRel.comp_nonempty_invariant (G := G) _ _ D.nonempty F.nonempty
        (presentationInvariant T hT F.words) (transitive T hT j)
    have hp : TRel.Nonempty (evaluate T (pairWords T D.words F.words)) := by
      obtain ⟨x,z,hxz⟩ := hn
      exact ⟨x,z,comp_subset_pairWords T D.words F.words x z hxz⟩
    exact ⟨⟨pairWords T D.words F.words,hp⟩,
      (quotientConvolution S T H cco π surjπ equivπ E hE hT D F).symm⟩

/-- C04 safe direction for arbitrary FULL exact quotient relations. -/
theorem fullExactPullback {i j : ι} {D : TRel Q i j} (hD : FullExact T D) :
    FullExact S (GroupActions.pullback (π i) (π j) D) := by
  obtain ⟨F,rfl⟩ := hD
  exact ⟨ExactCRT.liftQuotientExact S T H cco π surjπ equivπ E hE hT F,
    ExactCRT.liftQuotientExact_relation S T H cco π surjπ equivπ E hE hT F⟩

end General

section Canonical
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

include cco

/-- The source-complete instance on the LITERAL simultaneous quotients.
All action, surjectivity, equivariance, palette and kernel providers are proved.
-/
theorem canonicalExactCalculus : ExactCalculus (ExactCRT.CanonicalTyped.source S H J E represents) := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) := ExactCRT.CanonicalTyped.action S H J E represents
  apply quotientExactCalculus S _ H cco (ExactCRT.CanonicalTyped.projection J)
    (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents) E
    (ExactCRT.CanonicalTyped.projection_kernel S J E represents)
  intro i j x y x' y'
  exact ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
    (ExactCRT.CanonicalTyped.projection J) (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents) x y x' y'

theorem canonicalWordHelly : WordProfileHelly (ExactCRT.CanonicalTyped.source S H J E represents) := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) := ExactCRT.CanonicalTyped.action S H J E represents
  apply quotientWordHelly S _ H cco (ExactCRT.CanonicalTyped.projection J)
    (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents) E
    (ExactCRT.CanonicalTyped.projection_kernel S J E represents)
  intro i j x y x' y'
  exact ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
    (ExactCRT.CanonicalTyped.projection J) (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents) x y x' y'

end Canonical
end CCO.RigidGroupoid.Geometry.Quotient
