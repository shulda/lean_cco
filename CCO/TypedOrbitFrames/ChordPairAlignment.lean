import CCO.PairHomogeneity

/-!
# B053 T01/C03: one actual old-group alignment of a coloured chord

A cycle homomorphism can identify NONADJACENT formal vertices,
but the specified chord is a genuine old diversity atom and its
endpoints are distinct. The two actual chord IMAGES therefore
have identical complete old pair type. Original pair homogeneity
gives ONE group element moving BOTH images together, prior to
finite induced-image SAP gluing. This file does not assume that
the old (possibly noninjective) cycle source itself is an age
object; the finite induced-image pushout is a further obligation.
-/

universe u v w t
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- An actual specified old chord has DISTINCT endpoints, including
across original sorts. Real logical identity is never an atomic edge. -/
theorem actual_old_chord_endpoints_distinct
    {i j : ι} (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.colour x y = some a) :
    (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩ := by
  exact S.atomRel_ne hxy

/-- Two actual original images of the SAME specified typed chord atom
can be aligned by ONE original automorphism, not separate choices
for their endpoints. This uses true old two-point homogeneity. -/
theorem align_actual_typed_chord_pair
    (H : HomogeneousSource S G)
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a) :
    ∃ g : G, g • x = x' ∧ g • y = y' := by
  exact S.pair_homogeneous_of_homogeneous H
    x x' y y' (hxy.trans hx'y'.symm)

/-- Both genuine old chord images are independently injective on
their endpoints. Their common atomic colour therefore permits
amalgamation over a COMPLETE old two-point base, after taking
finite induced images (not their possibly noninjective sources). -/
theorem both_old_chord_images_are_diversity
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a) :
    (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ ∧
      (⟨i,x'⟩ : Sigma X) ≠ ⟨j,y'⟩ := by
  exact ⟨S.atomRel_ne hxy, S.atomRel_ne hx'y'⟩

end CCO.TypedOrbitFrames
