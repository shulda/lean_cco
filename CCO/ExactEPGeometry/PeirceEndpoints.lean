import CCO.RawExact.ActualOrbitalExact
import CCO.RigidGroupoid.Geometry.Basic
import CCO.RawSource

/-!
# B062 C12–C18: actual original Peircean endpoint witnesses

These are the equality-inclusive RAW intersection obligations before
applying the source AP-only mask primality TWICE. A real output atom is
the actual old optional pair colour, including genuine diagonal `none`.
The produced auxiliary factors are proven full exact from the accepted
convolution calculus, not assumed exact by a new axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

section Transport
include H

/-- A single witnessed original pair brings its ENTIRE real fine orbital
into an invariant RAW relation. Same sort, mixed sorts and the real
diagonal are all covered by the original pair-homogeneity theorem. -/
theorem invariant_of_same_actual_colour
    {i j : ι} (R : TRel X i j)
    (hInv : TRel.Invariant (G := G) R)
    (x : X i) (y : X j) (hxy : R x y)
    (x' : X i) (y' : X j)
    (hColour : S.colour x' y' = S.colour x y) : R x' y' := by
  obtain ⟨g, hgx, hgy⟩ :=
    S.pair_homogeneous_of_homogeneous H x x' y y' hColour.symm
  simpa only [hgx, hgy] using hInv g x y hxy

/-- Every nonempty exact RAW word-intersection contains entire original
pair orbitals, including the equality orbital at repeated endpoints. -/
theorem exact_of_same_actual_colour
    {i j : ι} (D : RawExact.NonemptyExact S i j)
    (x : X i) (y : X j)
    (hxy : RawExact.evaluate S D.words x y)
    (x' : X i) (y' : X j)
    (hColour : S.colour x' y' = S.colour x y) :
    RawExact.evaluate S D.words x' y' :=
  invariant_of_same_actual_colour S H
    (RawExact.evaluate S D.words)
    (RawExact.presentation_invariant_of_homogeneous S H D.words)
    x y hxy x' y' hColour

/-- A complete old fine-colour output pair carrying a represented
composite transports its genuine middle witness along the original
pair action. This does NOT impose any child phase or marked-age assumption. -/
theorem raw_comp_of_same_actual_colour
    {i j k : ι} (D : RawExact.NonemptyExact S i j)
    (E : RawExact.NonemptyExact S j k)
    (x : X i) (z : X k)
    (h : TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S E.words) x z)
    (x' : X i) (z' : X k)
    (hColour : S.colour x' z' = S.colour x z) :
    TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S E.words) x' z' := by
  apply invariant_of_same_actual_colour S H
    (TRel.comp (RawExact.evaluate S D.words) (RawExact.evaluate S E.words))
    (TRel.invariant_comp (G := G)
      (RawExact.evaluate S D.words) (RawExact.evaluate S E.words)
      (RawExact.presentation_invariant_of_homogeneous S H D.words)
      (RawExact.presentation_invariant_of_homogeneous S H E.words))
    x z h x' z' hColour

end Transport

/-- The first genuinely represented Peirce intersection, before the
first mask-primality choice. Its middle point is the ORIGINAL endpoint z
of the selected output atom, not an invented formal edge. -/
theorem first_peirce_intersection_nonempty
    {i j k : ι} (D : RawExact.NonemptyExact S i j)
    (E : RawExact.NonemptyExact S j k)
    (x : X i) (z : X k)
    (h : TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S E.words) x z) :
    TRel.Nonempty
      (fun x' y' => RawExact.evaluate S D.words x' y' ∧
        TRel.comp (S.rawAtomRel (S.colour x z))
          (TRel.converse (RawExact.evaluate S E.words)) x' y') := by
  obtain ⟨y, hD, hE⟩ := h
  exact ⟨x, y, hD, z, rfl, hE⟩

/-- The first auxiliary domain `{c}; Eᵒᵖ` is actual RAW full exact.
This remains true if c is the genuine diagonal and never uses SAP. -/
theorem first_peirce_auxiliary_exact
    {i j k : ι} (C : ExactCalculus S)
    (E : RawExact.NonemptyExact S j k)
    (x : X i) (z : X k) :
    FullExact S
      (TRel.comp (S.rawAtomRel (S.colour x z))
        (TRel.converse (RawExact.evaluate S E.words))) :=
  C.comp
    (fullExact_actual_atom S x z)
    (fullExact_converse S (R := RawExact.evaluate S E.words) ⟨E, rfl⟩)

/-- The second Peirce intersection is nonempty once the first selected
old a-edge and the c-output share an actual triangle witness. -/
theorem second_peirce_intersection_nonempty
    {i j k : ι} (E : RawExact.NonemptyExact S j k)
    (x : X i) (y : X j) (z : X k)
    (hE : RawExact.evaluate S E.words y z) :
    TRel.Nonempty
      (fun y' z' => RawExact.evaluate S E.words y' z' ∧
        TRel.comp (TRel.converse (S.rawAtomRel (S.colour x y)))
          (S.rawAtomRel (S.colour x z)) y' z') := by
  exact ⟨y, z, hE, x, rfl, rfl⟩

/-- The second auxiliary domain `{a}ᵒᵖ; {c}` is also real RAW full exact;
its proof does not rely on the selected phase witnesses being distinct. -/
theorem second_peirce_auxiliary_exact
    {i j k : ι} (C : ExactCalculus S)
    (x : X i) (y : X j) (z : X k) :
    FullExact S
      (TRel.comp (TRel.converse (S.rawAtomRel (S.colour x y)))
        (S.rawAtomRel (S.colour x z))) :=
  C.comp
    (fullExact_converse S
      (R := S.rawAtomRel (S.colour x y)) (fullExact_actual_atom S x y))
    (fullExact_actual_atom S x z)

end CCO.ExactEPGeometry
