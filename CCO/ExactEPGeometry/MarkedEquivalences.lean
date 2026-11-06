import CCO.ExactEPGeometry.ExactEquivalenceBasics

/-!
# B062 / C29: real one-stage exact-equivalence restriction

On a genuinely named child of the actual AP-character marked limit, the
trace of a source equality-inclusive exact equivalence is an actual
equivalence relation. Its identity is literally the current diagonal,
and old invariant intersections restrict to pointwise current meets.

These are the REFLEXIVE/SYMMETRIC/TRANSITIVE and literal meet parts of
C29. Word-exactness of the current relation, arbitrary-prefix
iteration, finite exact-equivalence lattice structure and surjectivity
remain the separate C23–C33 obligations. Neither quotient SAP nor
unconditional downward exact descent is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- ACTUAL child carrier: only points with the full specified unary owner
name are admitted. An inactive/impossible nominal label has empty carrier,
rather than a fabricated point or extra diagonal colour. -/
abbrev MarkedChild {M : MaskData S}
    (completion : Age.CompletionProperty S M) (i : ι) (ε : Bit) :=
  {a : Age.Limit S H completion //
    (Age.limitCoding S H completion).table.owner a =
      Age.ownerEquiv S (i,ε)}

/-- Literal restriction of an old binary relation to an ACTUAL marked
child. The old orbital-union membership is read from the current real
pair colour, and is not declared a formal colour-set relation. -/
def markedChildRelation {M : MaskData S}
    (completion : Age.CompletionProperty S M)
    {i : ι} (R : TRel X i i) (ε : Bit) :
    MarkedChild S H completion i ε →
      MarkedChild S H completion i ε → Prop :=
  fun a b => markedTrace S H completion R ε ε a.val b.val

/-- The old RAW identity restricts to the ACTUAL new logical identity.
In particular the real diagonal is neither a fresh diversity atom nor
an extra copy of the phase gate. -/
theorem markedChild_ident
    {M : MaskData S} (completion : Age.CompletionProperty S M)
    {i : ι} (ε : Bit)
    (a b : MarkedChild S H completion i ε) :
    markedChildRelation S H completion (TRel.ident X i) ε a b ↔
      a = b := by
  change markedTrace S H completion (TRel.ident X i) ε ε a.val b.val ↔ a = b
  rw [markedTrace_identity_iff S H completion ε a.val b.val]
  constructor
  · rintro ⟨h,_⟩
    exact Subtype.ext h
  · intro h
    exact ⟨congrArg Subtype.val h,a.property⟩

/-- Literal CURRENT trace commutes with pointwise original relation meets,
provided the second old factor is invariant. There is no nonempty global
intersection hypothesis here because the SAME actual fixed pair orbital
witnesses each factor. This must not be confused with existential
type-SUPPORT meet preservation C47, which DOES need a nonempty old meet. -/
theorem markedTrace_inter
    {M : MaskData S} (completion : Age.CompletionProperty S M)
    {i j : ι} (R T : TRel X i j)
    (hTInv : TRel.Invariant (G := G) T)
    (ε η : Bit) (a b : Age.Limit S H completion) :
    markedTrace S H completion (fun x y => R x y ∧ T x y) ε η a b ↔
      markedTrace S H completion R ε η a b ∧
      markedTrace S H completion T ε η a b := by
  constructor
  · rintro ⟨ha,hb,x,y,⟨hR,hT⟩,hCode⟩
    exact ⟨⟨ha,hb,x,y,hR,hCode⟩,⟨ha,hb,x,y,hT,hCode⟩⟩
  · rintro ⟨⟨ha,hb,x,y,hR,hCodeR⟩,⟨_,_,x',y',hT,hCodeT⟩⟩
    have hNames : taggedColour S (⟨i,x⟩ : Sigma X) ⟨j,y⟩ =
        taggedColour S (⟨i,x'⟩ : Sigma X) ⟨j,y'⟩ :=
      (Age.colourEquiv S).injective (hCodeR.symm.trans hCodeT)
    have hColour : S.colour x y = S.colour x' y' := by
      simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and]
        using hNames
    have hTxy : T x y :=
      invariant_of_same_actual_colour S H T hTInv x' y' hT x y hColour
    exact ⟨ha,hb,x,y,⟨hR,hTxy⟩,hCodeR⟩

/-- On one displayed child, the ACTUAL old invariant meet is exactly
the current pointwise meet; this is the meet portion of C29 (before the
finite exact-lattice homomorphism is constructed). -/
theorem markedChild_inter
    {M : MaskData S} (completion : Age.CompletionProperty S M)
    {i : ι} (R T : TRel X i i)
    (hTInv : TRel.Invariant (G := G) T)
    (ε : Bit) (a b : MarkedChild S H completion i ε) :
    markedChildRelation S H completion (fun x y => R x y ∧ T x y) ε a b ↔
      markedChildRelation S H completion R ε a b ∧
      markedChildRelation S H completion T ε a b :=
  markedTrace_inter S H completion R T hTInv ε ε a.val b.val

/-- An original equality-inclusive full RAW exact equivalence restricts
to a genuine equivalence on an actual child of the homogeneous marked age.
Transitivity uses the compiled real forward trace product C11, so the
middle witness is in the SAME child; symmetry uses the actual converse
old orbital, and reflexivity is the genuine marked diagonal C29. -/
theorem markedChild_exact_equiv
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D : RawExact.NonemptyExact S i i)
    (hEquiv : RawSymmetric.EquivRel (RawExact.evaluate S D.words))
    (ε : Bit) :
    RawSymmetric.EquivRel
      (markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have hId : markedTrace S H (P.completion_property cco)
        (TRel.ident X i) ε ε a.val a.val :=
      (markedTrace_identity_iff S H (P.completion_property cco)
        ε a.val a.val).mpr ⟨rfl,a.property⟩
    obtain ⟨ha,hb,x,y,hxy,hCode⟩ := hId
    change x = y at hxy
    subst y
    exact ⟨ha,hb,x,x,hEquiv.refl x,hCode⟩
  · intro a b hab
    obtain ⟨hb,ha,x,y,hConverse,hCode⟩ :=
      markedTrace_reverse S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε ε a.val b.val hab
    exact ⟨hb,ha,x,y,hEquiv.symm y x hConverse,hCode⟩
  · intro a b c hab hbc
    obtain ⟨ha,hc,x,z,hComp,hCode⟩ :=
      marked_trace_comp_forward S H (P.completion_property cco)
        D D ε ε ε a.val b.val c.val hab hbc
    obtain ⟨y,hxy,hyz⟩ := hComp
    exact ⟨ha,hc,x,z,hEquiv.trans x y z hxy hyz,hCode⟩

end
end CCO.ExactEPGeometry
