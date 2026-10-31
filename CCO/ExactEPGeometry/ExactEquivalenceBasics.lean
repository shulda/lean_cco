import CCO.ExactEPGeometry.MarkedSupports

/-!
# B062 / C29–C31: genuine marked equality and original exact reflexivity

The true RAW identity has as its current marked trace precisely the
ACTUAL equality relation on each realized child sort.  There is no
additional equality-coloured diversity edge joining distinct vertices.

If a current exact equivalence is the trace of a source RAW exact
relation, a reflexive marked point supplies an actual OLD diagonal pair.
Original homogeneity sends that witnessed diagonal to all points of the
single ORIGINAL source sort. Original invariant same-sort symmetry is
already proved in the accepted RAW source. This proves the critical
C31 lifting obligation at one true AP-character stage, not the still-open
source-to-prefix exact-surjectivity C23–C33.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- C29: the full marked-age trace of ORIGINAL RAW identity is
precisely CURRENT logical equality with the indicated actual unary
name. It is not an extra phase-consistent diversity relation. -/
theorem markedTrace_identity_iff
    {M : MaskData S} (completion : Age.CompletionProperty S M)
    {i : ι} (ε : Bit)
    (a b : Age.Limit S H completion) :
    markedTrace S H completion (TRel.ident X i) ε ε a b ↔
      a = b ∧
      (Age.limitCoding S H completion).table.owner a =
        Age.ownerEquiv S (i,ε) := by
  constructor
  · rintro ⟨ha,_,x,y,hxy,hcode⟩
    change x = y at hxy
    subst y
    have hnone : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
    have hColour :
        (Age.limitCoding S H completion).table.colour a b =
          Age.colourEquiv S (⟨i,i,none⟩ : Age.Colour S) := by
      simpa [taggedColour, hnone] using hcode
    exact ⟨marked_eq_of_diagonal_colour S H completion a b i hColour,ha⟩
  · rintro ⟨rfl,ha⟩
    let x : X i := Classical.choice (S.nonemptySort i)
    have hdiag := marked_diagonal_of_owner S H completion a i ε ha
    have hnone : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
    refine ⟨ha,ha,x,x,rfl,?_⟩
    simpa [taggedColour, hnone] using hdiag

/-- In an ACTUAL original transitive homogeneous named sort,
one invariant witnessed diagonal already contains the WHOLE original
logical identity. This uses the original group action, not a quotient
automorphism lift or an extra SAP premise. -/
theorem original_invariant_reflexive_of_one
    {i : ι} (R : TRel X i i)
    (hInv : TRel.Invariant (G := G) R)
    (x : X i) (hxx : R x x) :
    ∀ y : X i, R y y := by
  intro y
  obtain ⟨g,hgy⟩ := S.original_sort_transitive_of_homogeneous H i x y
  simpa only [hgy] using hInv g x x hxx

/-- C31 actual one-character-step application. A witnessed diagonal in
the current marked trace of the REAL source exact D implies:
(1) old logical Id is contained in D everywhere on the original sort;
(2) D is symmetric already at the original source strength.

The first point follows from a genuine old diagonal pair, not from
assuming reflexivity of D; the second from the original paired orbital
homogeneity. Transitivity is NOT asserted here and is the separate
finite stable-powers obligation C32. -/
theorem old_exact_reflexive_symmetric_of_marked_diagonal
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D : RawExact.NonemptyExact S i i)
    (ε : Bit) (a : Age.Limit S H (P.completion_property cco))
    (hDiag : markedTrace S H (P.completion_property cco)
      (RawExact.evaluate S D.words) ε ε a a) :
    (∀ y : X i, RawExact.evaluate S D.words y y) ∧
      (∀ x y : X i, RawExact.evaluate S D.words x y →
        RawExact.evaluate S D.words y x) := by
  obtain ⟨ha,_,x,y,hD,hcode⟩ := hDiag
  have hCurrentDiag :=
    marked_diagonal_of_owner S H (P.completion_property cco) a i ε ha
  have hOldCode : taggedColour S (⟨i,x⟩ : Sigma X) ⟨i,y⟩ =
      (⟨i,i,none⟩ : Age.Colour S) :=
    (Age.colourEquiv S).injective (hcode.symm.trans hCurrentDiag)
  have hOldEqual : (⟨i,x⟩ : Sigma X) = ⟨i,y⟩ :=
    tagged_colour_diagonal_eq S (⟨i,x⟩ : Sigma X)
      ⟨i,y⟩ i hOldCode
  have hxy : x = y := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hOldEqual
  subst y
  have hInv : TRel.Invariant (G := G) (RawExact.evaluate S D.words) :=
    RawExact.presentation_invariant_of_homogeneous S H D.words
  have hSym :
      TRel.converse (RawExact.evaluate S D.words) =
        RawExact.evaluate S D.words :=
    invariant_same_sort_converse S H (RawExact.evaluate S D.words) hInv
  constructor
  · exact original_invariant_reflexive_of_one S H
      (RawExact.evaluate S D.words) hInv x hD
  · intro u v huv
    have hRev : TRel.converse (RawExact.evaluate S D.words) v u := huv
    rw [hSym] at hRev
    exact hRev

end
end CCO.ExactEPGeometry
