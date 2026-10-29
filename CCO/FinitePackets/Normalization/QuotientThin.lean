import CCO.FinitePackets.Normalization.SquareKernel
import CCO.FinitePackets.Normalization.PaletteDescent
import CCO.RawExact.CanonicalQuotients
import CCO.GroupQuotient

/-! C20/C21: actual old-G quotient orbitals and their equality-inclusive
saturated pullbacks. Their thinness uses the square kernel and original
commutation. No homogeneous/CCO quotient source is asserted here. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original CCO.FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

include H in
theorem colourKernelInvariant (K : ColourEq S ()) : RawExact.CanonicalQuotients.Invariant G K.val :=
  ⟨colourInvariant_groupInvariant S H K.property⟩

@[instance_reducible] def originalQuotientAction (K : ColourEq S ()) :
    MulAction G (Quotient K.val) := by
  letI : RawExact.CanonicalQuotients.Invariant G K.val := colourKernelInvariant S H K
  infer_instance

include H

theorem old_orbital_iff_colour (a b x y : M) :
    GroupActions.orbital (G := G) a b x y ↔ col S x y = col S a b := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    exact col_invariant S H g a b
  · intro hc
    exact S.pair_homogeneous_of_homogeneous H a x b y hc.symm

variable (K : ColourEq S ())

theorem quotient_projection_equivariant (g : G) (x : M) :
    letI := originalQuotientAction S H K
    (Quotient.mk'' (g • x) : Quotient K.val) = g • (Quotient.mk'' x) := rfl

theorem actual_quotient_orbital_pullback (a b : M) :
    letI := originalQuotientAction S H K
    GroupActions.pullback (Quotient.mk'' : M → Quotient K.val) (Quotient.mk'' : M → Quotient K.val)
      (GroupActions.orbital (G := G) (Quotient.mk'' a : Quotient K.val) (Quotient.mk'' b : Quotient K.val)) =
      (fun x y => ∃ u z, K x u ∧ col S u z = col S a b ∧ K z y) := by
  letI := originalQuotientAction S H K
  rw [GroupActions.orbital_pullback _ _
    (quotient_projection_equivariant S H K) (quotient_projection_equivariant S H K)]
  funext x y
  apply propext
  change (∃ u z, Quotient.mk'' x = (Quotient.mk'' u : Quotient K.val) ∧
    GroupActions.orbital (G := G) a b u z ∧
    (Quotient.mk'' z : Quotient K.val) = Quotient.mk'' y) ↔ _
  simp only [Quotient.eq,old_orbital_iff_colour S H]

theorem actual_quotient_orbital_representatives (q r : Quotient K.val) :
    letI := originalQuotientAction S H K
    ∃ a b : M, q = Quotient.mk'' a ∧ r = Quotient.mk'' b ∧
      GroupActions.orbital (G := G) q r =
        GroupActions.orbital (G := G) (Quotient.mk'' a : Quotient K.val) (Quotient.mk'' b) := by
  letI := originalQuotientAction S H K
  obtain ⟨a,rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨b,rfl⟩ := Quotient.mk''_surjective r
  exact ⟨a,b,rfl,rfl,rfl⟩

noncomputable def actualQuotientSource : AtomicSource Unit (fun _ => Quotient K.val) := by
  letI := originalQuotientAction S H K
  exact RawExact.QuotientPalette.actualQuotientAtomicSource (i := ())
    (fun _ : Unit => Quotient K.val) S H
    (fun _ => Quotient.mk'') (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K)

theorem actualQuotientSource_colour_invariant (g : G) (q r : Quotient K.val) :
    letI := originalQuotientAction S H K
    (actualQuotientSource S H K).colour (i := ()) (j := ()) (g • q) (g • r) =
      (actualQuotientSource S H K).colour q r := by
  letI := originalQuotientAction S H K
  exact RawExact.QuotientPalette.actualQuotientAtomicSource_colour_invariant (i := ())
    (fun _ : Unit => Quotient K.val) S H
    (fun _ => Quotient.mk'') (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K) g q r

theorem actualQuotientSource_colour_orbital (q r q' r' : Quotient K.val) :
    letI := originalQuotientAction S H K
    (actualQuotientSource S H K).colour (i := ()) (j := ()) q r =
      (actualQuotientSource S H K).colour q' r' ↔
        GroupActions.orbital (G := G) q r q' r' := by
  letI := originalQuotientAction S H K
  exact RawExact.QuotientPalette.actualQuotientAtomicSource_colour_eq_iff_orbital (i := ())
    (fun _ : Unit => Quotient K.val) S H
    (fun _ => Quotient.mk'') (fun _ => Quotient.mk''_surjective)
    (fun _ => quotient_projection_equivariant S H K) q r q' r'

theorem quotient_palette_strictly_drops (hK : K ≠ ⊥) :
    letI := S.finiteAtom () ()
    letI := (actualQuotientSource S H K).finiteAtom () ()
    Fintype.card ((actualQuotientSource S H K).Atom () ()) < Fintype.card (Atom S) := by
  letI := originalQuotientAction S H K
  apply quotient_diversity_palette_lt S (actualQuotientSource S H K) H
    (Quotient.mk'' : M → Quotient K.val) Quotient.mk''_surjective
    (quotient_projection_equivariant S H K) (actualQuotientSource_colour_invariant S H K)
  intro hinj
  apply hK
  apply ColourEq.ext
  intro x y
  exact ⟨fun h => hinj (Quotient.sound h),fun h => h ▸ K.val.refl x⟩

theorem quotient_orbital_thin_of_square {c : FullColour S}
    (hsq : ∀ x z, (∃ y, col S x y = c ∧ col S y z = c) → K x z)
    (a b : M) (hab : col S a b = c) :
    letI := originalQuotientAction S H K
    ∀ q : Quotient K.val, ∃! r : Quotient K.val,
      GroupActions.orbital (G := G) (Quotient.mk'' a : Quotient K.val) (Quotient.mk'' b) q r := by
  letI := originalQuotientAction S H K
  intro q
  obtain ⟨x,rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨g,hga⟩ := S.original_sort_transitive_of_homogeneous H () a x
  refine ⟨Quotient.mk'' (g • b),⟨g,by change (Quotient.mk'' (g • a) : Quotient K.val) = Quotient.mk'' x; exact congrArg Quotient.mk'' hga,rfl⟩,?_⟩
  rintro r ⟨h,hha,hhb⟩
  have hk : K (h • a) (g • a) := Quotient.exact (hha.trans (congrArg Quotient.mk'' hga).symm)
  have hgb : col S (g • a) (g • b) = c := (col_invariant S H g a b).trans hab
  have hhbcol : col S (h • a) (h • b) = c := (col_invariant S H h a b).trans hab
  have hc : ColourInvariant S () (fun u z => col S u z = c) :=
    fun u z u' z' he => by
      change col S u z = col S u' z' at he
      change (col S u z = c) ↔ (col S u' z' = c)
      rw [he]
  have hcomm := invariant_relations_commute S H K.property hc
  have hpath : RawSymmetric.compose K.val.r (fun u z => col S u z = c)
      (h • a) (g • b) := ⟨g • a,hk,hgb⟩
  rw [hcomm] at hpath
  obtain ⟨z,haz,hzb⟩ := hpath
  have hz : K (h • b) z := hsq _ _ ⟨h • a,(col_symm S _ _).trans hhbcol,haz⟩
  have he : (Quotient.mk'' (h • b) : Quotient K.val) = Quotient.mk'' (g • b) :=
    Quotient.sound (K.val.trans hz hzb)
  exact hhb.symm.trans he

theorem square_quotient_packet_orbital_thin (F : ColourEq S ())
    (a b : M) (hab : F a b) :
    letI := originalQuotientAction S H (squareKernel S H F)
    ∀ q : Quotient (squareKernel S H F).val,
      ∃! r : Quotient (squareKernel S H F).val,
        GroupActions.orbital (G := G)
          (Quotient.mk'' a : Quotient (squareKernel S H F).val) (Quotient.mk'' b) q r := by
  exact quotient_orbital_thin_of_square S H (squareKernel S H F)
    (fun x z h => fullColour_square_le_kernel S H (fullColourBelow_at S F a b hab) x z h)
    a b rfl

/-- The literal induced F/K equivalence on ACTUAL quotient classes. -/
def quotientPacket (F : ColourEq S ()) (hKF : K ≤ F) : Setoid (Quotient K.val) :=
  F.val.mapOfSurjective (Quotient.mk'' : M → Quotient K.val)
    (fun _ _ h => hKF (Quotient.exact h)) Quotient.mk''_surjective

theorem quotientPacket_projection (F : ColourEq S ()) (hKF : K ≤ F) (a b : M) :
    quotientPacket S K F hKF (Quotient.mk'' a) (Quotient.mk'' b) ↔ F a b := by
  constructor
  · rintro ⟨x,y,hxy,hxa,hyb⟩
    exact F.val.trans (hKF (K.val.symm (Quotient.exact hxa)))
      (F.val.trans hxy (hKF (Quotient.exact hyb)))
  · intro hab
    exact ⟨a,b,hab,rfl,rfl⟩

/-- Every orbital below F/H0 is represented by some old pair in F.
The arbitrary quotient orbital may be the actual quotient diagonal. -/
theorem square_quotient_every_packet_orbital_thin (F : ColourEq S ())
    (q r : Quotient (squareKernel S H F).val)
    (hqr : quotientPacket S (squareKernel S H F) F (squareKernel_le S H F) q r) :
    letI := originalQuotientAction S H (squareKernel S H F)
    ∀ q' : Quotient (squareKernel S H F).val,
      ∃! r' : Quotient (squareKernel S H F).val,
        GroupActions.orbital (G := G) q r q' r' := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := hqr
  exact square_quotient_packet_orbital_thin S H F a b hab

/-- Thinness in the ACTUAL quotient palette, including equality.
No quotient homogeneity or semantic CCO is a premise. -/
theorem square_quotient_every_packet_colour_thin (F : ColourEq S ())
    (c : FullColour (actualQuotientSource S H (squareKernel S H F)))
    (hc : ∀ q r : Quotient (squareKernel S H F).val,
      col (actualQuotientSource S H (squareKernel S H F)) q r = c →
        quotientPacket S (squareKernel S H F) F (squareKernel_le S H F) q r) :
    ThinColour (actualQuotientSource S H (squareKernel S H F)) c := by
  letI := originalQuotientAction S H (squareKernel S H F)
  obtain ⟨a,b,hab⟩ := colour_realized (actualQuotientSource S H (squareKernel S H F)) c
  intro q
  obtain ⟨r,hr,hu⟩ := square_quotient_every_packet_orbital_thin S H F a b (hc a b hab) q
  refine ⟨r,?_,?_⟩
  · exact ((actualQuotientSource_colour_orbital S H (squareKernel S H F) a b q r).mpr hr).symm.trans hab
  · intro r' hr'
    apply hu
    apply (actualQuotientSource_colour_orbital S H (squareKernel S H F) a b q r').mp
    exact hab.trans hr'.symm

end CCO.FinitePackets.Normalization
