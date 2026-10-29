import CCO.AclOwners.CoordinateQuotients
import CCO.AclOwners.CoordinateMeets
import CCO.AclOwners.CorrespondenceUpper

/-! Actual ORIGINAL core quotient consumers. Each quotient has its full
canonical finite orbital source, true finite bottom and unary real acl.
These original cores are distinct from later maximal-core choices. -/

universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

noncomputable def oldFiniteBottom (D : Direction S) :
    ColourEq (actualQuotientSource S H (oldCore S H cco D)) () :=
  quotientColourEq S H (oldCore S H cco D) (oldCorrespondence S H cco D)
    (core_le S _)

/-- C18: the quotient finite bottom is the ENTIRE R_i/C_i relation; every
finite-class full invariant relation is below it. -/
theorem oldFiniteBottom_greatest (normalized : NoFiniteExactKernel S) (D : Direction S) :
    RealClosure.Bounds.FiniteClasses (actualQuotientSource S H (oldCore S H cco D))
      (oldFiniteBottom S H cco D) ∧
    ∀ E : ColourEq (actualQuotientSource S H (oldCore S H cco D)) (),
      RealClosure.Bounds.FiniteClasses (actualQuotientSource S H (oldCore S H cco D)) E →
      E ≤ oldFiniteBottom S H cco D :=
  quotient_greatest_finite S H _ _ (core_le S _) (oldCore_sigma S H cco normalized D)

/-- The genuine full invariant finite bottom has a least strict upper
member, obtained by transporting E_i join R_i. -/
theorem oldFiniteBottom_least_upper (normalized : NoFiniteExactKernel S) (D : Direction S) :
    ∃ V : ColourEq (actualQuotientSource S H (oldCore S H cco D)) (),
      oldFiniteBottom S H cco D < V ∧
      ∀ E : ColourEq (actualQuotientSource S H (oldCore S H cco D)) (),
        oldFiniteBottom S H cco D < E → V ≤ E := by
  have h := oldCorrespondence_least_upper S H cco normalized D
  exact ⟨_,quotient_least_strict S H _ _ (core_le S _) _ h.1 h.2⟩

/-- Every actual old-core quotient is infinite, witnessed by the injective
image of its selected minimal infinite class. No quotient normalization or
second minimal direction is needed for this assertion. -/
theorem oldCore_quotient_infinite (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Infinite (Quotient (oldCore S H cco D).val) := by
  classical
  obtain ⟨x⟩ := S.nonemptySort ()
  letI : Infinite (ClassPoint S () D.val x) := not_finite_iff_infinite.mp (by
    intro hf
    exact D.property.1 ((finiteClasses_iff_at S H D.val x).mpr hf))
  let f : ClassPoint S () D.val x → Quotient (oldCore S H cco D).val :=
    fun y => Quotient.mk'' y.val
  apply Infinite.of_injective f
  intro a b hab
  apply Subtype.ext
  have hD : D.val a.val b.val := D.val.val.trans (D.val.val.symm a.property) b.property
  have hC : oldCore S H cco D a.val b.val := Quotient.exact hab
  have he : (D.val ⊓ oldCore S H cco D) a.val b.val := ⟨hD,hC⟩
  rwa [oldCore_disjoint S H cco normalized D] at he

/-- C18/C19 instantiated on the literal original core quotient source. -/
theorem oldCore_quotient_directionCount (normalized : NoFiniteExactKernel S) (D : Direction S) :
    directionCount (actualQuotientSource S H (oldCore S H cco D)) = 1 := by
  have h := oldCorrespondence_least_upper S H cco normalized D
  exact quotient_directionCount_one S H _ _ (core_le S _) (coreExact S H _)
    (coreExact_represents S H _) cco (oldCore_sigma S H cco normalized D) _ h.1 h.2

/-- C20: the actual full quotient finite bottom gives unary closure for
EVERY finite input, independently of unsafe-clique hypotheses. -/
theorem oldCore_quotient_acl (normalized : NoFiniteExactKernel S) (D : Direction S)
    (U : Finset (Quotient (oldCore S H cco D).val))
    (x : Quotient (oldCore S H cco D).val) :
    letI := originalQuotientAction S H (oldCore S H cco D)
    x ∈ Acl G U ↔ ∃ u ∈ U, oldFiniteBottom S H cco D u x := by
  have h := oldCorrespondence_least_upper S H cco normalized D
  exact quotient_acl_iff_relation S H _ _ (core_le S _) (coreExact S H _)
    (coreExact_represents S H _) cco (oldCore_sigma S H cco normalized D) _ h.1 h.2 U x

/-- The quotient finite bottom is literally the old original correspondence
on representatives, including repeated/equal coordinates. -/
theorem oldFiniteBottom_projection (D : Direction S) (x y : M) :
    oldFiniteBottom S H cco D (Quotient.mk'' x) (Quotient.mk'' y) ↔
      oldCorrespondence S H cco D x y :=
  quotientColourEq_projection S H _ _ (core_le S _) x y

/-- The complete original direction count, rather than a selected coordinate
subfamily, supplies another direction when r is at least two. -/
theorem exists_other_direction (hcount : 2 ≤ directionCount S) (D : Direction S) :
    ∃ E : Direction S, D ≠ E := by
  classical
  by_contra hn
  have hall : ∀ E : Direction S, D = E := by
    intro E
    by_contra hDE
    exact hn ⟨E,hDE⟩
  letI : Subsingleton (Direction S) := ⟨fun E F => (hall E).symm.trans (hall F)⟩
  letI : Nonempty (Direction S) := ⟨D⟩
  have he : directionCount S = 1 := Nat.card_unique
  have hbad : 2 ≤ 1 := by simpa only [he] using hcount
  exact Nat.not_succ_le_self 1 hbad

/-- C16: at r>=2 each original core is an infinite nonidentity exact
kernel and its ACTUAL quotient strictly reduces the diversity palette. -/
theorem oldCore_strict_source (normalized : NoFiniteExactKernel S)
    (hcount : 2 ≤ directionCount S) (D : Direction S) :
    ¬ RealClosure.Bounds.FiniteClasses S (oldCore S H cco D) ∧
      oldCore S H cco D ≠ ⊥ ∧
      ExactCRT.IsExactEq S (i := ()) (oldCore S H cco D).val ∧
      Nat.card ((actualQuotientSource S H (oldCore S H cco D)).Atom () ()) < Nat.card (Atom S) := by
  obtain ⟨E,hE⟩ := exists_other_direction S hcount D
  have hinf := oldCore_infinite_of_other S H cco normalized D E hE
  have hne : oldCore S H cco D ≠ ⊥ := fun he => hinf (he ▸ finiteClasses_bot S)
  refine ⟨hinf,hne,core_exact S H _,?_⟩
  letI := S.finiteAtom () ()
  letI := (actualQuotientSource S H (oldCore S H cco D)).finiteAtom () ()
  simpa only [Nat.card_eq_fintype_card] using
    quotient_palette_strictly_drops S H (oldCore S H cco D) hne

end CCO.AclOwners
