import CCO.TerminalLattice.OldAbsorption
import CCO.PositiveWords

/-!
# B050 C25: ORIGINAL same-sort STRONG product algebra

A same-sort source has symmetric OLD diversity colours, hence actual
STRONG product commutation of arbitrary old menus. Associativity is
proved by the accepted B001 genuine complete-edge SAP gluing, which
aligns two real triangles and separates their off-edge points.

No mixed-sort commutation, synthetic STRONG identity, Set-Pasch
assumption, exact-product formula, CCO or NR2 is introduced.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- C25 commutation of actual old same-sort STRONG diversity menus,
without any extra source hypothesis beyond the symmetric old sort. -/
theorem original_same_sort_strong_commute {i : ι}
    (D E : S.Menu i i) :
    S.product D E = S.product E D :=
  S.loop_product_commute D E

/-- C25 associativity of actual old same-sort STRONG products:
the original source's AgeSAP supplies the complete-edge gluing
constructor. No CCO/NR2 or exactness assumptions are required. -/
theorem original_same_sort_strong_assoc
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (D E F : S.Menu i i) :
    S.product (S.product D E) F =
      S.product D (S.product E F) :=
  S.product_assoc_of_edge_gluing
    (S.realEdgeGluing_of_SAP H sap) D E F

/-- The same verified C25 equations directly for arbitrary positive
original same-sort word profiles, whose internal word sorts may vary.
All operations commute ONLY as complete same-sort endpoint menus. -/
theorem original_positive_profiles_commute
    {i : ι} (a b : PositiveWord S i i) :
    S.product (PositiveWord.profile S a) (PositiveWord.profile S b) =
      S.product (PositiveWord.profile S b) (PositiveWord.profile S a) :=
  original_same_sort_strong_commute S _ _

theorem original_positive_profiles_assoc
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (a b c : PositiveWord S i i) :
    S.product (S.product (PositiveWord.profile S a)
        (PositiveWord.profile S b)) (PositiveWord.profile S c) =
      S.product (PositiveWord.profile S a)
        (S.product (PositiveWord.profile S b)
          (PositiveWord.profile S c)) :=
  original_same_sort_strong_assoc S H sap _ _ _

end CCO.TerminalLattice
