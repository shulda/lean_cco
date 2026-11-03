import CCO.StrongExact.SourceExactCalculus
import CCO.TerminalLattice.OriginalCCOUniverseBridge

/-!
# B060 independent typed STRONG exact-domain distributivity

This is the generic source branch of `lem:ramsey-typed-distributivity`.
It accepts ANY actual homogeneous named-sorted SAP+semantic HOM CCO
atomic source, not necessarily a clone cover or a terminal source.

All menus consist of genuinely positive STRONG diversity profiles.
A finite exact meet is required to evaluate nonempty. Logical equality
never becomes a diversity colour, and no NR2 or hidden quotient SAP
is assumed. The proof is a genuine TWO-SIDED combination of the
independently accepted one-sided typed convolution theorems.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Source B060 C35–C41, the generic part of the selected typed
distributivity export. Both indexing families can be empty;
each entry is a finite list of positive STRONG words (so a domain
within either indexing family is itself an exact finite meet).
Only the two actually evaluated outer meets must be nonempty.

Repeated sorts, mixed sorts, nonempty exact presentation guards
and real equality exclusion are exactly those of the source.
-/
theorem original_typed_exact_double_meet
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι}
    (lefts : List (List (PositiveWord S i j)))
    (rights : List (List (PositiveWord S j k)))
    (hLeft : (StrongExact.present S
      (StrongExact.flattenedPresentations S lefts)).Nonempty)
    (hRight : (StrongExact.present S
      (StrongExact.flattenedPresentations S rights)).Nonempty) :
    S.product
        (StrongExact.present S (StrongExact.flattenedPresentations S lefts))
        (StrongExact.present S (StrongExact.flattenedPresentations S rights)) =
      {c | ∀ left ∈ lefts, ∀ right ∈ rights,
        c ∈ S.product (StrongExact.present S left)
          (StrongExact.present S right)} := by
  have cco0 : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  have hOne (left : List (PositiveWord S i j)) (hl : left ∈ lefts) :
      (StrongExact.present S left).Nonempty := by
    obtain ⟨a, ha⟩ := hLeft
    refine ⟨a, ?_⟩
    intro w hw
    exact ha w (List.mem_flatMap.mpr ⟨left, hl, hw⟩)
  rw [StrongExact.product_distrib_left_exact_of_SAP_CCO S H sap cco0
    lefts (StrongExact.flattenedPresentations S rights) hLeft hRight]
  ext c
  constructor
  · intro h left hl right hr
    have hProd := h left hl
    rw [StrongExact.product_distrib_right_exact_of_SAP_CCO S H sap cco0
      left rights (hOne left hl) hRight] at hProd
    exact hProd right hr
  · intro h left hl
    rw [StrongExact.product_distrib_right_exact_of_SAP_CCO S H sap cco0
      left rights (hOne left hl) hRight]
    exact h left hl

/-- Source B060 C37/C41: exact positive STRONG typed domains
are closed under actual convolution, WITHOUT adjoining RAW equality.
The receiving source CCO premise is transported to the finite diagram
universe by the accepted B050 bridge, not added a second time.
-/
theorem original_typed_exact_product
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι} {A : S.Menu i j} {B : S.Menu j k}
    (hA : StrongExact.Exact S A) (hB : StrongExact.Exact S B) :
    StrongExact.Exact S (S.product A B) := by
  have cco0 : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  exact StrongExact.exact_product_of_SAP_CCO S H sap cco0 hA hB

end CCO.CloneTupleGeometry
