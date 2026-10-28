import CCO.StrongExact.ThetaCycleHom
import CCO.StrongExact.HellyReductions
import CCO.StrongExact.ExactClosure
import CCO.StrongExact.ExactDistribution

/-!
# Original-source consumers of the proved theta cycle bridge

The source homogeneous SAP+CCO hypotheses now discharge `WordHelly` in
finite exact-menu Helly, exact convolution, and original exact product
closure. These consumers retain the STRONG diversity guard and the
required nonempty evaluated factors. General endpoint-survivor semantics,
three-root sufficiency, PC completeness and triangle-fullness are separate.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

/-- Full finite exact-menu 2-Helly under original source hypotheses.
The empty family is included; the result is a genuine diversity atom. -/
theorem exact_helly_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (menus : List (S.Menu i j))
    (hExact : ∀ A ∈ menus, Exact S A)
    (hPair : ∀ A ∈ menus, ∀ B ∈ menus, (A ∩ B).Nonempty) :
    (meetMenus S menus).Nonempty :=
  exact_helly_of_wordHelly S (wordHelly_of_SAP_CCO S H sap cco)
    menus hExact hPair

/-- The full original-source C08 finite-presentation convolution
identity, including typed Top represented by an empty restriction list. -/
theorem exact_convolution_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k))
    (hws : (present S ws).Nonempty)
    (hvs : (present S vs).Nonempty) :
    S.product (present S ws) (present S vs) =
      convolutionBound S ws vs :=
  exact_convolution_of_wordHelly S H sap
    (wordHelly_of_SAP_CCO S H sap cco) ws vs hws hvs

/-- Actual product closure in the original exact family; the result
uses no equality-enriched RAW envelope or uninstantiated provider. -/
theorem exact_product_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {A : S.Menu i j} {B : S.Menu j k}
    (hA : Exact S A) (hB : Exact S B) :
    Exact S (S.product A B) :=
  exact_product_of_wordHelly S H sap
    (wordHelly_of_SAP_CCO S H sap cco) hA hB

/-- Left multiplication distributes over a finite exact meet whose
evaluation is nonempty, including an empty restriction family. -/
theorem product_distrib_right_exact_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (left : List (PositiveWord S i j))
    (rights : List (List (PositiveWord S j k)))
    (hLeft : (present S left).Nonempty)
    (hMeet : (present S (flattenedPresentations S rights)).Nonempty) :
    S.product (present S left)
      (present S (flattenedPresentations S rights)) =
        {c | ∀ right ∈ rights,
          c ∈ S.product (present S left) (present S right)} :=
  product_distrib_right_exact_of_wordHelly S H sap
    (wordHelly_of_SAP_CCO S H sap cco) left rights hLeft hMeet

/-- The corresponding right-factor distribution with the same
nonempty-evaluation guard and original typed strong products. -/
theorem product_distrib_left_exact_of_SAP_CCO
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (lefts : List (List (PositiveWord S i j)))
    (right : List (PositiveWord S j k))
    (hMeet : (present S (flattenedPresentations S lefts)).Nonempty)
    (hRight : (present S right).Nonempty) :
    S.product (present S (flattenedPresentations S lefts))
      (present S right) =
        {c | ∀ left ∈ lefts,
          c ∈ S.product (present S left) (present S right)} :=
  product_distrib_left_exact_of_wordHelly S H sap
    (wordHelly_of_SAP_CCO S H sap cco) lefts right hMeet hRight

end CCO.StrongExact
