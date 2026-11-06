import CCO.CloneTupleGeometry.FiniteTypedExact

/-! The independent selected B060 export. Its ancestry contains only the
generic typed STRONG exact-product proof. No clone terminalisation,
invariant-equivalence NR2 or optional original-F-MI branch is imported. -/

universe u v w p q
namespace CCO.CloneTupleGeometry
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- `lem:ramsey-typed-distributivity`, C41: actual homogeneous typed
SAP+HOM CCO alone supplies both-sided nonempty STRONG meet distribution.
Every factor is an actual finite positive-profile exact domain, and the
two evaluated meets explicitly retain their required nonemptiness. -/
theorem ramsey_typed_distributivity
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι} {I : Type p} {J : Type q} [Finite I] [Finite J]
    (A : I → S.Menu i j) (B : J → S.Menu j k)
    (hA : ∀ a, StrongExact.Exact S (A a))
    (hB : ∀ b, StrongExact.Exact S (B b))
    (hLeft : ({c | ∀ a, c ∈ A a} : S.Menu i j).Nonempty)
    (hRight : ({c | ∀ b, c ∈ B b} : S.Menu j k).Nonempty) :
    S.product ({c | ∀ a, c ∈ A a} : S.Menu i j)
      ({c | ∀ b, c ∈ B b} : S.Menu j k) =
      {c | ∀ a b, c ∈ S.product (A a) (B b)} :=
  original_typed_exact_finite_double_meet S H sap cco A B hA hB hLeft hRight

end CCO.CloneTupleGeometry
