import CCO.CloneSAP.Homogeneity
import CCO.CloneSAP.Amalgamation
import CCO.CloneSAP.TriangleReflection
import CCO.CloneSAP.ExactKernel
import CCO.CloneSAP.EdgeCases
import CCO.CloneSAP.CCO.Cycles

/-! Source export `thm:internal-clone-sap`. Each independent branch has its
own proof above: AP only for strong real amalgamation, original triangle age
only for the complete triangle quotient, and diversity-only old CCO only for
c-component contraction. The full represented kernel is a positive RAW word.
No later Ramsey theorem or external provider is assumed. -/
universe u v w z t
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
open TerminalPowers

/-- C26: pure-clone SAPification of the actual original named-sorted source.
Finite and singleton old carriers and zero old diversity palettes are allowed.
Countability is retained, while only the clone fibres are forced infinite. -/
theorem internal_clone_sap {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    [Countable (Sigma X)] (H : HomogeneousSource S G)
    (triangles : TriangleDefined.{u,v,w,z} S) (ap : AgeAP S)
    (cco : SemanticCCO.{u,v,z,w} S) :
    Countable (Sigma (Carrier X)) ∧
    HomogeneousSource (source S) (FullAut (source S)) ∧
    TriangleDefined.{u,v,w,z} (source S) ∧ AgeSAP (source S) ∧
    SemanticCCO.{u,v,z,w} (source S) ∧
    (∀ i, RawExact.evaluate (source S) (kernelExact S i).words =
      (kernelSetoid (X := X) i).r) ∧
    (∀ i, Nonempty (Quotient (kernelSetoid (X := X) i) ≃ X i)) := by
  exact ⟨countable_real_points,homogeneous S H,triangle_defined S triangles,
    strong_amalgamation S ap,CCO.cco_forward S cco,kernelExact_relation S,
    fun i => ⟨quotientOwnerEquiv i⟩⟩

end CCO.CloneSAP
