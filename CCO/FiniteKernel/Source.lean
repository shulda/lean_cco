import CCO.FiniteKernel.CompactProjection
import CCO.FiniteKernel.OwnerHomogeneity
import CCO.FiniteKernel.LinearInvariant
import CCO.FiniteKernel.Named.Boundary

/-! Original real-point consumers of the kernel/CSP and dual width criteria.
These conclusions return genuine FULL-source automorphisms, rather than an
uninstantiated tuple group or a hypothetical extension provider.
-/

universe u v w z t
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

theorem prescribed_actual_automorphism [Countable X] (A : Finset I)
    (g : ∀ i : ↥A,P.Intrinsic i.val) (hfinite : P.FiniteExtensionProperty A g) :
    ∃ gamma : S.Aut, (∀ x,P.owner (gamma.val x) = P.owner x) ∧
      ∀ (i : ↥A) (x : P.Fibre i.val), gamma.val x.val = ((g i).val x).val := by
  obtain ⟨n,hn⟩ := (P.compact_projection_of_countable_source A g).mpr hfinite
  refine ⟨n.val,P.kernel_fixes n,?_⟩
  intro i x
  have hi := congrFun hn i
  exact congrArg (fun h : P.Intrinsic i.val => ((h.val x).val)) hi

theorem owner_homogeneous_actual_automorphism
    (H : (S.ownerExpansion P.owner).Homogeneous) (A : Finset I) (g : P.solutions A) :
    ∃ gamma : S.Aut, (∀ x,P.owner (gamma.val x) = P.owner x) ∧
      ∀ (i : ↥A) (x : P.Fibre i.val), gamma.val x.val = ((g.val i).val x).val := by
  obtain ⟨n,hn⟩ := P.owner_homogeneous_extension H A g
  refine ⟨n.val,P.kernel_fixes n,?_⟩
  intro i x
  have hi := congrFun hn i
  exact congrArg (fun h : P.Intrinsic i.val => ((h.val x).val)) hi

variable (V : I → Type t) [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

/-- The EXACT width-two row condition, together with the ACTUAL marginal
constraints, extends a prescribed finite motion to one actual global kernel
automorphism. No owner homogeneity or unrestricted elimination is asserted.
-/
theorem width_two_actual_motion [Countable X] [DecidableEq I] (A : Finset I)
    (hrows : pairRows F2 V (P.localPairSpace V e) ⊓ restrictedTestSpace F2 V A =
      marginalRows F2 V (pairRows F2 V (P.localPairSpace V e)) A)
    (g : FiniteProduct V A) (hg : g ∈ marginalSpace F2 V (P.linearKernel V e) A) :
    ∃ n : P.kernel, ∀ i : ↥A,P.restrictFibre i.val n = e i.val (Multiplicative.ofAdd (g i)) := by
  have hproj : g ∈ finiteProjection F2 V (P.linearKernel V e) A := by
    rw [(P.source_width_two V e A).mpr hrows]
    exact hg
  obtain ⟨x,hx,hxg⟩ := hproj
  have hxperp : x ∈ perp F2 V (pairRows F2 V (P.localPairSpace V e)) := by
    rw [← P.linearKernel_eq_perp V e]
    exact hx
  obtain ⟨n,hn⟩ := (P.actual_motion_iff V e x).mp hxperp
  refine ⟨n,?_⟩
  intro i
  exact (hn i.val).trans
    (congrArg (fun a : V i.val => e i.val (Multiplicative.ofAdd a)) (congrFun hxg i))

end
end CCO.FiniteKernel.FinitePartition
