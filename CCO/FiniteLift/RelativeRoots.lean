import CCO.FiniteLift.RelativeRequests
import CCO.FiniteLift.OwnerCorrection
import CCO.FiniteLift.Ordinary

/-! C25–C26: relative reconstruction preserves the selected ORIGINAL
root and both whole finite actions on the SAME carrier. The extra owner
onto/kernel hypothesis is used only for the one root correction. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product Owners.Provider OwnerCover
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

/-- Keep a GIVEN whole quotient transport, choose its one compatible
owner correction, and force a literal real root in the same joint lift. -/
theorem relative_selected_root (finiteK : K.FiniteClasses)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteDbar : Dbar.Finite) (finiteBbar : Bbar.Finite)
    (imageD : rK S HS cco K H '' Dbar = Bbar)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (z a : fullPreimage K.proj Dbar)
    (β : OrbitalAut G K.Q (Subtype.val : Dbar → K.Q))
    (hβz : β.val (fullProjection K.proj Dbar z) = fullProjection K.proj Dbar a) :
    ∃ (α : OrbitalAut G A (Subtype.val : fullPreimage K.proj Dbar → A))
      (γ : OrbitalAut G H.Q (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q)),
      α.val z = a ∧ finiteAction K.proj K.onto K.proj_smul Dbar α = β ∧
      (realOwner S HS cco K H Dbar Bbar imageD).action α = γ ∧
      ownerAction S HS cco K H Bbar γ =
        (quotientOwner S HS cco K H Dbar Bbar imageD).action β := by
  classical
  let Qbar := quotientOwner S HS cco K H Dbar Bbar imageD
  let Qreal := realOwner S HS cco K H Dbar Bbar imageD
  let C := fullOwnerQuotient S HS cco K H Bbar
  let δ := Qbar.action β
  have hδ : δ.val (C.projection (Qreal.projection z)) = C.projection (Qreal.projection a) := by
    change (Qbar.action β).val (Qbar.projection (fullProjection K.proj Dbar z)) =
      Qbar.projection (fullProjection K.proj Dbar a)
    rw [Qbar.action_projection,hβz]
  obtain ⟨γ,hγ,hγpoint⟩ := owner_kernel_point S HS cco K H Bbar onto fibres
    (Qreal.projection z) (Qreal.projection a) δ hδ
  let req := singletonRequest (S.original_sort_transitive_of_homogeneous HS ())
    K.proj (fullPreimage K.proj Dbar) Dbar (fun x => x.property) z a β hβz
  have compH : ∀ x : req.part.domain,
      H.proj (req.part.map x).val = (γ.val (Qreal.projection x.val)).val := by
    intro x
    have hx : x.val = z := Set.mem_singleton_iff.mp x.property
    change H.proj a.val = (γ.val (Qreal.projection x.val)).val
    rw [hx]
    exact (congrArg Subtype.val hγpoint).symm
  obtain ⟨α,hp,hK,hH⟩ := three_sort_lift S HS cco K H finiteK Dbar Bbar
    finiteDbar finiteBbar imageD req.part β γ hγ req.compatible compH
  exact ⟨α,γ,hp ⟨z,Set.mem_singleton z⟩,hK,hH,hγ⟩

theorem relative_roots (finiteK : K.FiniteClasses)
    (safe : A → A → Prop) (A0 : Set A) (finiteA : A0.Finite)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteBbar : Bbar.Finite) (imageD : rK S HS cco K H '' Dbar = Bbar)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (w : RelativeWitness (quotientOwner S HS cco K H Dbar Bbar imageD)
      (aclSet (FullAut G K.Q)) (quotientSafe K.proj safe) (K.proj '' A0)) :
    ∀ (Z : Set (fullPreimage K.proj Dbar)),
      Unsafe (fun x y : fullPreimage K.proj Dbar => safe x.val y.val) Z →
      ∀ z ∈ Z, ∃ α : OrbitalAut G A (Subtype.val : fullPreimage K.proj Dbar → A),
        (∀ x ∈ Z, (α.val x).val ∈ aclSet G A0) ∧ (α.val z).val ∈ A0 := by
  classical
  intro Z hZ z hz
  let Q := fullQuotient K.proj K.onto K.proj_smul Dbar
  have hZbar := unsafe_fullProjection K.proj Dbar safe hZ
  obtain ⟨β,hβZ,hβz⟩ := w.roots (Q.projection '' Z) hZbar
    (Q.projection z) ⟨z,hz,rfl⟩
  obtain ⟨a,ha,he⟩ := hβz
  have haD : a ∈ fullPreimage K.proj Dbar :=
    full_preimage_contains_closure S HS cco K finiteK A0 finiteA Dbar w.closure
      (subset_aclSet G A0 ha)
  let aD : fullPreimage K.proj Dbar := ⟨a,haD⟩
  obtain ⟨α,γ,hαz,hαK,hαH,hγ⟩ := relative_selected_root S HS cco K H finiteK
    Dbar Bbar w.finite finiteBbar imageD onto fibres z aD β (Subtype.ext he.symm)
  have projα (x : fullPreimage K.proj Dbar) :
      K.proj (α.val x).val = (β.val (fullProjection K.proj Dbar x)).val := by
    have hh := finiteAction_projection K.proj K.onto K.proj_smul Dbar α x
    rw [hαK] at hh
    exact (congrArg Subtype.val hh).symm
  refine ⟨α,?_,?_⟩
  · intro x hx
    rw [K.acl_pullback HS cco finiteK A0 finiteA]
    change K.proj (α.val x).val ∈ aclSet (FullAut G K.Q) (K.proj '' A0)
    rw [projα]
    exact hβZ (Q.projection x) ⟨x,hx,rfl⟩
  · change (α.val z).val ∈ A0
    rw [hαz]
    exact ha

/-- The stronger relative branch: exact H, the COMPLETE finite inverse
owner set and its ACTUAL onto/fibre-transitive full-group map remain
explicit. One D handles ALL requests and ALL selected roots. -/
theorem relative_reconstruction (finiteK : K.FiniteClasses)
    (safe : A → A → Prop) (A0 : Set A) (finiteA : A0.Finite) (_nonemptyA : A0.Nonempty)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteBbar : Bbar.Finite) (imageD : rK S HS cco K H '' Dbar = Bbar)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (w : RelativeWitness (quotientOwner S HS cco K H Dbar Bbar imageD)
      (aclSet (FullAut G K.Q)) (quotientSafe K.proj safe) (K.proj '' A0)) :
    RelativeWitness (realOwner S HS cco K H Dbar Bbar imageD) (aclSet G) safe A0 where
  finite := K.fullPreimage_finite finiteK Dbar w.finite
  closure := full_preimage_contains_closure S HS cco K finiteK A0 finiteA Dbar w.closure
  extensions := relative_extensions S HS cco K H finiteK Dbar Bbar w.finite
    finiteBbar imageD A0 w.extensions
  roots := relative_roots S HS cco K H finiteK safe A0 finiteA Dbar Bbar
    finiteBbar imageD onto fibres w

end CCO.FiniteLift
