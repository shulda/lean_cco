import CCO.FiniteLift.WitnessBasics
import CCO.FiniteLift.Closure

/-! C15–C18: the SAME full K-preimage of the supplied quotient witness
handles every source map and every selected original root. The quotient
witness is an input; there is no age EPPA, owner H or owner-master premise. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product Owners.Provider
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K : ExactKernel S G)

include HS cco

/-- C15: partial maps may have arbitrary sparse domains/ranges in A0.
The quotient extension and the simultaneous lift preserve one fixed D. -/
theorem ordinary_extensions (Dbar : Set K.Q) (finiteB : Dbar.Finite)
    (finiteD : (fullPreimage K.proj Dbar).Finite)
    (A0 : Set A)
    (ep : EPPAFor (G := G) (ι := (Subtype.val : Dbar → K.Q))
      {q | q.val ∈ K.proj '' A0}) :
    EPPAFor (G := G) (ι := (Subtype.val : fullPreimage K.proj Dbar → A))
      {x | x.val ∈ A0} := by
  intro p hDom hRan
  let Q := fullQuotient K.proj K.onto K.proj_smul Dbar
  let pbar := Q.projectedPartial p
  have hbarDom : pbar.domain ⊆ {q | q.val ∈ K.proj '' A0} := by
    rintro q ⟨x,hx,rfl⟩
    exact ⟨x.val,hDom hx,rfl⟩
  have hbarRan : ∀ q : pbar.domain, pbar.map q ∈ {q | q.val ∈ K.proj '' A0} := by
    intro q
    exact ⟨(p.map (Q.domainLift p q)).val,hRan _,rfl⟩
  obtain ⟨β,hβ⟩ := ep pbar hbarDom hbarRan
  have comp : ∀ x : p.domain,
      K.proj (p.map x).val = (β.val (fullProjection K.proj Dbar x.val)).val := by
    intro x
    have hh := hβ ⟨Q.projection x.val,⟨x.val,x.property,rfl⟩⟩
    rw [Q.partial_projection p x] at hh
    exact (congrArg Subtype.val hh).symm
  obtain ⟨α,hp,_⟩ := full_preimage_lift S HS cco K Dbar finiteB finiteD p β comp
  exact ⟨α,hp⟩

/-- The fixed real carrier contains the original closure, without
asserting that the supplied witness itself is absolutely closed. -/
theorem full_preimage_contains_closure (finiteK : K.FiniteClasses)
    (A0 : Set A) (finiteA : A0.Finite) (Dbar : Set K.Q)
    (contains : aclSet (FullAut G K.Q) (K.proj '' A0) ⊆ Dbar) :
    aclSet G A0 ⊆ fullPreimage K.proj Dbar := by
  rw [K.acl_pullback HS cco finiteK A0 finiteA]
  exact fun _ hx => contains hx

/-- C17: the singleton real map is lifted together with the ENTIRE
quotient action. Its root lands literally in A0, and the whole clique
lands in the actual original closure. -/
theorem ordinary_roots (finiteK : K.FiniteClasses)
    (safe : A → A → Prop) (A0 : Set A) (finiteA : A0.Finite)
    (Dbar : Set K.Q)
    (w : OrdinaryWitness (G := G) (aclSet (FullAut G K.Q))
      (quotientSafe K.proj safe) (K.proj '' A0) Dbar) :
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
  let r := singletonRequest (S.original_sort_transitive_of_homogeneous HS ())
    K.proj (fullPreimage K.proj Dbar) Dbar (fun x => x.property) z aD β
    (Subtype.ext he.symm)
  obtain ⟨α,hp,hα⟩ := full_preimage_lift S HS cco K Dbar w.finite
    (K.fullPreimage_finite finiteK Dbar w.finite) r.part β r.compatible
  have projα (x : fullPreimage K.proj Dbar) :
      K.proj (α.val x).val = (β.val (fullProjection K.proj Dbar x)).val := by
    have hh := finiteAction_projection K.proj K.onto K.proj_smul Dbar α x
    rw [hα] at hh
    exact (congrArg Subtype.val hh).symm
  refine ⟨α,?_,?_⟩
  · intro x hx
    rw [K.acl_pullback HS cco finiteK A0 finiteA]
    change K.proj (α.val x).val ∈ aclSet (FullAut G K.Q) (K.proj '' A0)
    rw [projα]
    exact hβZ (Q.projection x) ⟨x,hx,rfl⟩
  · have hh := congrArg Subtype.val (hp ⟨z,Set.mem_singleton z⟩)
    change (α.val z).val = a at hh
    rw [hh]
    exact ha

/-- C18: one genuine finite original witness, with no relative-owner
inputs. The explicitly nonempty original input is retained as in source. -/
theorem ordinary_reconstruction (finiteK : K.FiniteClasses)
    (safe : A → A → Prop) (A0 : Set A) (finiteA : A0.Finite) (_nonemptyA : A0.Nonempty)
    (Dbar : Set K.Q)
    (w : OrdinaryWitness (G := G) (aclSet (FullAut G K.Q))
      (quotientSafe K.proj safe) (K.proj '' A0) Dbar) :
    OrdinaryWitness (G := G) (aclSet G) safe A0 (fullPreimage K.proj Dbar) where
  finite := K.fullPreimage_finite finiteK Dbar w.finite
  closure := full_preimage_contains_closure S HS cco K finiteK A0 finiteA Dbar w.closure
  extensions := ordinary_extensions S HS cco K Dbar w.finite
    (K.fullPreimage_finite finiteK Dbar w.finite) A0 w.extensions
  roots := ordinary_roots S HS cco K finiteK safe A0 finiteA Dbar w

end CCO.FiniteLift
