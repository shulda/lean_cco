import CCO.OwnerTransversal.TypedCompletion
import CCO.OwnerTransversal.AnchoredInjective
import CCO.OwnerTransversal.TypedOrbitSAP

/-! Only this optional typed SAP branch uses original AgeSAP and infinite
E-classes.  The basic typed AP, CCO and exact age theorems do not import it. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (E : ColourEq S ()) {B : Type} [Fintype B] (q : B → Quotient E.val)
variable (hq : Function.Injective q)

def typedForget (p : Sigma (OwnerCarrier S E q)) : M := p.2.val

include hq in
theorem typedForget_injective : Function.Injective (typedForget S E q) := by
  rintro ⟨b,x⟩ ⟨c,y⟩ hxy
  have hValue : x.val = y.val := hxy
  have hbc : b = c := hq (x.property.symm.trans ((congrArg Quotient.mk'' hValue).trans y.property))
  subst c
  exact congrArg (Sigma.mk b) (Subtype.ext hValue)

include H hq in
/-- The actual named-source stabilizer orbit is infinite.  Naming the
owners is discharged by C08 on the original source, before any SAP
conclusion for this new source is used. -/
theorem typedOwner_infinite_orbits (sap : AgeSAP S)
    (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y}) :
    letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
      ownerCarrierAction S H E q
    ∀ (C : FiniteInduced (X := OwnerCarrier S E q)) (x : Sigma (OwnerCarrier S E q)),
      x ∉ C.vertices → (RealAction.orbitOver (G := ownerFixer S H E q) C.vertices x).Infinite := by
  classical
  letI := originalQuotientAction S H E
  letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
    ownerCarrierAction S H E q
  intro C x hx hFinite
  let realC := (C.finite_vertices.image (typedForget S E q)).toFinset
  have hxC : typedForget S E q x ∉ realC := by
    intro hh
    obtain ⟨y,hy,hxy⟩ := (C.finite_vertices.image (typedForget S E q)).mem_toFinset.mp hh
    exact hx ((typedForget_injective S E q hq hxy) ▸ hy)
  let realZ := (hFinite.image (typedForget S E q)).toFinset
  obtain ⟨g,hg,hOwn,hFresh⟩ := fresh_fixed_owners_of_SAP S H sap E hInfinite
    (fun b => (q b).out) realC realZ (typedForget S E q x) hxC
  have hqg (b : B) : g • q b = q b := by
    calc
      g • q b = g • (Quotient.mk'' (q b).out : Quotient E.val) :=
        congrArg (fun z : Quotient E.val => g • z) (Quotient.out_eq _).symm
      _ = Quotient.mk'' (g • (q b).out) := rfl
      _ = Quotient.mk'' (q b).out := (Quotient.sound (hOwn b)).symm
      _ = q b := Quotient.out_eq _
  let k : ownerFixer S H E q := ⟨g,hqg⟩
  have hfix : ∀ c ∈ C.vertices, k • c = c := by
    intro c hc
    apply typedForget_injective S E q hq
    change g • typedForget S E q c = typedForget S E q c
    apply hg
    exact (C.finite_vertices.image (typedForget S E q)).mem_toFinset.mpr ⟨c,hc,rfl⟩
  have hmem : k • x ∈ RealAction.orbitOver (G := ownerFixer S H E q) C.vertices x :=
    ⟨k,hfix,rfl⟩
  apply hFresh
  change typedForget S E q (k • x) ∈ realZ
  exact (hFinite.image (typedForget S E q)).mem_toFinset.mpr ⟨k • x,hmem,rfl⟩

include H in
/-- C16, fully discharged for the ACTUAL typed owner source.  The whole
off-base factor is moved simultaneously, retaining every internal fine
colour and each individually named owner. -/
theorem typedOwner_ageSAP [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (sap : AgeSAP S) (hInfinite : ∀ x : M, Set.Infinite {y : M | E x y}) :
    AgeSAP (typedOwnerSource S E q hq) := by
  letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
    ownerCarrierAction S H E q
  exact ageSAP_of_infinite_stabilizer_orbits _ (typedOwner_homogeneous S H E q hq cco hE)
    (typedOwner_infinite_orbits S H E q hq sap hInfinite)

end CCO.OwnerTransversal
