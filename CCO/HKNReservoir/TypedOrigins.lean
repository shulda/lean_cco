import CCO.SafeReadings.TransversalCCO

universe v w t z
namespace CCO.HKNReservoir
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))
variable {I : Type z} [Finite I]
variable (P : OriginPattern S H R I) (sort : I → ↥B)
variable (hpal : ∀ i j a, P.edge i j = some a →
  ∃ p : SafeReadings.TransversalSource.Palette S H R B (sort i) (sort j), p.val = a)

/-- Attach only the literal typed owner tags to the existing partial
origin records. Missing records remain missing. -/
def typedOriginEdge (i j : I) : Option (SafeReadings.TransversalSource.Palette S H R B (sort i) (sort j)) :=
  match he : P.edge i j with
  | none => none
  | some a => some (hpal i j a he).choose

theorem typedOriginEdge_map (i j : I) :
    (typedOriginEdge S H R B P sort hpal i j).map Subtype.val = P.edge i j := by
  unfold typedOriginEdge
  split
  · rename_i he; exact he.symm
  · rename_i a he
    exact (congrArg some (hpal i j a he).choose_spec).trans he.symm

theorem typedOriginEdge_some (i j : I)
    (a : SafeReadings.TransversalSource.Palette S H R B (sort i) (sort j)) :
    typedOriginEdge S H R B P sort hpal i j = some a ↔ P.edge i j = some a.val := by
  constructor
  · intro ha
    have hh := congrArg (Option.map Subtype.val) ha
    exact (typedOriginEdge_map S H R B P sort hpal i j).symm.trans hh
  · intro ha
    apply Option.map_injective Subtype.val_injective
    exact (typedOriginEdge_map S H R B P sort hpal i j).trans ha

def typedOriginDiagram : PartialDiagram (SafeReadings.TransversalSource.source S H R B) I where
  finite_type := inferInstance
  vertexSort := sort
  edge i j _ := typedOriginEdge S H R B P sort hpal i j
  edge_reverse := by
    intro i j hij a
    have hi := typedOriginEdge_some S H R B P sort hpal i j a
    have hj := typedOriginEdge_some S H R B P sort hpal j i
      ((SafeReadings.TransversalSource.source S H R B).conv a)
    exact hi.trans ((Iff.of_eq (congrArg (· = some a.val) (P.symmetric i j))).trans hj.symm)

/-- Every actual homomorphic typed completion gives an actual named
origin certificate through the INTERNALLY constructed U age. -/
theorem named_origins_of_typed_hom
    (hsort : ∀ i, P.owner i = (sort i).val)
    (h : DiagramHom (typedOriginDiagram S H R B P sort hpal)) :
    Nonempty (OriginMap S H R B P) := by
  let u : I → TransversalAge.U S H R B := fun i => (h.point i).val
  obtain ⟨f,ho,hc,_⟩ := TransversalAge.realize_tuple S H R B u
  refine ⟨⟨f,?_,?_⟩⟩
  · intro i
    exact (congrArg Subtype.val ((ho i).trans (h.point i).property)).trans (hsort i).symm
  · intro i j a ha
    have hij : i ≠ j := by rintro rfl; rw [P.diagonal] at ha; cases ha
    let b := (hpal i j a ha).choose
    have hb : b.val = a := (hpal i j a ha).choose_spec
    have he : (typedOriginDiagram S H R B P sort hpal).edge i j hij = some b :=
      (typedOriginEdge_some S H R B P sort hpal i j b).mpr (ha.trans (congrArg some hb.symm))
    have hp := h.preserves_edge i j hij b he
    exact (hc i j).trans (((SafeReadings.TransversalSource.colour_some_iff S H R B _ _ b).mp hp).trans (congrArg some hb))

end
end CCO.HKNReservoir
