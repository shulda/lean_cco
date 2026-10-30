import CCO.Finite
import CCO.CloneSAP.FiniteUnion
import Mathlib.Data.Fintype.EquivFin

/-! B048 C32: the actual infinite one-colour pair source has SAP and
homomorphic CCO. Finite diagrams embed injectively; neither homogeneity,
full-language SAP nor a completion provider is assumed. -/
universe u v w z
namespace CCO.FullPhaseLift.Boundary.OneColour
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [Subsingleton ι] [∀ i j, Subsingleton (S.Atom i j)]

/-- On a one-sort/one-diversity-colour source, the full tagged pair name
is determined precisely by equality of the two real points. -/
theorem taggedColour_eq_of_equality_pattern (p q r s : Sigma X)
    (h : p = q ↔ r = s) : taggedColour S p q = taggedColour S r s := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases r with ⟨k,z⟩
  rcases s with ⟨l,t⟩
  have hj : j = i := Subsingleton.elim _ _
  have hk : k = i := Subsingleton.elim _ _
  have hl : l = i := Subsingleton.elim _ _
  subst j
  subst k
  subst l
  have hn : S.colour x y = none ↔ S.colour z t = none :=
    (S.colour_none_iff x y).trans (h.trans (S.colour_none_iff z t).symm)
  have hc : S.colour x y = S.colour z t := by
    by_cases hx : S.colour x y = none
    · exact hx.trans (hn.mp hx).symm
    · have hz : S.colour z t ≠ none := fun he => hx (hn.mpr he)
      obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hx
      obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp hz
      rw [ha,hb,Subsingleton.elim a b]
  exact congrArg (fun c => (⟨i,i,c⟩ : Σ i, Σ j, Option (S.Atom i j))) hc

private def finiteEmbedding {V : Type z} [Finite V] [Infinite (Sigma X)] : V ↪ Sigma X := by
  letI : Fintype V := Fintype.ofFinite V
  exact (Fintype.equivFin V).toEmbedding.trans
    ((⟨Fin.val,Fin.val_injective⟩ : Fin (Fintype.card V) ↪ ℕ).trans (Infinite.natEmbedding (Sigma X)))

private theorem sigma_cast {i j : ι} (h : i = j) (x : X i) :
    (⟨j,cast (congrArg X h) x⟩ : Sigma X) = ⟨i,x⟩ := by
  cases h
  rfl

/-- A finite partial pair diagram has an actual INJECTIVE typed
realization. All specified diversity edges are preserved automatically. -/
theorem finite_diagram_embedding [Infinite (Sigma X)] {V : Type z}
    (D : PartialDiagram S V) : ∃ f : DiagramHom D, f.IsInjective := by
  letI : Finite V := D.finite_type
  let e : V ↪ Sigma X := finiteEmbedding
  let point (x : V) : X (D.vertexSort x) :=
    cast (congrArg X (Subsingleton.elim (e x).1 (D.vertexSort x))) (e x).2
  have tag (x : V) : (⟨D.vertexSort x,point x⟩ : Sigma X) = e x :=
    sigma_cast (Subsingleton.elim (e x).1 (D.vertexSort x)) (e x).2
  let f : DiagramHom D := {
    point := point
    preserves_edge := by
      intro x y hxy a _
      have hn : (⟨D.vertexSort x,point x⟩ : Sigma X) ≠ ⟨D.vertexSort y,point y⟩ := by
        rw [tag,tag]
        exact fun he => hxy (e.injective he)
      cases hc : S.colour (point x) (point y) with
      | none => exact False.elim (hn ((S.colour_none_iff _ _).mp hc))
      | some b => exact congrArg some (Subsingleton.elim b a) }
  refine ⟨f,?_⟩
  intro x y h
  apply e.injective
  exact (tag x).symm.trans (h.trans (tag y))

/-- Every finite diagram is realizable; the cycle premise is unnecessary
for this actual source instance, rather than postulated as an oracle. -/
theorem semanticCCO [Infinite (Sigma X)] : SemanticCCO.{u,v,z,w} S := by
  intro V D _
  obtain ⟨f,_⟩ := finite_diagram_embedding S D
  exact ⟨f⟩

/-- True age SAP, including exact base intersection and arbitrary empty
base/legs. Only the displayed base points are identified in the formal
union before it is injected into the infinite actual carrier. -/
theorem ageSAP [Infinite (Sigma X)] : AgeSAP S where
  strong_amalgamate := by
    classical
    intro C A B s t
    let V := CloneSAP.FiniteUnion.Union (A := A.vertices) t.toEmbedding
    letI : Finite A.vertices := A.finite_vertices.to_subtype
    letI : Finite B.vertices := B.finite_vertices.to_subtype
    letI : Fintype A.vertices := Fintype.ofFinite _
    letI : Fintype B.vertices := Fintype.ofFinite _
    letI : Finite V := by dsimp [V,CloneSAP.FiniteUnion.Union,CloneSAP.FiniteUnion.OffBase]; infer_instance
    let e : V ↪ Sigma X := finiteEmbedding
    let D : FiniteInduced (X := X) := ⟨Set.range e,Set.finite_range e⟩
    let lift : V ↪ D.vertices := ⟨fun v => ⟨e v,⟨v,rfl⟩⟩,fun x y h => e.injective (congrArg Subtype.val h)⟩
    let l := (CloneSAP.FiniteUnion.left t.toEmbedding).trans lift
    let r := (CloneSAP.FiniteUnion.right s.toEmbedding t.toEmbedding).trans lift
    let le : InducedEmbedding S A D := {
      toEmbedding := l
      preserves_sort := fun _ => Subsingleton.elim _ _
      preserves_colours := by
        intro x y
        apply taggedColour_eq_of_equality_pattern S
        constructor
        · intro h
          exact congrArg (fun z : A.vertices => (l z).val) (Subtype.ext h)
        · intro h
          exact congrArg Subtype.val (l.injective (Subtype.ext h)) }
    let re : InducedEmbedding S B D := {
      toEmbedding := r
      preserves_sort := fun _ => Subsingleton.elim _ _
      preserves_colours := by
        intro x y
        apply taggedColour_eq_of_equality_pattern S
        constructor
        · intro h
          exact congrArg (fun z : B.vertices => (r z).val) (Subtype.ext h)
        · intro h
          exact congrArg Subtype.val (r.injective (Subtype.ext h)) }
    refine ⟨D,le,re,?_,?_⟩
    · intro c
      exact congrArg lift (CloneSAP.FiniteUnion.commute s.toEmbedding t.toEmbedding c)
    · intro a b h
      exact CloneSAP.FiniteUnion.intersection s.toEmbedding t.toEmbedding a b (lift.injective h)

end
end CCO.FullPhaseLift.Boundary.OneColour
