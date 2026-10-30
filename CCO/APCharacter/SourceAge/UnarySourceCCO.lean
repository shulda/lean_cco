import CCO.APCharacter.SourceAge.UnarySourceHomogeneity
import CCO.RawExact.DiagramReindex

/-! Actual cycle completion of the canonical child source. New cycle
witnesses are read as literal marked-limit witnesses; one actual marked
completion is then pulled back to the original child carriers. -/
universe u v w t z
namespace CCO.APCharacter.SourceAge.UnarySource
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section
variable (I : Identification S H completion)
variable {V : Type z} (D : PartialDiagram (source I) V)

def oldDiagram : PartialDiagram S V where
  finite_type := D.finite_type
  vertexSort x := (D.vertexSort x).1
  edge x y h := (D.edge x y h).map Subtype.val
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      rfl
    · intro ha
      obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse y x h.symm b).mp hb]
      change some (S.conv b.val) = some a
      rw [he,S.conv_invol]

abbrev bits (x : V) : Bit := (D.vertexSort x).2.val

/-- Existing new atoms have actual marked old witnesses; this derives the
local mask condition for each specified edge, including all valid children. -/
theorem old_legal : M.LocalLegal (oldDiagram I D) (bits I D) := by
  refine ⟨fun x => (D.vertexSort x).2.property,?_⟩
  intro x y h a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨p,q,hpq⟩ := b.property
  have hm := (global_marking I).2 ⟨(D.vertexSort x).1,p.val⟩ ⟨(D.vertexSort y).1,q.val⟩
  have hp : mark I ⟨(D.vertexSort x).1,p.val⟩ = (D.vertexSort x).2.val :=
    congrArg Subtype.val p.property
  have hq : mark I ⟨(D.vertexSort y).1,q.val⟩ = (D.vertexSort y).2.val :=
    congrArg Subtype.val q.property
  rw [hpq,hp,hq] at hm
  exact hm

def newCycle (K : SimpleCycle (oldDiagram I D)) : SimpleCycle D where
  length := K.length
  length_ge_three := K.length_ge_three
  length_pos := K.length_pos
  vertices := K.vertices
  next_ne := K.next_ne
  specified := by
    intro p
    obtain ⟨a,ha⟩ := K.specified p
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨b,hb⟩

/-- A new-source cycle homomorphism yields a literal marked-limit cycle
realization; nonadjacent collisions and independent witnesses are retained. -/
theorem cycle_realizes {V : Type} (D : PartialDiagram (source I) V)
    (cycles : ∀ K : SimpleCycle D, CycleHom K) (K : SimpleCycle (oldDiagram I D)) :
    Age.CycleRealizes S H completion (oldDiagram I D) (bits I D) K := by
  obtain ⟨p,hp⟩ := cycles (newCycle I D K)
  let q (i : Fin K.length) : NewPoint I := ⟨D.vertexSort (K.vertices i),p i⟩
  refine ⟨fun i => newEquiv I (q i),?_,?_⟩
  · intro i
    exact new_owner I (q i)
  · intro i a ha
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
    have he := hp i b hb
    rw [new_colour]
    apply congrArg (Age.colourEquiv S)
    change (⟨(D.vertexSort (K.vertices i)).1,
      (D.vertexSort (K.vertices (cyclicNext K.length_pos i))).1,
      ((source I).colour (p i) (p (cyclicNext K.length_pos i))).map Subtype.val⟩ : Age.Colour S) = _
    rw [he]
    rfl

/-- Pull a marked-limit network back to the literal child carriers, not
an isomorphic unnamed replacement source. -/
def pullRealization {V : Type} (D : PartialDiagram (source I) V)
    (hD : Age.DiagramRealizes S H completion (oldDiagram I D) (bits I D)) : DiagramHom D := by
  classical
  let point := hD.choose
  have ho := hD.choose_spec.1
  have hc := hD.choose_spec.2
  let p (x : V) := (newEquiv I).symm (point x)
  have hs (x : V) : (p x).1 = D.vertexSort x := by
    apply childLabel_injective I
    apply (Age.ownerEquiv S).injective
    exact (new_owner I (p x)).symm.trans
      (((congrArg (Age.limitCoding S H completion).table.owner
        ((newEquiv I).apply_symm_apply (point x)))).trans (ho x))
  let q (x : V) : Rank.Point (β I) (tag I) (D.vertexSort x) :=
    cast (congrArg (Rank.Point (β I) (tag I)) (hs x)) (p x).2
  have he (x : V) : newEquiv I ⟨D.vertexSort x,q x⟩ = point x :=
    (congrArg (newEquiv I) (sigma_cast (hs x) (p x).2)).trans
      ((newEquiv I).apply_symm_apply (point x))
  refine ⟨q,?_⟩
  intro x y h a ha
  apply (Rank.colour_some_iff S (β I) (tag I) (q x) (q y) a).mpr
  have hed : (oldDiagram I D).edge x y h = some a.val := by
    change (D.edge x y h).map Subtype.val = some a.val
    rw [ha]
    rfl
  have hh := hc x y h a.val hed
  change (Age.limitCoding S H completion).table.colour (point x) (point y) =
    Age.colourEquiv S ⟨(D.vertexSort x).1,(D.vertexSort y).1,some a.val⟩ at hh
  rw [← he x,← he y,new_colour,erase_tagged] at hh
  have hOld := (Age.colourEquiv S).injective hh
  change taggedColour S ⟨(D.vertexSort x).1,(q x).val⟩ ⟨(D.vertexSort y).1,(q y).val⟩ =
    ⟨(D.vertexSort x).1,(D.vertexSort y).1,some a.val⟩ at hOld
  simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hOld

/-- Genuine semantic HOM CCO for the canonical new source, in arbitrary
formal-vertex universes. Finite reindexing is proved by the accepted API. -/
theorem semanticCCO : SemanticCCO.{u,v,z,w} (source I) := by
  apply semanticCCO_of_fin
  intro n D cycles
  exact ⟨pullRealization I D (Age.marked_cco S H completion (oldDiagram I D) (bits I D)
    (old_legal I D) (fun K => cycle_realizes I D cycles K))⟩

end
end CCO.APCharacter.SourceAge.UnarySource
