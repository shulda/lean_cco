import CCO.APCharacter.Completion.SpecifiedPaths
import CCO.APCharacter.Completion.Identification
import CCO.APCharacter.Completion.QuotientDiagram

/-! All old simple x-y path profiles containing the ORIGINAL identity
force atomic coherence on every pair of duplicated incident edges. -/
universe u v w z
namespace CCO.APCharacter.Completion
open StrongPC
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V) (f : DiagramHom D)

private theorem tagged_some {i j : ι} (x : X i) (y : X j) (a : S.Atom i j)
    (ha : S.colour x y = some a) :
    taggedColour S ⟨i,x⟩ ⟨j,y⟩ = ⟨i,j,some a⟩ :=
  congrArg (fun c => (⟨i,j,c⟩ : Σ i, Σ j, Option (S.Atom i j))) ha

/-- Original identity-containing endpoint profiles, not quotient-gate
membership and not an already constructed folded homomorphism. -/
def IdentityBound (x y : V) : Prop :=
  ∀ p : SimpleSpecifiedPath D x y, ∃ a b,
    PositiveWord.represented S p.val.word a b ∧ S.colour a b = none

/-- C23, in both orientations and with the original sort tags retained. -/
theorem identity_incident_coherence (x y : V) (hxy : x ≠ y)
    (bound : IdentityBound D x y) (z : V)
    (hxz : (graph D).Adj x z) (hyz : (graph D).Adj y z) :
    taggedColour S (f.image x) (f.image z) = taggedColour S (f.image y) (f.image z) ∧
    taggedColour S (f.image z) (f.image x) = taggedColour S (f.image z) (f.image y) := by
  obtain ⟨hxz,a,ha⟩ := hxz
  obtain ⟨hyz,b,hb⟩ := hyz
  let p : SimpleSpecifiedPath D x y :=
    ⟨SpecifiedPath.cons hxz hxy a ha
      (SpecifiedPath.edge hyz.symm (S.conv b) ((D.edge_reverse y z hyz b).mp hb)),by
        simp [SpecifiedPath.vertexList,hxz,hxy,hyz.symm]⟩
  obtain ⟨rx,ry,rz,hxz',hzy',heq⟩ :
      ∃ rx ry rz, S.colour rx rz = some a ∧
        S.colour rz ry = some (S.conv b) ∧ S.colour rx ry = none := by
    obtain ⟨rx,ry,hp,heq⟩ := bound p
    obtain ⟨rz,hxz',hzy'⟩ := hp
    exact ⟨rx,ry,rz,hxz',hzy',heq⟩
  have heq' := (S.colour_none_iff rx ry).mp heq
  have hyz' : S.colour ry rz = some b := (S.colour_swap ry rz b).mpr hzy'
  have hxzF := f.preserves_edge x z hxz a ha
  have hyzF := f.preserves_edge y z hyz b hb
  constructor
  · calc
      taggedColour S (f.image x) (f.image z) = ⟨D.vertexSort x,D.vertexSort z,some a⟩ :=
        tagged_some _ _ _ hxzF
      _ = taggedColour S ⟨D.vertexSort x,rx⟩ ⟨D.vertexSort z,rz⟩ := (tagged_some _ _ _ hxz').symm
      _ = taggedColour S ⟨D.vertexSort y,ry⟩ ⟨D.vertexSort z,rz⟩ := congrArg (fun q => taggedColour S q _) heq'
      _ = ⟨D.vertexSort y,D.vertexSort z,some b⟩ := tagged_some _ _ _ hyz'
      _ = taggedColour S (f.image y) (f.image z) := (tagged_some _ _ _ hyzF).symm
  · calc
      taggedColour S (f.image z) (f.image x) = ⟨D.vertexSort z,D.vertexSort x,some (S.conv a)⟩ :=
        tagged_some _ _ _ ((S.colour_swap _ _ a).mp hxzF)
      _ = taggedColour S ⟨D.vertexSort z,rz⟩ ⟨D.vertexSort x,rx⟩ :=
        (tagged_some _ _ _ ((S.colour_swap _ _ a).mp hxz')).symm
      _ = taggedColour S ⟨D.vertexSort z,rz⟩ ⟨D.vertexSort y,ry⟩ :=
        congrArg (fun q => taggedColour S _ q) heq'
      _ = ⟨D.vertexSort z,D.vertexSort y,some (S.conv b)⟩ := tagged_some _ _ _ hzy'
      _ = taggedColour S (f.image z) (f.image y) :=
        (tagged_some _ _ _ ((S.colour_swap _ _ b).mp hyzF)).symm

end CCO.APCharacter.Completion
