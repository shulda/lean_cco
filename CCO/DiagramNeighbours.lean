import CCO.DiagramMove
import CCO.StabilizerSAP
import Mathlib.Data.Set.Finite.Range

/-!
# The actual neighbour-image stabilizer base for one-vertex repair

No injectivity of the current homomorphism is assumed. The base is the
SET of current images of formally adjacent vertices, so repeated
neighbour images count only once. Every displayed edge is diversity,
which proves that the current moving point lies outside that set.
Age-SAP and original homogeneity then supply a fresh stabilizer image,
and local surgery changes only the chosen formal vertex.
-/

universe u v w

namespace CCO.DiagramHom

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X} {V : Type w}
variable {D : PartialDiagram S V}

/-- Current images of exactly the displayed out-neighbours of one
formal vertex. Converse compatibility makes this also its
undirected neighbour-image set. -/
def neighbourBase (f : DiagramHom D) (x : V) :
    FiniteInduced (X := X) where
  vertices := {p | ∃ (y : V) (h : x ≠ y)
       (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
       D.edge x y h = some a ∧ p = f.image y}
  finite_vertices := by
    letI : Finite V := D.finite_type
    apply (Set.finite_range f.image).subset
    intro p hp
    rcases hp with ⟨y, h, a, ha, rfl⟩
    exact ⟨y, rfl⟩

/-- The current point is not one of its neighbour images, even when
multiple formally distinct neighbours have the same actual image. -/
theorem image_not_neighbourBase (f : DiagramHom D) (x : V) :
    f.image x ∉ (neighbourBase f x).vertices := by
  rintro ⟨y, hxy, a, ha, heq⟩
  have hcolour : S.atomRel a (f.point x) (f.point y) :=
    f.preserves_edge x y hxy a ha
  exact (S.atomRel_ne hcolour) heq

variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- A group element fixing the SET-valued neighbour base fixes the
individual typed real image at each displayed outgoing edge. -/
theorem fixes_out_neighbour
    (f : DiagramHom D) (x : V) (g : G)
    (hg : g ∈ RealAction.pointwiseStabilizer
      (G := G) (neighbourBase f x).vertices)
    (y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a) :
    g • f.point y = f.point y := by
  have hmem : f.image y ∈ (neighbourBase f x).vertices :=
    ⟨y, hxy, a, ha, rfl⟩
  have hfix := (RealAction.mem_pointwiseStabilizer
    (G := G) (neighbourBase f x).vertices g).mp hg
    (f.image y) hmem
  have htag :
      (⟨D.vertexSort y, g • f.point y⟩ : Sigma X) =
      (⟨D.vertexSort y, f.point y⟩ : Sigma X) := by
    simpa only [image, Sigma.smul_mk] using hfix
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag

/-- Incoming neighbours have the same current stabilizer base,
by the actually named typed converse of the specified atom. -/
theorem fixes_in_neighbour
    (f : DiagramHom D) (x : V) (g : G)
    (hg : g ∈ RealAction.pointwiseStabilizer
      (G := G) (neighbourBase f x).vertices)
    (y : V) (hyx : y ≠ x)
    (a : S.Atom (D.vertexSort y) (D.vertexSort x))
    (ha : D.edge y x hyx = some a) :
    g • f.point y = f.point y := by
  have hback : D.edge x y hyx.symm = some (S.conv a) :=
    (D.edge_reverse y x hyx a).mp ha
  exact fixes_out_neighbour f x g hg y hyx.symm (S.conv a) hback

/-- A local one-point move can avoid the ENTIRE current finite image and
an arbitrary further finite forbidden set. All other current images
are fixed. The choice uses the *derived* age-SAP stabilizer-orbit
infinitude theorem rather than a new orbit hypothesis. -/
theorem fresh_move_one_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (f : DiagramHom D) (x : V)
    (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ f' : DiagramHom D,
      f'.image x ∉ Z ∪ Set.range f.image ∧
      (∀ y : V, y ≠ x → f'.image y = f.image y) := by
  letI : Finite V := D.finite_type
  have hRange : (Set.range f.image).Finite := Set.finite_range _
  have hTotal : (Z ∪ Set.range f.image).Finite := hZ.union hRange
  obtain ⟨p, ⟨g, hg, hgp⟩, hpFresh⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap
      (neighbourBase f x) (f.image x) (image_not_neighbourBase f x)
      (Z ∪ Set.range f.image) hTotal
  have hOut : ∀ (y : V) (hxy : x ≠ y)
        (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
        D.edge x y hxy = some a → g • f.point y = f.point y := by
    intro y hxy a ha
    exact fixes_out_neighbour f x g hg y hxy a ha
  have hIn : ∀ (y : V) (hyx : y ≠ x)
        (a : S.Atom (D.vertexSort y) (D.vertexSort x)),
        D.edge y x hyx = some a → g • f.point y = f.point y := by
    intro y hyx a ha
    exact fixes_in_neighbour f x g hg y hyx a ha
  let f' : DiagramHom D := moveOne H f x g hOut hIn
  refine ⟨f', ?_, ?_⟩
  · have hmove : f'.image x = g • f.image x := by
      change (⟨D.vertexSort x, f'.point x⟩ : Sigma X) =
        g • (⟨D.vertexSort x, f.point x⟩ : Sigma X)
      rw [moveOne_at H f x g hOut hIn]
      rfl
    rw [hmove, hgp]
    exact hpFresh
  · intro y hyx
    change (⟨D.vertexSort y, f'.point y⟩ : Sigma X) =
      (⟨D.vertexSort y, f.point y⟩ : Sigma X)
    rw [moveOne_away H f x g hOut hIn y hyx]

end CCO.DiagramHom
