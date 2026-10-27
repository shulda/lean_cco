import CCO.DiagramAction

/-!
# Local one-vertex surgery on a specified diversity diagram

Unlike a simultaneous group transport, only the image of the chosen
formal vertex changes. The moving group element needs to fix the
CURRENT IMAGES of all its specified neighbours, not a list of distinct
neighbour vertices. There is no assumption that the neighbour map is
injective, and the other formal images are untouched.
-/

universe u v w

namespace CCO.DiagramHom

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X} {V : Type w}
variable {D : PartialDiagram S V}
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Repair one formal vertex using an old automorphism that fixes each
current neighbour image. Both directed edge incidences are checked;
this avoids any reliance on injectivity of the neighbour list. -/
noncomputable def moveOne
    (H : HomogeneousSource S G) (f : DiagramHom D)
    (x : V) (g : G)
    (hOut : ∀ (v : V) (hxv : x ≠ v)
       (a : S.Atom (D.vertexSort x) (D.vertexSort v)),
       D.edge x v hxv = some a → g • f.point v = f.point v)
    (hIn : ∀ (u : V) (hux : u ≠ x)
       (a : S.Atom (D.vertexSort u) (D.vertexSort x)),
       D.edge u x hux = some a → g • f.point u = f.point u) :
    DiagramHom D := by
  classical
  refine {
    point := Function.update f.point x (g • f.point x)
    preserves_edge := ?_
  }
  intro u v huv a ha
  by_cases hux : u = x
  · subst u
    have hvx : v ≠ x := Ne.symm huv
    have hfix := hOut v huv a ha
    have hcol : S.colour (g • f.point x) (f.point v) = some a := by
      calc
        S.colour (g • f.point x) (f.point v) =
            S.colour (g • f.point x) (g • f.point v) := by rw [hfix]
        _ = S.colour (f.point x) (f.point v) :=
          S.colourInvariant_of_homogeneous H g (f.point x) (f.point v)
        _ = some a := f.preserves_edge x v huv a ha
    simpa [Function.update, hvx] using hcol
  · by_cases hvx : v = x
    · subst v
      have hfix := hIn u huv a ha
      have hcol : S.colour (f.point u) (g • f.point x) = some a := by
        calc
          S.colour (f.point u) (g • f.point x) =
              S.colour (g • f.point u) (g • f.point x) := by rw [hfix]
          _ = S.colour (f.point u) (f.point x) :=
            S.colourInvariant_of_homogeneous H g (f.point u) (f.point x)
          _ = some a := f.preserves_edge u x huv a ha
      simpa [Function.update, hux] using hcol
    · simpa [Function.update, hux, hvx] using
        (f.preserves_edge u v huv a ha)

/-- The chosen vertex moves to the requested orbit point. -/
theorem moveOne_at
    (H : HomogeneousSource S G) (f : DiagramHom D)
    (x : V) (g : G)
    (hOut : ∀ (v : V) (hxv : x ≠ v)
       (a : S.Atom (D.vertexSort x) (D.vertexSort v)),
       D.edge x v hxv = some a → g • f.point v = f.point v)
    (hIn : ∀ (u : V) (hux : u ≠ x)
       (a : S.Atom (D.vertexSort u) (D.vertexSort x)),
       D.edge u x hux = some a → g • f.point u = f.point u) :
    (moveOne H f x g hOut hIn).point x = g • f.point x := by
  classical
  simp [moveOne]

/-- Every other formal vertex retains exactly its former real image. -/
theorem moveOne_away
    (H : HomogeneousSource S G) (f : DiagramHom D)
    (x : V) (g : G)
    (hOut : ∀ (v : V) (hxv : x ≠ v)
       (a : S.Atom (D.vertexSort x) (D.vertexSort v)),
       D.edge x v hxv = some a → g • f.point v = f.point v)
    (hIn : ∀ (u : V) (hux : u ≠ x)
       (a : S.Atom (D.vertexSort u) (D.vertexSort x)),
       D.edge u x hux = some a → g • f.point u = f.point u)
    (v : V) (hvx : v ≠ x) :
    (moveOne H f x g hOut hIn).point v = f.point v := by
  classical
  simp [moveOne, hvx]

end CCO.DiagramHom
