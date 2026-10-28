import CCO.StrongExact.ThetaCompatibleLines
import CCO.StrongExact.ThetaGraphBridge

/-!
# Glue two actual word lines at their literal common roots

The two chosen original words already have line witnesses over the same
real endpoints. This file constructs one typed point function on the theta
vertices agreeing with both lines, and proves preservation of their actual
old diversity letters. Other branches receive arbitrary original points;
no edge assertion is made about those branches.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

private theorem sigma_eq_of_cast {s t : ι} (h : s = t)
    (x : X s) (y : X t) (hc : h ▸ x = y) :
    (⟨s,x⟩ : Sigma X) = ⟨t,y⟩ := by
  cases h
  cases hc
  rfl

private theorem cast_of_sigma_eq {s t : ι} (h : s = t)
    (x : X s) (y : X t)
    (hc : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩) : h ▸ x = y := by
  cases hc
  rfl

/-- Glue the two literal line witnesses at their common endpoints.
All point choices remain in the original named sorts. -/
noncomputable def thetaPairLinePoint
    (ws : List (PositiveWord S i j)) (b c : Fin ws.length)
    (x : X i) (y : X j)
    (lineB : LiteralLine S (ws.get b) x y)
    (lineC : LiteralLine S (ws.get c) x y) :
    ∀ z : thetaVertices S ws, X (thetaVertexSort S ws z) := by
  classical
  intro z
  cases z with
  | inl root =>
      cases root with
      | false => exact x
      | true => exact y
  | inr tag =>
      rcases tag with ⟨d,t⟩
      by_cases hdB : d = b
      · subst d
        exact lineB.point t.val
      · by_cases hdC : d = c
        · subst d
          exact lineC.point t.val
        · exact Classical.choice
            (S.nonemptySort (wordPositionSort S (ws.get d) t.val))

/-- At every position of the first word, the glued point has exactly
the same original typed value as its given line witness. -/
theorem thetaPairLinePoint_first_image
    (ws : List (PositiveWord S i j)) (b c : Fin ws.length)
    (x : X i) (y : X j)
    (lineB : LiteralLine S (ws.get b) x y)
    (lineC : LiteralLine S (ws.get c) x y)
    (z : wordPositions S (ws.get b)) :
    (⟨thetaVertexSort S ws (thetaBranchPosition S ws b z),
      thetaPairLinePoint S ws b c x y lineB lineC
        (thetaBranchPosition S ws b z)⟩ : Sigma X) =
      ⟨wordPositionSort S (ws.get b) z, lineB.point z⟩ := by
  classical
  by_cases hSource : z = wordSource S (ws.get b)
  · subst z
    rw [thetaBranchPosition_source S ws b]
    exact (sigma_eq_of_cast (wordSource_sort S (ws.get b))
      (lineB.point (wordSource S (ws.get b))) x lineB.source).symm
  · by_cases hTarget : z = wordTarget S (ws.get b)
    · subst z
      rw [thetaBranchPosition_target S ws b]
      exact (sigma_eq_of_cast (wordTarget_sort S (ws.get b))
        (lineB.point (wordTarget S (ws.get b))) y lineB.target).symm
    · let t : wordInterior S (ws.get b) := ⟨z,hSource,hTarget⟩
      have hz := thetaBranchPosition_interior S ws b t
      change thetaBranchPosition S ws b z = _ at hz
      rw [hz]
      simp [thetaPairLinePoint, thetaVertexSort, t]

/-- Distinct branch tags ensure that the second line is also kept
literally, including when some original named sorts coincide. -/
theorem thetaPairLinePoint_second_image
    (ws : List (PositiveWord S i j)) (b c : Fin ws.length)
    (hbc : b ≠ c) (x : X i) (y : X j)
    (lineB : LiteralLine S (ws.get b) x y)
    (lineC : LiteralLine S (ws.get c) x y)
    (z : wordPositions S (ws.get c)) :
    (⟨thetaVertexSort S ws (thetaBranchPosition S ws c z),
      thetaPairLinePoint S ws b c x y lineB lineC
        (thetaBranchPosition S ws c z)⟩ : Sigma X) =
      ⟨wordPositionSort S (ws.get c) z, lineC.point z⟩ := by
  classical
  by_cases hSource : z = wordSource S (ws.get c)
  · subst z
    rw [thetaBranchPosition_source S ws c]
    exact (sigma_eq_of_cast (wordSource_sort S (ws.get c))
      (lineC.point (wordSource S (ws.get c))) x lineC.source).symm
  · by_cases hTarget : z = wordTarget S (ws.get c)
    · subst z
      rw [thetaBranchPosition_target S ws c]
      exact (sigma_eq_of_cast (wordTarget_sort S (ws.get c))
        (lineC.point (wordTarget S (ws.get c))) y lineC.target).symm
    · let t : wordInterior S (ws.get c) := ⟨z,hSource,hTarget⟩
      have hz := thetaBranchPosition_interior S ws c t
      change thetaBranchPosition S ws c z = _ at hz
      rw [hz]
      simp [thetaPairLinePoint, hbc.symm, thetaVertexSort, t]

/-- Exact preservation on one ordered formal pair. Keeping this as a
single predicate lets endpoint equalities transport the atom types too. -/
def ThetaPairPreserves
    {ws : List (PositiveWord S i j)}
    (D : PartialDiagram S (thetaVertices S ws))
    (point : ∀ z : thetaVertices S ws, X (D.vertexSort z))
    (z t : thetaVertices S ws) : Prop :=
  ∀ (hzt : z ≠ t)
    (a : S.Atom (D.vertexSort z) (D.vertexSort t)),
    D.edge z t hzt = some a →
      S.colour (point z) (point t) = some a

/-- Ordered preservation reverses using the ACTUAL diagram converse
and the ACTUAL original colour converse. -/
theorem thetaPairPreserves_reverse
    {ws : List (PositiveWord S i j)}
    (D : PartialDiagram S (thetaVertices S ws))
    (point : ∀ z : thetaVertices S ws, X (D.vertexSort z))
    {z t : thetaVertices S ws}
    (h : ThetaPairPreserves S D point z t) :
    ThetaPairPreserves S D point t z := by
  intro htz a ha
  have hf := h htz.symm (S.conv a) ((D.edge_reverse t z htz a).mp ha)
  exact (S.colour_swap (point t) (point z) a).mpr hf

private theorem colour_uncast_both
    {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (a : S.Atom s' t') (x : X s) (y : X t)
    (hxy : S.colour (hs ▸ x) (ht ▸ y) = some a) :
    S.colour x y = some (hs.symm ▸ (ht.symm ▸ a)) := by
  cases hs
  cases ht
  simpa using hxy

/-- Any typed theta point function agreeing with one actual literal
line preserves every specified forward branch letter. -/
theorem thetaPairPreserves_of_literalLine
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (point : ∀ z : thetaVertices S ws, X (thetaVertexSort S ws z))
    (b : Fin ws.length) (x : X i) (y : X j)
    (line : LiteralLine S (ws.get b) x y)
    (hPoint : ∀ z : wordPositions S (ws.get b),
      (⟨thetaVertexSort S ws (thetaBranchPosition S ws b z),
        point (thetaBranchPosition S ws b z)⟩ : Sigma X) =
        ⟨wordPositionSort S (ws.get b) z, line.point z⟩)
    (e : wordEdgeIndex S (ws.get b)) :
    ThetaPairPreserves S ((thetaEdgesOfLong S ws hLong).toDiagram)
      point (thetaBranchEdgeSource S ws b e)
      (thetaBranchEdgeTarget S ws b e) := by
  intro hne a ha
  have hOld := thetaEdgesOfLong_preserves_forward S ws hLong b e
  have hAtom : a = thetaBranchEdgeAtom S ws b e :=
    Option.some.inj (ha.symm.trans hOld)
  subst a
  rw [thetaBranchEdgeAtom_cast S ws b e]
  apply colour_uncast_both S
    (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
    (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
  have hs := cast_of_sigma_eq
    (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
    (point (thetaBranchEdgeSource S ws b e))
    (line.point (wordEdgeSource S (ws.get b) e))
    (hPoint (wordEdgeSource S (ws.get b) e))
  have ht := cast_of_sigma_eq
    (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
    (point (thetaBranchEdgeTarget S ws b e))
    (line.point (wordEdgeTarget S (ws.get b) e))
    (hPoint (wordEdgeTarget S (ws.get b) e))
  rw [hs,ht]
  exact line.edges e

end CCO.StrongExact
