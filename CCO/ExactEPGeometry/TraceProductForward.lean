import CCO.ExactEPGeometry.MarkedPairGeometry
import CCO.ExactEPGeometry.PeirceEndpoints

/-!
# B062 C11/C22: REAL forward trace product in a homogeneous marked age

The marked middle point belongs to the DISPLAYED child sort. One actual
finite chart contains all three points at once, including every legitimate
collision. Its old middle point is the SAME point on both input edges.
Original orbital invariance transfers exact-domain membership from the two
separately described marked input edges to that common OLD chart witness.
This is the nontrivial semantic bridge needed for the forward TP inclusion.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- Real old exactness is a UNION OF COMPLETE ORIGINAL ORBITALS.
An arbitrary old chart pair with the same FULL tagged optional colour
as a known exact-domain pair also belongs to that domain. The two sorts
are identified by equality of full tagged codes, never by coercing an
arbitrary mixed relation to a one-sort symmetric one. -/
theorem actual_exact_of_tagged_colour
    {i j : ι} (D : RawExact.NonemptyExact S i j)
    (p q : Sigma X) (x : X i) (y : X j)
    (hD : RawExact.evaluate S D.words x y)
    (hName : taggedColour S p q =
      taggedColour S (⟨i,x⟩ : Sigma X) ⟨j,y⟩) :
    ∃ (x' : X i) (y' : X j),
      p = ⟨i,x'⟩ ∧ q = ⟨j,y'⟩ ∧
      RawExact.evaluate S D.words x' y' := by
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  have hs : s = i := congrArg Sigma.fst hName
  have ht : t = j := congrArg
    (fun z : APCharacter.Age.Colour S => z.2.1) hName
  cases hs
  cases ht
  have hOld : S.colour a b = S.colour x y := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using hName
  exact ⟨a,b,rfl,rfl,exact_of_same_actual_colour S H D x y hD a b hOld⟩

variable {M : APCharacter.MaskData S}
variable (completion : APCharacter.Age.CompletionProperty S M)

/-- Forward C22 for one true AP-character marked limit. We do not merely
infer product colour-set membership: the output is the full binary relation
on the prescribed ACTUAL marked endpoints. The common old middle witness
is read in one finite age chart, never assumed to be the same point across
two unrelated old-pair witnesses. Equality and noninjective old walks remain. -/
theorem marked_trace_comp_forward
    {i j k : ι}
    (D : RawExact.NonemptyExact S i j)
    (E : RawExact.NonemptyExact S j k)
    (ε η θ : APCharacter.Bit)
    (a b c : APCharacter.Age.Limit S H completion)
    (hAB : markedTrace S H completion
      (RawExact.evaluate S D.words) ε η a b)
    (hBC : markedTrace S H completion
      (RawExact.evaluate S E.words) η θ b c) :
    markedTrace S H completion
      (TRel.comp (RawExact.evaluate S D.words)
        (RawExact.evaluate S E.words)) ε θ a c := by
  obtain ⟨ha, _, x, y, hD, hABCode⟩ := hAB
  obtain ⟨_, hc, y', z, hE, hBCCode⟩ := hBC
  let triple : Fin 3 → APCharacter.Age.Limit S H completion := ![a,b,c]
  obtain ⟨C, q, _, hPairCode⟩ :=
    APCharacter.Age.finite_tuple_names S H completion triple
  let p0 := C.point (q 0)
  let p1 := C.point (q 1)
  let p2 := C.point (q 2)
  have hChartAB :
      (APCharacter.Age.limitCoding S H completion).table.colour a b =
      APCharacter.Age.colourEquiv S (taggedColour S p0 p1) := by
    calc
      _ = (APCharacter.Age.limitCoding S H completion).table.colour
        (triple 0) (triple 1) := by simp [triple]
      _ = C.table.colour (q 0) (q 1) := hPairCode 0 1
      _ = APCharacter.Age.colourEquiv S (taggedColour S p0 p1) :=
        congrArg (fun T : APCharacter.Age.Table S (Fin C.size) =>
          T.colour (q 0) (q 1)) C.table_eq
  have hChartBC :
      (APCharacter.Age.limitCoding S H completion).table.colour b c =
      APCharacter.Age.colourEquiv S (taggedColour S p1 p2) := by
    calc
      _ = (APCharacter.Age.limitCoding S H completion).table.colour
        (triple 1) (triple 2) := by simp [triple]
      _ = C.table.colour (q 1) (q 2) := hPairCode 1 2
      _ = APCharacter.Age.colourEquiv S (taggedColour S p1 p2) :=
        congrArg (fun T : APCharacter.Age.Table S (Fin C.size) =>
          T.colour (q 1) (q 2)) C.table_eq
  have hChartAC :
      (APCharacter.Age.limitCoding S H completion).table.colour a c =
      APCharacter.Age.colourEquiv S (taggedColour S p0 p2) := by
    calc
      _ = (APCharacter.Age.limitCoding S H completion).table.colour
        (triple 0) (triple 2) := by simp [triple]
      _ = C.table.colour (q 0) (q 2) := hPairCode 0 2
      _ = APCharacter.Age.colourEquiv S (taggedColour S p0 p2) :=
        congrArg (fun T : APCharacter.Age.Table S (Fin C.size) =>
          T.colour (q 0) (q 2)) C.table_eq
  have hOldAB : taggedColour S p0 p1 =
      taggedColour S (⟨i,x⟩ : Sigma X) ⟨j,y⟩ :=
    (APCharacter.Age.colourEquiv S).injective
      (hChartAB.symm.trans hABCode)
  have hOldBC : taggedColour S p1 p2 =
      taggedColour S (⟨j,y'⟩ : Sigma X) ⟨k,z⟩ :=
    (APCharacter.Age.colourEquiv S).injective
      (hChartBC.symm.trans hBCCode)
  obtain ⟨x₀, y₀, hP0, hP1, hRealD⟩ :=
    actual_exact_of_tagged_colour S H D p0 p1 x y hD hOldAB
  obtain ⟨y₁, z₀, hP1', hP2, hRealE⟩ :=
    actual_exact_of_tagged_colour S H E p1 p2 y' z hE hOldBC
  have hMid : y₀ = y₁ := by
    have h : (⟨j,y₀⟩ : Sigma X) = ⟨j,y₁⟩ := hP1.symm.trans hP1'
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
  subst y₁
  have hOut :
      (APCharacter.Age.limitCoding S H completion).table.colour a c =
      APCharacter.Age.colourEquiv S
        (taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨k,z₀⟩) := by
    calc
      _ = APCharacter.Age.colourEquiv S (taggedColour S p0 p2) := hChartAC
      _ = APCharacter.Age.colourEquiv S
        (taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨k,z₀⟩) :=
        congrArg (APCharacter.Age.colourEquiv S) (by rw [hP0,hP2])
  exact ⟨ha, hc, x₀, z₀, ⟨y₀,hRealD,hRealE⟩, hOut⟩

end
end CCO.ExactEPGeometry
