import CCO.ExactEPGeometry.MarkedPair

/-!
# B062: literal exact-domain traces in the ACTUAL AP-character marked age

The exact trace of an original invariant RAW relation is read from the
complete old pair orbital in the homogeneous marked limit. It is NOT
defined to include mask legality as an extra conjunct. Legality of the
actual pair is proved from a genuine finite chart, using the accepted
realized-age theorem. This is the critical reverse bridge for C10.

The nonempty old intersection hypothesis is retained. These are the
one-step source-level facts; tower iteration and C22 remain separate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : APCharacter.MaskData S}
variable (completion : APCharacter.Age.CompletionProperty S M)

/-- Read the exact original name of a marked pair from the finite chart in
the actual homogeneous limit. The returned mask is the ACTUAL source mask,
not an assumed `allows` clause in a freshly defined trace. -/
theorem limit_pair_colour_allowed
    {i j : ι} (a b : APCharacter.Age.Limit S H completion)
    (ε η : APCharacter.Bit) (c : Option (S.Atom i j))
    (ha : (APCharacter.Age.limitCoding S H completion).table.owner a =
      APCharacter.Age.ownerEquiv S (i, ε))
    (hb : (APCharacter.Age.limitCoding S H completion).table.owner b =
      APCharacter.Age.ownerEquiv S (j, η))
    (hc : (APCharacter.Age.limitCoding S H completion).table.colour a b =
      APCharacter.Age.colourEquiv S
        (⟨i, j, c⟩ : APCharacter.Age.Colour S)) :
    M.allowed c ε η := by
  let pair : Fin 2 → APCharacter.Age.Limit S H completion :=
    fun k => if k = 0 then a else b
  have pair0 : pair 0 = a := by simp [pair]
  have pair1 : pair 1 = b := by simp [pair]
  obtain ⟨C, q, ho, hcol⟩ :=
    APCharacter.Age.finite_tuple_names S H completion pair
  have table0 : C.table.owner (q 0) =
      APCharacter.Age.ownerEquiv S ((C.point (q 0)).1, C.bits (q 0)) :=
    congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.owner (q 0))
      C.table_eq
  have table1 : C.table.owner (q 1) =
      APCharacter.Age.ownerEquiv S ((C.point (q 1)).1, C.bits (q 1)) :=
    congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.owner (q 1))
      C.table_eq
  have tableCol : C.table.colour (q 0) (q 1) =
      APCharacter.Age.colourEquiv S (taggedColour S (C.point (q 0)) (C.point (q 1))) :=
    congrArg (fun T : APCharacter.Age.Table S (Fin C.size) => T.colour (q 0) (q 1))
      C.table_eq
  have howner0 : APCharacter.Age.ownerEquiv S
      ((C.point (q 0)).1, C.bits (q 0)) =
      APCharacter.Age.ownerEquiv S (i, ε) := by
    calc
      _ = C.table.owner (q 0) := table0.symm
      _ = (APCharacter.Age.limitCoding S H completion).table.owner (pair 0) := (ho 0).symm
      _ = (APCharacter.Age.limitCoding S H completion).table.owner a := by rw [pair0]
      _ = APCharacter.Age.ownerEquiv S (i, ε) := ha
  have howner1 : APCharacter.Age.ownerEquiv S
      ((C.point (q 1)).1, C.bits (q 1)) =
      APCharacter.Age.ownerEquiv S (j, η) := by
    calc
      _ = C.table.owner (q 1) := table1.symm
      _ = (APCharacter.Age.limitCoding S H completion).table.owner (pair 1) := (ho 1).symm
      _ = (APCharacter.Age.limitCoding S H completion).table.owner b := by rw [pair1]
      _ = APCharacter.Age.ownerEquiv S (j, η) := hb
  have hname0 : ((C.point (q 0)).1, C.bits (q 0)) = (i, ε) :=
    (APCharacter.Age.ownerEquiv S).injective howner0
  have hname1 : ((C.point (q 1)).1, C.bits (q 1)) = (j, η) :=
    (APCharacter.Age.ownerEquiv S).injective howner1
  have hi : (C.point (q 0)).1 = i := congrArg Prod.fst hname0
  have hj : (C.point (q 1)).1 = j := congrArg Prod.fst hname1
  have hε : C.bits (q 0) = ε := congrArg Prod.snd hname0
  have hη : C.bits (q 1) = η := congrArg Prod.snd hname1
  have hcolour : taggedColour S (C.point (q 0)) (C.point (q 1)) =
      (⟨i, j, c⟩ : APCharacter.Age.Colour S) := by
    apply (APCharacter.Age.colourEquiv S).injective
    calc
      _ = C.table.colour (q 0) (q 1) := tableCol.symm
      _ = (APCharacter.Age.limitCoding S H completion).table.colour (pair 0) (pair 1) :=
        (hcol 0 1).symm
      _ = (APCharacter.Age.limitCoding S H completion).table.colour a b := by
        rw [pair0, pair1]
      _ = APCharacter.Age.colourEquiv S (⟨i, j, c⟩ : APCharacter.Age.Colour S) := hc
  have hlegal := C.legal.2 (q 0) (q 1)
  cases hi
  cases hj
  have hraw : S.colour (C.point (q 0)).2 (C.point (q 1)).2 = c := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and] using hcolour
  simpa only [hraw, hε, hη] using hlegal

/-- Semantic REAL trace: the pair's complete current unary names match the
prescribed child types and its original optional orbital is represented by
an actual old pair belonging to D. For invariant D this is precisely its
old orbital-union interpretation in the current prefix. -/
def markedTrace {i j : ι} (D : TRel X i j)
    (ε η : APCharacter.Bit)
    (a b : APCharacter.Age.Limit S H completion) : Prop :=
  (APCharacter.Age.limitCoding S H completion).table.owner a =
    APCharacter.Age.ownerEquiv S (i, ε) ∧
  (APCharacter.Age.limitCoding S H completion).table.owner b =
    APCharacter.Age.ownerEquiv S (j, η) ∧
  ∃ x : X i, ∃ y : X j, D x y ∧
    (APCharacter.Age.limitCoding S H completion).table.colour a b =
      APCharacter.Age.colourEquiv S
        (taggedColour S (⟨i, x⟩ : Sigma X) ⟨j, y⟩)

/-- The source theorem C10 for ONE ACTUAL AP-only full-character step:
if an original finite exact meet has an actual old witness and every
individual original exact domain has a nonempty trace between those
realized marked types, then their combined REAL marked trace is nonempty.
The proof uses the *unmodified* coded relation, deriving source mask
legality backwards from a finite actual marked-age chart. -/
theorem marked_exact_meet_prime
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : APCharacter.SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (L : List (RawExact.NonemptyExact S i j))
    (ε η : APCharacter.Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (hMeet : TRel.Nonempty (rawExactFamily S L))
    (hEach : ∀ d ∈ L, ∃ a b,
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S d.words) ε η a b) :
    ∃ a b, markedTrace S H (P.completion_property cco)
      (rawExactFamily S L) ε η a b := by
  have hEachMask : ∀ d ∈ L, ∃ x y,
      RawExact.evaluate S d.words x y ∧
      P.allows (S.colour x y) ε η := by
    intro d hd
    obtain ⟨a, b, ha, hb, x, y, hxy, hc⟩ := hEach d hd
    refine ⟨x, y, hxy, ?_⟩
    exact limit_pair_colour_allowed S H (P.completion_property cco)
      a b ε η (S.colour x y) ha hb hc
  obtain ⟨a, b, x, y, hAll, ha, hb, hc⟩ :=
    marked_exact_family_witness (S := S) (H := H)
      P cco L ε η hv hw hMeet hEachMask
  exact ⟨a, b, ha, hb, x, y, hAll, hc⟩

end
end CCO.ExactEPGeometry
