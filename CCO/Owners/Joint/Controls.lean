import CCO.Owners.Joint.Carrier

/-! Small compiled boundary controls for the joint-owner interfaces.
These deliberately incomplete diagrams are not claimed to satisfy the
standing CCO source or exact-quotient theorem hypotheses. -/

namespace CCO.Owners.Joint.Controls

/-- Repeating the identity coordinate gives the diagonal, not the full
formal product admitted by coarse, indiscriminate owner comparison. -/
def repeatedIdentity (x : Bool) : Bool × Bool := (x, x)

theorem repeated_fst_onto : Function.Surjective (fun x => (repeatedIdentity x).1) :=
  fun x => ⟨x, rfl⟩

theorem repeated_snd_onto : Function.Surjective (fun x => (repeatedIdentity x).2) :=
  fun x => ⟨x, rfl⟩

/-- Both coordinate marginals are onto, but a compatible coarse owner
test would admit this tuple which no original diagonal point realizes. -/
theorem repeated_identity_missing : (false, true) ∉ Set.range repeatedIdentity := by
  rintro ⟨x, hx⟩
  have hf : x = false := congrArg Prod.fst hx
  have ht : x = true := congrArg Prod.snd hx
  exact Bool.false_ne_true (hf.symm.trans ht)

theorem repeated_identity_not_onto : ¬Function.Surjective repeatedIdentity := by
  intro onto
  exact repeated_identity_missing (onto (false, true))

/-- The empty coordinate family has no coordinate on which an empty
owner image could force its product empty. -/
def emptyIndexDiagram : OwnerDiagram.{0,0,0,0} Empty Empty (fun _ => Empty) where
  beta i := nomatch i
  beta_surjective i := nomatch i
  jointly_injective b := nomatch b
  Comparison _ _ := PUnit
  left i := nomatch i
  right i := nomatch i
  commute b := nomatch b

def emptyIndexOwn (i : Empty) : Empty → Empty := nomatch i

def emptyIndexWitness : Carrier emptyIndexDiagram (fun _ => Empty) emptyIndexOwn :=
  ⟨(fun i => nomatch i), (fun i => nomatch i)⟩

/-- Dropping the nonempty-index gate while also dropping owner fullness
allows an inhabited formal witness above an empty owner. -/
theorem empty_index_carrier_nonempty :
    Nonempty (Carrier emptyIndexDiagram (fun _ => Empty) emptyIndexOwn) :=
  ⟨emptyIndexWitness⟩

/-- Full owner compatibility rules out precisely that spurious witness. -/
theorem empty_index_not_full : ¬FullOwners emptyIndexDiagram := by
  intro full
  obtain ⟨b, _⟩ := full (fun i => nomatch i) (fun i => nomatch i)
  exact nomatch b

end CCO.Owners.Joint.Controls
