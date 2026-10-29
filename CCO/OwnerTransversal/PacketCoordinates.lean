import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Logic.Embedding.Basic

/-! Generic full-packet inflation and point-aligned origins.
The group is arbitrary: no commutativity, exponent-two, finite-source,
closure, amalgamation or faithfulness of its OWNER action is assumed.
Fine matrix transport is stated as separate explicit data. -/

universe u v w z
namespace CCO.OwnerTransversal.PacketCoordinates

variable {K : Type u} [Group K] {I : Type v}
variable {X : Type w} [MulAction K X]

def inflate (origin : I → X) (p : I × K) : X := p.2 • origin p.1

/-- Freeness inside each packet and separation of different packets are
distinct hypotheses. Neither says the owner-label action is free. -/
theorem inflate_injective (origin : I → X)
    (free : ∀ i, Function.Injective (fun g : K => g • origin i))
    (separated : ∀ i j (g h : K), g • origin i = h • origin j → i = j) :
    Function.Injective (inflate (K := K) origin) := by
  rintro ⟨i, g⟩ ⟨j, h⟩ he
  change g • origin i = h • origin j at he
  have hij := separated i j g h he
  subst j
  have hgh := free i he
  subst h
  rfl

/-- Invariant packet labels give the required separation. These labels
index whole real packets, and need not be the named owner coordinates. -/
theorem inflate_injective_of_packet_labels {B : Type*}
    (packet : X → B) (invariant : ∀ (g : K) x, packet (g • x) = packet x)
    (origin : I → X)
    (free : ∀ i, Function.Injective (fun g : K => g • origin i))
    (distinct : Function.Injective (fun i => packet (origin i))) :
    Function.Injective (inflate (K := K) origin) := by
  apply inflate_injective (K := K) origin free
  intro i j g h he
  apply distinct
  simpa only [invariant] using congrArg packet he

def inflateEmbedding (origin : I → X)
    (free : ∀ i, Function.Injective (fun g : K => g • origin i))
    (separated : ∀ i j (g h : K), g • origin i = h • origin j → i = j) :
    (I × K) ↪ X := ⟨inflate origin, inflate_injective origin free separated⟩

theorem inflate_action (origin : I → X) (i : I) (g h : K) :
    inflate origin (i, g * h) = g • inflate origin (i, h) := mul_smul g h (origin i)

theorem inflate_packet_label {B : Type*} (packet : X → B)
    (invariant : ∀ (g : K) x, packet (g • x) = packet x)
    (origin : I → X) (p : I × K) : packet (inflate origin p) = packet (origin p.1) :=
  invariant p.2 (origin p.1)

/-- Owner transport permits any action on the owners, including a
nonfaithful action with nontrivial stabilizers. -/
theorem inflate_owner {O : Type*} [MulAction K O] (owner : X → O)
    (equivariant : ∀ (g : K) x, owner (g • x) = g • owner x)
    (origin : I → X) (labels : I → O) (origins : ∀ i, owner (origin i) = labels i)
    (p : I × K) : owner (inflate origin p) = p.2 • labels p.1 := by
  rw [inflate, equivariant, origins]

/-- All fine pairs are transported, including equal points and two
points of the same packet. No action on the colour palette is assumed free. -/
theorem full_matrix_transport {Y C : Type*} [MulAction K Y]
    (originX : I → X) (originY : I → Y)
    (colourX : X → X → C) (colourY : Y → Y → C) (mix : K → K → C → C)
    (matrixX : ∀ i j (g h : K), colourX (g • originX i) (h • originX j) =
      mix g h (colourX (originX i) (originX j)))
    (matrixY : ∀ i j (g h : K), colourY (g • originY i) (h • originY j) =
      mix g h (colourY (originY i) (originY j)))
    (origins : ∀ i j, colourY (originY i) (originY j) = colourX (originX i) (originX j))
    (p q : I × K) :
    colourY (inflate originY p) (inflate originY q) =
      colourX (inflate originX p) (inflate originX q) := by
  unfold inflate
  rw [matrixY, origins, ← matrixX]

/-- A chart of the whole source packets turns the inflation into an
actual embedding on their original point carrier. -/
def chartEmbedding {Y : Type*} [MulAction K Y] (chart : X ≃ I × K)
    (origin : I → Y)
    (free : ∀ i, Function.Injective (fun g : K => g • origin i))
    (separated : ∀ i j (g h : K), g • origin i = h • origin j → i = j) : X ↪ Y :=
  chart.toEmbedding.trans (inflateEmbedding origin free separated)

variable {P U : Type*} [MulAction K P]

/-- The origin is an actual OLD point, obtained from the inverse of its
point-coordinate phase. Naming only its owner does not define this choice. -/
def alignedOrigin (f : P → U × K) (p : P) : P := (f p).2⁻¹ • p

theorem alignedOrigin_image (f : P → U × K)
    (equivariant : ∀ (g : K) p, f (g • p) = ((f p).1, g * (f p).2)) (p : P) :
    f (alignedOrigin f p) = ((f p).1, 1) := by
  unfold alignedOrigin
  rw [equivariant]
  simp

theorem reconstruct_alignedOrigin (f : P → U × K) (p : P) :
    (f p).2 • alignedOrigin f p = p := smul_inv_smul (f p).2 p

theorem alignedOrigin_unique (f : P → U × K) (injective : Function.Injective f)
    (equivariant : ∀ (g : K) p, f (g • p) = ((f p).1, g * (f p).2))
    (p q : P) (zero : f q = ((f p).1, 1)) : q = alignedOrigin f p :=
  injective (zero.trans (alignedOrigin_image f equivariant p).symm)

theorem alignedOrigin_action (f : P → U × K)
    (equivariant : ∀ (g : K) p, f (g • p) = ((f p).1, g * (f p).2))
    (g : K) (p : P) : alignedOrigin f (g • p) = alignedOrigin f p := by
  unfold alignedOrigin
  rw [equivariant g p]
  simp only [mul_inv_rev, mul_smul, inv_smul_smul]

theorem alignedOrigin_of_zero (f : P → U × K) (p : P) (zero : (f p).2 = 1) :
    alignedOrigin f p = p := by
  unfold alignedOrigin
  rw [zero]
  simp

end CCO.OwnerTransversal.PacketCoordinates
