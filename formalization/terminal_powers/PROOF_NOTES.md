# B032 — same-sort positive pure powers, without CCO

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5` is unchanged.
One Foundations III lemma and its TPP equation are prepared here. These
are human proof contracts, not a compiled Lean theorem or an end-to-end
certificate of the article. The actual hypotheses are visible SAP and
FULL original sortwise NR2. No semantic CCO is used.

## N01: The actual orbital graph and two invariant equivalences

Fix an original named sort a and an actual same-sort diversity orbital t.
All invariance refers to G=Aut(U) of the WHOLE typed source acting on a.
Do not substitute the possibly larger automorphism group of an induced
reduct. Completeness and homogeneity identify the old pair colours with
these actual pair orbitals. Same-sort t is symmetric and irreflexive.
Choose a real t-edge. Named-sort transitivity transports its first point
to any x, so every x has a distinct t-neighbour.

Define C(x,y) by existence of a finite t-walk and Y(x,y) by one of even
length. The length-zero walk supplies reflexivity in BOTH graph relations.
Reversal gives symmetry and concatenation transitivity; applying any g
to a walk gives G invariance. Thus Y<=C are actual invariant equivalences
in the FULL original sortwise lattice. They need not be exact.

Within one component choose a root. Two vertices whose connecting walks
from the root have the same parity are Y-related by reverse/concatenate.
There are at most two Y-classes in a component. An odd closed walk makes
both parities available and collapses those classes. These are statements
about represented graph walks; zero-length reflexivity is not a STRONG
word menu. Every component has a genuine edge by the neighbour argument.

## N02: FULL NR2 excludes bipartite components

Named-sort transitivity carries any component onto any other, preserving
its graph and bipartiteness. If ONE component is bipartite, ALL are. In
a connected bipartite graph, paths alternate the two sides. Vertices on
the same side have an even connecting walk; opposite sides only odd walks.
Each side is nonempty because the component has an edge. Therefore Y has
EXACTLY two classes inside EVERY C-class, not merely at most two.

This yields a genuine invariant interval Y<C with [C:Y]=2. FULL original
NR2 forbids it. C can be a proper equivalence below Top, and Y may be
nonexact. Excluding only a global two-class quotient or only index-two
intervals in an exact sublattice would not justify this step. Thus every
t-component is connected nonbipartite. This is the selected existing
real_closure C25 proof, whose actual premises contain no CCO, SAP,
countability or additional theorem import.

The diversity connectivity palette F_t is a union of old same-sort
diversity orbitals. It is finite because the original palette is finite.
It is NONEMPTY: each actual t-edge is connected, so t belongs to F_t.
Logical equality lies in C but is omitted from F_t.

## N03: Constructive all-length walks and ONE finite uniform threshold

In a connected nonbipartite component fix x. If no odd closed walk existed
at x, every vertex would have a well-defined parity of a walk from x:
two different parities for the same endpoint, followed by reversal,
would produce an odd closed walk at x. Edges then switch parity, giving
a bipartition. This contradicts N02, so a finite odd closed walk at x
exists. Irreflexivity rules out length one, hence its odd length m>=3.
Equivalently one may walk to an odd cycle, traverse it and return; the
detour has length 2d+q, still odd.

For connected distinct x,y choose a positive t-walk of length l>=1.
The original walk and the odd detour followed by it give x->y walks of
lengths l and l+m, with opposite parity. Also choose a t-neighbour v of
x. A prependable x->v->x backtrack has length exactly two. For ANY
n>=l+m, choose the base length with the parity of n. Its length is at
most n and differs from n by a nonnegative even integer. Prepend the
required number of backtracks. This gives a walk of EXACTLY n edges
between the original literal endpoints. Repeated points are allowed.

For EACH c in finite nonempty F_t, choose ONE realized ordered pair
(x_c,y_c) of colour c. It is distinct. Let N_c=l_c+m_c and take
N_t=max_{c in F_t}N_c. This is a finite POSITIVE integer. The choices
are made before varying n or any later pair. For every n>=N_t each
representative pair has an n-edge t-walk. For ANY actual pair (x,y) of
that same c, ambient pair homogeneity supplies one original g carrying
(x_c,y_c) to (x,y). It preserves sort a and literal t, so it transports
the walk without changing its length. Thus the SAME N_t works for
EVERY connected diversity pair and EVERY n>=N_t.

This expands the selected real_closure C26 uniform-walk argument. That
provider also permits diagonal endpoints, but such endpoints are not used
in the STRONG conclusion. We import only C25/C26, not the additional
all-equivalence RAW representation C27 or the CCO distributivity C28.
The graph/threshold proof uses no SAP.

## N04: Separate formal occurrences and fixed-root SAP injection

For n>=N_t>=1 and one actual connected diversity pair x!=y, take the
represented n-edge walk from N03. Make a finite partial typed diagram
with formal vertices Fin(n+1), EVERY vertex sort equal to original a,
and ONLY successive edges specified, each with actual diversity t.
The converse is the same t. Walk occurrences are separate FORMAL vertices
even if the original homomorphism sent them to the same real point.

Let S={0,n}. These two formal vertices differ since n>=1, and their
images are exactly the DISTINCT x,y. The homomorphism is therefore
injective on S, including n=1. It can revisit a terminal internally;
injectivity elsewhere is not an input. Apply the accepted SAP provider
strong_selectors C04/C05 with forbidden set empty. Its actual ancestry
uses only the named-sorted homogeneous SAP source, not CCO, NR2,
countability or primitivity. It fixes BOTH literal endpoint images while
making ALL n+1 formal vertices distinct and preserving every t-edge.

This provider obtains infinite pointwise-stabilizer orbits from repeated
finite SAP amalgams over the complete current neighbour-image base.
That base is a SET of current real neighbours; it need not arise from
an injective formal neighbour list. Replacing one point preserves all
specified diversity edges and avoids every current image. Thus the walk
becomes an actual injective typed path, not just a differently named
homomorphism. No extra orbit-infinitude axiom is introduced here.

The same provider identifies positive STRONG word profiles with represented
word endpoints restricted to distinct actual points. Hence the old colour
c of the FIXED endpoints belongs to the STRONG product of n copies of t.
All intermediate and endpoint sort labels may repeat: all are a here.
There is no artificial identity atom or STRONG word of length zero.

## N05: Reverse inclusion, profile equality and hypothesis separation

For the upper inclusion use the direct POSITIVE left-associated recursion:
P_t(1)={t}, P_t(n+1)=P_t(n)*{t} for n>=1. At n=1 every pair of colour t
is connected. A legal diversity triangle witnessing c in the successor
product has x-z of a previously connected colour and z-y a t-edge.
Connectivity transitivity gives x C y. The output c is diversity by
definition of the strong product, so c belongs to F_t. This proves
P_t(n) subset F_t for EVERY positive n, independently of NR2 or SAP.
It does not require an all-length walk or an injective path.

Under SAP the usual strong associativity and positive-word path semantics
agree with this chosen recursion. N04 gives the reverse F_t subset P_t(n)
for EVERY n>=N_t, so the source equality holds for all such n. The graph
branch and uniformization need FULL NR2 but not SAP; the injective-path
step needs SAP; the upper inclusion needs neither. Neither selected
provider ancestry imports CCO or its exact-ball/Helly/distributivity
consequences. No threshold optimality or computable formula is claimed,
only the finite witness choices and the constructive positive bound.

## N06: Boundaries, diagnostics and the exact source export

If no same-sort diversity atom t exists, the source's universal assertion
over t is vacuous. For an existing t, F_t is nonempty and N_t>=1. A
singleton sort is therefore never accidentally used with a nonexistent
diversity atom. The notation never defines a zeroth STRONG power or treats
equality as a diversity atom. Closed walks and zero-length walks are
legitimate RAW graph proof tools and are removed before STRONG output.

"Finite complete typed source" means finite language/palettes. It does
NOT assert a finite actual carrier. With SAP, a named sort admitting a
diversity edge has the unbounded supplies needed for these injective paths.
Finite graphs can test eventual represented walk lengths, even-walk
classes and parity obstructions. They do not model arbitrary-length
injective paths in a fixed finite host or certify the source's SAP.
A triangle is a useful negative check: its long RAW walks persist while
an injective path of length exceeding its host size cannot exist there.

The single numbered export is `lem:typed-terminal-pure-power` and its one
auxiliary equation is `eq:typed-terminal-pure-power`. The result is
SAP+FULL original sortwise NR2, with no CCO assumption. It neither proves
nor imports a new exactness/distributivity theorem or any EPPA/HKN input.
Actual receiving Lean signatures still require implementation, peer review
and build/axiom validation under that team's current protocol.
