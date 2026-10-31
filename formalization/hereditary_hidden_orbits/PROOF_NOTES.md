# B054 — hereditary hidden orbits through fresh real frames

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Six definitions, 30 human proof claims, ONE source12 result, its named HO
equation and four implementation tasks. This is human proof preparation.
The examples are boundary diagnostics, not additional numbered exports.

## N01: Actual unary action and finite real generation

**D01–D02; C01–C04.** Put `H = widehat(M)` for the ACTUAL interpreted
hidden structure. Let `G = Aut(M)` be the automorphism group of the WHOLE
old typed source. Every `g` acts on a quotient vertex by
`g([x]_J) = [gx]_J`. Invariance of the actual kernels makes this
well-defined. The named projections, upward maps and quotient transitions
are equivariant; all hidden relations are actual interpreted relations.
Consequently the induced action is a subgroup of `Aut(H)`. We do not
claim that every hidden automorphism comes from the original group.

Every real vertex is its identity-term value. Every proper quotient vertex
is `F_J(x)` for an actual original real representative. Thus the union of
the named real sorts generates the entire ACTUAL hidden universe. This
is a statement about the whole interpretation; it does not require that
a particular finite closed hidden base contain any real generator.

The selected unary-term provider gives a uniform finite singleton bound
`m_typ` in actual completed diagrams. With unary functions, every term has
only one original argument, so

    cl(T) = union {cl({t}) : t in T}.

Hence finite sets have finite closure. Identity terms ensure `T <= cl(T)`.
No nullary generators are present, so `cl(empty)=empty`. Malformed total
unary PARTIAL inputs have no such automatic singleton bound; they are
outside the present actual interpreted structure.

An automorphism commutes with every named term. If it fixes `T`
pointwise, then it fixes EACH vertex of `cl(T)` pointwise. Conversely
fixing `cl(T)` fixes `T`. Therefore both the original induced group and
the full hidden group have the same stabilizer for `T` and `cl(T)`.
No setwise/pointwise stabilizer substitution is made.

## N02: Transfer from literal real bases to arbitrary hidden closed bases

**D03; C05–C12.** Two source-specific inputs have already been proved:

1. For every finite COMPLETE original real `D`, every hidden vertex
   outside `cl(D)` has infinite orbit under the ORIGINAL `G_D`.
2. For arbitrary finite actual induced unary-closed `A <= B`, actual
   fresh quotient representatives give one finite old real `D` with
   `A <= cl(D)` and `cl(D) intersect B = A`.

For the second input retain the actual real vertices of `A` and choose
one fresh real representative of each proper quotient vertex of `A`.
The representatives can lie on different original sorts. Their forced
term values lie in `A`; all unforced term values avoid `B`. Unary
closure is a union of singleton closures, proving the exact intersection.
The terminal infinite-cover assumption is the literal original source
hypothesis: every strict FULL invariant cover has infinite relative
index. Thus every strict relative interval has infinite index by a
finite saturated chain and an injection of fine classes. This input is
stronger than merely excluding index two and is retained where the
freshness provider uses it.

Now fix ANY finite actual closed hidden `A` and any actual `u` outside
`A`. In particular `A` may consist only of orphan quotient vertices.
Let

    B = cl(A union {u}).

This is finite and closed by N01. Apply input 2 to obtain `D`. Since
`u` belongs to `B` but not `A`, the exact intersection gives
`u notin cl(D)`. Apply input 1 to the SAME actual `u` and SAME literal
real frame `D`; its orbit `G_D.u` is infinite.

Every `g` fixing `D` fixes every term value on `D`, hence fixes
`A <= cl(D)` pointwise. Thus

    G_D <= G_A,       G_D.u <= G_A.u.

The latter orbit is therefore infinite. This is the stronger original
induced-group assertion HO. It does not use hidden homogeneity, hidden
SAP, a hidden completion theorem, or a new choice of transport charts.
This explicit argument discharges the forward direction of the selected
generic `unary_fresh_frames` theorem with all its hypotheses: actual
subgroup action, real generation, finite unary closures, real-base
infinite orbits and fresh frame separation.

## N03: Arbitrary finite parameters and the full hidden group

**D04–D05; C13–C21, C29.** Given a finite hidden parameter set `T`, put
`A=cl(T)`. By N01 it is an actual finite closed base and
`G_T=G_A`. Every vertex in `cl(T)` is fixed by `G_T`; every vertex
outside it has infinite `G_T` orbit by N02. Thus finite-orbit closure
and fixed-point closure for the ORIGINAL induced group both equal
`cl(T)`.

For the full hidden group write `K=Aut(H)`. We know

    G_T <= K_T,       G_T.u <= K_T.u.

If `u` is outside `cl(T)`, its original orbit is infinite, so its
FULL hidden orbit is infinite too. This is the required direction of
orbit inclusion. There is no need to identify the groups. If `u` lies
inside `cl(T)`, every full hidden automorphism fixing `T` fixes it:
all named unary terms are preserved. Hence

    acl_H(T) = dcl_H(T) = cl_H(T).

Here `acl` means finite orbit and `dcl` means singleton orbit for the
FULL hidden pointwise stabilizer. The source explicitly uses the
orbit-theoretic closure convention. No separate first-order closure
identification is needed for this package.

For `T=empty`, the term closure is literally empty. The real-base
orbit input already applies to the empty real base, so every hidden
vertex has infinite original-group orbit there. One may take the
fresh frame `D=empty` for `A=empty`; no constant or arbitrary quotient
representative is introduced. Finite closure also follows directly
from the singleton bound and the number of parameters.

The export records BOTH the stronger original-group HO assertion and
the stated full-hidden closure equalities. It concerns precisely the
named actual terminal hidden sorts. It is not an elimination-of-all-
imaginaries statement.

## N04: Signature boundaries and bounded controls

**D06; C22–C28, C30.** Hidden hereditary SAP will require a separate
proof of homogeneity of the actual hidden structure before the generic
homogeneous-unary SAP criterion can be applied. This package does not
assume that step and does not export SAP from old real homogeneity.

The original row/column clone example shows why the hidden MI-only
signature is substantive. If one INCORRECTLY also names the exact
NON-MI cell quotient `Q_L`, an orphan row `a` and column `b` determine
one unique cell `c` by the two upward maps. The unary closure of
`{a,b}` contains no cell: the stabilizer of a single row can move the
column arbitrarily and conversely, so there is no equivariant unary
term selecting their intersection. Yet `c` is fixed over `{a,b}`.
Two copies of the extension adding `c` cannot be strongly amalgamated
over that closed base, since the joint upward map is injective.

This failure is visible even over a real-generated base. Choose real
`x=(r,c0,k0)` and `y=(r0,c,k1)` with `r!=r0` and `c!=c0`. Their
singleton term closures contain their own two cell vertices but not
cross-cell `(r,c)`. A real `z=(r,c,k2)` generates that cross-cell,
which is already uniquely fixed by the row of `x` and column of `y`.
Thus the required original REAL-base infinite-orbit input also fails
in the enlarged signature. The generic frame theorem is not being
contradicted.

In the separate block/bit/clone example, let `J` be same block and
`K` same block and bit, with `[J:K]=2`. The coarse-only signature names
`Q_J` but no term with kernel `K`, so that finite cut is invisible to
its term-sensitive criterion. Once `Q_K` is added, a `Q_J` orphan has
exactly two `Q_K` points above it. Their pair is finite and invariant,
and a bit swap exchanges them, so neither is a unary term value of
the coarse point. This is the explicit finite-index obstruction. It
shows that global full infinite-cover input is sufficient for the
actual terminal language, not necessary for EVERY smaller signature.

The parent/row/column example allows non-Cartesian incidence globally:
row and column classes over different parents are incompatible.
Within a common parent they have an infinite actual clone fibre.
Named upward maps retain the parent compatibility. The proof of HO
uses actual fresh real frames and does not assume that all quotient
axes form one unrestricted Cartesian product.

The control script uses finite clone WINDOWS and their explicit
permutation actions. It checks literal fresh-frame intersections,
pointwise stabilizer containment and subgroup/full-group orbit
inclusion. It also checks the unique cell and two-bit fibre boundary.
Every orbit in a finite window is finite; the script is NEVER a
certificate of infinite orbits, full hidden homogeneity or unbounded
SAP/CCO. The unbounded conclusions are supplied by the human proof
and the precise selected provider contracts.
