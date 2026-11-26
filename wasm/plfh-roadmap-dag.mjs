// Interactive 50-card Serokell Dependent Haskell Roadmap Dependency DAG
// plus the 3 TharkunAB companion packages.
// Source of truth: TharkunAB/ghc docs/dependent-haskell/ROADMAP.md (Wave 16 / dependent-haskell-alpha).

const SEROKELL_BASE = "https://ghc.serokell.io/dh#";
const FORK_ROADMAP_BASE =
  "https://github.com/TharkunAB/ghc/blob/dependent-haskell/docs/dependent-haskell/roadmap/";

export const ROADMAP_NODES = [
  // Row 0 — Goal
  {
    id: "R01",
    label: "Dependent Haskell",
    short: "Dependent Haskell",
    row: 0,
    x: 580,
    w: 186,
    status: "fork",
    act: "act-1",
    card: "card-nat",
    slug: "dependent-haskell",
    proposals: ["#378", "#102"],
    deps: ["R02", "R06", "R20"],
    summary:
      "Umbrella -XDependentTypes bundle, native dependent Core (DepFunTy, TermVarTy, ExistsTy), general GHC plugin support, 642 Showcase observations, 25/25 PLFH chapters, and standalone dependent-base.",
  },
  // Row 1 — Three Pillars
  {
    id: "R02",
    label: "Dependent retained quantifiers",
    short: "Retained quantifiers",
    row: 1,
    x: 210,
    w: 178,
    status: "fork",
    act: "act-1",
    card: "card-nat",
    slug: "dependent-retained-quantifiers",
    proposals: ["#378 §4.2–4.5"],
    deps: ["R03", "R04"],
    summary:
      "Visible and invisible foreach (including %1 linear and %m multiplicity-polymorphic binders, runtime Type case, and off-diagonal GADT refutation) plus retained Sigma (some) with OverloadedRecordDot.",
  },
  {
    id: "R06",
    label: "Universal promotion",
    short: "Universal promotion",
    row: 1,
    x: 580,
    w: 178,
    status: "fork",
    boundary: true,
    act: "act-2",
    card: "card-lists",
    slug: "universal-promotion",
    proposals: ["#378 §4.10", "#509"],
    deps: ["R07", "R10", "R12", "R13", "R14"],
    summary:
      "Ordinary Haskell functions, literals, unboxed values, classes, and data families promote directly to types. Boundary: effectful IO and uncertified non-structural functions remain outside type-level conversion (#378 §4.10).",
  },
  {
    id: "R20",
    label: "Clean up the language",
    short: "Clean up language",
    row: 1,
    x: 950,
    w: 178,
    status: "fork",
    act: "act-3",
    card: "card-exists",
    slug: "clean-up-the-language",
    proposals: ["#378", "#473", "#242", "#523"],
    deps: ["R21", "R22", "R23", "R24", "R27", "R28", "R35", "R39", "R49"],
    summary:
      "Mixed declaration staging, Proposal #473 erased existentials, #242 unsaturated families, constrained families, #523 local type synonyms, namespace management, and pun warnings.",
  },
  // Row 2 — Core Capabilities
  {
    id: "R03",
    label: "Dependent products",
    short: "Dep. products",
    row: 2,
    x: 78,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-nat",
    slug: "dependent-products",
    forkDoc: "R03-dependent-products.md",
    proposals: ["#378 §4.4–4.5", "#111"],
    deps: ["R05", "R39"],
    summary:
      "Retained foreach (x :: a) -> b x (and Unicode ∏), @arg/@pat overrides, runtime Type matching, linear %1 and %m foreach, off-diagonal GADT refutation, and point-free/dependent hole fits.",
  },
  {
    id: "R04",
    label: "Dependent sums",
    short: "Dep. sums",
    row: 2,
    x: 189,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-sigma",
    slug: "dependent-sums",
    forkDoc: "R04-dependent-sums.md",
    proposals: ["#378 §4.2", "#282"],
    deps: ["R05", "R22"],
    summary:
      "GHC.Sigma (Pair, first, second), multi-binder some syntax, dependent OverloadedRecordDot (r.rowItems, p.second), and parameterized single-constructor dependent record updates.",
  },
  {
    id: "R07",
    label: "Promote literals",
    short: "Promote literals",
    row: 2,
    x: 300,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-nat",
    slug: "promote-literals",
    proposals: ["#364"],
    deps: ["R08", "R09", "R24"],
    summary:
      "Written characters, strings, Natural, and nonnegative numerals at certified ground Num domains (such as Peano Nat) promote automatically without extra boilerplate.",
  },
  {
    id: "R10",
    label: "Promote unboxed types",
    short: "Unboxed types",
    row: 2,
    x: 411,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-large-elim",
    slug: "promote-unboxed-types",
    forkDoc: "R10-unboxed-promotion.md",
    proposals: ["#378"],
    deps: ["R11"],
    summary:
      "Closed and open type families match Int#, Word#, Char#, and unboxed tuples (# a, b #) across module interfaces. Mutable heap primitives remain runtime-only.",
  },
  {
    id: "R12",
    label: "Promote classes",
    short: "Promote classes",
    row: 2,
    x: 522,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-lists",
    slug: "promote-classes",
    forkDoc: "R12-promote-classes.md",
    proposals: ["#509"],
    deps: ["R13", "R24"],
    summary:
      "Multi-parameter type classes, superclass selector projection, newtype instances, and ground binary methods publish checked source equations into .hi interfaces.",
  },
  {
    id: "R13",
    label: "Function promotion",
    short: "Fn promotion",
    row: 2,
    x: 633,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-lists",
    slug: "function-promotion",
    forkDoc: "R16-open-term-evaluator.md",
    proposals: ["#509", "#378 §4.7"],
    deps: ["R15", "R16", "R17", "R18", "R19", "R21", "R23"],
    summary:
      "Structural functions, De Bruijn substitution, empty-case Void branches (unlocking all 12 Connectives Iso laws), and mutually recursive Term -> Type large eliminations promote automatically under -XDependentTypes.",
  },
  {
    id: "R14",
    label: "Data family promotion",
    short: "Data families",
    row: 2,
    x: 744,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-large-elim",
    slug: "data-family-promotion",
    forkDoc: "R14-data-family-promotion.md",
    proposals: ["#378"],
    deps: [],
    summary:
      "Data-family instance constructors, newtype instances, and existential or constrained data-family constructors promote across compiled interfaces.",
  },
  {
    id: "R22",
    label: "Existential quantification",
    short: "Existentials",
    row: 2,
    x: 855,
    w: 98,
    status: "fork",
    act: "act-3",
    card: "card-exists",
    slug: "existential-quantification",
    forkDoc: "R22-existential-quantification.md",
    proposals: ["#473"],
    deps: [],
    summary:
      "Proposal #473 erased existentials: Exists, pattern Pack, constraint pairing (/\\), Witness tokens, withExists, mapExists, and uncurryExists checked at -O0 and -O2.",
  },
  {
    id: "R24",
    label: "Constrained type families",
    short: "Constrained TFs",
    row: 2,
    x: 966,
    w: 98,
    status: "fork",
    act: "act-3",
    card: "card-exists",
    slug: "constrained-type-families",
    forkDoc: "R24-constrained-type-families.md",
    proposals: ["#378"],
    deps: [],
    summary:
      "Associated and standalone open constrained type families verify class premises and superclass equalities before reducing, failing closed in source-hidden clients.",
  },
  {
    id: "R27",
    label: "Deprecate CUSKs",
    short: "Deprecate CUSKs",
    row: 2,
    x: 1077,
    w: 98,
    status: "fork",
    boundary: true,
    act: "act-3",
    card: "card-local-type",
    slug: "deprecate-cusks",
    forkDoc: "R27-deprecate-cusks.md",
    proposals: ["#378"],
    deps: ["R26", "R29"],
    summary:
      "-XDependentTypes implies StandaloneKindSignatures (NoCUSKs) and -Wcusks emits checked SAKS edits. Boundary: Haskell98/Haskell2010 keep CUSKs by default for backwards compatibility.",
  },
  // Row 3 — Evaluators, Core & Cleanup
  {
    id: "R05",
    label: "Dependent Core language",
    short: "Dependent Core",
    row: 3,
    x: 78,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-linear",
    slug: "dependent-core-language",
    forkDoc: "R05-dependent-core.md",
    proposals: ["ICFP 2017", "ICFP 2019"],
    deps: [],
    summary:
      "Native DepFunTy, TermVarTy, and ExistsTy in System FC with INLINE/INLINABLE unfoldings, linear DepFunTy Core Lint, general installCoreToDos plugin support, and -O2 retained optimization.",
  },
  {
    id: "R39",
    label: "Visible forall",
    short: "Visible forall",
    row: 3,
    x: 189,
    w: 98,
    status: "upstream",
    act: "act-2",
    card: "card-sections",
    slug: "visible-forall",
    proposals: ["#281"],
    deps: ["R34", "R40", "R41", "R43"],
    summary:
      "Upstream RequiredTypeArguments (forall a -> ...), enabling visible type arguments such as cong Succ and cong (plus m) with zero @ sigils.",
  },
  {
    id: "R11",
    label: "Homogeneous equality",
    short: "Homog. equality",
    row: 3,
    x: 300,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-refute",
    slug: "homogeneous-equality",
    forkDoc: "R11-homogeneous-equality.md",
    proposals: ["ICFP 2017"],
    deps: [],
    summary:
      "Scoped homogeneous kind proofs for GADT pattern and constructor coercions across nested matches. Observational function equality stays modular via dependent-obs-eq.",
  },
  {
    id: "R15",
    label: "Closed term evaluator",
    short: "Closed eval",
    row: 3,
    x: 411,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-large-elim",
    slug: "closed-term-evaluator",
    forkDoc: "R15-closed-term-evaluator.md",
    proposals: ["#509"],
    deps: [],
    summary:
      "Evaluates both imported and same-module closed term calls (lists, pairs, Maybe, Either, matrices, GADT constructors) and reads structured results back at compile time.",
  },
  {
    id: "R16",
    label: "Open term evaluator",
    short: "Open eval",
    row: 3,
    x: 522,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-lists",
    slug: "open-term-evaluator",
    forkDoc: "R16-open-term-evaluator.md",
    proposals: ["#509"],
    deps: [],
    summary:
      "Symbolically reduces ordinary recursive functions over unknown foreach variables across .hi interfaces while tracking rewrite-rule soundness guards per demanded function.",
  },
  {
    id: "R17",
    label: "Type-level lambdas",
    short: "Type lambdas",
    row: 3,
    x: 633,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-sections",
    slug: "type-level-lambdas",
    forkDoc: "R17-type-level-lambdas.md",
    proposals: ["#242", "#378"],
    deps: ["R05", "R16"],
    summary:
      "Inline type lambdas (@(\\y -> ...)), T2T operator sections ((x :), (: ys)), and %U predicate variable captures (LeibnizU) check across compiled interfaces.",
  },
  {
    id: "R18",
    label: "Type-level let-bindings",
    short: "Type lets",
    row: 3,
    x: 744,
    w: 98,
    status: "fork",
    act: "act-3",
    card: "card-local-type",
    slug: "type-level-let-bindings",
    forkDoc: "R18-type-level-lets.md",
    proposals: ["#523"],
    deps: ["R05", "R16"],
    summary:
      "Complete on the fork: ordered type-level let bindings in six source contexts plus #523 local type synonyms inside term let/where blocks capturing retained foreach variables.",
  },
  {
    id: "R19",
    label: "Type-level case-expressions",
    short: "Type case",
    row: 3,
    x: 855,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-typecase",
    slug: "type-level-case-expressions",
    forkDoc: "R19-type-level-cases.md",
    proposals: ["#378 §4.9"],
    deps: ["R05", "R16"],
    summary:
      "Type-level case expressions, closed-family case RHSs, Template Haskell quotation/splicing of retained signatures, and runtime foreach (a :: Type) case matching.",
  },
  {
    id: "R21",
    label: "Dependency analysis",
    short: "Dep. analysis",
    row: 3,
    x: 966,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-large-elim",
    slug: "dependency-analysis",
    forkDoc: "R21-dependency-analysis.md",
    proposals: ["#378"],
    deps: [],
    summary:
      "Automatically stages mixed same-module term/type declarations, mutually recursive value groups, local type synonyms, and mutual datatype/Type eliminations (such as Adequacy logVLam).",
  },
  {
    id: "R23",
    label: "Unsaturated type families",
    short: "Unsaturated TFs",
    row: 3,
    x: 1077,
    w: 98,
    status: "fork",
    act: "act-2",
    card: "card-sections",
    slug: "unsaturated-type-families",
    forkDoc: "R23-unsaturated-type-families.md",
    proposals: ["#242", "ICFP 2019"],
    deps: ["R25"],
    summary:
      "Matchability polymorphism (%M / %U / %m), partial application of promoted functions in cong (plus m) and All/Any/Leibniz, and rank-2 binder matchability deferral (138/138 focused tests).",
  },
  // Row 4 — Syntax, Namespaces & Upstream Mid-Tier
  {
    id: "R34",
    label: "Syntactic unification",
    short: "Syntax unif.",
    row: 4,
    x: 78,
    w: 98,
    status: "fork",
    boundary: true,
    act: "act-1",
    card: "card-typecase",
    slug: "syntactic-unification",
    proposals: ["#378 §4.3", "#281"],
    deps: ["R44", "R45", "R46", "R47"],
    summary:
      "Unified term/type surface for foreach, ∏, exists, some, Type patterns, T2T sections, and data herald. Boundary: internal HsExpr/HsType ASTs remain separate (#25121) and bare a -> b in patterns stays reserved for ViewPatterns.",
  },
  {
    id: "R40",
    label: "Visibility coercions",
    short: "Vis. coercions",
    row: 4,
    x: 189,
    w: 98,
    status: "upstream",
    act: "act-2",
    card: "card-sections",
    slug: "visibility-coercions",
    proposals: ["#281"],
    deps: [],
    summary: "Upstream GHC support for visibility coercions between visible and invisible forall.",
  },
  {
    id: "R41",
    label: "Nested quantification in GADTs",
    short: "Nested GADT ∀",
    row: 4,
    x: 300,
    w: 98,
    status: "fork",
    act: "act-1",
    card: "card-refute",
    slug: "nested-quantification-in-gadts",
    forkDoc: "R41-nested-quantification-in-gadts.md",
    proposals: ["#402"],
    deps: [],
    summary:
      "Complete on the fork: prefix GADT constructors accept interleaved fields, constraint groups, visible/invisible forall telescopes, and ordered type data in source order.",
  },
  {
    id: "R43",
    label: "Term variable capture",
    short: "Term capture",
    row: 4,
    x: 411,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "term-variable-capture",
    proposals: ["#281"],
    deps: [],
    summary: "Upstream term-variable scoping rules inside visible type arguments.",
  },
  {
    id: "R35",
    label: "Namespace management",
    short: "Namespaces",
    row: 4,
    x: 522,
    w: 98,
    status: "fork",
    act: "act-3",
    card: "card-exists",
    slug: "namespace-management",
    forkDoc: "R35-namespace-management.md",
    proposals: ["#581", "#765"],
    deps: ["R36", "R37", "R38", "R42"],
    summary:
      "Complete on the fork (all 25 namespace registrations): clean disambiguation of type (+) and data Pack across imports, re-exports, and compiled interfaces.",
  },
  {
    id: "R28",
    label: "Invisible type arguments",
    short: "Invis. type args",
    row: 4,
    x: 633,
    w: 98,
    status: "upstream",
    act: "act-3",
    card: "card-exists",
    slug: "invisible-type-arguments",
    proposals: ["#425"],
    deps: ["R29", "R30", "R31", "R32", "R33"],
    summary: "Upstream GHC invisible type binders and visible type/kind applications.",
  },
  {
    id: "R25",
    label: "Modifiers syntax",
    short: "Modifiers (%)",
    row: 4,
    x: 744,
    w: 98,
    status: "upstream",
    act: "act-2",
    card: "card-sections",
    slug: "modifiers-syntax",
    proposals: ["#370"],
    deps: [],
    summary: "Upstream generalized % modifier syntax powering %M / %U matchability and %1 linearity.",
  },
  {
    id: "R26",
    label: "Standalone kind signatures",
    short: "SAKS",
    row: 4,
    x: 855,
    w: 98,
    status: "upstream",
    act: "act-3",
    card: "card-local-type",
    slug: "standalone-kind-signatures",
    proposals: ["#54"],
    deps: [],
    summary: "Upstream StandaloneKindSignatures (implied by -XDependentTypes).",
  },
  {
    id: "R08",
    label: "Promote Char",
    short: "Promote Char",
    row: 4,
    x: 966,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "promote-char",
    proposals: ["#378"],
    deps: [],
    summary: "Upstream DataKinds promotion for character literals.",
  },
  {
    id: "R09",
    label: "Promote Natural",
    short: "Promote Natural",
    row: 4,
    x: 1077,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "promote-natural",
    proposals: ["#364"],
    deps: [],
    summary: "Upstream GHC.TypeNats Natural unification with term-level Natural.",
  },
  // Row 5 — Namespace / Syntax / Binder Leaves
  {
    id: "R44",
    label: "No star kind syntax",
    short: "No * kind",
    row: 5,
    x: 78,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-typecase",
    slug: "no-star-kind-syntax",
    proposals: ["#143"],
    deps: ["R50"],
    summary: "Upstream NoStarIsType migration from * to Data.Kind.Type.",
  },
  {
    id: "R45",
    label: "The forall keyword",
    short: "forall keyword",
    row: 5,
    x: 189,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "the-forall-keyword",
    proposals: ["#378"],
    deps: [],
    summary: "Upstream reservation of forall across terms and types.",
  },
  {
    id: "R46",
    label: "The tilde operator",
    short: "Tilde (~)",
    row: 5,
    x: 300,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "the-tilde-operator",
    proposals: ["#229"],
    deps: ["R48"],
    summary: "Upstream whitespace-aware ~ parsing for lazy patterns vs. equality.",
  },
  {
    id: "R47",
    label: "The dot type operator",
    short: "Dot (.)",
    row: 5,
    x: 411,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-sigma",
    slug: "the-dot-type-operator",
    proposals: ["#229", "#282"],
    deps: ["R48"],
    summary: "Upstream whitespace-aware . parsing for quantifiers and record dot syntax.",
  },
  {
    id: "R36",
    label: "Pun warnings",
    short: "Pun warnings",
    row: 5,
    x: 522,
    w: 98,
    status: "fork",
    act: "act-3",
    card: "card-exists",
    slug: "pun-warnings",
    forkDoc: "R36-pun-warnings.md",
    proposals: ["#765"],
    deps: [],
    summary:
      "Complete on the fork (all 16 registered cases): opt-in diagnostics when a type and data constructor share an unqualified punned name.",
  },
  {
    id: "R37",
    label: "Namespace-specified imports",
    short: "NS imports",
    row: 5,
    x: 633,
    w: 98,
    status: "upstream",
    act: "act-3",
    card: "card-exists",
    slug: "namespace-specified-imports",
    proposals: ["#581"],
    deps: [],
    summary: "Upstream ExplicitNamespaces import/export qualifiers (type (+), data Pack).",
  },
  {
    id: "R38",
    label: "No list or tuple puns",
    short: "No list puns",
    row: 5,
    x: 744,
    w: 98,
    status: "upstream",
    act: "act-2",
    card: "card-lists",
    slug: "no-list-or-tuple-puns",
    proposals: ["#475"],
    deps: [],
    summary:
      "Upstream NoListTuplePuns (implied by -XDependentTypes) so [], :, and [0, 1, 0] work in types with zero leading ticks.",
  },
  {
    id: "R42",
    label: "Embed types",
    short: "Embed types",
    row: 5,
    x: 855,
    w: 98,
    status: "upstream",
    act: "act-3",
    card: "card-exists",
    slug: "embed-types",
    proposals: ["#281"],
    deps: [],
    summary: "Upstream (type T) explicit type-namespace herald in term expressions and patterns.",
  },
  {
    id: "R29",
    label: "Invisible binders in types",
    short: "Invis. in types",
    row: 5,
    x: 966,
    w: 98,
    status: "upstream",
    act: "act-3",
    card: "card-local-type",
    slug: "invisible-binders-in-types",
    proposals: ["#425"],
    deps: ["R26"],
    summary: "Upstream TypeAbstractions (@k) in type and data declarations.",
  },
  {
    id: "R30",
    label: "Invisible binders in functions",
    short: "Invis. in fns",
    row: 5,
    x: 1077,
    w: 98,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "invisible-binders-in-functions",
    proposals: ["#448"],
    deps: [],
    summary: "Upstream @a type abstractions in function definitions and lambdas.",
  },
  // Row 6 — Upstream Bedrock Leaves
  {
    id: "R48",
    label: "Whitespace-sensitive operators",
    short: "Whitespace ops",
    row: 6,
    x: 220,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-sigma",
    slug: "whitespace-sensitive-operators",
    proposals: ["#229"],
    deps: [],
    summary: "Upstream Proposal #229 lexical rules enabling OverloadedRecordDot and @/~/! disambiguation.",
  },
  {
    id: "R49",
    label: "Unify type and kind variables",
    short: "Unify ty/ki vars",
    row: 6,
    x: 364,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "unify-type-and-kind-variables",
    proposals: ["PolyKinds"],
    deps: ["R50"],
    summary: "Upstream PolyKinds unification of type and kind variables.",
  },
  {
    id: "R50",
    label: "Unify types and kinds",
    short: "TypeInType",
    row: 6,
    x: 508,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-typecase",
    slug: "unify-types-and-kinds",
    proposals: ["TypeInType"],
    deps: [],
    summary: "Upstream Type :: Type (Richard Eisenberg's TypeInType foundation in GHC 8.0).",
  },
  {
    id: "R31",
    label: "Invisible binders in constructors",
    short: "Invis. in ctors",
    row: 6,
    x: 652,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-refute",
    slug: "invisible-binders-in-constructors",
    proposals: ["#126"],
    deps: [],
    summary: "Upstream @a patterns in constructor matches.",
  },
  {
    id: "R32",
    label: "Visible type applications",
    short: "TypeApplications",
    row: 6,
    x: 796,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "visible-type-applications",
    proposals: ["VTA"],
    deps: [],
    summary: "Upstream TypeApplications (@Int, @a).",
  },
  {
    id: "R33",
    label: "Visible kind applications",
    short: "VKA",
    row: 6,
    x: 940,
    w: 118,
    status: "upstream",
    act: "act-1",
    card: "card-nat",
    slug: "visible-kind-applications",
    proposals: ["#15"],
    deps: [],
    summary: "Upstream visible kind applications in types.",
  },
  // Row 7 — Companion Ecosystem Packages
  {
    id: "dependent-base",
    label: "TharkunAB/dependent-base",
    short: "dependent-base (22 mods)",
    row: 7,
    x: 240,
    w: 230,
    status: "pkg",
    act: "act-4",
    card: "card-dep-compose",
    repoUrl: "https://github.com/TharkunAB/dependent-base",
    proposals: ["linear-base", "agda-prelude"],
    deps: ["R03", "R04", "R16", "R22", "R23"],
    summary:
      "Standalone zero-wrapper standard library (Prelude.Dependent, Data.Function.Dependent with first-class dependent (.), Data.{Nat,List,Vec,Fin,Sigma,Exists,Decision,...}.Dependent + Properties) with Haskell2010 .hi-only interop.",
  },
  {
    id: "dependent-obs-eq",
    label: "TharkunAB/dependent-obs-eq",
    short: "dependent-obs-eq (Jules @analytichegel)",
    row: 7,
    x: 580,
    w: 278,
    status: "pkg",
    act: "act-5",
    card: "card-agda-mode",
    repoUrl: "https://github.com/TharkunAB/dependent-obs-eq",
    proposals: ["TcPlugin", "QuickCheck"],
    deps: ["R05", "R11", "R16"],
    summary:
      "Credited to Jules (@analytichegel): opt-in QuickCheck observational-equality TcPlugin (-fplugin=Dependent.Plugin.ObsEq) over uninterpreted open term calls (U:f) without weakening built-in Core conversion.",
  },
  {
    id: "dependent-proof-search",
    label: "TharkunAB/dependent-proof-search",
    short: "dependent-proof-search (HoleFitPlugin)",
    row: 7,
    x: 920,
    w: 258,
    status: "pkg",
    act: "act-5",
    card: "card-agda-mode",
    repoUrl: "https://github.com/TharkunAB/dependent-proof-search",
    proposals: ["HoleFitPlugin", "Haskell 2018"],
    deps: ["R03", "R05", "R16"],
    summary:
      "Standalone HoleFitPlugin (-fplugin=Dependent.Plugin.ProofSearch) supplying congruence/transitivity subgoal refinements (cong Succ _, trans (plusSuc m k) _) and bounded depth-D proof synthesis while keeping GHC.Tc.Errors.Hole completely general.",
  },
];

const ROW_Y = [40, 114, 198, 286, 376, 466, 554, 650];
const LANE_LABELS = [
  { row: 0, text: "GOAL" },
  { row: 1, text: "PILLARS" },
  { row: 2, text: "FEATURES" },
  { row: 3, text: "CORE & EVAL" },
  { row: 4, text: "SYNTAX & NS" },
  { row: 5, text: "BINDERS" },
  { row: 6, text: "BEDROCK" },
  { row: 7, text: "ECOSYSTEM" },
];

const SVG_NS = "http://www.w3.org/2000/svg";

function svgEl(tag, attrs = {}) {
  const el = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) {
    el.setAttribute(k, String(v));
  }
  return el;
}

export function mountRoadmapDag(mountEl) {
  if (!mountEl) return;

  const nodeMap = new Map(ROADMAP_NODES.map((n) => [n.id, n]));
  const dependentsMap = new Map(ROADMAP_NODES.map((n) => [n.id, []]));
  const edges = [];

  for (const n of ROADMAP_NODES) {
    for (const depId of n.deps) {
      if (!nodeMap.has(depId)) continue;
      edges.push({ from: n.id, to: depId });
      dependentsMap.get(depId).push(n.id);
    }
  }

  mountEl.innerHTML = "";

  // Controls & legend bar
  const topBar = document.createElement("div");
  topBar.className = "dag-toolbar";

  const filters = document.createElement("div");
  filters.className = "dag-filters";
  const filterSpecs = [
    { key: "all", label: "All (50 + 3)" },
    { key: "fork", label: "Fork implemented (27)" },
    { key: "upstream", label: "Upstream GHC (23)" },
    { key: "pkg", label: "Companion packages (3)" },
  ];

  const filterBtns = new Map();
  let activeFilter = "all";
  let selectedId = "R01";
  let hoveredId = null;

  for (const spec of filterSpecs) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "dag-filter-btn" + (spec.key === "all" ? " dag-filter-btn--active" : "");
    btn.textContent = spec.label;
    btn.addEventListener("click", () => {
      activeFilter = spec.key;
      for (const [k, b] of filterBtns.entries()) {
        b.classList.toggle("dag-filter-btn--active", k === activeFilter);
      }
      updateHighlight();
    });
    filterBtns.set(spec.key, btn);
    filters.append(btn);
  }

  const legend = document.createElement("div");
  legend.className = "dag-legend";
  legend.innerHTML = `
    <span class="dag-legend-item"><i class="dag-swatch dag-swatch--fork"></i>Fork (27)</span>
    <span class="dag-legend-item"><i class="dag-swatch dag-swatch--upstream"></i>Upstream GHC (23)</span>
    <span class="dag-legend-item"><i class="dag-swatch dag-swatch--pkg"></i>Companion pkg (3)</span>
    <span class="dag-legend-item"><i class="dag-line dag-line--dep"></i>Depends on</span>
    <span class="dag-legend-item"><i class="dag-line dag-line--rev"></i>Unlocks</span>
  `;

  topBar.append(filters, legend);

  // SVG viewport
  const svgWrap = document.createElement("div");
  svgWrap.className = "dag-svg-wrap";

  const svg = svgEl("svg", {
    viewBox: "0 0 1240 700",
    class: "dag-svg",
    role: "img",
    "aria-label":
      "Interactive 50-card Serokell Dependent Haskell roadmap dependency graph plus 3 companion packages",
  });

  // Shift every node right by GUTTER_X so left-margin lane labels never collide with cards.
  const GUTTER_X = 76;
  const nodeX = (n) => n.x + GUTTER_X;

  // Subtle lane bands
  const laneGroup = svgEl("g", { class: "dag-lanes" });
  for (const lane of LANE_LABELS) {
    const y = ROW_Y[lane.row];
    const band = svgEl("rect", {
      x: 4,
      y: y - 26,
      width: 1232,
      height: 56,
      rx: 6,
      class:
        lane.row === 7
          ? "dag-lane-band dag-lane-band--eco"
          : lane.row % 2 === 1
            ? "dag-lane-band dag-lane-band--alt"
            : "dag-lane-band",
    });
    const lbl = svgEl("text", {
      x: 12,
      y: y + 3,
      class: "dag-lane-label",
    });
    lbl.textContent = lane.text;
    laneGroup.append(band, lbl);
  }
  svg.append(laneGroup);

  // Edges layer
  const edgeGroup = svgEl("g", { class: "dag-edges" });
  const edgeEls = [];
  for (const e of edges) {
    const a = nodeMap.get(e.from);
    const b = nodeMap.get(e.to);
    const ax = nodeX(a);
    const bx = nodeX(b);
    const ay = ROW_Y[a.row];
    const by = ROW_Y[b.row];
    const goingDown = by >= ay;
    const y1 = goingDown ? ay + 16 : ay - 16;
    const y2 = goingDown ? by - 16 : by + 16;
    const midY = (y1 + y2) / 2;
    const dx = Math.abs(bx - ax);
    const bend = a.row === b.row ? (ax < bx ? -22 : 22) : 0;
    const d =
      a.row === b.row
        ? `M ${ax} ${ay - 16} Q ${(ax + bx) / 2} ${ay - 40 + bend} ${bx} ${by - 16}`
        : `M ${ax} ${y1} C ${ax} ${midY + Math.min(26, dx * 0.04)}, ${bx} ${midY - Math.min(26, dx * 0.04)}, ${bx} ${y2}`;
    const path = svgEl("path", {
      d,
      class: "dag-edge",
      "data-from": e.from,
      "data-to": e.to,
    });
    edgeGroup.append(path);
    edgeEls.push({ ...e, el: path });
  }
  svg.append(edgeGroup);

  // Nodes layer
  const nodeGroup = svgEl("g", { class: "dag-nodes" });
  const nodeEls = new Map();
  for (const n of ROADMAP_NODES) {
    const nx = nodeX(n);
    const y = ROW_Y[n.row];
    const h = 34;
    const g = svgEl("g", {
      class: `dag-node dag-node--${n.status}` + (n.boundary ? " dag-node--boundary" : ""),
      transform: `translate(${nx - n.w / 2}, ${y - h / 2})`,
      tabindex: "0",
      role: "button",
      "aria-label": `${n.id}: ${n.label}`,
      "data-node-id": n.id,
    });

    const rect = svgEl("rect", {
      width: n.w,
      height: h,
      rx: n.status === "pkg" ? 8 : 5,
      class: "dag-node-rect",
    });

    const titleEl = svgEl("title");
    titleEl.textContent = `${n.id}: ${n.label}`;

    const isWide = n.w >= 160;
    const idText = svgEl("text", {
      x: n.w / 2,
      y: isWide ? 14 : 13,
      "text-anchor": "middle",
      class: "dag-node-id",
    });
    idText.textContent = n.status === "pkg" ? n.id : n.boundary ? `${n.id}*` : n.id;

    const subText = svgEl("text", {
      x: n.w / 2,
      y: isWide ? 27 : 26,
      "text-anchor": "middle",
      class: "dag-node-sub",
    });
    subText.textContent = n.status === "pkg" ? n.short.replace(`${n.id} `, "") : n.short;

    g.append(titleEl, rect, idText, subText);

    g.addEventListener("mouseenter", () => {
      hoveredId = n.id;
      updateHighlight();
    });
    g.addEventListener("mouseleave", () => {
      hoveredId = null;
      updateHighlight();
    });
    g.addEventListener("click", () => {
      selectedId = n.id;
      renderInspector(n);
      updateHighlight();
    });
    g.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter" || ev.key === " ") {
        ev.preventDefault();
        selectedId = n.id;
        renderInspector(n);
        updateHighlight();
      }
    });

    nodeGroup.append(g);
    nodeEls.set(n.id, g);
  }
  svg.append(nodeGroup);
  svgWrap.append(svg);

  // Inspector panel below SVG
  const inspector = document.createElement("div");
  inspector.className = "dag-inspector";
  inspector.setAttribute("aria-live", "polite");

  const statusLabel = (n) => {
    if (n.status === "upstream") return "Inherited from upstream GHC";
    if (n.status === "pkg") return "Standalone companion package";
    return n.boundary
      ? "Implemented on fork (explicit design boundary)"
      : "Implemented on fork";
  };

  const renderInspector = (n) => {
    const revDeps = dependentsMap.get(n.id) || [];
    const upstreamLink = n.slug
      ? `<a href="${SEROKELL_BASE}${n.slug}" target="_blank" rel="noopener">Serokell ${n.id}</a>`
      : n.repoUrl
        ? `<a href="${n.repoUrl}" target="_blank" rel="noopener">${n.label}</a>`
        : "";
    const forkDocLink = n.forkDoc
      ? ` &middot; <a href="${FORK_ROADMAP_BASE}${n.forkDoc}" target="_blank" rel="noopener">Fork notes</a>`
      : "";
    const propsText =
      n.proposals && n.proposals.length > 0
        ? ` &middot; <span class="dag-insp-props">${n.proposals.join(", ")}</span>`
        : "";

    inspector.innerHTML = `
      <div class="dag-insp-head">
        <div>
          <span class="dag-insp-badge dag-insp-badge--${n.status}">${statusLabel(n)}</span>
          <strong class="dag-insp-title">${n.id === n.label ? n.label : `${n.id} — ${n.label}`}</strong>
          <span class="dag-insp-links">${upstreamLink}${forkDocLink}${propsText}</span>
        </div>
        <div class="dag-insp-actions">
          <button type="button" class="plfh-wasm-btn plfh-wasm-check dag-jump-btn">
            Jump to Live Example &darr;
          </button>
        </div>
      </div>
      <p class="dag-insp-summary">${n.summary}</p>
      <div class="dag-insp-rel-row">
        <div class="dag-insp-rel">
          <span class="dag-insp-rel-lbl">Depends on (${n.deps.length}):</span>
          <span class="dag-insp-pills" data-rel="deps"></span>
        </div>
        <div class="dag-insp-rel">
          <span class="dag-insp-rel-lbl">Unlocks (${revDeps.length}):</span>
          <span class="dag-insp-pills" data-rel="rev"></span>
        </div>
      </div>
    `;

    const jumpBtn = inspector.querySelector(".dag-jump-btn");
    jumpBtn.addEventListener("click", () => {
      const target =
        document.getElementById(n.card) || document.getElementById(n.act);
      if (target) {
        target.scrollIntoView({ behavior: "smooth", block: "start" });
        target.classList.add("showcase-card--pulse");
        setTimeout(() => target.classList.remove("showcase-card--pulse"), 1600);
      }
    });

    const addPills = (container, ids, cls) => {
      if (ids.length === 0) {
        container.innerHTML = `<span class="dag-insp-none">Leaf / none</span>`;
        return;
      }
      for (const id of ids) {
        const targetNode = nodeMap.get(id);
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = `dag-pill ${cls}`;
        btn.textContent = targetNode ? `${id} ${targetNode.short}` : id;
        btn.addEventListener("click", () => {
          selectedId = id;
          if (targetNode) renderInspector(targetNode);
          updateHighlight();
        });
        container.append(btn);
      }
    };

    addPills(inspector.querySelector('[data-rel="deps"]'), n.deps, "dag-pill--dep");
    addPills(inspector.querySelector('[data-rel="rev"]'), revDeps, "dag-pill--rev");
  };

  const updateHighlight = () => {
    const focusId = hoveredId || selectedId;
    const focusNode = nodeMap.get(focusId);
    const depSet = new Set(focusNode ? focusNode.deps : []);
    const revSet = new Set(focusId ? dependentsMap.get(focusId) || [] : []);

    for (const [id, g] of nodeEls.entries()) {
      const n = nodeMap.get(id);
      const matchesFilter = activeFilter === "all" || n.status === activeFilter;
      const isSelected = id === selectedId;
      const isFocus = id === focusId;
      const isDep = depSet.has(id);
      const isRev = revSet.has(id);
      const isNeighbor = isFocus || isDep || isRev;

      g.classList.toggle("dag-node--selected", isSelected);
      g.classList.toggle("dag-node--dep", isDep);
      g.classList.toggle("dag-node--rev", isRev);
      const dim =
        !matchesFilter || (hoveredId !== null && !isNeighbor);
      g.classList.toggle("dag-node--dim", dim);
    }

    for (const e of edgeEls) {
      const isOut = focusId && e.from === focusId;
      const isIn = focusId && e.to === focusId;
      e.el.classList.toggle("dag-edge--dep", Boolean(isOut));
      e.el.classList.toggle("dag-edge--rev", Boolean(isIn));
      e.el.classList.toggle(
        "dag-edge--dim",
        Boolean(focusId && !isOut && !isIn)
      );
    }
  };

  mountEl.append(topBar, svgWrap, inspector);
  renderInspector(nodeMap.get(selectedId));
  updateHighlight();
}
