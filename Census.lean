/-
Census.lean: the census of the Stoicheia edition's exported environment effects (d-effects, piece A).

Reference build for the d-effects-exported blueprint. Lean v4.35.0, Lean core only. Never run on the
Mac: it runs on GitHub's runners, in dodecaplex-co/stoicheia-probe.

  census env --root R --foundation F (repeatable) [--edition-commit SHA] --out O.json

Imports R's .olean closure and decodes every exported environment-extension entry of every package
module (R's own modules). An .olean holds exactly what a module exports, global and scoped
(ScopedEnvExtension.lean:76-116); that is what an importer's elaboration sees.

The claim, and only this claim: every exported entry of every package module is listed, decoded
with every field that changes elaboration, or the census refuses. Each extension with entries is
- decoded (an effect family), or
- on the reviewed list, by name, kind and reason; attributes are still listed as effects, and an
  own-declaration kind is checked entry by entry to name the module's own declaration, or
- unknown, which fails the census, scoped or not.
Every field of each decoded entry is kept in the record's `payload` (the field sweep below), or the
entry is refused (`unknown_payload`), which fails the census.
File-local effects never reach an .olean; they are piece B's (d-effects-local), and the JSON says so
in `not_claimed`.

Exit codes: 0 complete; 1 incomplete (the JSON is written first, with every reason); 2 usage;
3 unexpected error.
-/
import Lean

open Lean Meta Elab

namespace Census

/-! ## Flags -/

abbrev Flags := Array (String × String)

def parseFlags : List String → Except String Flags
  | [] => .ok #[]
  | k :: v :: rest =>
    if k.startsWith "--" then (parseFlags rest).map (#[(k, v)] ++ ·)
    else .error s!"unexpected argument {k}"
  | [k] => .error s!"{k} needs a value"

def Flags.get? (fl : Flags) (k : String) : Option String :=
  (fl.find? (·.1 == k)).map (·.2)

def Flags.all (fl : Flags) (k : String) : Array String :=
  (fl.filter (·.1 == k)).map (·.2)

def need (fl : Flags) (k : String) : IO String :=
  match fl.get? k with
  | some v => pure v
  | none => throw (IO.userError s!"usage: missing {k}")

def initPath : IO Unit := do
  let sysroot ← match (← IO.getEnv "LEAN_SYSROOT") with
    | some s => pure (System.FilePath.mk s)
    | none => findSysroot
  initSearchPath sysroot

/-! ## Records -/

structure Effect where
  family    : String
  ext       : String
  module    : Name
  part      : String := ""
  scope     : String
  ns        : Option Name := none
  target    : Option Name := none
  keys      : Array Name := #[]
  ownKeyed  : Bool := false
  coercion  : Bool := false
  detail    : String := ""
  /-- Every field of the 4.35 entry, as the field sweep below keeps it. -/
  payload   : Json := Json.null
  /-- Set when a field cannot be decoded soundly: the entry is refused (`unknown_payload`), never
  listed with the field dropped. -/
  refusal   : Option String := none

def Effect.outside (r : Effect) : Bool := r.part == "edition"

/-- Escapes its file: global or scoped, and keyed on nothing its own module declares. -/
def Effect.escapes (r : Effect) : Bool :=
  (r.scope == "global" || r.scope == "scoped") && !r.ownKeyed

def nameJson (n : Name) : Json := Json.str n.toString

def optName : Option Name → Json
  | some n => nameJson n
  | none => Json.null

def Effect.json (r : Effect) : Json :=
  Json.mkObj [
    ("family", Json.str r.family), ("extension", Json.str r.ext), ("module", nameJson r.module),
    ("part", Json.str r.part), ("outside_foundations", Json.bool r.outside), ("scope", Json.str r.scope),
    ("namespace", optName r.ns), ("target", optName r.target), ("keyed_on", Json.arr (r.keys.map nameJson)),
    ("own_keyed", Json.bool r.ownKeyed), ("escapes", Json.bool r.escapes), ("coercion", Json.bool r.coercion),
    ("detail", Json.str r.detail), ("payload", r.payload)]

/-! ## The field sweep (Lean v4.35.0)

Every field of every entry type this file decodes, from the toolchain's sources (paths under
src/lean/). Each field is kept, under the payload name given, or refused with `unknown_payload`
(exit 1). None is dropped as not behaviour-bearing, so the table has no such row. A `record` name
is a field of the effect record itself; `.1` and `.2` are the parts of a pair.
`test_census_keeps_every_field` checks each row against the decoder it names.

| entry type | field | source | decoder | kept as |
|---|---|---|---|---|
| ScopedEnvExtension.Entry | global | Lean/ScopedEnvExtension.lean:18 | entryScope | record "scope" |
| ScopedEnvExtension.Entry | scoped | Lean/ScopedEnvExtension.lean:19 | entryScope | record "scope", record "namespace" |
| DiscrTree.Key | star | Lean/Meta/DiscrTree/Types.lean:17 | keyJson | "star" |
| DiscrTree.Key | other | Lean/Meta/DiscrTree/Types.lean:18 | keyJson | "other" |
| DiscrTree.Key | lit | Lean/Meta/DiscrTree/Types.lean:19 | keyJson | "lit" |
| Literal | natVal | Lean/Expr.lean:20 | keyJson | "nat" |
| Literal | strVal | Lean/Expr.lean:22 | keyJson | "str" |
| DiscrTree.Key | fvar | Lean/Meta/DiscrTree/Types.lean:20 | keyJson | "fvar", "arity" |
| FVarId | name | Lean/Expr.lean:210 | keyJson | "fvar" |
| DiscrTree.Key | const | Lean/Meta/DiscrTree/Types.lean:21 | keyJson | "const", "name", "arity" |
| DiscrTree.Key | arrow | Lean/Meta/DiscrTree/Types.lean:22 | keyJson | "arrow" |
| DiscrTree.Key | proj | Lean/Meta/DiscrTree/Types.lean:23 | keyJson | "proj", "struct", "index", "arity" |
| InstanceEntry | keys | Lean/Meta/Instances.lean:51 | decodeInstances | "keys" |
| InstanceEntry | val | Lean/Meta/Instances.lean:52 | decodeInstances | "val" |
| InstanceEntry | priority | Lean/Meta/Instances.lean:53 | decodeInstances | "priority" |
| InstanceEntry | globalName? | Lean/Meta/Instances.lean:54 | decodeInstances | "global_name" |
| InstanceEntry | synthOrder | Lean/Meta/Instances.lean:56 | decodeInstances | "synth_order" |
| InstanceEntry | attrKind | Lean/Meta/Instances.lean:63 | decodeInstances | "attr_kind" |
| AttributeKind | every constructor | Lean/Attributes.lean:45 | attrKindString | "global", "local", "scoped" |
| SimpEntry | thm | Lean/Meta/Tactic/Simp/SimpTheorems.lean:522 | decodeSimp | "theorem" |
| SimpEntry | toUnfold | Lean/Meta/Tactic/Simp/SimpTheorems.lean:523 | decodeSimp | "unfold", "decl" |
| SimpEntry | toUnfoldThms | Lean/Meta/Tactic/Simp/SimpTheorems.lean:524 | decodeSimp | "unfold_by_equations", "decl", "theorems" |
| SimpTheorem | keys | Lean/Meta/Tactic/Simp/SimpTheorems.lean:156 | decodeSimp | "keys" |
| SimpTheorem | levelParams | Lean/Meta/Tactic/Simp/SimpTheorems.lean:162 | decodeSimp | "level_params" |
| SimpTheorem | proof | Lean/Meta/Tactic/Simp/SimpTheorems.lean:163 | decodeSimp | "proof" |
| SimpTheorem | priority | Lean/Meta/Tactic/Simp/SimpTheorems.lean:164 | decodeSimp | "priority" |
| SimpTheorem | post | Lean/Meta/Tactic/Simp/SimpTheorems.lean:165 | decodeSimp | "post" |
| SimpTheorem | perm | Lean/Meta/Tactic/Simp/SimpTheorems.lean:167 | decodeSimp | "perm" |
| SimpTheorem | origin | Lean/Meta/Tactic/Simp/SimpTheorems.lean:172 | decodeSimp | "origin" |
| SimpTheorem | rfl | Lean/Meta/Tactic/Simp/SimpTheorems.lean:176 | decodeSimp | "rfl" |
| SimpTheorem | backwardRfl | Lean/Meta/Tactic/Simp/SimpTheorems.lean:182 | decodeSimp | "backward_rfl" |
| Origin | decl | Lean/Meta/Tactic/Simp/SimpTheorems.lean:71 | originJson | "decl", "post", "inv" |
| Origin | fvar | Lean/Meta/Tactic/Simp/SimpTheorems.lean:78 | originJson | refused: never exported (SimpTheorems.lean:740-742) |
| Origin | stx | Lean/Meta/Tactic/Simp/SimpTheorems.lean:84 | originJson | refused: never exported (SimpTheorems.lean:740-742) |
| Origin | other | Lean/Meta/Tactic/Simp/SimpTheorems.lean:90 | originJson | "other", "name" |
| reducibilityCoreExt entry | .1 | Lean/ReducibilityAttrs.lean:51 | decodeReducibility | "decl" |
| reducibilityCoreExt entry | .2 | Lean/ReducibilityAttrs.lean:51 | decodeReducibility | "status" |
| reducibilityExtraExt entry | .1 | Lean/ReducibilityAttrs.lean:71 | decodeReducibility | "decl" |
| reducibilityExtraExt entry | .2 | Lean/ReducibilityAttrs.lean:71 | decodeReducibility | "status" |
| ReducibilityStatus | every constructor | Lean/ReducibilityAttrs.lean:41 | statusString | "reducible", "semireducible", "irreducible", "implicit_reducible", "instance_reducible" |
| ParserExtension.OLeanEntry | token | Lean/Parser/Extension.lean:61 | decodeParser | "token" |
| ParserExtension.OLeanEntry | kind | Lean/Parser/Extension.lean:62 | decodeParser | "kind" |
| ParserExtension.OLeanEntry | category | Lean/Parser/Extension.lean:63 | decodeParser | "category", "decl", "behavior" |
| ParserExtension.OLeanEntry | parser | Lean/Parser/Extension.lean:64 | decodeParser | "parser", "category", "decl", "priority" |
| LeadingIdentBehavior | every constructor | Lean/Parser/Basic.lean:1687 | identBehaviorString | "default", "symbol", "both" |
| KeyedDeclsAttribute.OLeanEntry | key | Lean/KeyedDeclsAttribute.lean:58 | decodeKeyed | "key" |
| KeyedDeclsAttribute.OLeanEntry | declName | Lean/KeyedDeclsAttribute.lean:60 | decodeKeyed | "decl" |
| coeExt entry | .1 | Lean/Meta/CoeAttr.lean:61 | decodeCoe | "decl" |
| CoeFnInfo | numArgs | Lean/Meta/CoeAttr.lean:48 | decodeCoe | "num_args" |
| CoeFnInfo | coercee | Lean/Meta/CoeAttr.lean:50 | decodeCoe | "coercee" |
| CoeFnInfo | type | Lean/Meta/CoeAttr.lean:52 | decodeCoe | "type" |
| CoeFnType | every constructor | Lean/Meta/CoeAttr.lean:31 | coeTypeString | "coe", "coeFun", "coeSort" |
| UnificationHintEntry | keys | Lean/Meta/UnificationHint.lean:18 | decodeHints | "keys" |
| UnificationHintEntry | val | Lean/Meta/UnificationHint.lean:19 | decodeHints | "val" |
| DefaultInstanceEntry | className | Lean/Meta/Instances.lean:379 | decodeDefaults | "class" |
| DefaultInstanceEntry | instanceName | Lean/Meta/Instances.lean:380 | decodeDefaults | "instance" |
| DefaultInstanceEntry | priority | Lean/Meta/Instances.lean:381 | decodeDefaults | "priority" |
| AliasEntry | .1 | Lean/ResolveName.lean:61 | decodeAliases | "alias" |
| AliasEntry | .2 | Lean/ResolveName.lean:61 | decodeAliases | "of" |
| ClassEntry | name | Lean/Class.lean:16 | decodeClasses | "name" |
| ClassEntry | outParams | Lean/Class.lean:25 | decodeClasses | "out_params" |
| ClassEntry | outLevelParams | Lean/Class.lean:32 | decodeClasses | "out_level_params" |
| CSimp.Entry | fromDeclName | Lean/Compiler/CSimpAttr.lean:19 | decodeCSimp | "from" |
| CSimp.Entry | toDeclName | Lean/Compiler/CSimpAttr.lean:20 | decodeCSimp | "to" |
| CSimp.Entry | thmName | Lean/Compiler/CSimpAttr.lean:21 | decodeCSimp | "thm" |
| TagAttribute entry | the name | Lean/Attributes.lean:177 | decodeReviewed | "decl" |
| ParametricAttribute entry | .1 | Lean/Attributes.lean:244 | decodeReviewed | "decl" |
| ParametricAttribute entry | .2 | Lean/Attributes.lean:244 | decodeReviewed | "value" |
| EnumAttributes entry | .1 | Lean/Attributes.lean:343 | decodeReviewed | "decl" |
| EnumAttributes entry | .2 | Lean/Attributes.lean:343 | decodeReviewed | "value" |
| deprecatedAttr value | deprecatedAttr | Lean/Linter/Deprecated.lean:52 | attrValue | "new_name", "text", "since" |
| DeprecationEntry | newName? | Lean/Linter/Deprecated.lean:35 | attrValue | "new_name" |
| DeprecationEntry | text? | Lean/Linter/Deprecated.lean:36 | attrValue | "text" |
| DeprecationEntry | since? | Lean/Linter/Deprecated.lean:37 | attrValue | "since" |
| inlineAttrs value | inlineAttrs | Lean/Compiler/InlineAttrs.lean:63 | attrValue | value (the inline kind) |
| InlineAttributeKind | every constructor | Lean/Compiler/InlineAttrs.lean:18 | inlineString | "inline", "noinline", "macro_inline", "inline_if_reduce", "always_inline" |
| specializeAttr value | specializeAttr | Lean/Compiler/Specialize.lean:78 | attrValue | value (the parameter positions) |
| implementedByAttr value | implementedByAttr | Lean/Compiler/ImplementedByAttr.lean:46 | attrValue | value (the implementing declaration) |
| exportAttr value | exportAttr | Lean/Compiler/ExportAttr.lean:54 | attrValue | value (the exported name) |
| externAttr value | externAttr | Lean/Compiler/ExternAttr.lean:61 | attrValue | "entries" |
| ExternAttrData | entries | Lean/Compiler/ExternAttr.lean:40 | attrValue | "entries" |
| ExternEntry | adhoc | Lean/Compiler/ExternAttr.lean:20 | externJson | "adhoc", "backend" |
| ExternEntry | inline | Lean/Compiler/ExternAttr.lean:21 | externJson | "inline", "backend", "pattern" |
| ExternEntry | standard | Lean/Compiler/ExternAttr.lean:22 | externJson | "standard", "backend", "fn" |
| ExternEntry | opaque | Lean/Compiler/ExternAttr.lean:24 | externJson | "opaque" |
| recursorAttribute value | recursorAttribute | Lean/Meta/RecursorInfo.lean:232 | attrValue | value (the major premise's position) |
| Grind.Entry | ext | Lean/Meta/Tactic/Grind/Extension.lean:157 | decodeGrind | "ext", "decl" |
| Grind.Entry | funCC | Lean/Meta/Tactic/Grind/Extension.lean:158 | decodeGrind | "funCC", "decl" |
| Grind.Entry | cases | Lean/Meta/Tactic/Grind/Extension.lean:159 | decodeGrind | "cases", "decl", "eager" |
| Grind.Entry | ematch | Lean/Meta/Tactic/Grind/Extension.lean:160 | decodeGrind | "ematch" |
| Grind.Entry | inj | Lean/Meta/Tactic/Grind/Extension.lean:161 | decodeGrind | "inj" |
| EMatchTheorem | levelParams | Lean/Meta/Tactic/Grind/Extension.lean:119 | decodeGrind | "level_params" |
| EMatchTheorem | proof | Lean/Meta/Tactic/Grind/Extension.lean:120 | decodeGrind | "proof" |
| EMatchTheorem | numParams | Lean/Meta/Tactic/Grind/Extension.lean:121 | decodeGrind | "num_params" |
| EMatchTheorem | patterns | Lean/Meta/Tactic/Grind/Extension.lean:122 | decodeGrind | "patterns" |
| EMatchTheorem | symbols | Lean/Meta/Tactic/Grind/Extension.lean:124 | decodeGrind | "symbols" |
| EMatchTheorem | origin | Lean/Meta/Tactic/Grind/Extension.lean:125 | decodeGrind | "origin" |
| EMatchTheorem | kind | Lean/Meta/Tactic/Grind/Extension.lean:127 | decodeGrind | "kind" |
| EMatchTheorem | minIndexable | Lean/Meta/Tactic/Grind/Extension.lean:129 | decodeGrind | "min_indexable" |
| EMatchTheorem | cnstrs | Lean/Meta/Tactic/Grind/Extension.lean:130 | decodeGrind | "cnstrs" |
| InjectiveTheorem | levelParams | Lean/Meta/Tactic/Grind/Extension.lean:142 | decodeGrind | "level_params" |
| InjectiveTheorem | proof | Lean/Meta/Tactic/Grind/Extension.lean:143 | decodeGrind | "proof" |
| InjectiveTheorem | symbols | Lean/Meta/Tactic/Grind/Extension.lean:145 | decodeGrind | "symbols" |
| InjectiveTheorem | origin | Lean/Meta/Tactic/Grind/Extension.lean:146 | decodeGrind | "origin" |
| EMatchTheoremKind | all, by its Repr | Lean/Meta/Tactic/Grind/Extension.lean:30 | decodeGrind | "kind" |
| EMatchTheoremConstraint | all, by its Repr | Lean/Meta/Tactic/Grind/Extension.lean:55 | decodeGrind | "cnstrs" |
| Grind.Origin | decl | Lean/Meta/Tactic/Grind/Theorems.lean:20 | grindOriginJson | "decl" |
| Grind.Origin | fvar | Lean/Meta/Tactic/Grind/Theorems.lean:22 | grindOriginJson | refused: never exported (Grind/Extension.lean:197-204) |
| Grind.Origin | stx | Lean/Meta/Tactic/Grind/Theorems.lean:27 | grindOriginJson | refused: never exported (Grind/Extension.lean:197-204) |
| Grind.Origin | local | Lean/Meta/Tactic/Grind/Theorems.lean:29 | grindOriginJson | refused: never exported (Grind/Extension.lean:197-204) |
| HeadIndex | fvar | Lean/HeadIndex.lean:29 | headIndexJson | "fvar" |
| HeadIndex | mvar | Lean/HeadIndex.lean:30 | headIndexJson | "mvar" |
| HeadIndex | const | Lean/HeadIndex.lean:31 | headIndexJson | "const", "name" |
| HeadIndex | proj | Lean/HeadIndex.lean:32 | headIndexJson | "proj", "struct", "index" |
| HeadIndex | lit | Lean/HeadIndex.lean:33 | headIndexJson | "lit", "nat", "str" |
| HeadIndex | sort | Lean/HeadIndex.lean:34 | headIndexJson | "sort" |
| HeadIndex | lam | Lean/HeadIndex.lean:35 | headIndexJson | "lam" |
| HeadIndex | forallE | Lean/HeadIndex.lean:36 | headIndexJson | "forallE" |
| MVarId | name | Lean/Expr.lean:258 | headIndexJson | "mvar" |

The reviewed list's `tag`, `map`, `decl` and `other` kinds are not decoded: they are counted under
their reviewed reason, and each `tag`, `map` and `decl` entry is checked to name the module's own
declaration. -/

/-! ## Keys and payloads -/

/-- The names a key path mentions, for `keyed_on` and the own-keyed test only; the payload keeps
every key in full (`keyJson`). -/
def keyConsts (keys : Array DiscrTree.Key) : Array Name :=
  keys.filterMap fun k => match k with
    | .const n _ => some n
    | .proj n _ _ => some n
    | _ => none

/-- One discrimination-tree key in full: every constructor of `DiscrTree.Key` in 4.35, with its
literal, arity, free variable or projection index. -/
def keyJson : DiscrTree.Key → Json
  | .star => Json.mkObj [("key", Json.str "star")]
  | .other => Json.mkObj [("key", Json.str "other")]
  | .lit (.natVal n) => Json.mkObj [("key", Json.str "lit"), ("nat", Lean.toJson n)]
  | .lit (.strVal s) => Json.mkObj [("key", Json.str "lit"), ("str", Json.str s)]
  | .fvar f a => Json.mkObj [("key", Json.str "fvar"), ("fvar", nameJson f.name), ("arity", Lean.toJson a)]
  | .const n a => Json.mkObj [("key", Json.str "const"), ("name", nameJson n), ("arity", Lean.toJson a)]
  | .arrow => Json.mkObj [("key", Json.str "arrow")]
  | .proj s i a => Json.mkObj [("key", Json.str "proj"), ("struct", nameJson s), ("index", Lean.toJson i),
      ("arity", Lean.toJson a)]

def keysJson (keys : Array DiscrTree.Key) : Json := Json.arr (keys.map keyJson)

/-- An expression in full (its derived `Repr`): an instance's value, a simp theorem's proof. -/
def exprJson (e : Expr) : Json := Json.str (reprStr e)

def namesJson (ns : Array Name) : Json := Json.arr (ns.map nameJson)

def optStr : Option String → Json
  | some s => Json.str s
  | none => Json.null

def entryScope {α : Type} : ScopedEnvExtension.Entry α → String × Option Name × α
  | .global a => ("global", none, a)
  | .scoped ns a => ("scoped", some ns, a)

def coeClasses : Array Name :=
  #[`Coe, `CoeTail, `CoeHead, `CoeOut, `CoeSort, `CoeFun, `CoeDep, `CoeT, `CoeHTCT, `CoeHTC,
    `CoeOTC, `CoeTC]

def statusString : ReducibilityStatus → String
  | .reducible => "reducible"
  | .semireducible => "semireducible"
  | .irreducible => "irreducible"
  | .implicitReducible => "implicit_reducible"
  | .instanceReducible => "instance_reducible"

def coeTypeString : CoeFnType → String
  | .coe => "coe"
  | .coeFun => "coeFun"
  | .coeSort => "coeSort"

def attrKindString : AttributeKind → String
  | .global => "global"
  | .local => "local"
  | .scoped => "scoped"

def identBehaviorString : Parser.LeadingIdentBehavior → String
  | .default => "default"
  | .symbol => "symbol"
  | .both => "both"

def inlineString : Compiler.InlineAttributeKind → String
  | .inline => "inline"
  | .noinline => "noinline"
  | .macroInline => "macro_inline"
  | .inlineIfReduce => "inline_if_reduce"
  | .alwaysInline => "always_inline"

/-- A simp theorem's origin. An exported entry's origin is a declaration (SimpTheorems.lean:740-742,
`unreachable!` otherwise); a local hypothesis or a simp argument cannot be decoded soundly, and refuses. -/
def originJson : Lean.Meta.Origin → Except String Json
  | .decl n post inv => .ok (Json.mkObj [("kind", Json.str "decl"), ("decl", nameJson n), ("post", Json.bool post),
      ("inv", Json.bool inv)])
  | .fvar _ => .error "the origin is a local hypothesis (Origin.fvar), which an exported entry never has"
  | .stx _ _ => .error "the origin is a simp argument (Origin.stx), which an exported entry never has"
  | .other n => .ok (Json.mkObj [("kind", Json.str "other"), ("name", nameJson n)])

def externJson : ExternEntry → Json
  | .adhoc b => Json.mkObj [("kind", Json.str "adhoc"), ("backend", nameJson b)]
  | .inline b p => Json.mkObj [("kind", Json.str "inline"), ("backend", nameJson b), ("pattern", Json.str p)]
  | .standard b f => Json.mkObj [("kind", Json.str "standard"), ("backend", nameJson b), ("fn", Json.str f)]
  | ExternEntry.opaque => Json.mkObj [("kind", Json.str "opaque")]

/-! ## The reviewed list: non-scoped extensions that are not effect families

By the declaration's user name (a private name is compared after `privateToUserName`). Kinds:
- `attr_tag`, `attr_map`: an attribute Lean only lets a module set on its own declarations
  (Attributes.lean:141, :326, :400). Listed as `attribute` effects; each entry checked to name the
  module's own declaration.
- `tag`, `map`: data keyed by the module's own declaration (EnvExtension.lean:156-159). Counted; each
  entry checked to name the module's own declaration.
- `decl`: entries whose first field is the name of the module's own declaration (a structure, a
  matcher, an IR declaration, a specialisation). Counted; each entry checked the same way.
- `other`: counted, with its reason; no entry names a declaration.
No scoped extension is on this list: a scoped extension is decoded, or the census fails.
`Lean.classExtension` is not on it either: `attribute [class]` can make another module's structure
a class (Class.lean:166), so classes are decoded as effects. -/
structure Reviewed where
  name   : String
  kind   : String
  reason : String

def ownDecl := "keyed by a declaration of the module itself (EnvExtension.lean:156-159)"
def ownAttr := "an attribute Lean only lets a module set on its own declarations (Attributes.lean:141, :326, :400)"
def compiled := "the compiler's output for the module's own declarations"

def reviewed : Array Reviewed := #[
  ⟨"Lean.declRangeExt", "map", "source ranges; " ++ ownDecl⟩,
  ⟨"Lean.docStringExt", "map", "docstrings; " ++ ownDecl⟩,
  ⟨"Lean.versoDocStringExt", "map", "docstrings; " ++ ownDecl⟩,
  ⟨"Lean.inheritDocStringExt", "map", "inherited docstrings; " ++ ownDecl⟩,
  ⟨"Lean.privateConstKindsExt", "map", "the kind of each private declaration; " ++ ownDecl⟩,
  ⟨"Lean.noConfusionExt", "map", "no-confusion data; " ++ ownDecl⟩,
  ⟨"Lean.projectionFnInfoExt", "map", "structure projections; " ++ ownDecl⟩,
  ⟨"Lean.auxParentProjInfoExt", "map", "structure parent projections; " ++ ownDecl⟩,
  ⟨"Lean.Linter.envLinterSnapshotExt", "map", "linter snapshots; " ++ ownDecl⟩,
  ⟨"Lean.Meta.congrKindsExt", "map", "congruence data; " ++ ownDecl⟩,
  ⟨"Lean.Meta.sparseCasesOnInfoExt", "map", "casesOn data; " ++ ownDecl⟩,
  ⟨"Lean.Meta.eqnOptionsExt", "map", "equation options; " ++ ownDecl⟩,
  ⟨"Lean.Meta.funIndInfoExt", "map", "functional induction data; " ++ ownDecl⟩,
  ⟨"Lean.Elab.Structural.eqnInfoExt", "map", "structural recursion equations; " ++ ownDecl⟩,
  ⟨"Lean.Elab.WF.eqnInfoExt", "map", "well-founded recursion equations; " ++ ownDecl⟩,
  ⟨"Lean.Elab.PartialFixpoint.eqnInfoExt", "map", "partial fixpoint equations; " ++ ownDecl⟩,
  ⟨"Lean.Compiler.LCNF.monoTypeExt", "map", compiled ++ "; " ++ ownDecl⟩,
  ⟨"Lean.Compiler.LCNF.impureTypeExt", "map", compiled ++ "; " ++ ownDecl⟩,
  ⟨"Lean.Compiler.LCNF.ctorLayoutExt", "map", compiled ++ "; " ++ ownDecl⟩,
  ⟨"Lean.Compiler.LCNF.trivialStructureInfoExt", "map", compiled ++ "; " ++ ownDecl⟩,
  ⟨"Lean.auxRecExt", "tag", "auxiliary recursors; " ++ ownDecl⟩,
  ⟨"Lean.sparseCasesOnExt", "tag", "sparse casesOn; " ++ ownDecl⟩,
  ⟨"Lean.protectedExt", "tag", "protected declarations; " ++ ownDecl⟩,
  ⟨"Lean.noncomputableExt", "tag", "noncomputable declarations; " ++ ownDecl⟩,
  ⟨"Lean.Meta.recExt", "tag", "recursors; " ++ ownDecl⟩,
  ⟨"Lean.Meta.matcherLikeExt", "tag", "matcher-like declarations; " ++ ownDecl⟩,
  ⟨"Lean.Meta.completionBlackListExt", "tag", "completion exclusions; " ++ ownDecl⟩,
  ⟨"Lean.metaExt", "tag", "meta declarations; " ++ ownDecl⟩,
  ⟨"Lean.Linter.deprecatedAttr", "attr_map", "@[deprecated]; " ++ ownAttr⟩,
  ⟨"Lean.Compiler.inlineAttrs", "attr_map", "@[inline], @[noinline], @[macro_inline] (abbrev sets @[inline]); " ++ ownAttr⟩,
  ⟨"Lean.Compiler.specializeAttr", "attr_map", "@[specialize]; " ++ ownAttr⟩,
  ⟨"Lean.Compiler.implementedByAttr", "attr_map", "@[implemented_by]; " ++ ownAttr⟩,
  ⟨"Lean.exportAttr", "attr_map", "@[export]; " ++ ownAttr⟩,
  ⟨"Lean.externAttr", "attr_map", "@[extern]; " ++ ownAttr⟩,
  ⟨"Lean.Meta.recursorAttribute", "attr_map", "@[recursor]; " ++ ownAttr⟩,
  ⟨"Lean.matchPatternAttr", "attr_tag", "@[match_pattern]; " ++ ownAttr⟩,
  ⟨"Lean.Elab.Term.elabAsElim", "attr_tag", "@[elab_as_elim]; " ++ ownAttr⟩,
  ⟨"Lean.Elab.Term.elabWithoutExpectedTypeAttr", "attr_tag", "@[elab_without_expected_type]; " ++ ownAttr⟩,
  ⟨"Lean.defeqAttr", "attr_tag", "@[defeq]; " ++ ownAttr⟩,
  ⟨"Lean.backwardDefeqAttr", "attr_tag", "@[backward_defeq]; " ++ ownAttr⟩,
  ⟨"Lean.ppNoDotAttr", "attr_tag", "@[pp_nodot]; " ++ ownAttr⟩,
  ⟨"Lean.ppUsingAnonymousConstructorAttr", "attr_tag", "@[pp_using_anonymous_constructor]; " ++ ownAttr⟩,
  ⟨"Lean.Meta.coeDeclAttr", "attr_tag", "@[coe_decl]; " ++ ownAttr⟩,
  ⟨"Lean.neverExtractAttr", "attr_tag", "@[never_extract]; " ++ ownAttr⟩,
  ⟨"Lean.Compiler.nospecializeAttr", "attr_tag", "@[nospecialize]; " ++ ownAttr⟩,
  ⟨"Lean.Compiler.weakSpecializeAttr", "attr_tag", "@[weak_specialize]; " ++ ownAttr⟩,
  ⟨"Lean.Elab.ComputedFields.computedFieldAttr", "attr_tag", "@[computed_field]; " ++ ownAttr⟩,
  ⟨"Lean.structureExt", "decl", "the structures the module declares (StructureInfo, first field structName)"⟩,
  ⟨"Lean.Meta.Match.Extension.extension", "decl", "matcher information for the module's own match auxiliaries (Entry, first field name)"⟩,
  ⟨"Lean.IR.declMapExt", "decl", compiled ++ " (IR Decl, first field the declaration's name)"⟩,
  ⟨"Lean.Compiler.LCNF.specExtension", "decl", compiled ++ " (SpecEntry, first field declName)"⟩,
  ⟨"Lean.namespacesExt", "other", "the namespace names the module opens with `namespace`: name-resolution data"⟩,
  ⟨"Lean.Compiler.LCNF.baseExt", "other", compiled⟩,
  ⟨"Lean.Compiler.LCNF.monoExt", "other", compiled⟩,
  ⟨"Lean.Compiler.LCNF.impureSigExt", "other", compiled⟩,
  -- Run 2: the name was wrong (the extension is in namespace UnreachableBranches), so it never matched.
  ⟨"Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "other", compiled ++ " (dead-branch summaries; its addImportedFn discards what it imports, and only the compiler reads it: ElimDeadBranches.lean:290-311)"⟩,
  ⟨"Lean.Compiler.LCNF.postponedCompileDeclsExt", "other", compiled ++ " (postponed compilation)"⟩,
  ⟨"Lean.declMetaExt", "other", "meta-phase marks of the module's declarations"⟩,
  ⟨"Lean.extraModUses", "other", "which imported modules this module uses: import-pruning data, read by no elaborator"⟩,
  ⟨"Lean.indirectModUseExt", "other", "import-pruning data, read by no elaborator"⟩,
  ⟨"Lean.isExtraRevModUseExt", "other", "import-pruning data, read by no elaborator"⟩,
  ⟨"Lean.modPkgExt", "other", "the module's own package id, set by Lake"⟩,
  -- Run 2: populated by every planted module, missing from the round-2 registry scan.
  ⟨"Lean.moduleDocExt", "other", "module docstrings (`/-! … -/`): its addImportedFn discards what it imports, so no importer's elaboration reads them; only doc tools do, through getModuleDoc? (DocString/Extension.lean:216-234)"⟩,
  ⟨"Lean.exportedAxiomsExt", "decl", "the axioms each of the module's own exported declarations uses, computed from their bodies when the .olean is written: a cache read by `#print axioms` and `collectAxioms`, never by elaboration (Util/CollectAxioms.lean:113-145)"⟩,
  ⟨"Lean.Compiler.LCNF.impureTrivialStructureInfoExt", "map", compiled ++ " (impure trivial-structure info, a MapDeclarationExtension: ToImpureType.lean:37-39); " ++ ownDecl⟩,
  ⟨"Lean.deprecatedModuleExt", "other", "whether the module itself is `deprecated_module` (one entry per module, ModPkgExt.lean:22-28; set at Elab/BuiltinCommand.lean:745): an importer gets only a warning at the import (Elab/Import.lean:84-100), which changes no elaboration"⟩]

def lookupReviewed (n : Name) : Option Reviewed :=
  let user := (privateToUserName n).toString
  reviewed.find? (·.name == user)

/-! ## Decoding -/

/-- One module's raw entries and the test for its own declarations. Piece B applies the same
decoder to a re-elaboration's `mkModuleData`. -/
structure Src where
  entries : Array (Name × Array EnvExtensionEntry)
  owns    : Name → Bool
  mod     : Name

def Src.raw (s : Src) (ext : Name) : Array EnvExtensionEntry :=
  match s.entries.find? (·.1 == ext) with
  | some (_, es) => es
  | none => #[]

def Src.mk' (s : Src) (family ext scope : String) (ns target : Option Name) (keys : Array Name)
    (own : Bool) (detail : String) (payload : Json) (coercion := false) : Effect :=
  { family, ext, module := s.mod, scope, ns, target, keys, ownKeyed := own, coercion, detail, payload }

unsafe def keyedNames : Array Name := #[
  Lean.Elab.macroAttribute.ext.ext.name,
  Lean.Elab.Term.termElabAttribute.ext.ext.name,
  Lean.Elab.Command.commandElabAttribute.ext.ext.name,
  Lean.Elab.Tactic.tacticElabAttribute.ext.ext.name,
  Lean.PrettyPrinter.Delaborator.delabAttribute.ext.ext.name,
  Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute.ext.ext.name]

structure Known where
  sets        : List (Name × SimpExtension)
  grindSets   : List (Name × Lean.Meta.Grind.Extension)
  scopedNames : NameSet
  decoded     : NameSet

unsafe def mkKnown : IO Known := do
  -- Every simp set, and grind's normaliser, a simp extension outside the simp map (Grind/Attr.lean:18).
  let sets := (← simpExtensionMapRef.get).toList ++ [(`grind_norm, Lean.Meta.Grind.normExt)]
  -- Every grind theorem set: `@[grind]`, `@[lia]` and any other Grind.registerAttr (Grind/Attr.lean:254-270).
  let grindSets := (← Lean.Meta.Grind.extensionMapRef.get).toList
  let scopedNames := (← scopedEnvExtensionsRef.get).foldl (fun s e => s.insert e.ext.name) ({} : NameSet)
  let mut decoded : NameSet := {}
  for n in #[instanceExtension.ext.name, reducibilityCoreExt.name, reducibilityExtraExt.ext.name,
      Parser.parserExtension.ext.name, coeExt.ext.name, unificationHintExtension.ext.name,
      defaultInstanceExtension.name, aliasExtension.name, classExtension.name,
      Compiler.CSimp.ext.ext.name] ++ keyedNames do
    decoded := decoded.insert n
  for (_, ext) in sets do
    decoded := decoded.insert ext.ext.name
  for (_, ext) in grindSets do
    decoded := decoded.insert ext.ext.name
  return { sets, grindSets, scopedNames, decoded }

/-- How the census treats an extension, as decodeAll does: decoded, reviewed, or neither, which fails
the census wherever the extension has entries. A scoped extension is never on the reviewed list. -/
def classify (k : Known) (n : Name) : String :=
  if k.decoded.contains n then "decoded"
  else if k.scopedNames.contains n then "neither"
  else if (lookupReviewed n).isSome then "reviewed"
  else "neither"

structure Decoded where
  effects        : Array Effect := #[]
  bookkeeping    : Array (Name × Nat) := #[]
  unknown        : Array (Name × Nat × Bool) := #[]
  notOwn         : Array String := #[]
  unknownPayload : Array String := #[]
  counts         : Array (Name × Nat) := #[]

unsafe def decodeInstances (s : Src) : Array Effect :=
  (s.raw instanceExtension.ext.name).map fun raw =>
    let e : ScopedEnvExtension.Entry InstanceEntry := unsafeCast raw
    let (scope, ns, i) := entryScope e
    let ks := keyConsts i.keys
    s.mk' "instance" instanceExtension.ext.name.toString scope ns i.globalName? ks (ks.any s.owns)
      s!"priority {i.priority}, synth order {i.synthOrder}, keys {i.keys.size}"
      (Json.mkObj [("keys", keysJson i.keys), ("val", exprJson i.val), ("priority", Lean.toJson i.priority),
        ("global_name", optName i.globalName?), ("synth_order", Lean.toJson i.synthOrder),
        ("attr_kind", Json.str (attrKindString i.attrKind))])
      (coercion := ks[0]?.any (coeClasses.contains ·))

unsafe def decodeSimp (s : Src) (sets : List (Name × SimpExtension)) : Array Effect := Id.run do
  let mut out : Array Effect := #[]
  for (attr, ext) in sets do
    let name := ext.ext.name.toString
    for raw in s.raw ext.ext.name do
      let e : ScopedEnvExtension.Entry SimpEntry := unsafeCast raw
      let (scope, ns, se) := entryScope e
      match se with
      | .thm t =>
        let ks := keyConsts t.keys
        let inv := match t.origin with | .decl _ _ inv => inv | _ => false
        let r := s.mk' "simp" name scope ns (some t.origin.key) ks (ks.any s.owns)
          s!"simp set {attr}: theorem, priority {t.priority}, post {t.post}, inv {inv}, perm {t.perm}, rfl {t.rfl}, keys {t.keys.size}"
          Json.null
        out := out.push <| match originJson t.origin with
          | .ok origin => { r with payload := Json.mkObj [("entry", Json.str "theorem"), ("simp_set", nameJson attr),
              ("keys", keysJson t.keys), ("level_params", namesJson t.levelParams), ("proof", exprJson t.proof),
              ("priority", Lean.toJson t.priority), ("post", Json.bool t.post), ("perm", Json.bool t.perm),
              ("origin", origin), ("rfl", Json.bool t.rfl), ("backward_rfl", Json.bool t.backwardRfl)] }
          | .error why => { r with refusal := some why }
      | .toUnfold n =>
        out := out.push (s.mk' "simp" name scope ns (some n) #[n] (s.owns n) s!"simp set {attr}: unfold"
          (Json.mkObj [("entry", Json.str "unfold"), ("simp_set", nameJson attr), ("decl", nameJson n)]))
      | .toUnfoldThms n thms =>
        out := out.push (s.mk' "simp" name scope ns (some n) #[n] (s.owns n)
          s!"simp set {attr}: unfold by equations {thms}"
          (Json.mkObj [("entry", Json.str "unfold_by_equations"), ("simp_set", nameJson attr), ("decl", nameJson n),
            ("theorems", namesJson thms)]))
  return out

unsafe def decodeReducibility (s : Src) : Array Effect := Id.run do
  let mut out : Array Effect := #[]
  for raw in s.raw reducibilityCoreExt.name do
    let (n, st) : Name × ReducibilityStatus := unsafeCast raw
    out := out.push (s.mk' "reducibility" reducibilityCoreExt.name.toString "global" none (some n) #[n] (s.owns n)
      (statusString st) (Json.mkObj [("decl", nameJson n), ("status", Json.str (statusString st))]))
  for raw in s.raw reducibilityExtraExt.ext.name do
    let e : ScopedEnvExtension.Entry (Name × ReducibilityStatus) := unsafeCast raw
    let (scope, ns, (n, st)) := entryScope e
    out := out.push (s.mk' "reducibility" reducibilityExtraExt.ext.name.toString scope ns (some n) #[n] (s.owns n)
      (statusString st) (Json.mkObj [("decl", nameJson n), ("status", Json.str (statusString st))]))
  return out

/-- Tokens and parsers change parsing for every importer; a syntax kind or a category alone does not. -/
unsafe def decodeParser (s : Src) : Array Effect × NameSet := Id.run do
  let name := Parser.parserExtension.ext.name.toString
  let entries : Array (ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry) :=
    (s.raw Parser.parserExtension.ext.name).map fun raw => unsafeCast raw
  let mut kinds : NameSet := {}
  let mut cats : NameSet := {}
  for e in entries do
    match (entryScope e).2.2 with
    | .kind k => kinds := kinds.insert k
    | .category cat _ _ => cats := cats.insert cat
    | _ => pure ()
  let mut out : Array Effect := #[]
  for e in entries do
    let (scope, ns, p) := entryScope e
    match p with
    | .token tk => out := out.push (s.mk' "notation" name scope ns none #[] false s!"token {tk}"
        (Json.mkObj [("entry", Json.str "token"), ("token", Json.str tk)]))
    | .kind k => out := out.push (s.mk' "notation" name scope ns (some k) #[k] true "syntax kind"
        (Json.mkObj [("entry", Json.str "kind"), ("kind", nameJson k)]))
    | .category cat d b =>
      out := out.push (s.mk' "notation" name scope ns (some d) #[cat] true s!"category {cat}, leading identifiers {(repr b).pretty}"
        (Json.mkObj [("entry", Json.str "category"), ("category", nameJson cat), ("decl", nameJson d),
          ("behavior", Json.str (identBehaviorString b))]))
    | .parser cat d prio =>
      out := out.push (s.mk' "notation" name scope ns (some d) #[cat] (cats.contains cat)
        s!"parser in category {cat}, priority {prio}"
        (Json.mkObj [("entry", Json.str "parser"), ("category", nameJson cat), ("decl", nameJson d),
          ("priority", Lean.toJson prio)]))
  return (out, kinds)

unsafe def decodeKeyed (s : Src) (ownKinds : NameSet) : Array Effect := Id.run do
  let mut out : Array Effect := #[]
  for ext in keyedNames do
    for raw in s.raw ext do
      let e : ScopedEnvExtension.Entry KeyedDeclsAttribute.OLeanEntry := unsafeCast raw
      let (scope, ns, k) := entryScope e
      let base := k.key.replacePrefix `app .anonymous
      let own := ownKinds.contains k.key || s.owns k.key || s.owns base
      out := out.push (s.mk' "macro" ext.toString scope ns (some k.declName) #[k.key] own s!"keyed on {k.key}"
        (Json.mkObj [("attribute", nameJson ext), ("key", nameJson k.key), ("decl", nameJson k.declName)]))
  return out

unsafe def decodeCoe (s : Src) : Array Effect :=
  (s.raw coeExt.ext.name).map fun raw =>
    let e : ScopedEnvExtension.Entry (Name × CoeFnInfo) := unsafeCast raw
    let (scope, ns, (n, info)) := entryScope e
    s.mk' "coercion" coeExt.ext.name.toString scope ns (some n) #[n] (s.owns n)
      s!"@[coe] {coeTypeString info.type}, explicit argument {info.coercee} of {info.numArgs}"
      (Json.mkObj [("decl", nameJson n), ("num_args", Lean.toJson info.numArgs), ("coercee", Lean.toJson info.coercee),
        ("type", Json.str (coeTypeString info.type))])

unsafe def decodeHints (s : Src) : Array Effect :=
  (s.raw unificationHintExtension.ext.name).map fun raw =>
    let e : ScopedEnvExtension.Entry UnificationHintEntry := unsafeCast raw
    let (scope, ns, h) := entryScope e
    let ks := keyConsts h.keys
    s.mk' "unif_hint" unificationHintExtension.ext.name.toString scope ns (some h.val) ks (ks.any s.owns)
      s!"unification hint, keys {h.keys.size}"
      (Json.mkObj [("keys", keysJson h.keys), ("val", nameJson h.val)])

unsafe def decodeDefaults (s : Src) : Array Effect :=
  (s.raw defaultInstanceExtension.name).map fun raw =>
    let d : DefaultInstanceEntry := unsafeCast raw
    s.mk' "default_instance" defaultInstanceExtension.name.toString "global" none (some d.instanceName)
      #[d.className] (s.owns d.className) s!"default instance of {d.className}, priority {d.priority}"
      (Json.mkObj [("class", nameJson d.className), ("instance", nameJson d.instanceName),
        ("priority", Lean.toJson d.priority)])

unsafe def decodeAliases (s : Src) : Array Effect :=
  (s.raw aliasExtension.name).map fun raw =>
    let a : Name × Name := unsafeCast raw
    s.mk' "alias" aliasExtension.name.toString "global" none (some a.1) #[a.2] false s!"alias of {a.2}"
      (Json.mkObj [("alias", nameJson a.1), ("of", nameJson a.2)])

/-- A class declared by the module itself is own-keyed; `attribute [class]` on another module's
structure (Class.lean:166) makes it a class for every importer, and escapes. -/
unsafe def decodeClasses (s : Src) : Array Effect :=
  (s.raw classExtension.name).map fun raw =>
    let c : ClassEntry := unsafeCast raw
    s.mk' "class" classExtension.name.toString "global" none (some c.name) #[c.name] (s.owns c.name)
      s!"class, out-params {c.outParams}"
      (Json.mkObj [("name", nameJson c.name), ("out_params", Lean.toJson c.outParams),
        ("out_level_params", Lean.toJson c.outLevelParams)])

/-- `@[csimp]` replaces calls to one declaration by another in all compiled code. -/
unsafe def decodeCSimp (s : Src) : Array Effect :=
  (s.raw Compiler.CSimp.ext.ext.name).map fun raw =>
    let e : ScopedEnvExtension.Entry Compiler.CSimp.Entry := unsafeCast raw
    let (scope, ns, c) := entryScope e
    s.mk' "csimp" Compiler.CSimp.ext.ext.name.toString scope ns (some c.thmName) #[c.fromDeclName, c.toDeclName]
      (s.owns c.fromDeclName) s!"replaces {c.fromDeclName} by {c.toDeclName}"
      (Json.mkObj [("from", nameJson c.fromDeclName), ("to", nameJson c.toDeclName), ("thm", nameJson c.thmName)])

/-- A grind theorem's symbol (HeadIndex.lean:28-37), in full. -/
def headIndexJson : HeadIndex → Json
  | .fvar f => Json.mkObj [("head", Json.str "fvar"), ("fvar", nameJson f.name)]
  | .mvar m => Json.mkObj [("head", Json.str "mvar"), ("mvar", nameJson m.name)]
  | .const n => Json.mkObj [("head", Json.str "const"), ("name", nameJson n)]
  | .proj s i => Json.mkObj [("head", Json.str "proj"), ("struct", nameJson s), ("index", Lean.toJson i)]
  | .lit (.natVal n) => Json.mkObj [("head", Json.str "lit"), ("nat", Lean.toJson n)]
  | .lit (.strVal s) => Json.mkObj [("head", Json.str "lit"), ("str", Json.str s)]
  | .sort => Json.mkObj [("head", Json.str "sort")]
  | .lam => Json.mkObj [("head", Json.str "lam")]
  | .forallE => Json.mkObj [("head", Json.str "forallE")]

/-- The names a grind theorem's symbols mention, for `keyed_on` and the own-keyed test. -/
def headConsts (hs : List HeadIndex) : Array Name :=
  hs.toArray.filterMap fun h => match h with
    | .const n => some n
    | .proj s _ => some s
    | _ => none

/-- A grind theorem's origin. An exported entry's is a declaration (Grind/Extension.lean:197-204,
`unreachable!` otherwise); any other refuses. -/
def grindOriginJson : Lean.Meta.Grind.Origin → Except String Json
  | .decl n => .ok (Json.mkObj [("kind", Json.str "decl"), ("decl", nameJson n)])
  | .fvar _ => .error "the origin is a local hypothesis (Grind.Origin.fvar), which an exported entry never has"
  | .stx _ _ => .error "the origin is a grind argument (Grind.Origin.stx), which an exported entry never has"
  | .local _ => .error "the origin is local (Grind.Origin.local), which an exported entry never has"

/-- `grind`'s theorem sets, scoped (Grind/Extension.lean:156-206): case splits, extensionality and
congruence marks, E-matching and injectivity theorems, each with every field that changes what `grind`
splits on or instantiates. Every structure and non-class inductive adds one `@[grind =]` E-matching
theorem per constructor, its `sizeOf_spec` (Meta/SizeOf.lean:470-473, Elab/MutualInductive.lean:1579-1580). -/
unsafe def decodeGrind (s : Src) (sets : List (Name × Lean.Meta.Grind.Extension)) : Array Effect := Id.run do
  let mut out : Array Effect := #[]
  for (attr, ext) in sets do
    let name := ext.ext.name.toString
    for raw in s.raw ext.ext.name do
      let e : ScopedEnvExtension.Entry Lean.Meta.Grind.Entry := unsafeCast raw
      let (scope, ns, ge) := entryScope e
      let grindSet := ("grind_set", nameJson attr)
      match ge with
      | .ext n =>
        out := out.push (s.mk' "grind" name scope ns (some n) #[n] (s.owns n) s!"grind set {attr}: ext"
          (Json.mkObj [("entry", Json.str "ext"), grindSet, ("decl", nameJson n)]))
      | .funCC n =>
        out := out.push (s.mk' "grind" name scope ns (some n) #[n] (s.owns n) s!"grind set {attr}: funCC"
          (Json.mkObj [("entry", Json.str "funCC"), grindSet, ("decl", nameJson n)]))
      | .cases n eager =>
        out := out.push (s.mk' "grind" name scope ns (some n) #[n] (s.owns n) s!"grind set {attr}: cases, eager {eager}"
          (Json.mkObj [("entry", Json.str "cases"), grindSet, ("decl", nameJson n), ("eager", Json.bool eager)]))
      | .ematch t =>
        let ks := headConsts t.symbols
        let r := s.mk' "grind" name scope ns (some t.origin.key) ks (ks.any s.owns)
          s!"grind set {attr}: ematch {reprStr t.kind}" Json.null
        out := out.push <| match grindOriginJson t.origin with
          | .ok origin => { r with payload := Json.mkObj [("entry", Json.str "ematch"), grindSet,
              ("level_params", namesJson t.levelParams), ("proof", exprJson t.proof),
              ("num_params", Lean.toJson t.numParams), ("patterns", Json.arr (t.patterns.toArray.map exprJson)),
              ("symbols", Json.arr (t.symbols.toArray.map headIndexJson)), ("origin", origin),
              ("kind", Json.str (reprStr t.kind)), ("min_indexable", Json.bool t.minIndexable),
              ("cnstrs", Json.arr (t.cnstrs.toArray.map fun c => Json.str (reprStr c)))] }
          | .error why => { r with refusal := some why }
      | .inj t =>
        let ks := headConsts t.symbols
        let r := s.mk' "grind" name scope ns (some t.origin.key) ks (ks.any s.owns)
          s!"grind set {attr}: inj" Json.null
        out := out.push <| match grindOriginJson t.origin with
          | .ok origin => { r with payload := Json.mkObj [("entry", Json.str "inj"), grindSet,
              ("level_params", namesJson t.levelParams), ("proof", exprJson t.proof),
              ("symbols", Json.arr (t.symbols.toArray.map headIndexJson)), ("origin", origin)] }
          | .error why => { r with refusal := some why }
  return out

/-- The value an own-declaration attribute map holds (`Name × α`, Attributes.lean:244 and :343),
decoded by the attribute's 4.35 type. An attribute map with no decoder here refuses
(`unknown_payload`): its value is never dropped. -/
unsafe def attrValue (ext : Name) (raw : EnvExtensionEntry) : Except String Json :=
  if ext == Linter.deprecatedAttr.ext.name then
    let d := (unsafeCast raw : Name × Linter.DeprecationEntry).2
    .ok (Json.mkObj [("new_name", optName d.newName?), ("text", optStr d.text?), ("since", optStr d.since?)])
  else if ext == Compiler.inlineAttrs.ext.name then
    .ok (Json.str (inlineString (unsafeCast raw : Name × Compiler.InlineAttributeKind).2))
  else if ext == Compiler.specializeAttr.ext.name then
    .ok (Lean.toJson (unsafeCast raw : Name × Array Nat).2)
  else if ext == Compiler.implementedByAttr.ext.name then
    .ok (nameJson (unsafeCast raw : Name × Name).2)
  else if ext == Lean.exportAttr.ext.name then
    .ok (nameJson (unsafeCast raw : Name × Name).2)
  else if ext == Lean.externAttr.ext.name then
    .ok (Json.mkObj [("entries", Json.arr ((unsafeCast raw : Name × ExternAttrData).2.entries.toArray.map externJson))])
  else if ext == Meta.recursorAttribute.ext.name then
    .ok (Lean.toJson (unsafeCast raw : Name × Nat).2)
  else .error s!"no decoder for the values of {ext}"

unsafe def decodeReviewed (s : Src) (ext : Name) (r : Reviewed) : Array Effect × Array String := Id.run do
  let mut out : Array Effect := #[]
  let mut bad : Array String := #[]
  for raw in s.raw ext do
    let target? : Option Name :=
      if r.kind == "attr_tag" || r.kind == "tag" then some (unsafeCast raw : Name)
      else if r.kind == "attr_map" || r.kind == "map" || r.kind == "decl" then some (unsafeCast raw : Name × EnvExtensionEntry).1
      else none
    if let some n := target? then
      if !s.owns n then bad := bad.push s!"not_own: {ext} in {s.mod} names {n}"
      if r.kind.startsWith "attr_" then
        let a := s.mk' "attribute" ext.toString "global" none (some n) #[n] (s.owns n)
          s!"own-declaration attribute ({r.name})" Json.null
        let value : Except String Json := if r.kind == "attr_tag" then .ok Json.null else attrValue ext raw
        out := out.push <| match value with
          | .ok v => { a with payload := Json.mkObj [("attribute", Json.str r.name), ("decl", nameJson n), ("value", v)] }
          | .error why => { a with refusal := some why }
  return (out, bad)

unsafe def decodeAll (s : Src) (k : Known) : Decoded := Id.run do
  let counts := s.entries.filterMap fun (n, es) => if es.isEmpty then none else some (n, es.size)
  let (parser, ownKinds) := decodeParser s
  -- Each field on its own line, at one column: a structure instance's later fields may not start left
  -- of its first (sepByIndent's checkColGe, Lean/Parser/Extra.lean:208-210).
  let mut d : Decoded := {
    counts := counts
    effects := decodeInstances s ++ decodeSimp s k.sets ++ decodeReducibility s ++ parser ++ decodeKeyed s ownKinds ++
      decodeCoe s ++ decodeHints s ++ decodeDefaults s ++ decodeAliases s ++ decodeClasses s ++ decodeCSimp s ++
      decodeGrind s k.grindSets }
  for (n, c) in counts do
    if k.decoded.contains n then pure ()
    else if k.scopedNames.contains n then d := { d with unknown := d.unknown.push (n, c, true) }
    else match lookupReviewed n with
      | some r =>
        let (es, bad) := decodeReviewed s n r
        d := { d with effects := d.effects ++ es, notOwn := d.notOwn ++ bad }
        if !r.kind.startsWith "attr_" then d := { d with bookkeeping := d.bookkeeping.push (n, c) }
      | none => d := { d with unknown := d.unknown.push (n, c, false) }
  -- An entry with a field that cannot be decoded soundly is refused, never listed without it.
  let unknownPayload := d.effects.filterMap fun e => e.refusal.map fun why =>
    s!"unknown_payload: {e.ext} in {s.mod} names {(e.target.map (·.toString)).getD "?"}: {why}"
  return { d with effects := d.effects.filter (·.refusal.isNone), unknownPayload }

/-! ## The environment pass -/

structure Config where
  root        : Name
  foundations : Array Name
  commit      : String
  out         : System.FilePath

def partOf (cfg : Config) (m : Name) : String :=
  if cfg.foundations.any (·.isPrefixOf m) then "foundations"
  else if cfg.root.isPrefixOf m then "edition"
  else "toolchain"

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def countBy (rs : Array Effect) (f : Effect → Option String) : Json :=
  let m := rs.foldl (fun m r => match f r with | some k => bump m k | none => m) ({} : Std.HashMap String Nat)
  Json.mkObj ((m.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, Lean.toJson v))

def notClaimed : Array String := #[
  "file-local effects (local attributes and commands, removals, activations, options, section instance variables): they never reach an .olean; piece B (d-effects-local) lists them",
  "proof-local instances: piece B",
  "agreement of the .olean with a re-elaboration of the source: piece B"]

unsafe def runEnv (fl : Flags) : IO UInt32 := do
  let cfg : Config := {
    root := (← need fl "--root").toName
    foundations := (fl.all "--foundation").map String.toName
    commit := (fl.get? "--edition-commit").getD ""
    out := System.FilePath.mk (← need fl "--out") }
  if cfg.foundations.isEmpty then throw (IO.userError "usage: give at least one --foundation")
  let k ← mkKnown
  let env ← importModules #[{ module := cfg.root }] {} (loadExts := false)
  let names := env.header.moduleNames
  -- The runtime registry: every persistent extension registered, scoped ones included
  -- (Environment.lean:1708, :1761), with how the census treats it; and any reviewed name that matches none.
  let registered := (← persistentEnvExtensionsRef.get).map (·.name)
  let registryGap := registered.filter (classify k · == "neither")
  let reviewedUnregistered := reviewed.filter fun r =>
    !registered.any fun n => (privateToUserName n).toString == r.name
  let mut reasons : Array String := #[]
  let mut effects : Array Effect := #[]
  let mut bookkeeping : Array Json := #[]
  let mut modulesJson : Array Json := #[]
  for i in [0:names.size] do
    let mod := names[i]!
    let part := partOf cfg mod
    let src : Src := { entries := (env.header.moduleData[i]!).entries, mod,
                       owns := fun n => (env.getModuleIdxFor? n).map (·.toNat) == some i }
    let total := src.entries.foldl (fun a e => a + e.2.size) 0
    if part == "toolchain" then
      modulesJson := modulesJson.push (Json.mkObj [("name", nameJson mod), ("part", Json.str part), ("entries", Lean.toJson total)])
      continue
    let d := decodeAll src k
    modulesJson := modulesJson.push (Json.mkObj [("name", nameJson mod), ("part", Json.str part),
      ("entries", Lean.toJson total), ("extensions", Json.mkObj (d.counts.toList.map fun (n, c) => (n.toString, Lean.toJson c)))])
    for (n, c, isScoped) in d.unknown do
      reasons := reasons.push s!"unknown_extension: {n} in {mod} ({c} entries{if isScoped then ", scoped" else ""})"
    for b in d.notOwn do reasons := reasons.push b
    for b in d.unknownPayload do reasons := reasons.push b
    for (n, c) in d.bookkeeping do
      bookkeeping := bookkeeping.push (Json.mkObj [("module", nameJson mod), ("extension", nameJson n),
        ("entries", Lean.toJson c), ("reason", Json.str ((lookupReviewed n).map (·.reason) |>.getD ""))])
    effects := effects ++ d.effects.map fun e => { e with part }
  let outside := effects.filter (·.outside)
  let escaping := outside.filter (·.escapes)
  let verdict := if reasons.isEmpty then "complete" else "incomplete"
  let summary := Json.mkObj [
    ("modules_walked", Lean.toJson names.size),
    ("toolchain_modules", Lean.toJson (names.filter (partOf cfg · == "toolchain")).size),
    ("foundations_modules", Lean.toJson (names.filter (partOf cfg · == "foundations")).size),
    ("edition_modules", Lean.toJson (names.filter (partOf cfg · == "edition")).size),
    ("effects", Lean.toJson effects.size),
    ("outside_foundations", Lean.toJson outside.size),
    ("escaping_outside_foundations", Lean.toJson escaping.size),
    ("own_keyed_outside_foundations", Lean.toJson (outside.filter (·.ownKeyed)).size),
    ("scoped_outside_foundations", Lean.toJson (outside.filter (·.scope == "scoped")).size),
    ("outside_by_family_and_scope", countBy outside fun r => some s!"{r.family}/{r.scope}"),
    ("escaping_by_family", countBy escaping fun r => some r.family)]
  let doc := Json.mkObj [
    ("schema", Json.str "stoicheia.effects-census.exported/1"),
    ("claim", Json.str "every exported entry of every package module, decoded with every field that changes elaboration, or the census refuses"),
    ("not_claimed", Json.arr (notClaimed.map Json.str)),
    ("lean_version", Json.str Lean.versionString), ("lean_githash", Json.str Lean.githash),
    ("root", nameJson cfg.root), ("foundations", Json.arr (cfg.foundations.map nameJson)),
    ("edition_commit", Json.str cfg.commit),
    ("reviewed", Json.arr (reviewed.map fun r => Json.mkObj [("extension", Json.str r.name), ("kind", Json.str r.kind), ("reason", Json.str r.reason)])),
    ("registry", Json.arr (registered.map fun n => Json.mkObj [("extension", nameJson n),
      ("scoped", Json.bool (k.scopedNames.contains n)), ("status", Json.str (classify k n))])),
    ("registry_gap", Json.arr (registryGap.map nameJson)),
    ("reviewed_unregistered", Json.arr (reviewedUnregistered.map fun r => Json.str r.name)),
    ("modules", Json.arr modulesJson), ("effects", Json.arr (effects.map Effect.json)),
    ("bookkeeping", Json.arr bookkeeping),
    ("summary", summary), ("verdict", Json.str verdict), ("reasons", Json.arr (reasons.map Json.str))]
  IO.FS.writeFile cfg.out doc.pretty
  IO.println s!"census: {verdict}: {names.size} modules, {effects.size} exported effects, {escaping.size} escaping outside the foundations"
  for r in reasons do IO.println s!"census: {r}"
  IO.println s!"census: registry: {registered.size} extensions registered, {registryGap.size} neither decoded nor reviewed, {reviewedUnregistered.size} reviewed names not registered"
  return (if verdict == "complete" then 0 else 1)

/-! ## Entry -/

unsafe def run (args : List String) : IO UInt32 := do
  try
    match args with
    | cmd :: rest =>
      let fl ← match parseFlags rest with
        | .ok fl => pure fl
        | .error msg => throw (IO.userError s!"usage: {msg}")
      initPath
      if cmd == "env" then runEnv fl
      else throw (IO.userError s!"usage: unknown subcommand {cmd}")
    | [] => throw (IO.userError "usage: census env --flag value ...")
  catch e =>
    let msg := toString e
    IO.eprintln s!"census: {msg}"
    return (if msg.startsWith "usage" then 2 else 3)

end Census

@[implemented_by Census.run]
opaque censusMain (args : List String) : IO UInt32

def main (args : List String) : IO UInt32 := censusMain args
