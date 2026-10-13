import Lean

/-!
# TeX statement exporter

`lake exe texexport <Root>...` loads the compiled `LRANotes` environment and,
for every user-written `theorem` and Prop-valued `def` whose module lies under
one of the given roots (default: every track), writes

* `generated/lean/<FullName>.tex`  — the statement rendered as mathematics,
  wrapped in an `lra-common` environment (`theorem` or `definition`);
* `generated/lean/<FullName>.lean` — the statement as written in the source,
  up to `:=`, for `\leanstatement*`.

The renderer emits semantic macros (`\leanReal`, `\leanpred`, `\leanvar`, …),
never raw symbols, so notation is defined once on the TeX side. Anything it
does not recognise is emitted through `\leanraw{…}` so gaps stay visible.
-/

open Lean Meta

namespace TexExport

/-! ## Text helpers -/

/-- Escape a string for use in TeX text or `\operatorname`. -/
def escapeTeX (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '_' => acc ++ "\\_"
    | '#' => acc ++ "\\#"
    | '%' => acc ++ "\\%"
    | '&' => acc ++ "\\&"
    | '$' => acc ++ "\\$"
    | '{' => acc ++ "\\{"
    | '}' => acc ++ "\\}"
    | '\\' => acc ++ "\\textbackslash{}"
    | '^' => acc ++ "\\textasciicircum{}"
    | '~' => acc ++ "\\textasciitilde{}"
    | c => acc.push c

def greek : List (Char × String) :=
  [('α', "\\alpha"), ('β', "\\beta"), ('γ', "\\gamma"), ('δ', "\\delta"),
   ('ε', "\\varepsilon"), ('ζ', "\\zeta"), ('η', "\\eta"), ('θ', "\\theta"),
   ('λ', "\\lambda"), ('μ', "\\mu"), ('ν', "\\nu"), ('ξ', "\\xi"),
   ('π', "\\pi"), ('ρ', "\\rho"), ('σ', "\\sigma"), ('τ', "\\tau"),
   ('φ', "\\varphi"), ('χ', "\\chi"), ('ψ', "\\psi"), ('ω', "\\omega")]

def subscriptDigit? (c : Char) : Option Char :=
  let n := c.toNat
  if 0x2080 ≤ n ∧ n ≤ 0x2089 then some (Char.ofNat (n - 0x2080 + '0'.toNat)) else none

/-- Render a bound-variable name. Single letters (optionally followed by digits
or primes) are typeset as math italics; longer names go through `\leanvar`. -/
def renderVarName (n : Name) : String := Id.run do
  let raw := n.eraseMacroScopes.toString.replace "✝" ""
  let chars := raw.toList
  match chars with
  | [] => return "\\leanvar{x}"
  | c :: rest =>
    let digits := rest.filterMap fun d => if d.isDigit then some d else subscriptDigit? d
    let primes := rest.filter (· == '\'')
    if digits.length + primes.length == rest.length then
      let base := match greek.lookup c with
        | some g => g
        | none => if c.isAlpha then c.toString else "\\leanvar{" ++ escapeTeX c.toString ++ "}"
      let sub := if digits.isEmpty then "" else "_{" ++ String.ofList digits ++ "}"
      let pr := if primes.isEmpty then "" else String.ofList primes
      return base ++ sub ++ pr
    else
      return "\\leanvar{" ++ escapeTeX raw ++ "}"

/-- `ZeroUniqueInReals` ↦ `Zero Unique In Reals`; `add_zero_right` ↦ `add zero right`. -/
def humanize (s : String) : String := Id.run do
  let mut out := ""
  let mut prevLower := false
  for c in s.toList do
    if c == '_' then
      out := out.push ' '; prevLower := false
    else
      if c.isUpper && prevLower then out := out.push ' '
      out := out.push c
      prevLower := c.isLower || c.isDigit
  return out

/-! ## Expression renderer

Each case returns the TeX string and its precedence; a child is parenthesised
when its precedence is lower than its context requires. -/

abbrev Rendered := String × Nat

def precAtom : Nat := 100
def precApp : Nat := 90
def precMul : Nat := 70
def precAdd : Nat := 65
def precRel : Nat := 50
def precNot : Nat := 40
def precAnd : Nat := 35
def precOr : Nat := 30
def precImp : Nat := 25
def precIff : Nat := 20
def precQuant : Nat := 10

def paren (r : Rendered) (need : Nat) : String :=
  if r.2 < need then "\\left(" ++ r.1 ++ "\\right)" else r.1

/-- Number systems, keyed by constant name. The macros are defined from the
`lra-governance` notation registry by `scripts/notation_macros.py`. -/
def numberSystems : List (Name × String) :=
  [(``Nat, "\\leanNat"), (``Int, "\\leanInt"), (`Rat, "\\leanRat"),
   (`Real, "\\leanReal"), (`Complex, "\\leanComplex")]

def binRel : List (Name × String) :=
  [(``Eq, "="), (``Ne, "\\neq"), (``LE.le, "\\le"), (``LT.lt, "<"),
   (``GE.ge, "\\ge"), (``GT.gt, ">")]

def raw (e : Expr) : MetaM Rendered := do
  let fmt ← ppExpr e
  return ("\\leanraw{" ++ escapeTeX (toString fmt) ++ "}", precAtom)

/-- Explicit arguments of an application, according to the function's binder info. -/
def explicitArgs (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let info ← getFunInfoNArgs f args.size
  let mut out := #[]
  for i in [:args.size] do
    let explicit := match info.paramInfo[i]? with
      | some p => p.binderInfo.isExplicit
      | none => true
    if explicit then out := out.push args[i]!
  return out

mutual

partial def render (e : Expr) : MetaM Rendered := do
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => return (toString n, precAtom)
  | .lit (.strVal s) => return ("\\text{``" ++ escapeTeX s ++ "''}", precAtom)
  | .sort .zero => return ("\\mathrm{Prop}", precAtom)
  | .sort _ => return ("\\mathrm{Type}", precAtom)
  | .fvar id => return (renderVarName (← id.getUserName), precAtom)
  | .forallE .. => renderForall e
  | .lam .. => renderLambda e
  | .app .. | .const .. => renderApp e
  | _ => raw e

/-- `∀` and implication. Consecutive binders over the same domain are merged:
`∀ x y : ℝ, P` ↦ `∀ x, y ∈ ℝ (P)`. -/
partial def renderForall (e : Expr) : MetaM Rendered := do
  let .forallE _ t b _ := e | raw e
  if !b.hasLooseBVars && (← isProp t) then
    let lhs ← render t
    let rhs ← render b
    return (paren lhs (precImp + 1) ++ " \\rightarrow " ++ paren rhs precImp, precImp)
  forallBoundedTelescope e (some 1) fun xs body => do
    let some x := xs[0]? | raw e
    gatherForall t #[renderVarName (← x.fvarId!.getUserName)] body

/-- Absorb further `∀` binders over the same domain, then render the body. -/
partial def gatherForall (t : Expr) (names : Array String) (body : Expr) : MetaM Rendered := do
  match body.consumeMData with
  | .forallE _ t' b' _ =>
    if b'.hasLooseBVars && t' == t then
      forallBoundedTelescope body (some 1) fun ys rest => do
        let some y := ys[0]? | raw body
        gatherForall t (names.push (renderVarName (← y.fvarId!.getUserName))) rest
    else finishForall t names body
  | _ => finishForall t names body

partial def finishForall (t : Expr) (names : Array String) (body : Expr) : MetaM Rendered := do
  let dom ← renderDomain t
  let inner ← render body
  return ("\\forall " ++ ", ".intercalate names.toList ++ dom ++ "\\,"
    ++ "\\left(" ++ inner.1 ++ "\\right)", precQuant)

/-- How a quantified variable's domain is written: `∈ ℝ` for types, `⊆ X` for
sets of `X`, `\colon A → B` for functions. -/
partial def renderDomain (t : Expr) : MetaM String := do
  let t := t.consumeMData
  if t.isAppOfArity `Set 1 then
    return " \\subseteq " ++ (← render t.appArg!).1
  if t.isForall then
    if ← isRelationType t then
      return " \\subseteq " ++ (← renderFunDomains t)
    return " \\colon " ++ (← renderFunType t)
  if (← isProp t) then
    return " \\colon " ++ (← render t).1
  return " \\in " ++ paren (← render t) precApp

/-- `R → R → R` ↦ `R × R → R`; `R → R → Prop` ↦ `R × R → Prop`. -/
partial def renderFunType (t : Expr) : MetaM String := do
  let rec go (t : Expr) (doms : Array String) : MetaM String := do
    match t.consumeMData with
    | .forallE _ d b _ =>
      if b.hasLooseBVars then return (← raw t).1
      go b (doms.push (paren (← render d) precApp))
    | cod =>
      return " \\times ".intercalate doms.toList ++ " \\to " ++ (← render cod).1
  go t #[]

/-- A curried predicate `A → B → Prop` is a relation. -/
partial def isRelationType (t : Expr) : MetaM Bool := do
  match t.consumeMData with
  | .forallE _ _ b _ => if b.hasLooseBVars then return false else isRelationType b
  | cod => return cod.isProp

/-- `A → B → Prop` ↦ `A × B`. -/
partial def renderFunDomains (t : Expr) : MetaM String := do
  let rec go (t : Expr) (doms : Array String) : MetaM String := do
    match t.consumeMData with
    | .forallE _ d b _ => go b (doms.push (paren (← render d) precApp))
    | _ => return " \\times ".intercalate doms.toList
  go t #[]

partial def renderLambda (e : Expr) : MetaM Rendered :=
  lambdaBoundedTelescope e 1 fun xs body => do
    let some x := xs[0]? | raw e
    let n := renderVarName (← x.fvarId!.getUserName)
    let b ← render body
    return (n ++ " \\mapsto " ++ b.1, precQuant)

partial def renderExists (body : Expr) : MetaM Rendered := do
  -- `Exists (fun x => p)` with the lambda as the body
  match body.consumeMData with
  | .lam n t _ _ =>
    lambdaBoundedTelescope body 1 fun _ inner => do
      let dom ← renderDomain t
      let r ← render inner
      return ("\\exists " ++ renderVarName n ++ dom ++ "\\,\\left(" ++ r.1 ++ "\\right)",
        precQuant)
  | _ => raw body

partial def renderApp (e : Expr) : MetaM Rendered := do
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    -- number systems and types
    if let some m := numberSystems.lookup c then
      if args.isEmpty then return (m, precAtom)
    if c == ``True then return ("\\top", precAtom)
    if c == ``False then return ("\\bot", precAtom)
    -- logical connectives
    if c == ``Not && args.size == 1 then
      let a ← render args[0]!
      return ("\\lnot " ++ paren a precNot, precNot)
    if c == ``And && args.size == 2 then
      let a ← render args[0]!; let b ← render args[1]!
      return (paren a (precAnd + 1) ++ " \\land " ++ paren b precAnd, precAnd)
    if c == ``Or && args.size == 2 then
      let a ← render args[0]!; let b ← render args[1]!
      return (paren a (precOr + 1) ++ " \\lor " ++ paren b precOr, precOr)
    if c == ``Iff && args.size == 2 then
      let a ← render args[0]!; let b ← render args[1]!
      return (paren a (precIff + 1) ++ " \\leftrightarrow " ++ paren b (precIff + 1), precIff)
    if c == ``Exists && args.size == 2 then
      return ← renderExists args[1]!
    -- relations
    if let some op := binRel.lookup c then
      if args.size ≥ 2 then
        let a ← render args[args.size - 2]!; let b ← render args[args.size - 1]!
        return (paren a (precRel + 1) ++ " " ++ op ++ " " ++ paren b (precRel + 1), precRel)
    if c == ``Membership.mem && args.size == 5 then
      -- `Membership.mem (γ := coll) a` takes the collection first
      let coll ← render args[3]!; let a ← render args[4]!
      return (paren a (precRel + 1) ++ " \\in " ++ paren coll (precRel + 1), precRel)
    -- arithmetic
    if c == ``HAdd.hAdd && args.size == 6 then
      let a ← render args[4]!; let b ← render args[5]!
      return (paren a precAdd ++ " + " ++ paren b (precAdd + 1), precAdd)
    if c == ``HSub.hSub && args.size == 6 then
      let a ← render args[4]!; let b ← render args[5]!
      return (paren a precAdd ++ " - " ++ paren b (precAdd + 1), precAdd)
    if c == ``HMul.hMul && args.size == 6 then
      let a ← render args[4]!; let b ← render args[5]!
      let sep := if a.2 == precAtom && b.2 == precAtom then " " else " \\cdot "
      return (paren a precMul ++ sep ++ paren b (precMul + 1), precMul)
    if c == ``HDiv.hDiv && args.size == 6 then
      let a ← render args[4]!; let b ← render args[5]!
      return ("\\frac{" ++ a.1 ++ "}{" ++ b.1 ++ "}", precAtom)
    if c == ``HPow.hPow && args.size == 6 then
      let a ← render args[4]!; let b ← render args[5]!
      return (paren a precAtom ++ "^{" ++ b.1 ++ "}", precApp)
    if c == ``Neg.neg && args.size == 3 then
      let a ← render args[2]!
      return ("-" ++ paren a precMul, precAdd)
    if c == ``OfNat.ofNat && args.size == 3 then
      return ← render args[1]!
    if c == ``Zero.zero then return ("0", precAtom)
    if c == ``One.one then return ("1", precAtom)
    if c == `Set && args.size == 1 then
      let a ← render args[0]!
      return ("\\mathcal{P}\\left(" ++ a.1 ++ "\\right)", precAtom)
    -- coercions are invisible in mathematical writing
    if let some info ← getCoeFnInfo? c then
      if info.numArgs == args.size then
        return ← render args[info.coercee]!
    -- structure projections: `O.le x y` ↦ `le_O(x, y)`
    if let some proj ← getProjectionFnInfo? c then
      if args.size > proj.numParams then
        let s ← render args[proj.numParams]!
        let rest := args.extract (proj.numParams + 1) args.size
        let field := "\\leanvar{" ++ escapeTeX c.getString! ++ "}_{" ++ s.1 ++ "}"
        let projApp := mkAppN fn (args.extract 0 (proj.numParams + 1))
        if rest.size == 2 && (← isRelationType (← inferType projApp)) then
          return ← relInfix field rest[0]! rest[1]!
        return ← applyTo field rest
    -- any other named constant: a type, or a predicate or function of the library
    let ex ← explicitArgs fn args
    -- a type is a term whose type is `Sort u` with `u ≠ 0`; propositions are not types
    let isType := match (← whnfR (← inferType e)) with
      | .sort l => !l.isZero
      | _ => false
    let head := (if isType then "\\leantype{" else "\\leanpred{") ++ escapeTeX c.getString! ++ "}"
    applyTo head ex
  | .fvar id =>
    let head := renderVarName (← id.getUserName)
    if args.size == 2 && (← isRelationType (← id.getType)) then
      return ← relInfix head args[0]! args[1]!
    applyTo head args
  | _ => raw e

/-- A relation symbol written between its arguments: `x \mathrel{le} y`. -/
partial def relInfix (rel : String) (a b : Expr) : MetaM Rendered := do
  let ra ← render a; let rb ← render b
  return (paren ra (precRel + 1) ++ " \\mathrel{" ++ rel ++ "} " ++ paren rb (precRel + 1), precRel)

partial def applyTo (head : String) (args : Array Expr) : MetaM Rendered := do
  if args.isEmpty then return (head, precAtom)
  let rs ← args.mapM fun a => do return (← render a).1
  return (head ++ "\\left(" ++ ", ".intercalate rs.toList ++ "\\right)", precApp)

end

/-! ## Statements -/

/-- A leading binder of a declaration, classified for the "Let … Suppose …" lines. -/
inductive Binder where
  | type (name : String)
  | data (name : String) (domain : String)
  | hyp (stmt : String)

def classify (x : Expr) : MetaM (Option Binder) := do
  let ld ← x.fvarId!.getDecl
  if ld.binderInfo.isInstImplicit then return none
  let t ← instantiateMVars ld.type
  if t.isSort then return some (.type (renderVarName ld.userName))
  if (← isProp t) then return some (.hyp (← render t).1)
  return some (.data (renderVarName ld.userName) (← renderDomain t))

/-- `Let $R$ be a set, $x, y \in \leanReal$, … . Suppose $…$ and $…$.` -/
def letLines (bs : Array Binder) : String := Id.run do
  let mut types := #[]
  let mut groups : Array (String × Array String) := #[]
  let mut hyps := #[]
  for b in bs do
    match b with
    | .type n => types := types.push n
    | .data n d =>
      match groups.back? with
      | some (d', ns) =>
        if d' == d then groups := groups.pop.push (d, ns.push n)
        else groups := groups.push (d, #[n])
      | none => groups := groups.push (d, #[n])
    | .hyp s => hyps := hyps.push s
  let mut clauses := #[]
  if !types.isEmpty then
    let ts := ", ".intercalate (types.toList.map fun t => "$" ++ t ++ "$")
    clauses := clauses.push (ts ++ (if types.size == 1 then " be a set" else " be sets"))
  for (d, ns) in groups do
    clauses := clauses.push ("$" ++ ", ".intercalate ns.toList ++ d ++ "$")
  let mut out := ""
  if !clauses.isEmpty then
    out := "Let " ++ ", ".intercalate clauses.toList ++ ".\n"
  if !hyps.isEmpty then
    let hs := hyps.toList.map fun h => "$" ++ h ++ "$"
    out := out ++ "Suppose " ++ " and ".intercalate hs ++ ".\n"
  return out

/-- Short formulas stay inline; quantified or long ones are displayed. -/
def formula (s : String) (lead : String) : String :=
  if s.length > 60 || (s.splitOn "\\forall").length > 1 || (s.splitOn "\\exists").length > 1 then
    lead ++ "\n\\[\n  " ++ s ++ "\n\\]\n"
  else
    lead ++ " $" ++ s ++ "$.\n"

def envFor (kind title label body : String) : String :=
  "\\begin{" ++ kind ++ "}[" ++ title ++ "]\\label{" ++ label ++ "}\n" ++ body
    ++ "\\end{" ++ kind ++ "}\n"

def renderTheorem (name : Name) (type : Expr) (unproved : Bool) : MetaM String :=
  forallTelescope type fun xs concl => do
    let bs ← xs.filterMapM classify
    let c ← render concl
    let lead := if bs.isEmpty then "" else letLines bs
    let stmt := if bs.isEmpty then "\\[\n  " ++ c.1 ++ "\n\\]\n"
      else formula c.1 (lead ++ "Then")
    let stmt := if unproved then stmt ++ "\\leanunproved\n" else stmt
    return envFor "theorem" (humanize name.getString!) ("lean:" ++ name.toString) stmt

def renderDef (name : Name) (type value : Expr) : MetaM (Option String) := do
  let arity := (← forallTelescope type fun xs _ => pure xs.size)
  lambdaBoundedTelescope value arity fun xs body => do
    if xs.size != arity then return none
    let resTy ← inferType body
    let bs ← xs.filterMapM classify
    let explicit ← xs.filterM fun x => do
      return (← x.fvarId!.getDecl).binderInfo.isExplicit
    let ex ← explicit.mapM fun x => do return (← render x).1
    let head := "\\leanpred{" ++ escapeTeX name.getString! ++ "}" ++
      (if ex.isEmpty then "" else "\\left(" ++ ", ".intercalate ex.toList ++ "\\right)")
    let rhs ← render body
    let sep := if (← whnfR resTy).isProp then "\\coloniff" else "\\coloneqq"
    let lead := letLines (bs.filter fun | .hyp _ => false | _ => true)
    let stmt := lead ++ (if lead.isEmpty then "" else "Define\n") ++
      "\\leandefinition{" ++ head ++ "}{" ++ sep ++ "}{" ++ rhs.1 ++ "}\n"
    return some (envFor "definition" (humanize name.getString!) ("lean:" ++ name.toString) stmt)

/-! ## Selection and output -/

def skipModules : List Name :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
   `LeanSearchClient, `ImportGraph, `Common, `LRANotes, `Lake, `Tools]

/-- Declarations generated for an inductive or structure live under its name
(`S.mk.inj`, `S.mk.sizeOf_spec`, …); a user declaration never does. -/
def underInductive (env : Environment) : Name → Bool
  | .anonymous => false
  | n@(.str p _) | n@(.num p _) =>
    (match env.find? n with
      | some (.inductInfo _) | some (.ctorInfo _) => true
      | _ => false) || underInductive env p

def isUserDecl (env : Environment) (n : Name) : Bool :=
  !n.isInternalDetail && !isAuxRecursor env n && !isNoConfusion env n &&
  !(env.isProjectionFn n) && !(underInductive env n.getPrefix) &&
  !(n.getPrefix.isAnonymous) &&
  !(Lean.Meta.isInstanceCore env n) && !(Lean.Meta.isMatcherCore env n)

/-- The source text of a declaration's statement, up to its `:=`. -/
def sourceStatement (path : System.FilePath) (r : DeclarationRanges) : IO (Option String) := do
  unless ← path.pathExists do return none
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let start := r.range.pos.line - 1
  let stop := r.range.endPos.line
  let chunk := "\n".intercalate ((lines.drop start).take (stop - start))
  match chunk.splitOn ":=" with
  | head :: _ :: _ => return some head.trimAsciiEnd.toString
  | _ => return some chunk.trimAsciiEnd.toString

end TexExport

open TexExport in
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LRANotes }] {} (loadExts := true)
  let roots : List Name := args.map String.toName
  let outDir : System.FilePath := "generated" / "lean"
  IO.FS.createDirAll outDir
  let ctx : Core.Context := { fileName := "<texexport>", fileMap := default,
                              maxHeartbeats := 0 }
  let mut count := 0
  let mut failed := 0
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let root := mod.getRoot
    if skipModules.contains root then continue
    if !roots.isEmpty && !roots.contains root then continue
    if !isUserDecl env n then continue
    let act : MetaM (Option String) := do
      match ci with
      | .thmInfo t => return some (← renderTheorem n t.type t.value.hasSorry)
      | .defnInfo d => renderDef n d.type d.value
      | _ => return none
    let res ← (act.run' {} {}).toIO ctx { env := env } |>.toBaseIO
    match res with
    | .error e =>
      failed := failed + 1
      IO.eprintln s!"texexport: {n}: {e}"
    | .ok (none, _) => pure ()
    | .ok (some tex, _) =>
      IO.FS.writeFile (outDir / (n.toString ++ ".tex")) tex
      let ranges? ← (findDeclarationRanges? n : CoreM _).toIO ctx { env := env }
      if let (some r, _) := ranges? then
        let path : System.FilePath :=
          (mod.components.map Name.toString |> System.mkFilePath).addExtension "lean"
        if let some src ← sourceStatement path r then
          IO.FS.writeFile (outDir / (n.toString ++ ".lean")) (src ++ "\n")
      count := count + 1
  IO.println s!"texexport: wrote {count} declaration(s) to {outDir}; {failed} failed"
  return if failed == 0 then 0 else 1
