/-
  Basic dependency graph extractor for Lean projects.

  Usage:
    lake exe depviz --roots My.Project.Root --dot-out deps.dot --svg-out deps.svg
-/
import Lean
import Std.Data.HashSet

open Lean

namespace DepViz

structure Node where
  name          : Name
  moduleName    : String
  kind          : String
  isUnsafe      : Bool
  hasSorry      : Bool
  noncomp       : Bool
  axioms        : Array Name
  deriving Inhabited

structure Edge where
  source : Name
  target : Name
  kind   : String -- "type" or "value"
  deriving Inhabited

structure Graph where
  nodes : Array Node
  edges : Array Edge
  deriving Inhabited

private def ppName (n : Name) : String :=
  n.toString

private def moduleOf (env : Environment) (decl : Name) : String :=
  match env.getModuleIdxFor? decl with
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | some m => ppName m
      | none => "_unknown_"
  | none => "_unknown_"

private def nameFromString (s : String) : Name :=
  (s.split (· = '.')).foldl (init := Name.anonymous) fun acc part =>
    let part := part.trim
    if part.isEmpty then acc else Name.str acc part

private def constKind : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "def"
  | .thmInfo _     => "thm"
  | .opaqueInfo _  => "opaque"
  | .quotInfo _    => "quot"
  | .ctorInfo _    => "ctor"
  | .recInfo _     => "rec"
  | .inductInfo _  => "inductive"

private def usedConsts (e : Expr) : Array Name :=
  e.getUsedConstants

private def isAxiomConst (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.axiomInfo _) => true
  | _ => false

private def noncompLike (env : Environment) (ci : ConstantInfo) : Bool :=
  match ci.value? (allowOpaque := true) with
  | some v =>
      let axioms := (usedConsts v).filter (isAxiomConst env)
      !axioms.isEmpty
  | none => false

private def gatherNode (env : Environment) (name : Name) (ci : ConstantInfo) : Node × Array Edge :=
  let typeUses := usedConsts ci.type
  let valueUses :=
    match ci.value? (allowOpaque := true) with
    | some v => usedConsts v
    | none => #[]
  let hasSorry :=
    let inType := ci.type.hasSorry
    let inValue :=
      match ci.value? (allowOpaque := true) with
      | some v => v.hasSorry
      | none => false
    inType || inValue
  let axiomsSet :=
    (typeUses ++ valueUses).foldl (init := Std.HashSet.emptyWithCapacity) fun s nm =>
      if isAxiomConst env nm then s.insert nm else s
  let node : Node := {
    name := name
    moduleName := moduleOf env name
    kind := constKind ci
    isUnsafe := ci.isUnsafe
    hasSorry := hasSorry
    noncomp := noncompLike env ci
    axioms := (axiomsSet.toList.toArray)
  }
  let mkEdges (deps : Array Name) (kind : String) : Array Edge :=
    deps.map fun dep => { source := dep, target := name, kind := kind }
  let edges := mkEdges typeUses "type" ++ mkEdges valueUses "value"
  (node, edges)

private def buildGraph (env : Environment) : Graph :=
  Id.run do
    let mut nodes := Array.mkEmpty 1024
    let mut edges := Array.mkEmpty 4096
    for (name, info) in env.constants.map₁ do
      if !name.isInternalDetail then
        let (node, es) := gatherNode env name info
        nodes := nodes.push node
        edges := edges ++ es
    pure { nodes := nodes, edges := edges }

private def escape (s : String) : String :=
  s.replace "\"" "\\\""

private def nodeLabel (n : Node) : String :=
  let base :=
    match n.name.components.reverse with
    | [] => ppName n.name
    | hd :: _ => hd.toString
  let tags :=
    let tags := (#[] : Array String)
    let tags := if n.hasSorry then tags.push "SORRY" else tags
    let tags := if !n.axioms.isEmpty then tags.push "AXIOM" else tags
    let tags := if n.isUnsafe then tags.push "UNSAFE" else tags
    let tags := if n.noncomp then tags.push "NONCOMP" else tags
    tags
  let extra :=
    if tags.isEmpty then
      ""
    else
      "\\n" ++ String.intercalate ", " tags.toList
  base ++ extra

private def colorFor (n : Node) : String × String :=
  if n.hasSorry then ("#d33", "filled")
  else if !n.axioms.isEmpty then ("#e6972b", "filled")
  else if n.isUnsafe then ("#555", "filled")
  else if n.noncomp then ("#777", "filled,diagonals")
  else ("#bbbbbb", "filled")

private def edgeStyle (e : Edge) : String :=
  match e.kind with
  | "type" => "dashed"
  | _ => "solid"

private def graphToDot (g : Graph) : String :=
  let header := #[
    "digraph DepViz {",
    "  rankdir=LR;",
    "  node [shape=ellipse, fontsize=10, fontname=\"Helvetica\"];",
    "  edge [arrowsize=0.8];"
  ]
  let nodeLines :=
    g.nodes.map fun n =>
      let (color, style) := colorFor n
      let label := escape (nodeLabel n)
      let name := escape (ppName n.name)
      s!"  \"{name}\" [label=\"{label}\", color=\"{color}\", style=\"{style}\", tooltip=\"{escape n.moduleName}\"];"
  let edgeLines :=
    g.edges.map fun e =>
      let src := escape (ppName e.source)
      let dst := escape (ppName e.target)
      let style := edgeStyle e
      let label := if e.kind = "type" then "type" else "value"
      s!"  \"{src}\" -> \"{dst}\" [style=\"{style}\", label=\"{label}\", fontsize=8];"
  let lines := (header ++ nodeLines ++ edgeLines).push "}"
  String.intercalate "\n" lines.toList

structure Options where
  roots         : Array Name
  dotOut        : String := "depgraph.dot"
  svgOut?       : Option String := none
  pngOut?       : Option String := none
  includePrefixes : Array String := #[]
  keepAll       : Bool := false
  deriving Inhabited

private partial def parseArgsAux : Options → List String → IO Options
  | opts, [] =>
      if opts.roots.isEmpty then
        throw <| IO.userError "missing --roots argument"
      else
        pure opts
  | opts, arg :: rest =>
      match arg with
      | "--roots" =>
          match rest with
          | roots :: rest' => do
              let names := roots.splitOn "," |>.map String.trim |>.filter (· ≠ "")
              if names.isEmpty then
                throw <| IO.userError "expected at least one module after --roots"
              let roots := names.map nameFromString |>.toArray
              parseArgsAux { opts with roots } rest'
          | [] => throw <| IO.userError "--roots expects a comma separated list"
      | "--dot-out" =>
          match rest with
          | path :: rest' => parseArgsAux { opts with dotOut := path } rest'
          | [] => throw <| IO.userError "--dot-out expects a path"
      | "--svg-out" =>
          match rest with
          | path :: rest' => parseArgsAux { opts with svgOut? := some path } rest'
          | [] => throw <| IO.userError "--svg-out expects a path"
      | "--png-out" =>
          match rest with
          | path :: rest' => parseArgsAux { opts with pngOut? := some path } rest'
          | [] => throw <| IO.userError "--png-out expects a path"
      | "--include-prefix" =>
          match rest with
          | pref :: rest' =>
              let prefixes := pref.splitOn "," |>.map String.trim |>.filter (· ≠ "")
              parseArgsAux { opts with includePrefixes := opts.includePrefixes ++ prefixes.toArray } rest'
          | [] => throw <| IO.userError "--include-prefix expects a comma separated list"
      | "--keep-all" =>
          parseArgsAux { opts with keepAll := true } rest
      | "--help" =>
          throw <| IO.userError "usage: lake exe depviz --roots Foo.Bar [--dot-out depgraph.dot] [--svg-out out.svg] [--png-out out.png]\n  [--include-prefix Mod1,Mod2] [--keep-all]"
      | other =>
          throw <| IO.userError s!"unknown option: {other}"

private def parseArgs (args : List String) : IO Options :=
  parseArgsAux default args

private def rootsToPrefixes (roots : Array Name) : Array String :=
  roots.map fun n =>
    let root := n.getRoot
    root.toString

private def filterGraph (g : Graph) (opts : Options) : Graph :=
  if opts.keepAll then
    g
  else
    let prefixes := rootsToPrefixes opts.roots ++ opts.includePrefixes
    let allow (module : String) : Bool :=
      prefixes.any fun pref => module.startsWith pref
    let nodes := g.nodes.filter fun n => allow n.moduleName
    let keepNames := nodes.foldl (init := Std.HashSet.emptyWithCapacity) fun acc n => acc.insert n.name
    let edges := g.edges.filter fun e => keepNames.contains e.source && keepNames.contains e.target
    { nodes, edges }

private def renderWithGraphviz (dotPath : String) (format : String) (outPath : String) : IO Unit := do
  let args := #["-T" ++ format, dotPath, "-o", outPath]
  let proc ← IO.Process.spawn { cmd := "dot", args }
  let exitCode ← proc.wait
  if exitCode != 0 then
    throw <| IO.userError s!"dot exited with status {exitCode}"

private def renderOutputs (dotPath : String) (opts : Options) : IO Unit := do
  if let some out := opts.svgOut? then
    try
      renderWithGraphviz dotPath "svg" out
    catch e =>
      IO.eprintln s!"warning: failed to render SVG via Graphviz: {e.toString}"
  if let some out := opts.pngOut? then
    try
      renderWithGraphviz dotPath "png" out
    catch e =>
      IO.eprintln s!"warning: failed to render PNG via Graphviz: {e.toString}"

def run (opts : Options) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let imports := opts.roots.map fun n => { module := n }
  let env ← Lean.importModules imports {} 0
  let graph := filterGraph (buildGraph env) opts
  let dot := graphToDot graph
  IO.FS.writeFile opts.dotOut dot
  IO.println s!"wrote DOT: {opts.dotOut}"
  renderOutputs opts.dotOut opts

def cliMain (args : List String) : IO UInt32 := do
  try
    let opts ← parseArgs args
    run opts
    return 0
  catch e =>
    IO.eprintln e.toString
    return 1

end DepViz

def main (args : List String) : IO UInt32 :=
  DepViz.cliMain args
