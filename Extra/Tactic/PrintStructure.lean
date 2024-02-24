import Std

open Lean Elab Command

/--
The command `#print structure foo` will print information about the structure `foo`.
-/
syntax (name := printStructure) "#print" "structure" ident : command

/--
Implementation for #print structure
-/
@[command_elab printStructure] def elabPrintStructure : CommandElab
| `(#print structure%$tk $id:ident) =>
  liftTermElabM do
    if let [name] ← resolveGlobalConst id then
      let env ← getEnv
      match getStructureInfo? env name with
      | none => throwErrorAt tk "expected structure"
      | some {structName, fieldNames, ..} =>
        let indInfo ← getConstInfoInduct structName
        let [ctorName] := indInfo.ctors | failure
        let ctorInfo ← getConstInfoCtor ctorName
        let levels := if indInfo.levelParams = [] then "" else
          ".{" ++ ", ".intercalate (indInfo.levelParams.map Name.toString) ++ "}"
        let mut msg := s!"structure {structName}{levels} : {← Meta.ppExpr indInfo.type}\n"
        msg := msg ++ s!"number of parameters: {indInfo.numParams}\n"
        msg := msg ++ s!"constructor:\n{ctorName} : {← Meta.ppExpr ctorInfo.type}\n"
        msg := msg ++ s!"projections:\n"
        for fieldName in fieldNames do
          let projInfo ← getConstInfo (structName ++ fieldName)
          msg := msg ++ s!"{structName ++ fieldName} : {← Meta.ppExpr projInfo.type}\n"
        logInfoAt tk msg
| _ => throwUnsupportedSyntax
