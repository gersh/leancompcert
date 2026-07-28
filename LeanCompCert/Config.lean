import LeanCompCert.C.Profile

namespace LeanCompCert

inductive RuntimeMode where
  | hybrid
  | compcert
  | strict
  deriving Repr, BEq, DecidableEq, Inhabited

def RuntimeMode.toString : RuntimeMode → String
  | .hybrid => "hybrid"
  | .compcert => "compcert"
  | .strict => "strict"

def RuntimeMode.parse? : String → Option RuntimeMode
  | "hybrid" => some .hybrid
  | "compcert" => some .compcert
  | "strict" => some .strict
  | _ => none

inductive OptLevel where
  | zero | one | two
  deriving Repr, BEq, DecidableEq, Inhabited

def OptLevel.toString : OptLevel → String
  | .zero => "0"
  | .one => "1"
  | .two => "2"

structure Config where
  ccomp : String := "ccomp"
  target : Option String := none
  profile : C.Profile := .portable
  runtime : RuntimeMode := .hybrid
  emitCDir : Option String := none
  emitLoweredIRDir : Option String := none
  keepTemporaries : Bool := false
  debugSymbols : Bool := false
  optLevel : OptLevel := .one
  differentialCheck : Bool := false
  rejectUnsafe : Bool := false
  experimentalCompiler : Bool := false
  reportFile : Option String := none
  deriving Repr, BEq, Inhabited

def Config.validate (config : Config) : Array String := Id.run do
  let mut errors := #[]
  if config.ccomp.isEmpty then
    errors := errors.push "ccomp path must not be empty"
  if config.runtime == .strict && config.profile != .strict then
    errors := errors.push "strict runtime mode requires the strict generated-C profile"
  if config.profile == .strict && config.runtime != .strict then
    errors := errors.push "strict generated-C profile requires the strict runtime mode"
  return errors

end LeanCompCert
