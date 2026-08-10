import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492268349137722, 362492376664238711⟩, ⟨(-604862757336256370), (-598660803884396710)⟩, true⟩

def state01 : KState := ⟨⟨362482392193134791, 362482500534757281⟩, ⟨232634742391691796, 238838945004923760⟩, true⟩

def words00 : List Nat := [371285317142705728, 371285317145651287, 371285317080015312, 371285317112625436, 371285317151377525, 371285317154323120, 371285317007884104, 371285316859174595, 371285316709243171, 371285316699655347]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472718788596092, 362472827156757590⟩, ⟨1053147817801026592, 1059354271318503056⟩, true⟩

def words01 : List Nat := [371285316774195710, 371285316883182092, 371285316975062666, 371285316978008740, 371285316884465786, 371285316834961131, 371285316852148163, 371285316855094312, 371285316740375846, 371285316596410013]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490167358712863, 362490275753225947⟩, ⟨(-426922189041230994), (-420713500247959860)⟩, true⟩

def words02 : List Nat := [371285316451176985, 371285316377394380, 371285316240982666, 371285316234636528, 371285316227379218, 371285316207589239, 371285316110294949, 371285316133588152, 371285316260596807, 371285316322118829]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490212467537333, 362490320888979093⟩, ⟨(-430753176649521671), (-424542203365274623)⟩, true⟩

def words03 : List Nat := [371285316382705058, 371285316444349061, 371285316562261868, 371285316612674781, 371285316689063422, 371285316766547782, 371285316842995357, 371285316845956407, 371285316851722453, 371285316914445964]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473440001913279, 362473548449568232⟩, ⟨992335508547443437, 998548705896969401⟩, true⟩

def words04 : List Nat := [371285317083337955, 371285317086924607, 371285317089163111, 371285317065711976, 371285317045594350, 371285317048842488, 371285316993509735, 371285316945813087, 371285316897083147, 371285316849166311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk848A
