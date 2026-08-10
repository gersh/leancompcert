import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636A

def state06 : KState := ⟨⟨362496051891456444, 362496111589689974⟩, ⟨(-683729310220608342), (-681162384261282338)⟩, true⟩

def words05 : List Nat := [371285410599584290, 371285410634849658, 371285410880154222, 371285411008048664, 371285411183860052, 371285411360512597, 371285411488085792, 371285411490286957, 371285411580998775, 371285411751731707]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480120236988990, 362480179954491598⟩, ⟨330557267615433291, 333125420344123101⟩, true⟩

def words06 : List Nat := [371285412040408865, 371285412042572616, 371285412027151478, 371285412011695292, 371285411995410245, 371285411946820099, 371285411857674705, 371285411938145614, 371285412014766956, 371285412017006820]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500014902259021, 362500074639370532⟩, ⟨(-936170115673703740), (-933600714347804894)⟩, true⟩

def words07 : List Nat := [371285412100983674, 371285412268314538, 371285412621639144, 371285412789199232, 371285412923566758, 371285413058566475, 371285413385211384, 371285413589935650, 371285413821669669, 371285414054355413]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499354407737822, 362499414164378428⟩, ⟨(-894166137403194724), (-891595492365246110)⟩, true⟩

def words08 : List Nat := [371285414285376645, 371285414287546882, 371285414444560166, 371285414625766802, 371285414865303122, 371285414900938415, 371285414909771532, 371285414919349067, 371285415174730527, 371285415397011528]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488481409412668, 362488541185546409⟩, ⟨(-201537323572852626), (-198965436918594632)⟩, true⟩

def words09 : List Nat := [371285415864972830, 371285416333780352, 371285416750524549, 371285416839228613, 371285417001846234, 371285417165558063, 371285417574767661, 371285417656172844, 371285417706830926, 371285417758333044]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk636B
