import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599A

def state06 : KState := ⟨⟨362516913470607810, 362516966181020268⟩, ⟨(-1909480337652997643), (-1907345467988780917)⟩, true⟩

def words05 : List Nat := [371285152783695740, 371285153148180422, 371285153757161128, 371285154054312511, 371285154273105999, 371285154492488309, 371285154989656149, 371285155348810016, 371285155880724498, 371285156413538259]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494665940774426, 362494718669509281⟩, ⟨(-575410955630421761), (-573274987260346221)⟩, true⟩

def words06 : List Nat := [371285156880031575, 371285157116976199, 371285157586376230, 371285158056794580, 371285158589818791, 371285158752600911, 371285158912199207, 371285159072490411, 371285159304392387, 371285159466106631]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486890570633249, 362486943317625592⟩, ⟨(-108997164926968476), (-106860101565472890)⟩, true⟩

def words07 : List Nat := [371285159905353514, 371285160345410068, 371285160783739168, 371285160883056784, 371285161067528704, 371285161253086822, 371285161655857309, 371285161688585954, 371285161719807052, 371285161751770314]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495549759395956, 362495602524577198⟩, ⟨(-628407701432028655), (-626269547007689931)⟩, true⟩

def words08 : List Nat := [371285162061218012, 371285162267043338, 371285162438797362, 371285162611363821, 371285162757158397, 371285162759188768, 371285162612903204, 371285162661338803, 371285162956728038, 371285163132884983]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496051130465483, 362496103914161724⟩, ⟨(-658473698172781565), (-656334432942814035)⟩, true⟩

def words09 : List Nat := [371285163307461548, 371285163482735529, 371285163830814919, 371285164081287564, 371285164375626329, 371285164670707664, 371285164914536296, 371285164916567033, 371285165004398056, 371285165189258093]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk599B
