import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk707A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk707B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk707A

def state06 : KState := ⟨⟨362500328586870684, 362500402956865613⟩, ⟨(-1072797792691604272), (-1069243790088176638)⟩, true⟩

def words05 : List Nat := [371285291294406601, 371285291337876823, 371285291579416071, 371285291616673745, 371285291618550024, 371285291621106034, 371285291803895103, 371285291888288620, 371285292103494418, 371285292319790273]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480609924357820, 362480684316226088⟩, ⟨322509938504449892, 326065488980294326⟩, true⟩

def words06 : List Nat := [371285292520222713, 371285292522646595, 371285292456986144, 371285292412871195, 371285292381375684, 371285292383800770, 371285292166745042, 371285291949440260, 371285291731123409, 371285291713272581]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465399730757751, 362465474144425682⟩, ⟨1399056822833342262, 1402613916184636040⟩, true⟩

def words07 : List Nat := [371285291661093580, 371285291674987226, 371285291690854683, 371285291693295653, 371285291529782544, 371285291402352475, 371285291273649176, 371285291229227992, 371285290950611156, 371285290673334762]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476513254037166, 362476587689408428⟩, ⟨612436018357629350, 615994647978502156⟩, true⟩

def words08 : List Nat := [371285290395010824, 371285290273735917, 371285290067891734, 371285290062340423, 371285290055992290, 371285290005440010, 371285289688326572, 371285289545259207, 371285289405332575, 371285289407842932]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491917671061707, 362491992128597342⟩, ⟨(-478135552127643797), (-474575353382485941)⟩, true⟩

def words09 : List Nat := [371285289286766334, 371285289125493682, 371285288998460229, 371285289001170148, 371285289003662125, 371285289037052689, 371285289070092636, 371285289072572106, 371285289083840507, 371285289181557294]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk707B
