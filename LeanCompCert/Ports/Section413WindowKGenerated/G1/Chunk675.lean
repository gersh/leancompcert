import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk675

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486674754722112, 362486742181177277⟩, ⟨(-87397751563070074), (-84323852176826588)⟩, true⟩

def state01 : KState := ⟨⟨362460537378121904, 362460604825124419⟩, ⟨1677015602414341263, 1680090888855256883⟩, true⟩

def words00 : List Nat := [371285493069223778, 371285493071528390, 371285492891064979, 371285492711663886, 371285492531357526, 371285492372977410, 371285492103915620, 371285491862635170, 371285491620585813, 371285491373618795]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487877392631562, 362487944860475426⟩, ⟨(-168846852689510552), (-165770159146221560)⟩, true⟩

def words01 : List Nat := [371285491006552506, 371285490859887447, 371285490764257860, 371285490766562856, 371285490528342043, 371285490238349816, 371285489947449234, 371285489854818153, 371285489731087398, 371285489770071756]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477235039717205, 362477302528377419⟩, ⟨549812475559138758, 552890574728258362⟩, true⟩

def words02 : List Nat := [371285489801949598, 371285489804307476, 371285489849167622, 371285489983093361, 371285490152854094, 371285490155164431, 371285490098324716, 371285490011714020, 371285489924181793, 371285489861040358]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469780189991026, 362469847699396277⟩, ⟨1053345157603709512, 1056424657789569244⟩, true⟩

def words03 : List Nat := [371285489839171294, 371285489939454789, 371285490039246610, 371285490041552263, 371285489849133760, 371285489699879119, 371285489616219580, 371285489618525321, 371285489395055818, 371285489166049958]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474183525106860, 362474251055156204⟩, ⟨755904721029364967, 758985615624230633⟩, true⟩

def words04 : List Nat := [371285488936034815, 371285488789615444, 371285488532644832, 371285488368196211, 371285488203034651, 371285488021020980, 371285487546252847, 371285487291626591, 371285487035825909, 371285486963603639]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474381259633324, 362474448810698746⟩, ⟨742540953988833945, 745623268327039975⟩, true⟩

def words05 : List Nat := [371285486799009476, 371285486583261436, 371285486366549434, 371285486332221401, 371285486189963580, 371285486079318062, 371285485967947999, 371285485812313469, 371285485431636121, 371285485271153558]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476448260039359, 362476515831646661⟩, ⟨602910455230088773, 605994157483571009⟩, true⟩

def words06 : List Nat := [371285485109369873, 371285485093173985, 371285484918664647, 371285484744052708, 371285484568534493, 371285484460833363, 371285484242641614, 371285484244239376, 371285484245026657, 371285484222315354]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500190779987132, 362500258372449987⟩, ⟨(-1001535133648197923), (-998450022079008259)⟩, true⟩

def words07 : List Nat := [371285484091182412, 371285484052899868, 371285484085064981, 371285484087386602, 371285484003192373, 371285483865492824, 371285483805368487, 371285483807955087, 371285484028029834, 371285484249218917]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486021914642418, 362486089527932956⟩, ⟨(-43994485444729716), (-40907966236219090)⟩, true⟩

def words08 : List Nat := [371285484469551501, 371285484471858975, 371285484487629626, 371285484577775142, 371285484676337373, 371285484678645721, 371285484527742594, 371285484376169097, 371285484288314680, 371285484299925733]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468541570746155, 362468609204868735⟩, ⟨1137672495570530788, 1140760422919147990⟩, true⟩

def words09 : List Nat := [371285484508088187, 371285484717255466, 371285484925749888, 371285484928057678, 371285484844841889, 371285484771393762, 371285484778603244, 371285484780911546, 371285484606050597, 371285484359053930]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk675
