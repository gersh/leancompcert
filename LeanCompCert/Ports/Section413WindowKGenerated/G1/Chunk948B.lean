import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948A

def state06 : KState := ⟨⟨362490549579079996, 362490686296713665⟩, ⟨(-529973510058829501), (-521217277487829427)⟩, true⟩

def words05 : List Nat := [371285190923221071, 371285191027019371, 371285191185940718, 371285191290862559, 371285191419932767, 371285191550304205, 371285191658156185, 371285191661481620, 371285191697624115, 371285191759680661]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483053863445498, 362483190610680593⟩, ⟨181109151778017301, 189868192490097073⟩, true⟩

def words06 : List Nat := [371285191893144394, 371285191896468626, 371285191881997827, 371285191865336580, 371285191860346568, 371285191864010693, 371285191870057391, 371285191916279856, 371285191958481483, 371285191961924296]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498270331455500, 362498407108831199⟩, ⟨(-1262565558656281665), (-1253803658357506651)⟩, true⟩

def words07 : List Nat := [371285191968032533, 371285191996952529, 371285192135313660, 371285192188490632, 371285192200447971, 371285192213386483, 371285192295083222, 371285192338109755, 371285192479642873, 371285192622702707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494667736327749, 362494804543650589⟩, ⟨(-920780470364561859), (-912015728523066363)⟩, true⟩

def words08 : List Nat := [371285192764085590, 371285192767410527, 371285192851210844, 371285192945886507, 371285193044848984, 371285193069683568, 371285193090929141, 371285193113295596, 371285193245426048, 371285193350507688]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487579470405269, 362487716307700170⟩, ⟨(-248086726453458499), (-239319140412011163)⟩, true⟩

def words09 : List Nat := [371285193547150597, 371285193745174342, 371285193939393242, 371285194020714181, 371285194134518314, 371285194250048819, 371285194420224989, 371285194471493890, 371285194500596082, 371285194530896849]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948B
