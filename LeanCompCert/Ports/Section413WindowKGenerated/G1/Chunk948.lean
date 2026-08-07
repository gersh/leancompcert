import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492175877257005, 362492312415321523⟩, ⟨(-684218706645223508), (-675479502643004420)⟩, true⟩

def state01 : KState := ⟨⟨362482663166051629, 362482799733739380⟩, ⟨217622019860793673, 226364032298538801⟩, true⟩

def words00 : List Nat := [371285187284465927, 371285187287788124, 371285187256695810, 371285187226342058, 371285187194745950, 371285187193434272, 371285187197083660, 371285187253404520, 371285187284688610, 371285187288135526]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499638480187661, 362499775077831854⟩, ⟨(-1391894315286810855), (-1383149462524241059)⟩, true⟩

def words01 : List Nat := [371285187351358141, 371285187441449001, 371285187621503021, 371285187654331781, 371285187659077319, 371285187664833604, 371285187765064242, 371285187811255651, 371285187967349823, 371285188124915051]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496422318174520, 362496558945823081⟩, ⟨(-1086909576866835438), (-1078161878938801812)⟩, true⟩

def words02 : List Nat := [371285188280879434, 371285188372354615, 371285188573986294, 371285188777408864, 371285189013176384, 371285189136028070, 371285189259894481, 371285189384851206, 371285189524344428, 371285189648030811]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482741517687882, 362482878175267229⟩, ⟨210527192857847401, 219277729278426345⟩, true⟩

def words03 : List Nat := [371285189807255293, 371285189967856942, 371285190115721078, 371285190119044461, 371285190136417799, 371285190158334068, 371285190289769645, 371285190293093212, 371285190276536117, 371285190255921789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494531097542661, 362494667784938374⟩, ⟨(-907652918943352598), (-898899554593732092)⟩, true⟩

def words04 : List Nat := [371285190320688507, 371285190373207121, 371285190443150985, 371285190514371464, 371285190567715740, 371285190571040634, 371285190530766947, 371285190569190948, 371285190717072500, 371285190820493153]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk948
