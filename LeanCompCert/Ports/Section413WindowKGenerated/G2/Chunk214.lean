import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360490054217042593, 360490056891146122⟩, ⟨1931189734017768917, 1931228455803025943⟩, true⟩

def state01 : KState := ⟨⟨360661464197096469, 360661466873802895⟩, ⟨(-1737833285221599730), (-1737794507721330186)⟩, true⟩

def words00 : List Nat := [360580296994906756, 360580294951554501, 360580294693642341, 360580294919552599, 360580294919806893, 360580293249942487, 360580294506273972, 360580296220340694, 360580299451391162, 360580303242598312]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581787373210048, 360581790052551917⟩, ⟨(-31672520091337837), (-31633686153852773)⟩, true⟩

def words01 : List Nat := [360580305540469518, 360580307838152736, 360580308953897146, 360580311392742072, 360580313288399770, 360580315183925459, 360580315253703391, 360580315253979506, 360580313222809587, 360580313292076036]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360530022733191510, 360530025415131468⟩, ⟨1077307351706388390, 1077346241308416084⟩, true⟩

def words02 : List Nat := [360580314644298110, 360580314644574261, 360580313827229232, 360580311581288607, 360580309335511628, 360580306488171412, 360580304739379886, 360580302932276087, 360580301125311198, 360580298221538767]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578680008195262, 360578682692742937⟩, ⟨34459451846716782, 34498397345166488⟩, true⟩

def words03 : List Nat := [360580295875964035, 360580294662127430, 360580294400452119, 360580295434617084, 360580295434871639, 360580294582164370, 360580293729485219, 360580292217904646, 360580291834550616, 360580291759783290]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360536945369277019, 360536948056459645⟩, ⟨929017779523292594, 929056781528009714⟩, true⟩

def words04 : List Nat := [360580291684987387, 360580289926740251, 360580286839663163, 360580284981664612, 360580283123766551, 360580280724203006, 360580276161213153, 360580270506110352, 360580264851477462, 360580260726927152]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360438641612937396, 360438644302721250⟩, ⟨3038347916822108442, 3038386974636446336⟩, true⟩

def words05 : List Nat := [360580258708006797, 360580257634674391, 360580256561411644, 360580254402932617, 360580251570400691, 360580247209147218, 360580242848217035, 360580239822750637, 360580234636310245, 360580228038724813]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360471218790390910, 360471221482789165⟩, ⟨2339076163153850425, 2339115277086142215⟩, true⟩

def words06 : List Nat := [360580221441693040, 360580215156067510, 360580210568533856, 360580206365734846, 360580202163308340, 360580196086471448, 360580187850127961, 360580181773273471, 360580175696908345, 360580169562765232]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360445460974654841, 360445463669688180⟩, ⟨2892252062683370236, 2892291233203932800⟩, true⟩

def words07 : List Nat := [360580164488815593, 360580157873760653, 360580151259267248, 360580146308810633, 360580142459570683, 360580138017259269, 360580133575325263, 360580128050674682, 360580120368158020, 360580114099539388]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360486838758266450, 360486841455911721⟩, ⟨2003146589566652018, 2003185816204364360⟩, true⟩

def words08 : List Nat := [360580107831413317, 360580103719372831, 360580098643789088, 360580091649864476, 360580084656545748, 360580077124167518, 360580070684399591, 360580066399563544, 360580062115097225, 360580056244939379]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586760565181842, 360586763265439854⟩, ⟨(-144624590914921124), (-144585308116157978)⟩, true⟩

def words09 : List Nat := [360580051907776374, 360580049724650466, 360580047541643970, 360580047512245640, 360580047198049162, 360580045010738146, 360580042823581765, 360580039894091643, 360580038367100757, 360580038680159349]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214
