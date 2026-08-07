import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk017

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362260230348214330, 362260230361131663⟩, ⟨(-2921684248985683726), (-2921684234022175650)⟩, true⟩

def state01 : KState := ⟨⟨361599012811354372, 361599012824435165⟩, ⟨(-1799714893513768510), (-1799714878271577048)⟩, true⟩

def words00 : List Nat := [360543346592605889, 360544036835576581, 360544788182283965, 360545538647651029, 360546044296873985, 360546221711036357, 360546221711051676, 360546218267108626, 360546547983321041, 360547163100138510]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359744382865813376, 359744382879056486⟩, ⟨1383184527728562329, 1383184543249148119⟩, true⟩

def words01 : List Nat := [360547876750251729, 360548589567151431, 360549123339714530, 360549331101974710, 360549331101989431, 360549307126071380, 360549317818693545, 360549317818710796, 360549027755856086, 360548559939085061]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360145063331574218, 360145063344981009⟩, ⟨697945555438818750, 697945571241764558⟩, true⟩

def words02 : List Nat := [360548092665967211, 360548112390308404, 360548598287415911, 360549083621167683, 360549255054223953, 360549255054241250, 360549103349502616, 360548968985717429, 360548834777351225, 360548500091363532]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360523631675382679, 360523631688955295⟩, ⟨41296205964282009, 41296222054950345⟩, true⟩

def words03 : List Nat := [360548267025667681, 360547859723179081, 360547452890742076, 360547524688418903, 360547574891862973, 360547625037505341, 360547625037521031, 360547503255563038, 360547378797650259, 360547365149906416]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361263546630723441, 361263546644461575⟩, ⟨(-1250309161828521558), (-1250309145449016760)⟩, true⟩

def words04 : List Nat := [360547661739219614, 360547934338990037, 360547955502498070, 360547976641751603, 360547976641766357, 360548018371456452, 360548458619231015, 360548898363580905, 360549084275615093, 360549492306683725]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361693645074662523, 361693645088567306⟩, ⟨(-2007119336391136687), (-2007119319719146057)⟩, true⟩

def words05 : List Nat := [360549961470147317, 360550430098346640, 360551218193715504, 360551693905448686, 360551891469317759, 360552088808300261, 360552257223093865, 360552588056289424, 360553236384163072, 360553883975722817]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360658432202577319, 360658432216651164⟩, ⟨(-184517785055353892), (-184517768084974322)⟩, true⟩

def words06 : List Nat := [360554360380688626, 360554527395398412, 360554792580103357, 360555057464321174, 360555228171079755, 360555228171097503, 360555090506134948, 360554753792187965, 360554417458920444, 360554243753587938]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359561401602419026, 359561401616661470⟩, ⟨1759943357316373326, 1759943374586049274⟩, true⟩

def words07 : List Nat := [360554243753602814, 360554084032533684, 360553924491633217, 360553606634168176, 360552982570601767, 360552243306285927, 360551504874001447, 360551078369519256, 360550689629338898, 360550133849574981]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361203042048694110, 361203042063106628⟩, ⟨(-1171614965027217359), (-1171614947453964217)⟩, true⟩

def words08 : List Nat := [360549578693928270, 360549081911693300, 360548874250309404, 360548924893242888, 360548924893259794, 360548649083021211, 360548306162514609, 360548271186072460, 360548508572890228, 360548874029910669]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360727951976513993, 360727951991099587⟩, ⟨(-318303942363355149), (-318303924479416465)⟩, true⟩

def words09 : List Nat := [360549085538532496, 360549296811229329, 360549521456584273, 360549973715584220, 360550335517660861, 360550696917066966, 360550894662699389, 360551018180902881, 360551116477479136, 360551214664903354]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk017
