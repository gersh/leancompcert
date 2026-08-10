import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk214B
