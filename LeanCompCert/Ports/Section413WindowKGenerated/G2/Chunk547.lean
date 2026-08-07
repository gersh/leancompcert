import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574311974809152, 360574330883104885⟩, ⟨404060339147320438, 404759153437001320⟩, true⟩

def state01 : KState := ⟨⟨360608252156281482, 360608271071751297⟩, ⟨(-1452690399152681417), (-1451991192405298321)⟩, true⟩

def words00 : List Nat := [360581730380073629, 360581730564651916, 360581730799736543, 360581731034957697, 360581731035670767, 360581730953936140, 360581730826791363, 360581730893829036, 360581731294097129, 360581731779974410]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595046159909916, 360595065082636997⟩, ⟨(-730039752554828923), (-729340148725961185)⟩, true⟩

def words01 : List Nat := [360581732097669266, 360581732415442467, 360581733066464852, 360581733973266566, 360581734734345054, 360581735495519402, 360581736000366035, 360581736252962722, 360581736497170650, 360581736741621191]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600230775348798, 360600249705237595⟩, ⟨(-1013847599345872632), (-1013147603591558860)⟩, true⟩

def words02 : List Nat := [360581737319126104, 360581737563727964, 360581737564408277, 360581737510831160, 360581737457136919, 360581737187051370, 360581737492862963, 360581737812838781, 360581737963105583, 360581738302127995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601850820281677, 360601869757360304⟩, ⟨(-1102538913475109803), (-1101838524186596555)⟩, true⟩

def words03 : List Nat := [360581738901015574, 360581739500104429, 360581740088755990, 360581740344580047, 360581740345281822, 360581740290429746, 360581740437361768, 360581740807215369, 360581741175551331, 360581741544061560]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579351849759637, 360579370794078361⟩, ⟨129012481987645175, 129713267634443605⟩, true⟩

def words04 : List Nat := [360581741712144895, 360581741712905894, 360581741681493210, 360581741715970723, 360581741716607530, 360581741667115327, 360581741421863093, 360581740866477641, 360581740310966890, 360581739986181274]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583683540863580, 360583702492351330⟩, ⟨(-108106347404254708), (-107405169218107298)⟩, true⟩

def words05 : List Nat := [360581740233185636, 360581740523598120, 360581740647322473, 360581740780256069, 360581740780893177, 360581740774546657, 360581740871945776, 360581741075058943, 360581741111555446, 360581741148160791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588036900724264, 360588055859403307⟩, ⟨(-346496676319967210), (-345795104301983596)⟩, true⟩

def words06 : List Nat := [360581741176413196, 360581741372607166, 360581741724576586, 360581742076678115, 360581742143736905, 360581742144498194, 360581742098210595, 360581742241964224, 360581742272632107, 360581742388692494]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591758715918527, 360591777681843473⟩, ⟨(-550359615525408561), (-549657646613877003)⟩, true⟩

def words07 : List Nat := [360581742389370721, 360581742339012963, 360581742570043602, 360581743087803523, 360581743372567626, 360581743657434117, 360581743734806227, 360581743735567723, 360581743769932271, 360581743953970418]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618083917923340, 360618102891022312⟩, ⟨(-1992550690741563940), (-1991848328800577574)⟩, true⟩

def words08 : List Nat := [360581744318253385, 360581744861249240, 360581745235176265, 360581745609165888, 360581745899315652, 360581746404623818, 360581747242169223, 360581748079829950, 360581748659009472, 360581749323304976]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630716280592044, 360630735260879188⟩, ⟨(-2684875641004273193), (-2684172885187911095)⟩, true⟩

def words09 : List Nat := [360581749882089308, 360581750441078629, 360581751257045454, 360581751741028966, 360581751946235429, 360581752151505421, 360581752546249953, 360581753108610220, 360581754003060901, 360581754897652461]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547
