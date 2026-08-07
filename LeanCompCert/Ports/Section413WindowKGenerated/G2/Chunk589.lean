import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360540262928510503, 360540284982751693⟩, ⟨2458881633899792371, 2459759224998259815⟩, true⟩

def state01 : KState := ⟨⟨360569483066498917, 360569505128503371⟩, ⟨737631814722433019, 738509863115319353⟩, true⟩

def words00 : List Nat := [360582045891126391, 360582045471281535, 360582045194900250, 360582044879051746, 360582044563176990, 360582043923496639, 360582042996256103, 360582042357486484, 360582041718497076, 360582041367904412]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553070921855582, 360553092991707041⟩, ⟨1704637015640364812, 1705515526339237250⟩, true⟩

def words01 : List Nat := [360582041155837972, 360582040783419256, 360582040410841188, 360582040385975527, 360582040386664199, 360582040372747898, 360582040358733010, 360582040168302071, 360582039774086782, 360582039283735881]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564656823449053, 360564678901051469⟩, ⟨1021958428757847843, 1022837396181549511⟩, true⟩

def words02 : List Nat := [360582038793128382, 360582038590802147, 360582038291794699, 360582037848469271, 360582037405025312, 360582036888490017, 360582036614024501, 360582036376986703, 360582036139869767, 360582035720942553]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584712605020568, 360584734690403477⟩, ⟨(-160100870782401333), (-159221444816207177)⟩, true⟩

def words03 : List Nat := [360582035427080709, 360582035306414898, 360582035185514715, 360582035056216277, 360582034721738128, 360582034144103651, 360582033566330748, 360582033276780367, 360582033273777712, 360582033320477344]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560810137680378, 360560832230907707⟩, ⟨1248785188728146141, 1249665077082376563⟩, true⟩

def words04 : List Nat := [360582033321218843, 360582033159751975, 360582032958211725, 360582033001966244, 360582033002655221, 360582032972321415, 360582032654925738, 360582032113348392, 360582031571637030, 360582030959950666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360537090539261310, 360537112640243102⟩, ⟨2647270618422658288, 2648150963941578612⟩, true⟩

def words05 : List Nat := [360582030601017226, 360582030468909562, 360582030336716670, 360582030035144855, 360582029740609806, 360582029287815983, 360582028834795395, 360582028383280765, 360582027766234515, 360582027005303170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566505341671025, 360566527450433613⟩, ⟨912795058162169031, 913675862475457713⟩, true⟩

def words06 : List Nat := [360582026244216641, 360582025474932407, 360582024867498213, 360582024547957633, 360582024228363580, 360582023666057687, 360582022816824209, 360582022255582865, 360582021694089183, 360582021360260228]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554651934790249, 360554674051391217⟩, ⟨1611795617350401094, 1612676883932443186⟩, true⟩

def words07 : List Nat := [360582021098261229, 360582020620823939, 360582020143245551, 360582019761279815, 360582019522329240, 360582019076113764, 360582018629828388, 360582018039831878, 360582017289298146, 360582016826635918]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571406038530845, 360571428162902637⟩, ⟨623547277241473646, 624429002185051974⟩, true⟩

def words08 : List Nat := [360582016363718967, 360582015969274757, 360582015728961314, 360582015343894494, 360582014958706230, 360582014454233309, 360582014122761498, 360582013990490576, 360582013858146970, 360582013499437390]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601068489874733, 360601090622024435⟩, ⟨(-1126429727545644697), (-1125547543745811581)⟩, true⟩

def words09 : List Nat := [360582013428686086, 360582013537612894, 360582013606340931, 360582013607169032, 360582013593119057, 360582013320645257, 360582013062129563, 360582013220145252, 360582013544157501, 360582013868346603]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589
