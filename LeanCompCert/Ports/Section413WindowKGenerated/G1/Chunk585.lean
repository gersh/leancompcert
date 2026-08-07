import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483549194879568, 362483599271641269⟩, ⟨80620121068827663, 82598990743412989⟩, true⟩

def state01 : KState := ⟨⟨362471492995152914, 362471543089491439⟩, ⟨785994384699769635, 787974282711311865⟩, true⟩

def words00 : List Nat := [371285011387542858, 371285011389518802, 371285011191497786, 371285010993114828, 371285010793964589, 371285010683371426, 371285010470676068, 371285010474422861, 371285010475925404, 371285010433239710]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494722027366935, 362494772139625717⟩, ⟨(-573260059433348762), (-571279112821865322)⟩, true⟩

def words01 : List Nat := [371285010266660467, 371285010331300861, 371285010467063331, 371285010469044915, 371285010307927904, 371285010103715462, 371285009947082007, 371285009949279984, 371285010019885094, 371285010188995655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486063992619630, 362486114122682053⟩, ⟨(-66591984162105106), (-64609995588533452)⟩, true⟩

def words02 : List Nat := [371285010356303741, 371285010358281958, 371285010299259050, 371285010390398532, 371285010569029089, 371285010571015109, 371285010471344306, 371285010310313754, 371285010242150135, 371285010263264163]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474889995186746, 362474940143027506⟩, ⟨587517455904360320, 589500485135221972⟩, true⟩

def words03 : List Nat := [371285010355594587, 371285010448694994, 371285010541158993, 371285010543171573, 371285010436173459, 371285010368620936, 371285010522196290, 371285010524173436, 371285010358716796, 371285010188895891]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491622951596270, 362491673117156241⟩, ⟨(-392095484863263308), (-390111418259432448)⟩, true⟩

def words04 : List Nat := [371285010018243820, 371285009967995377, 371285009948643272, 371285010086500730, 371285010175959903, 371285010177937674, 371285009930154896, 371285009938905037, 371285010238620711, 371285010354466289]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491430442769166, 362491480626361836⟩, ⟨(-380835358971842485), (-378850236464329111)⟩, true⟩

def words05 : List Nat := [371285010453277278, 371285010552778805, 371285010800324217, 371285010903078900, 371285011009558935, 371285011116749862, 371285011206697505, 371285011208682906, 371285011186783856, 371285011299737217]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490741914379277, 362490792115604465⟩, ⟨(-340446226204434384), (-338460071044206342)⟩, true⟩

def words06 : List Nat := [371285011671420019, 371285011848675900, 371285012021604051, 371285012195174995, 371285012373188399, 371285012421476470, 371285012760733990, 371285013100801848, 371285013386033214, 371285013486743012]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362516456915173187, 362516507134267990⟩, ⟨(-1846713000055774124), (-1844725798181812452)⟩, true⟩

def words07 : List Nat := [371285013813634363, 371285014141538929, 371285014760169415, 371285014990770695, 371285015133950000, 371285015277791297, 371285015634949749, 371285015883033995, 371285016421953285, 371285016961717474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502755863333163, 362502806100315330⟩, ⟨(-1044096560507558303), (-1042108310701817241)⟩, true⟩

def words08 : List Nat := [371285017481217403, 371285017704842170, 371285018047359458, 371285018390884098, 371285018820912275, 371285018991471240, 371285019136615248, 371285019282404161, 371285019644491416, 371285019950382716]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475626310994950, 362475676565798514⟩, ⟨545647270940222564, 547636564993724390⟩, true⟩

def words09 : List Nat := [371285020447719167, 371285020945864758, 371285021442417103, 371285021551096741, 371285021746730050, 371285021943318229, 371285022173771257, 371285022175750945, 371285022056907822, 371285021899672128]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585
