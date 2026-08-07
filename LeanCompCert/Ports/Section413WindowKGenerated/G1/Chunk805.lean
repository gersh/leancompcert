import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk805

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473559981628912, 362473657200344985⟩, ⟨921230981843666264, 926515594672338264⟩, true⟩

def state01 : KState := ⟨⟨362468409495644890, 362468506739233160⟩, ⟨1335941004772786782, 1341227619943275682⟩, true⟩

def words00 : List Nat := [371285166569752371, 371285166568035113, 371285166507805743, 371285166530698547, 371285166532873112, 371285166532192437, 371285166325083785, 371285166163834938, 371285166001198711, 371285165882444479]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475658257127906, 362475755526116393⟩, ⟨752322523916905134, 757611184179651030⟩, true⟩

def words01 : List Nat := [371285165677608660, 371285165463921935, 371285165249057172, 371285165189611098, 371285165075138444, 371285165009197697, 371285164942343676, 371285164876261598, 371285164620894262, 371285164507539390]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471527263044873, 362471624556856377⟩, ⟨1084988670467435144, 1090279329609409780⟩, true⟩

def words02 : List Nat := [371285164392609413, 371285164342451920, 371285164183934329, 371285164014068284, 371285163843166011, 371285163718867270, 371285163516244222, 371285163468935867, 371285163420604078, 371285163353945778]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487223068211072, 362487320387136515⟩, ⟨(-179095393287992564), (-173802711590346694)⟩, true⟩

def words03 : List Nat := [371285163187728093, 371285163101940448, 371285163041797827, 371285163044582903, 371285162890351707, 371285162705477184, 371285162519448876, 371285162488661782, 371285162416420169, 371285162446316432]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483931561777101, 362484028905909631⟩, ⟨86026616376788661, 91321328378347237⟩, true⟩

def words04 : List Nat := [371285162465473381, 371285162468326360, 371285162469241381, 371285162540917146, 371285162646093509, 371285162648890719, 371285162633048172, 371285162618211832, 371285162624962294, 371285162628173795]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478363063836259, 362478460433060080⟩, ⟨534637613495887725, 539934346727600993⟩, true⟩

def words05 : List Nat := [371285162743441413, 371285162873939060, 371285162974741833, 371285162977527483, 371285162872866592, 371285162817031186, 371285162854493701, 371285162857280330, 371285162776571392, 371285162696549748]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478824140081545, 362478921534279145⟩, ⟨497501473486614797, 502800218733161673⟩, true⟩

def words06 : List Nat := [371285162633906745, 371285162636979595, 371285162597134046, 371285162587246076, 371285162576496999, 371285162530179244, 371285162277708098, 371285162180672674, 371285162082139723, 371285162073173686]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476390529461648, 362476487949004256⟩, ⟨693622401595695589, 698923189017644543⟩, true⟩

def words07 : List Nat := [371285161997802917, 371285161917939117, 371285161898979237, 371285161906369205, 371285161922756381, 371285161940235026, 371285161942374542, 371285161928770367, 371285161709072850, 371285161604862008]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470905775171280, 362471003219525713⟩, ⟨1135635702971474480, 1140938489859231406⟩, true⟩

def words08 : List Nat := [371285161522724615, 371285161525512586, 371285161371607473, 371285161218820148, 371285161064891304, 371285160941647206, 371285160764342734, 371285160690003591, 371285160614750377, 371285160540407451]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480113748888941, 362480211218515286⟩, ⟨393490340683666697, 398795164354943165⟩, true⟩

def words09 : List Nat := [371285160366663789, 371285160226676044, 371285160085203449, 371285160083482172, 371285159896492472, 371285159692778308, 371285159487978150, 371285159320851824, 371285159107547950, 371285159049338549]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk805
