import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk135

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360679543322451862, 360679544342731996⟩, ⟨(-1318790435978731888), (-1318781107461647516)⟩, true⟩

def state01 : KState := ⟨⟨360638231810337382, 360638232832194294⟩, ⟨(-761133676951549065), (-761124327140022475)⟩, true⟩

def words00 : List Nat := [360581873648834024, 360581880310744211, 360581882749268931, 360581885187448275, 360581885187588420, 360581886979090170, 360581890813052709, 360581894646479922, 360581894983969564, 360581899153921774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360694542830753178, 360694543854189414⟩, ⟨(-1522036701446235937), (-1522027330290120795)⟩, true⟩

def words01 : List Nat := [360581906562720560, 360581913970471376, 360581926831195911, 360581937133282724, 360581942141851146, 360581947149691408, 360581951958015419, 360581959540668577, 360581967868047227, 360581976194231562]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360649279017072686, 360649280042103561⟩, ⟨(-910493163106237968), (-910483770382930706)⟩, true⟩

def words02 : List Nat := [360581981768180176, 360581981912252007, 360581987500611785, 360581993088197178, 360581997119706532, 360581997119874073, 360581995723321214, 360581991387690645, 360581987052668868, 360581991314708474]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578927606774256, 360578928633384893⟩, ⟨41556486221149104, 41565900326780832⟩, true⟩

def words03 : List Nat := [360581996095886954, 360582000876388916, 360582002061727347, 360582002061895063, 360582000289718986, 360581997116204079, 360581996202628208, 360581998719503125, 360581998719652585, 360581998493084065]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360620108515097048, 360620109543291512⟩, ⟨(-516116632850923849), (-516107197292512987)⟩, true⟩

def words04 : List Nat := [360581998793269801, 360582003173928747, 360582010393074526, 360582017611186194, 360582019598003555, 360582020176730491, 360582020176866965, 360582019702604453, 360582020451066604, 360582023262036069]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360531477290474451, 360531478320269372⟩, ⟨685751474601542060, 685760931854172422⟩, true⟩

def words05 : List Nat := [360582023336640335, 360582023411255787, 360582028903328167, 360582037289167042, 360582044281188533, 360582051272205863, 360582055530975040, 360582055531143021, 360582054389984121, 360582050660376612]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579845635233630, 360579846666610832⟩, ⟨29181917260880541, 29191395977144677⟩, true⟩

def words06 : List Nat := [360582046931264139, 360582046661208349, 360582040993468202, 360582031062229821, 360582021132428395, 360582009818278014, 360582003449170741, 360582002486090075, 360582001523133043, 360581997838016665]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360698245342742166, 360698246375709043⟩, ⟨(-1578387045073509270), (-1578377544777630246)⟩, true⟩

def words07 : List Nat := [360582000394834256, 360582003109815628, 360582005483407169, 360582007184558218, 360582007184713343, 360582004337774775, 360582004041474445, 360582009719914805, 360582018279451334, 360582026837767977]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360515450853139613, 360515451887709698⟩, ⟨904190739353056716, 904200261428427250⟩, true⟩

def words08 : List Nat := [360582032638802142, 360582033055580506, 360582034151992989, 360582035248292600, 360582035248435338, 360582031483343359, 360582022336945668, 360582009031929447, 360581995728839339, 360581986123282063]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360543864018800583, 360543865054956964⟩, ⟨518178097595001132, 518187641236217656⟩, true⟩

def words09 : List Nat := [360581981717845426, 360581982207831612, 360581982207981915, 360581979307064578, 360581976649395043, 360581972621626498, 360581969948213359, 360581969948382649, 360581969889051941, 360581967087400804]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk135
