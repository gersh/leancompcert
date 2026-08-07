import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk503

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362508809471545079, 362508846047904696⟩, ⟨(-1199353011838567828), (-1198110061813141510)⟩, true⟩

def state01 : KState := ⟨⟨362477569455724481, 362477606047274018⟩, ⟨372143015277230381, 373386729431455405⟩, true⟩

def words00 : List Nat := [371285027681141455, 371285027798684426, 371285028000924582, 371285028204039674, 371285028527422007, 371285028529101594, 371285028326226912, 371285028085408389, 371285027843952315, 371285027767199112]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475069954776767, 362475106561466368⟩, ⟨498005573886092323, 499250049813188233⟩, true⟩

def words01 : List Nat := [371285027867939859, 371285028116888548, 371285028362957143, 371285028364648239, 371285028257101914, 371285028211943796, 371285028452811238, 371285028454491333, 371285028260097798, 371285028064841034]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483772694027358, 362483809315771460⟩, ⟨60054823850565005, 61300057397003825⟩, true⟩

def words02 : List Nat := [371285028066176453, 371285028068073466, 371285028161269958, 371285028255106804, 371285028256417920, 371285028211517749, 371285027640152225, 371285027388477625, 371285027276596830, 371285027278366275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484068546271346, 362484105183300898⟩, ⟨45211808803078269, 46457811744281161⟩, true⟩

def words03 : List Nat := [371285027255426531, 371285027220811034, 371285027543453802, 371285027706041421, 371285027988885099, 371285028272404840, 371285028438394775, 371285028440075356, 371285028080218927, 371285028063947388]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469079227430493, 362469115879430051⟩, ⟨799886768457040146, 801133525065058782⟩, true⟩

def words04 : List Nat := [371285028422627514, 371285028424308249, 371285028275819453, 371285028089273477, 371285027902042628, 371285027836478510, 371285027573599681, 371285027441418340, 371285027308696109, 371285027170891125]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500182121556367, 362500218788783313⟩, ⟨(-766350104381563018), (-765102580997198406)⟩, true⟩

def words05 : List Nat := [371285026856044351, 371285026705906630, 371285026728367608, 371285026730053194, 371285026500956961, 371285026203933338, 371285025909957150, 371285025911854319, 371285026122443877, 371285026426022503]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477122078653502, 362477158761041584⟩, ⟨395076086035078759, 396324373012292293⟩, true⟩

def words06 : List Nat := [371285026729182429, 371285026730871880, 371285027002221743, 371285027336257381, 371285027683471300, 371285027685152793, 371285027507300031, 371285027303511673, 371285027099034770, 371285027023360669]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362458000775404577, 362458037472937071⟩, ⟨1358390795188704823, 1359639845067871643⟩, true⟩

def words07 : List Nat := [371285026963398902, 371285027060336237, 371285027136323637, 371285027138005735, 371285026742723159, 371285026416195333, 371285026153955324, 371285026155637329, 371285025697198435, 371285025163390979]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490565071249098, 362490601783839073⟩, ⟨(-282303167440003087), (-281053358890665723)⟩, true⟩

def words08 : List Nat := [371285024628860805, 371285024447114606, 371285024085409756, 371285024102638347, 371285024103940581, 371285024055156993, 371285023790750334, 371285023856767622, 371285024219904664, 371285024332332045]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481186121907847, 362481222849880576⟩, ⟨190339844324224526, 191590428081764002⟩, true⟩

def words09 : List Nat := [371285024371824961, 371285024411878174, 371285024552298255, 371285024554153294, 371285024591265089, 371285024671299053, 371285024730849080, 371285024732532191, 371285024320521476, 371285024247263151]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk503
