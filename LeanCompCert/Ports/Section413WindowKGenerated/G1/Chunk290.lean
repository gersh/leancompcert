import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk290

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362533173745137190, 362533185365154555⟩, ⟨(-1387996699904857683), (-1387768912150109763)⟩, true⟩

def state01 : KState := ⟨⟨362487248245332997, 362487259873720074⟩, ⟨(-56075299065174518), (-55847268545259456)⟩, true⟩

def words00 : List Nat := [371285334319656601, 371285334510872733, 371285335111077738, 371285335711705662, 371285336670481093, 371285336671407835, 371285336047595380, 371285335225749630, 371285334768611926, 371285334836025915]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474738968509652, 362474750605232647⟩, ⟨306997537775684320, 307225810163125646⟩, true⟩

def words01 : List Nat := [371285335897516803, 371285336959301707, 371285337990122242, 371285337991049375, 371285337619557657, 371285337300510314, 371285337848154838, 371285337849088206, 371285337661306819, 371285337297519454]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498360361391491, 362498372006426171⟩, ⟨(-378352586658159370), (-378124073022985358)⟩, true⟩

def words02 : List Nat := [371285337755757323, 371285338154953637, 371285339740767216, 371285341326860184, 371285342730648704, 371285342867581858, 371285344191067385, 371285345514931045, 371285346718762003, 371285347168390176]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362509575731098651, 362509587384597145⟩, ⟨(-703918595268941547), (-703689835887657285)⟩, true⟩

def words03 : List Nat := [371285347618115857, 371285348068132853, 371285349704109605, 371285350754139017, 371285352161202138, 371285353568534130, 371285354976196819, 371285354977124778, 371285355639768836, 371285356475334804]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362504807105354943, 362504818767123556⟩, ⟨(-565362107653650616), (-565133108065086636)⟩, true⟩

def words04 : List Nat := [371285358382082891, 371285359165715954, 371285359736144018, 371285360306818332, 371285361062882575, 371285361334627360, 371285362576352786, 371285363818376613, 371285364958638637, 371285365629260313]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362527742966181210, 362527754636331349⟩, ⟨(-1231839371912263533), (-1231610128797814799)⟩, true⟩

def words05 : List Nat := [371285366686132550, 371285367743406733, 371285369552942113, 371285369986447896, 371285370264819115, 371285370543469034, 371285371272038829, 371285371547540587, 371285373006639836, 371285374466041345]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362516570993680723, 362516582672222620⟩, ⟨(-907182429406245266), (-906952942385485086)⟩, true⟩

def words06 : List Nat := [371285375914143520, 371285376310097999, 371285377889535785, 371285379469371544, 371285381405515222, 371285381765578899, 371285382126654107, 371285382488013576, 371285383739522371, 371285384813793757]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500370421985491, 362500382108905554⟩, ⟨(-436152498399581989), (-435922767781952919)⟩, true⟩

def words07 : List Nat := [371285386380541399, 371285387947560338, 371285389283402601, 371285389284331684, 371285389163885262, 371285389284078585, 371285390586218539, 371285391125075812, 371285391641286788, 371285392157810958]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495966900136168, 362495978595378955⟩, ⟨(-307941185272393226), (-307711212587680842)⟩, true⟩

def words08 : List Nat := [371285393442631867, 371285394195376790, 371285395944093524, 371285397693064952, 371285399163815921, 371285399164745559, 371285399317499800, 371285399574693088, 371285400690924718, 371285401055501066]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475378092264025, 362475389795974029⟩, ⟨291218857830615649, 291449076870304791⟩, true⟩

def words09 : List Nat := [371285401421752992, 371285401788301147, 371285403143245593, 371285404055523151, 371285404863686203, 371285405672151375, 371285406407511520, 371285406408441554, 371285405571212237, 371285405228168885]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk290
