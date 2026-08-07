import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk463

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362447221325294499, 362447252107631661⟩, ⟨1767425300819926770, 1768388227592679906⟩, true⟩

def state01 : KState := ⟨⟨362483789936368383, 362483820732451792⟩, ⟨74132239557724101, 75095802851925889⟩, true⟩

def words00 : List Nat := [371285445413950504, 371285445056370504, 371285444464755042, 371285444218723753, 371285443972237720, 371285443610658957, 371285442822586821, 371285442500823519, 371285442320201993, 371285442321802946]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469871262872401, 362469902072976961⟩, ⟨718858847376617607, 719823060061305403⟩, true⟩

def words01 : List Nat := [371285442287937187, 371285442230839313, 371285442461912885, 371285442560840950, 371285442732085336, 371285442903895654, 371285443075610860, 371285443077147516, 371285442628061738, 371285442294480876]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469454722357858, 362469485546141811⟩, ⟨738169469618247567, 739134316003850831⟩, true⟩

def words02 : List Nat := [371285441960041218, 371285441866690595, 371285441421105508, 371285440975205695, 371285440528754944, 371285440124564504, 371285439552420903, 371285439446020029, 371285439339092316, 371285439233083401]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495136477741047, 362495167315431312⟩, ⟨(-451814508743152359), (-450849018009950865)⟩, true⟩

def words03 : List Nat := [371285438962415889, 371285439036904976, 371285439305337364, 371285439306874667, 371285438955164999, 371285438529824364, 371285438141697973, 371285438143391707, 371285438159222481, 371285438370911126]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473234261488339, 362473265113054763⟩, ⟨563193139616674625, 564159273441878695⟩, true⟩

def words04 : List Nat := [371285438566645896, 371285438568189553, 371285438522424548, 371285438614461615, 371285438718183451, 371285438719721275, 371285438203583945, 371285437592389298, 371285436980610431, 371285436834164621]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483774194519321, 362483805059947560⟩, ⟨74728021516318253, 75694797907048201⟩, true⟩

def words05 : List Nat := [371285436774580472, 371285436978230933, 371285437181811567, 371285437183387759, 371285437232311378, 371285437315252885, 371285437805982509, 371285437853212875, 371285437854378134, 371285437820903278]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489995551180098, 362490026430398480⟩, ⟨(-213719370069832282), (-212751954300960046)⟩, true⟩

def words06 : List Nat := [371285437866908386, 371285437868602976, 371285437972268532, 371285438229168733, 371285438353173289, 371285438354711862, 371285437912568721, 371285437904608025, 371285438290908627, 371285438391445235]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484157646738992, 362484188539947431⟩, ⟨57052231722942282, 58020296281818268⟩, true⟩

def words07 : List Nat := [371285438434127957, 371285438477306567, 371285438924900278, 371285439162326806, 371285439411790271, 371285439661841481, 371285439910570739, 371285439912109628, 371285439541666579, 371285439516581365]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476497759024147, 362476528665958277⟩, ⟨412463196563433805, 413431897791763825⟩, true⟩

def words08 : List Nat := [371285439927560603, 371285439980041853, 371285440032717376, 371285440085937356, 371285440280363476, 371285440282076398, 371285440446686253, 371285440650200025, 371285440755285389, 371285440756878557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499882970063655, 362499913890935417⟩, ⟨(-672523932858989399), (-671554584994993829)⟩, true⟩

def words09 : List Nat := [371285440704786011, 371285440845603721, 371285441281472061, 371285441283011384, 371285441100454112, 371285440844941796, 371285440588806084, 371285440568610868, 371285440730021072, 371285441043690854]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk463
