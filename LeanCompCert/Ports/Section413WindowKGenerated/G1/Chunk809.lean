import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494789180294443, 362494887404822044⟩, ⟨(-792250169427792992), (-786884387348734882)⟩, true⟩

def state01 : KState := ⟨⟨362488869976164507, 362488968225947485⟩, ⟨(-313413881411100868), (-308046056043246238)⟩, true⟩

def words00 : List Nat := [371285161005827267, 371285161008632385, 371285161007420984, 371285161057454837, 371285161111405113, 371285161114253121, 371285161041468357, 371285160963027444, 371285160954692115, 371285161004975760]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484074625561639, 362484172900622768⟩, ⟨74660348926342950, 80030219676273388⟩, true⟩

def words01 : List Nat := [371285161206591908, 371285161409394029, 371285161581530434, 371285161589866996, 371285161644340509, 371285161700189439, 371285161907239963, 371285161911691755, 371285161913807548, 371285161904820449]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489855788834647, 362489954088942781⟩, ⟨(-393137979301644626), (-387766081619761550)⟩, true⟩

def words02 : List Nat := [371285161995438044, 371285162023071861, 371285162202142172, 371285162382322290, 371285162548679643, 371285162551480518, 371285162543500347, 371285162551094088, 371285162709773167, 371285162771874912]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502088574176524, 362502186899764774⟩, ⟨(-1383190755638465363), (-1377816795723337481)⟩, true⟩

def words03 : List Nat := [371285162831152263, 371285162891347918, 371285163103031583, 371285163272629438, 371285163487977504, 371285163704418603, 371285163892770761, 371285163990802617, 371285164203018786, 371285164416774407]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487226794103133, 362487325144659746⟩, ⟨(-180202093627358745), (-174826112643711939)⟩, true⟩

def words04 : List Nat := [371285164681722602, 371285164744150379, 371285164805920033, 371285164868671047, 371285164977254473, 371285165010820490, 371285165173146035, 371285165336635961, 371285165461551258, 371285165491132999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506658439177835, 362506756815075357⟩, ⟨(-1753290915516365929), (-1747912883061230193)⟩, true⟩

def words05 : List Nat := [371285165619421628, 371285165749175338, 371285166029964260, 371285166155530862, 371285166241576375, 371285166328409712, 371285166553588067, 371285166710238900, 371285166978818855, 371285167248703138]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496611055604393, 362496709456774317⟩, ⟨(-939794888809612117), (-934414810169867717)⟩, true⟩

def words06 : List Nat := [371285167517529014, 371285167660477880, 371285167954947449, 371285168250879155, 371285168592354138, 371285168731405509, 371285168870894484, 371285169011353867, 371285169194097611, 371285169339816766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480415111503776, 362480513537879826⟩, ⟨371687250199478118, 377069369908363590⟩, true⟩

def words07 : List Nat := [371285169521101274, 371285169703480459, 371285169885117291, 371285169887918908, 371285169866190207, 371285169869439394, 371285169972048532, 371285169974856274, 371285169919375587, 371285169864996502]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491784157491707, 362491882608977817⟩, ⟨(-549039590975973081), (-543655437726692069)⟩, true⟩

def words08 : List Nat := [371285169881424687, 371285169904489298, 371285169966932914, 371285170030505291, 371285170068025278, 371285170070827191, 371285169904926015, 371285169881335904, 371285169981765472, 371285170067612398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483943674300573, 362484042151349207⟩, ⟨86011970200821028, 91398193882330216⟩, true⟩

def words09 : List Nat := [371285170152297049, 371285170237946108, 371285170379346881, 371285170445679858, 371285170536029196, 371285170627424477, 371285170681231539, 371285170684034079, 371285170534505423, 371285170524113187]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk809
