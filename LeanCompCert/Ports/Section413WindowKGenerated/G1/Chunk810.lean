import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483943674300573, 362484042151349207⟩, ⟨86011970200821028, 91398193882330216⟩, true⟩

def state01 : KState := ⟨⟨362478450053174062, 362478548555187391⟩, ⟨531048181721904299, 536436427672486685⟩, true⟩

def words00 : List Nat := [371285170650487361, 371285170653290168, 371285170605713019, 371285170553350598, 371285170499873167, 371285170459487963, 371285170369928747, 371285170388947637, 371285170406719268, 371285170409621072]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494489700674133, 362494588228024544⟩, ⟨(-768444253069794422), (-763053954434468864)⟩, true⟩

def words01 : List Nat := [371285170329815540, 371285170295022087, 371285170372983033, 371285170375786313, 371285170289126572, 371285170158706810, 371285170045877569, 371285170049050209, 371285170131166033, 371285170250531864]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489004585342524, 362489103137979019⟩, ⟨(-324026425521282473), (-318634078081093719)⟩, true⟩

def words02 : List Nat := [371285170368464395, 371285170371275586, 371285170445548557, 371285170561264113, 371285170684843229, 371285170707166771, 371285170728965742, 371285170751665115, 371285170837134385, 371285170888863482]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474567186632286, 362474665764571364⟩, ⟨845997674803431746, 851392072642718192⟩, true⟩

def words03 : List Nat := [371285171091538013, 371285171295427504, 371285171498313367, 371285171530520029, 371285171595145455, 371285171661152878, 371285171788622199, 371285171791426503, 371285171716202435, 371285171589752050]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499427727039319, 362499526330066537⟩, ⟨(-1168791634089333698), (-1163395202977042518)⟩, true⟩

def words04 : List Nat := [371285171484598390, 371285171487703739, 371285171573259732, 371285171694206201, 371285171791038997, 371285171793893336, 371285171885024002, 371285172009138288, 371285172283939741, 371285172463945490]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490279534079705, 362490378162685831⟩, ⟨(-427255243812107338), (-421856739402237146)⟩, true⟩

def words05 : List Nat := [371285172643181997, 371285172823340391, 371285173065267865, 371285173254497961, 371285173456698874, 371285173660005650, 371285173851146584, 371285173853951455, 371285173906290775, 371285173973995805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480639563955899, 362480738217511108⟩, ⟨354223708481524277, 359624235396371583⟩, true⟩

def words06 : List Nat := [371285174174482808, 371285174177287944, 371285174175190888, 371285174173734813, 371285174205802952, 371285174208895042, 371285174179070084, 371285174186944302, 371285174189041670, 371285174189330479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501527017839029, 362501625696763269⟩, ⟨(-1339229087791595226), (-1333826504079670282)⟩, true⟩

def words07 : List Nat := [371285174233902755, 371285174334714627, 371285174495056610, 371285174530135941, 371285174532313386, 371285174528861041, 371285174669910071, 371285174742557624, 371285174947358319, 371285175153429077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491153630385436, 362491252334686939⟩, ⟨(-498154521073341999), (-492749879648667059)⟩, true⟩

def words08 : List Nat := [371285175315131084, 371285175317937240, 371285175424192115, 371285175555731370, 371285175732657354, 371285175735463298, 371285175709828047, 371285175678898141, 371285175751354345, 371285175829530403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492625909210958, 362492724638734961⟩, ⟨(-617511673572087262), (-612104986726557764)⟩, true⟩

def words09 : List Nat := [371285176043252587, 371285176258113564, 371285176472046033, 371285176541206250, 371285176613211932, 371285176686597051, 371285176910508786, 371285177006676535, 371285177101859616, 371285177198053261]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk810
