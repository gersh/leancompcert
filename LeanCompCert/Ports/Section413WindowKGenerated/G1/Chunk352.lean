import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk352

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460358889429238, 362460376288311225⟩, ⟨866337446034011850, 866751358494922844⟩, true⟩

def state01 : KState := ⟨⟨362472734274656877, 362472751683777121⟩, ⟨430717613353194521, 431131886253438007⟩, true⟩

def words00 : List Nat := [371284999314964881, 371284999316223663, 371284999023082271, 371284998974415739, 371284998925400892, 371284998747339425, 371284997704047402, 371284996991441187, 371284996278260552, 371284996270151829]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458810162981143, 362458827582492824⟩, ⟨921086266194292299, 921500905030607985⟩, true⟩

def words01 : List Nat := [371284995923263584, 371284995354068691, 371284994784682339, 371284994785941674, 371284994386140485, 371284994235361829, 371284994084217602, 371284993809862728, 371284992460985916, 371284991719489719]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474497241896559, 362474514671597726⟩, ⟨368560258653250761, 368975256415590563⟩, true⟩

def words02 : List Nat := [371284991040413061, 371284991041564507, 371284990388382598, 371284989708649383, 371284989028482504, 371284988577319093, 371284987884979517, 371284987942495400, 371284987995881271, 371284987997070778]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500944574111395, 362500962014170773⟩, ⟨(-563389020038496667), (-562973657304022925)⟩, true⟩

def words03 : List Nat := [371284987730215450, 371284987761228531, 371284988198937627, 371284988200081848, 371284987680530659, 371284987018824618, 371284986397427907, 371284986398709891, 371284986596947601, 371284987051561766]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464500752655271, 362464518203036186⟩, ⟨720970356335990282, 721386082853759694⟩, true⟩

def words04 : List Nat := [371284987419299356, 371284987420443968, 371284986843133543, 371284986798640930, 371284986753592900, 371284986737193011, 371284985648126254, 371284984562874645, 371284983477204942, 371284983056450478]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452273754992794, 362452291215679924⟩, ⟨1152154728392004074, 1152570818256665426⟩, true⟩

def words05 : List Nat := [371284982700532357, 371284982925624243, 371284983153538485, 371284983154683251, 371284982310614889, 371284981497477969, 371284980683778770, 371284980674638806, 371284979912842977, 371284978987042848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494823274972676, 362494840745909849⟩, ⟨(-348283243331567131), (-347866791997640845)⟩, true⟩

def words06 : List Nat := [371284978060796927, 371284977749999411, 371284977070009143, 371284977101207449, 371284977102093429, 371284977005014986, 371284976723634946, 371284976985722825, 371284977779258158, 371284978060077363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486855866089553, 362486873347494226⟩, ⟨(-67230954541427825), (-66814133968032561)⟩, true⟩

def words07 : List Nat := [371284978344395908, 371284978629086858, 371284979246621438, 371284979465363378, 371284979763261971, 371284980061568391, 371284980215262773, 371284980216409253, 371284979521363498, 371284979576513584]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480426023200229, 362480443514797948⟩, ⟨159782149700591916, 160199329938783690⟩, true⟩

def words08 : List Nat := [371284980434064325, 371284980715777127, 371284980977751443, 371284981240085313, 371284981749580508, 371284981860743408, 371284982249787479, 371284982639279938, 371284983024236459, 371284983025422454]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362529767139027229, 362529784640973635⟩, ⟨(-1581649129340810774), (-1581231583844796226)⟩, true⟩

def words09 : List Nat := [371284983571650195, 371284984247054307, 371284985514574754, 371284986117033066, 371284986657586717, 371284987198478299, 371284988409578747, 371284989274062477, 371284990543836201, 371284991814032620]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk352
