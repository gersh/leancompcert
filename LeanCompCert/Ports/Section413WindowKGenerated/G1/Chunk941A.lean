import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503539226900911, 362503673678615727⟩, ⟨(-1750645876903296277), (-1742103729800091823)⟩, true⟩

def state01 : KState := ⟨⟨362489815201296344, 362489949682767088⟩, ⟨(-459194629047606424), (-450649681756772424)⟩, true⟩

def words00 : List Nat := [371285160729274592, 371285160756841468, 371285160889404117, 371285161023740644, 371285161139119562, 371285161142415107, 371285161117955741, 371285161088334448, 371285161137069297, 371285161191711242]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482583791302931, 362482718302467184⟩, ⟨221439181985474461, 229986923879523935⟩, true⟩

def words01 : List Nat := [371285161357781380, 371285161525246929, 371285161691927955, 371285161708937705, 371285161730294583, 371285161753241512, 371285161887421238, 371285161890717331, 371285161874655359, 371285161852444655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485197302092852, 362485331842803408⟩, ⟨(-24481741626369192), (-15931218687861050)⟩, true⟩

def words02 : List Nat := [371285161915692274, 371285161968039856, 371285162114461941, 371285162262193347, 371285162390022212, 371285162401811454, 371285162458228206, 371285162516386126, 371285162592405913, 371285162597616511]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488541342770687, 362488675913489904⟩, ⟨(-339268944839059333), (-330715597032708861)⟩, true⟩

def words03 : List Nat := [371285162602293900, 371285162608032747, 371285162683540547, 371285162715093494, 371285162773514071, 371285162833290896, 371285162891577199, 371285162894896458, 371285162890527887, 371285162931929982]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484295917177592, 362484430517311116⟩, ⟨60421078423343415, 68977195443339049⟩, true⟩

def words04 : List Nat := [371285163066172195, 371285163069469147, 371285163065484238, 371285163040744195, 371285163014698513, 371285163015896342, 371285163041212540, 371285163103599459, 371285163144693721, 371285163148170844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941A
