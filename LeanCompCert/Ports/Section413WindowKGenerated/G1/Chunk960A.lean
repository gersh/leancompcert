import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494036016442270, 362494176169247155⟩, ⟨(-864863241755760969), (-855779186208849649)⟩, true⟩

def state01 : KState := ⟨⟨362487352168472141, 362487492351218291⟩, ⟨(-223148766186379586), (-214061836118254010)⟩, true⟩

def words00 : List Nat := [371285262099382238, 371285262186991620, 371285262274259760, 371285262362609998, 371285262449284610, 371285262483301881, 371285262578220351, 371285262674556544, 371285262769187648, 371285262795895274]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496748567414960, 362496888780618087⟩, ⟨(-1125307851817597658), (-1116217997424048840)⟩, true⟩

def words01 : List Nat := [371285262912350793, 371285263030625898, 371285263255715658, 371285263352166630, 371285263420828646, 371285263490591599, 371285263667560027, 371285263804493546, 371285263927903510, 371285264052720815]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495143376329192, 362495283619916924⟩, ⟨(-971216996058397240), (-962124223979298936)⟩, true⟩

def words02 : List Nat := [371285264165979431, 371285264169348175, 371285264239721266, 371285264327077129, 371285264422292563, 371285264447647672, 371285264471594630, 371285264496648929, 371285264619615594, 371285264727851036]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484356582567773, 362484496856525578⟩, ⟨64708318091400508, 73804006761202196⟩, true⟩

def words03 : List Nat := [371285264891970329, 371285265057494076, 371285265188916648, 371285265192284213, 371285265195684558, 371285265216469203, 371285265333651752, 371285265337022134, 371285265332185200, 371285265328066199]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489177481572927, 362489317785678708⟩, ⟨(-398302173734811066), (-389203589504143830)⟩, true⟩

def words04 : List Nat := [371285265369593331, 371285265373304980, 371285265470746074, 371285265576247014, 371285265666872686, 371285265670240742, 371285265616010810, 371285265608436231, 371285265688586009, 371285265734273683]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960A
