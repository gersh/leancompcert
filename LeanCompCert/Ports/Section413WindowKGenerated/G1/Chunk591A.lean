import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489950442490327, 362490001593072251⟩, ⟨(-295868143370853299), (-293826132312687849)⟩, true⟩

def state01 : KState := ⟨⟨362477613634681359, 362477664803078517⟩, ⟨433297241256050590, 435340305287587480⟩, true⟩

def words00 : List Nat := [371285030202634079, 371285030204634007, 371285030098781473, 371285029950799946, 371285029802030588, 371285029739590887, 371285029613570417, 371285029695409329, 371285029719045987, 371285029721117556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509241890129394, 362509293076599485⟩, ⟨(-1436417572702660299), (-1434373440287186337)⟩, true⟩

def words01 : List Nat := [371285029662035968, 371285029728615678, 371285030080726354, 371285030178385987, 371285030195457999, 371285030213106451, 371285030468859649, 371285030594914107, 371285031006663893, 371285031419315489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504027351602056, 362504078556144681⟩, ⟨(-1128106286782468992), (-1126061085828049990)⟩, true⟩

def words02 : List Nat := [371285031832289315, 371285032042597691, 371285032538732210, 371285033035874979, 371285033530740704, 371285033803379888, 371285034074179591, 371285034345667269, 371285034733684631, 371285035058050145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486468482950235, 362486519705480146⟩, ⟨(-89693626862617285), (-87647362229656479)⟩, true⟩

def words03 : List Nat := [371285035593116065, 371285036128957644, 371285036642728944, 371285036775634609, 371285036993503653, 371285037212441570, 371285037618982253, 371285037644857828, 371285037671426703, 371285037698712766]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489696932648906, 362489748173096564⟩, ⟨(-280626051394610403), (-278578727015330805)⟩, true⟩

def words04 : List Nat := [371285038011420978, 371285038182742479, 371285038388574291, 371285038595201946, 371285038758359246, 371285038760359023, 371285038542136843, 371285038424302713, 371285038471451208, 371285038553191316]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591A
