import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489234119082734, 362489278499634708⟩, ⟨(-242323193224674777), (-240668251564895291)⟩, true⟩

def state01 : KState := ⟨⟨362487658688668267, 362487703085763234⟩, ⟨(-155269153733394421), (-153613298812665187)⟩, true⟩

def words00 : List Nat := [371284919054493469, 371284919190213027, 371284919326003774, 371284919462400047, 371284919674427940, 371284919723887205, 371284920100217430, 371284920477305559, 371284920738272874, 371284920790589942]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520212153308406, 362520256567179551⟩, ⟨(-1952737280442084480), (-1951080499225113686)⟩, true⟩

def words01 : List Nat := [371284921006577789, 371284921223493151, 371284921767087083, 371284921970987523, 371284922121377788, 371284922272392531, 371284922750180577, 371284923064511730, 371284923705639927, 371284924347566993]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496412518547271, 362496456949190255⟩, ⟨(-638496239501911449), (-636838532059690911)⟩, true⟩

def words02 : List Nat := [371284924982021422, 371284925180197868, 371284925465032287, 371284925750842352, 371284926117672143, 371284926119530398, 371284926098818416, 371284926052211394, 371284926283770794, 371284926494698038]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467009425361257, 362467053872732063⟩, ⟨985647219988486893, 987305851395459423⟩, true⟩

def words03 : List Nat := [371284926873004556, 371284927252070475, 371284927583459575, 371284927585317797, 371284927480050509, 371284927475571254, 371284927539095489, 371284927540954136, 371284927218288385, 371284926896834081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362497817335358836, 362497861799383202⟩, ⟨(-716312969367980223), (-714653417936099995)⟩, true⟩

def words04 : List Nat := [371284926574549357, 371284926507128077, 371284926498198996, 371284926658797278, 371284926758799217, 371284926760660549, 371284926525518837, 371284926546602064, 371284926893950612, 371284927130002809]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552A
