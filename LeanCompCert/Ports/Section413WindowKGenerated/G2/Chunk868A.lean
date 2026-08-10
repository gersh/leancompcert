import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578332775128189, 360578382160384663⟩, ⟨327769663605888847, 330664472122189131⟩, true⟩

def state01 : KState := ⟨⟨360582042029206253, 360582091426243141⟩, ⟨5784244445649887, 8680075560217059⟩, true⟩

def words00 : List Nat := [360582191616044757, 360582191559955205, 360582191683478155, 360582191807237527, 360582191818708716, 360582191819957531, 360582191698665371, 360582191574308501, 360582191449587993, 360582191415594140]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579631317943383, 360579680726876352⟩, ⟨215097362944012410, 217994226814400074⟩, true⟩

def words01 : List Nat := [360582191415557278, 360582191334810138, 360582191304331753, 360582191465867893, 360582191570185893, 360582191674705248, 360582191701768810, 360582191703017953, 360582191630055401, 360582191602559541]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360559828744680927, 360559878165390851⟩, ⟨1934377082730917702, 1937274969134619314⟩, true⟩

def words02 : List Nat := [360582191574666792, 360582191518224209, 360582191329091991, 360582191038914292, 360582190748542253, 360582190382836973, 360582190098386172, 360582189853632421, 360582189608725912, 360582189290222530]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587949515021914, 360587998947523600⟩, ⟨(-507519817840962700), (-504620907500559112)⟩, true⟩

def words03 : List Nat := [360582189034284179, 360582188860016914, 360582188685372328, 360582188606378587, 360582188507047371, 360582188281054251, 360582188054823454, 360582187961407164, 360582188019145410, 360582188087359616]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577728323259630, 360577777767680193⟩, ⟨380126534747978661, 383026480183334419⟩, true⟩

def words04 : List Nat := [360582188089161711, 360582188094786099, 360582188232572483, 360582188370722776, 360582188422138058, 360582188423387584, 360582188371780988, 360582188253989119, 360582188135978279, 360582187974705908]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868A
