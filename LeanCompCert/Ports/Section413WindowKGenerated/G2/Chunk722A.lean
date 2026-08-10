import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582037547256064, 360582071227276817⟩, ⟨19223618086599009, 20866100506609015⟩, true⟩

def state01 : KState := ⟨⟨360575032149949832, 360575065839724000⟩, ⟨524942622831680198, 526585809496073628⟩, true⟩

def words00 : List Nat := [360582360228349815, 360582360101326270, 360582359917375701, 360582359880867994, 360582359844097115, 360582359674783714, 360582359366040636, 360582358947229967, 360582358528234709, 360582358261957709]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360542400569862069, 360542434269306600⟩, ⟨2881521042258449939, 2883164927267623691⟩, true⟩

def words01 : List Nat := [360582358252275042, 360582358343791687, 360582358344705079, 360582358340595183, 360582358144892158, 360582357775820622, 360582357406444703, 360582357196253765, 360582356794549373, 360582356242821799]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607655484775725, 360607689193897178⟩, ⟨(-1831533948534046354), (-1829889364611067436)⟩, true⟩

def words02 : List Nat := [360582355690875689, 360582355330642855, 360582355066666522, 360582354994286409, 360582354921838853, 360582354686880729, 360582354647235833, 360582354723821584, 360582354991469741, 360582355343270563]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583061990290063, 360583095709189312⟩, ⟨(-55023170798725303), (-53377880577492291)⟩, true⟩

def words03 : List Nat := [360582355599374476, 360582355855583060, 360582356026471120, 360582356293586860, 360582356511810199, 360582356730194695, 360582356806710667, 360582356807738351, 360582356811534630, 360582356822953276]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574405697441628, 360574439425993844⟩, ⟨570305522257873948, 571951509858537806⟩, true⟩

def words04 : List Nat := [360582356890865941, 360582356891891941, 360582356849467959, 360582356681566994, 360582356513503517, 360582356297153642, 360582356176989666, 360582356053126213, 360582355929147551, 360582355709867319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk722A
