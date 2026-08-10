import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594619108315873, 360594671129301997⟩, ⟨(-1123396849081753411), (-1120270347035419049)⟩, true⟩

def state01 : KState := ⟨⟨360585184058885050, 360585236092089261⟩, ⟨(-283757364634768868), (-280629775119507792)⟩, true⟩

def words00 : List Nat := [360582084002864286, 360582084004147427, 360582083955601520, 360582083995237562, 360582083996330033, 360582083949026359, 360582083803299619, 360582083594472045, 360582083385403202, 360582083338214802]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556754781413660, 360556806826721176⟩, ⟨2246884543468936539, 2250013210359379071⟩, true⟩

def words01 : List Nat := [360582083365398975, 360582083392857920, 360582083394001267, 360582083358193752, 360582083196169123, 360582082974582913, 360582082752624654, 360582082656913006, 360582082476774435, 360582082194170731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585685637746706, 360585737695167162⟩, ⟨(-328675874996549709), (-325546129751713735)⟩, true⟩

def words02 : List Nat := [360582081911282205, 360582081754764596, 360582081679376483, 360582081623614294, 360582081567748822, 360582081404201539, 360582081243335320, 360582081183460749, 360582081123200024, 360582081147113656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571943854173364, 360571995923836172⟩, ⟨894807975317702255, 897938810557248809⟩, true⟩

def words03 : List Nat := [360582081148257400, 360582081114470645, 360582081080457671, 360582081019768452, 360582081020842527, 360582081013179431, 360582081005392743, 360582080917435386, 360582080703290819, 360582080591519879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568824301108709, 360568876382855475⟩, ⟨1172568821195160352, 1175700732450402100⟩, true⟩

def words04 : List Nat := [360582080491964344, 360582080493248015, 360582080394377123, 360582080219388499, 360582080044201524, 360582079788314989, 360582079630584317, 360582079470206830, 360582079309692941, 360582079086195738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk890A
