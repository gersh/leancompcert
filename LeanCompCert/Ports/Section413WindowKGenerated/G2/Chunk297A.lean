import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360624792698041512, 360624797998807497⟩, ⟨(-1226389849322580649), (-1226283378184088285)⟩, true⟩

def state01 : KState := ⟨⟨360586313697863551, 360586319002336309⟩, ⟨(-83544753981097955), (-83438172732041525)⟩, true⟩

def words00 : List Nat := [360583511751022528, 360583511987414845, 360583511987765575, 360583511661313669, 360583511334821075, 360583510375572938, 360583510379123632, 360583510770945050, 360583510771299086, 360583510676371783]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360626427178995874, 360626432487185822⟩, ⟨(-1275769909544168902), (-1275663217839335984)⟩, true⟩

def words01 : List Nat := [360583510676692638, 360583510483619935, 360583510806605036, 360583510806998832, 360583510533957610, 360583509229174344, 360583507924401347, 360583508322865947, 360583509767470135, 360583511212065896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619750305450550, 360619755617393863⟩, ⟨(-1077291388970269469), (-1077184585696720187)⟩, true⟩

def words02 : List Nat := [360583512094600919, 360583513595138238, 360583516223131768, 360583518851063553, 360583520785944869, 360583521961427549, 360583522543545875, 360583523125664377, 360583523373901061, 360583524593018743]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360518131687900683, 360518137003556148⟩, ⟨1944422584235684130, 1944529497890249440⟩, true⟩

def words03 : List Nat := [360583526138797308, 360583527684545654, 360583528213617721, 360583528214011849, 360583527617345517, 360583526464981109, 360583525312567621, 360583524976926592, 360583523515737454, 360583521317540353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593535040882407, 360593540360264739⟩, ⟨(-298538844599859163), (-298431820090283831)⟩, true⟩

def words04 : List Nat := [360583519119402236, 360583518047864666, 360583517545917051, 360583516976526496, 360583516407142396, 360583514897909668, 360583512594518451, 360583511154022734, 360583509713508482, 360583509375756982]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297A
