import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604069550836998, 360604073037966171⟩, ⟨(-508153185629875314), (-508095859012781326)⟩, true⟩

def state01 : KState := ⟨⟨360632199459427185, 360632202949540478⟩, ⟨(-1192052574244834898), (-1191995175098808584)⟩, true⟩

def words00 : List Nat := [360583166174770448, 360583166915426294, 360583166915708630, 360583166801145592, 360583166686534793, 360583166419089065, 360583167931931882, 360583169444710704, 360583169828060465, 360583171845303762]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360667337278154274, 360667340771261011⟩, ⟨(-2046785397896151907), (-2046727925964265535)⟩, true⟩

def words01 : List Nat := [360583173227230245, 360583174609130736, 360583176920332292, 360583177552593236, 360583177552885506, 360583176765779422, 360583176881787182, 360583179089440203, 360583182550292315, 360583186010931902]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580281304898136, 360580284801022072⟩, ⟨70375553478670294, 70433098804028410⟩, true⟩

def words02 : List Nat := [360583188075386445, 360583188461719150, 360583189327735305, 360583190193771527, 360583190194041938, 360583189842786451, 360583187813818153, 360583184548910903, 360583181284211624, 360583179708494495]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360524282347453478, 360524285846569835⟩, ⟨1433263965893563156, 1433321584039404600⟩, true⟩

def words03 : List Nat := [360583180344081055, 360583181098653638, 360583181098936255, 360583181001049120, 360583180091333908, 360583178418373561, 360583176759925456, 360583176760242824, 360583175758893599, 360583173339751405]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609797212381350, 360609800714492546⟩, ⟨(-648582616789459111), (-648524925734219847)⟩, true⟩

def words04 : List Nat := [360583170920736567, 360583169668952365, 360583169259126690, 360583169088149542, 360583168917163503, 360583167277479778, 360583166459207192, 360583166612718834, 360583167246987788, 360583168341048572]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243A
