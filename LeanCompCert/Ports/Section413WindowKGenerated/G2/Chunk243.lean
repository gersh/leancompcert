import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243

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

def state06 : KState := ⟨⟨360603436285479639, 360603439790618349⟩, ⟨(-493784483686484749), (-493726718896825087)⟩, true⟩

def words05 : List Nat := [360583168585066525, 360583168829099035, 360583168829360515, 360583170160884070, 360583171099993587, 360583172039077628, 360583172039360985, 360583171882126090, 360583171862545095, 360583172694895808]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563588731623887, 360563592239751301⟩, ⟨477100418067057960, 477158255676962384⟩, true⟩

def words06 : List Nat := [360583174057035317, 360583174953802515, 360583175004385654, 360583175054996668, 360583175055264412, 360583174010813805, 360583173965772709, 360583173586612224, 360583173207448287, 360583171979417980]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360699558082009327, 360699561593136433⟩, ⟨(-2837192946341418417), (-2837135035614283225)⟩, true⟩

def words07 : List Nat := [360583172055156207, 360583172934321316, 360583175495402182, 360583178102470397, 360583179269425472, 360583180436310054, 360583182313898023, 360583185406668079, 360583190180353720, 360583194953719909]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360651444914532580, 360651448428692403⟩, ⟨(-1664300396136646731), (-1664242411457252521)⟩, true⟩

def words08 : List Nat := [360583198343615679, 360583200631300237, 360583203865758078, 360583207100043209, 360583209896133975, 360583211597178304, 360583212021867233, 360583212446561118, 360583213807111137, 360583216605009190]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582652473965293, 360582655991117394⟩, ⟨14019473528461540, 14077531204580804⟩, true⟩

def words09 : List Nat := [360583221082162411, 360583225559009193, 360583229056791583, 360583230886884228, 360583230980609722, 360583231074406754, 360583232143339317, 360583232962148469, 360583232962434456, 360583232939117582]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk243
