import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547626011616790, 360547680118169101⟩, ⟨3110892860784399717, 3114206756838352455⟩, true⟩

def state01 : KState := ⟨⟨360589799191396912, 360589853310309335⟩, ⟨(-714465305129926040), (-711150287951969212)⟩, true⟩

def words00 : List Nat := [360582014986068196, 360582014645575142, 360582014365678712, 360582014207450031, 360582014049123070, 360582013787520400, 360582013617774551, 360582013534183377, 360582013486574418, 360582013574357224]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580708661765487, 360580762793186279⟩, ⟨110171056433100716, 113487208306593426⟩, true⟩

def words01 : List Nat := [360582013601297453, 360582013628375735, 360582013652471429, 360582013753578929, 360582013823853703, 360582013894340769, 360582013895515650, 360582013874453198, 360582013766730269, 360582013754477137]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565580543807683, 360565634687558568⟩, ⟨1482671525328151001, 1485988795850838163⟩, true⟩

def words02 : List Nat := [360582013827926653, 360582013829236681, 360582013795251962, 360582013700523188, 360582013605585678, 360582013449842285, 360582013354760082, 360582013208821474, 360582013062748399, 360582012829252064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585301574238838, 360585355730352916⟩, ⟨(-306689229153386213), (-303370836856489495)⟩, true⟩

def words03 : List Nat := [360582012649797814, 360582012592064594, 360582012546919593, 360582012564144020, 360582012565354102, 360582012468055953, 360582012370509178, 360582012393339008, 360582012431250727, 360582012469458101]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587650393003649, 360587704561614326⟩, ⟨(-519962110046303535), (-516642583749445783)⟩, true⟩

def words04 : List Nat := [360582012470646938, 360582012401902985, 360582012252477156, 360582012196788217, 360582012140749761, 360582012054514037, 360582011939387118, 360582011762658788, 360582011585659916, 360582011593120872]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907A
