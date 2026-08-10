import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602892297007605, 360602908774156045⟩, ⟨(-1072884487521140891), (-1072314452820233063)⟩, true⟩

def state01 : KState := ⟨⟨360570227000370874, 360570243484264415⟩, ⟨599597909365538578, 600168289448647698⟩, true⟩

def words00 : List Nat := [360581965759420815, 360581965760128866, 360581965814761754, 360581966032829983, 360581966033438247, 360581965889661924, 360581965365383467, 360581964579408276, 360581963793328038, 360581963232154450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543006524598065, 360543023015168467⟩, ⟨1993800415923017299, 1994371137961221829⟩, true⟩

def words01 : List Nat := [360581963065126645, 360581963127097107, 360581963127728089, 360581962960405789, 360581962593592926, 360581962131700503, 360581961669613269, 360581961587978327, 360581961126030449, 360581960366553888]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580514232889042, 360580530730141334⟩, ⟨72392491475335702, 72963555793803192⟩, true⟩

def words02 : List Nat := [360581959606945488, 360581958785289301, 360581958155967149, 360581957842754945, 360581957529498931, 360581956897336891, 360581956275497207, 360581955712051592, 360581955148413141, 360581954965077774]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584234800731942, 360584251304737131⟩, ⟨(-118357325822240505), (-117785915519040829)⟩, true⟩

def words03 : List Nat := [360581954937908429, 360581954720164447, 360581954502305987, 360581954120038198, 360581953929926464, 360581953644833175, 360581953359679446, 360581952883310891, 360581952593620265, 360581952639302830]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567599132531778, 360567615643208506⟩, ⟨734133500934833688, 734705253119989234⟩, true⟩

def words04 : List Nat := [360581953064695129, 360581953110297764, 360581953110931192, 360581952895854622, 360581952680670173, 360581952283044147, 360581952130617063, 360581951968520027, 360581951806356136, 360581951355464506]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512A
