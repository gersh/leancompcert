import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk798A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557326581419776, 360557368051138378⟩, ⟨1978196433304336701, 1980431461366803739⟩, true⟩

def state01 : KState := ⟨⟨360543570890587602, 360543612371042347⟩, ⟨3075969002969329318, 3078204887829998412⟩, true⟩

def words00 : List Nat := [360582185177928552, 360582185024866382, 360582184714998750, 360582184326405876, 360582183937643093, 360582183445515035, 360582183041881959, 360582182573124014, 360582182104252686, 360582181533902014]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582307482232743, 360582348973461490⟩, ⟨(-15786915778299072), (-13550170990351662)⟩, true⟩

def words01 : List Nat := [360582181051568418, 360582180726349178, 360582180400790217, 360582180232228239, 360582180067623779, 360582179752020582, 360582179436199094, 360582179277457181, 360582179213179064, 360582179216492894]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571673370848913, 360571714872965981⟩, ⟨832967775792803870, 835205389739598426⟩, true⟩

def words02 : List Nat := [360582179217537636, 360582179101006182, 360582178864125792, 360582178784299338, 360582178704174304, 360582178549477869, 360582178274813730, 360582177855238414, 360582177435435212, 360582177172724714]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557393962666438, 360557435475531909⟩, ⟨1972972030244200172, 1975210502289636382⟩, true⟩

def words03 : List Nat := [360582177042592067, 360582177026307959, 360582177009903324, 360582176874952708, 360582176621849850, 360582176261132048, 360582175900089065, 360582175625286059, 360582175394718439, 360582175086031529]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587945721158857, 360587987244818323⟩, ⟨(-466329732035459724), (-464090398143763290)⟩, true⟩

def words04 : List Nat := [360582174777093618, 360582174625160597, 360582174718621488, 360582174844347497, 360582174845400655, 360582174847301382, 360582175015093868, 360582175183229109, 360582175216106493, 360582175290075819]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk798A
