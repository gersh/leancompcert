import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360715317899898853, 360715319762693739⟩, ⟨(-2362669428894869844), (-2362646732627777372)⟩, true⟩

def state01 : KState := ⟨⟨360634371678105256, 360634373543053592⟩, ⟨(-905287610538544779), (-905264875498400113)⟩, true⟩

def words00 : List Nat := [360584078159008675, 360584084351461006, 360584088342317518, 360584092332759122, 360584094602992522, 360584098415700470, 360584102694823895, 360584106973514569, 360584108974493785, 360584111765501075]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360686912234484297, 360686914101597541⟩, ⟨(-1852159805101195420), (-1852137031060840728)⟩, true⟩

def words01 : List Nat := [360584113663266084, 360584115560884282, 360584120530319639, 360584122440748786, 360584122440959715, 360584121722575633, 360584122097657946, 360584126097896821, 360584131802189004, 360584137505900253]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565311870759944, 360565313740050450⟩, ⟨339345155516146400, 339367968801997270⟩, true⟩

def words02 : List Nat := [360584141662414085, 360584142762024735, 360584145849504158, 360584148936707648, 360584149742607191, 360584149742836282, 360584147492863464, 360584143674957286, 360584139857432199, 360584136145419391]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360426854857288360, 360426856728740706⟩, ⟨2836498018552793453, 2836520870827351367⟩, true⟩

def words03 : List Nat := [360584135101714703, 360584133416646734, 360584131731736377, 360584128502849108, 360584123435073715, 360584117579646089, 360584111724799050, 360584106865881005, 360584100526430124, 360584091810272156]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360663946380173261, 360663948253787589⟩, ⟨(-1441841123006359870), (-1441818231718835206)⟩, true⟩

def words04 : List Nat := [360584083095027225, 360584077442341068, 360584073761296135, 360584073141891561, 360584072522538442, 360584069300887608, 360584066197131947, 360584066153958105, 360584069127138590, 360584073552567777]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180A
