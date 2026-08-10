import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615364004518474, 360615384081884153⟩, ⟨(-1892511861672344416), (-1891748159271279412)⟩, true⟩

def state01 : KState := ⟨⟨360575031662015859, 360575051746858579⟩, ⟨378234145771203908, 378998269166936750⟩, true⟩

def words00 : List Nat := [360581783820141321, 360581783857663130, 360581783876543903, 360581783895662400, 360581783896318606, 360581783835508637, 360581783571382125, 360581783136373060, 360581782701219943, 360581782314593741]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558623460079113, 360558643552302505⟩, ⟨1302337969371780500, 1303102508410666586⟩, true⟩

def words01 : List Nat := [360581782391006400, 360581782587087264, 360581782624825453, 360581782625610104, 360581782485542779, 360581782130534455, 360581781775302838, 360581781688145002, 360581781435829986, 360581781025818320]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561020114621515, 360561040214256241⟩, ⟨1167445293054890854, 1168210249536245910⟩, true⟩

def words02 : List Nat := [360581780615639813, 360581780309932291, 360581780453152612, 360581780648376832, 360581780649100857, 360581780575655547, 360581780187734388, 360581779802911429, 360581779417886222, 360581778901448435]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564069004253935, 360564089111361487⟩, ⟨995666580385879220, 996431957848584100⟩, true⟩

def words03 : List Nat := [360581778534000861, 360581777921693288, 360581777309257206, 360581777011649313, 360581776921282909, 360581776675034520, 360581776428695664, 360581776003449931, 360581775472620554, 360581775159601611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582102310044554, 360582122424552475⟩, ⟨(-20435763434376955), (-19669968998548281)⟩, true⟩

def words04 : List Nat := [360581774846325213, 360581774795087072, 360581774795798205, 360581774580874404, 360581774365830343, 360581774005697185, 360581773803324280, 360581773707644432, 360581773611889411, 360581773362974180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563A
