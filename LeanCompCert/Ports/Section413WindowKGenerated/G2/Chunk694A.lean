import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554434597582244, 360554465618282324⟩, ⟨1958712969711295560, 1960167145927550682⟩, true⟩

def state01 : KState := ⟨⟨360580385851268185, 360580416881235734⟩, ⟨157614366088386231, 159069185513851711⟩, true⟩

def words00 : List Nat := [360582709695471969, 360582709496699549, 360582709555874671, 360582709689595767, 360582709690517443, 360582709632150047, 360582709366187754, 360582709074022475, 360582708781568071, 360582708614206688]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564045492194864, 360564076531525155⟩, ⟨1291922336095523501, 1293377805434508607⟩, true⟩

def words01 : List Nat := [360582708582067515, 360582708403767694, 360582708225267579, 360582708247324146, 360582708272500174, 360582708297835589, 360582708298720044, 360582708217802664, 360582707997366993, 360582707730105313]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570215585598804, 360570246634180692⟩, ⟨863481027795265607, 864937139424718247⟩, true⟩

def words02 : List Nat := [360582707462525239, 360582707227609785, 360582706843672708, 360582706346476010, 360582705849134505, 360582705299479054, 360582704925180472, 360582704758042383, 360582704590799436, 360582704320187098]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585532485337444, 360585563543205257⟩, ⟨(-200112155262390798), (-198655398865042640)⟩, true⟩

def words03 : List Nat := [360582704169072549, 360582704197678117, 360582704198490634, 360582704137327287, 360582703922730645, 360582703530945208, 360582703138984125, 360582702845034704, 360582702721333410, 360582702763566931]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554482151030606, 360554513218257140⟩, ⟨1956030711201973323, 1957488117515092161⟩, true⟩

def words04 : List Nat := [360582702764442640, 360582702692784926, 360582702413734863, 360582702100953639, 360582701787914411, 360582701309302873, 360582700771336026, 360582700071530155, 360582699371556742, 360582698792303434]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694A
