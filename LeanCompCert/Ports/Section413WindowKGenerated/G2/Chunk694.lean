import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694

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

def state06 : KState := ⟨⟨360553175848771444, 360553206925250991⟩, ⟨2046855681978539212, 2048313730959753972⟩, true⟩

def words05 : List Nat := [360582698387264301, 360582698154893923, 360582697922431273, 360582697586224730, 360582697395515372, 360582697110395432, 360582696824995429, 360582696746582106, 360582696460950890, 360582696037415687]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583366122234083, 360583397208005088⟩, ⟨(-50334646256943911), (-48875951844772059)⟩, true⟩

def words06 : List Nat := [360582695613682441, 360582695186350499, 360582694912522317, 360582694845647612, 360582694778702625, 360582694507187121, 360582694098383360, 360582693896632627, 360582693694580599, 360582693663334006]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564256095902255, 360564287191042532⟩, ⟨1277398134555033727, 1278857479897082961⟩, true⟩

def words07 : List Nat := [360582693664219876, 360582693557234401, 360582693548790413, 360582693753081311, 360582693812618662, 360582693872305821, 360582693873181952, 360582693829473977, 360582693578602080, 360582693314817678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565121590170472, 360565152694584415⟩, ⟨1217308756208017441, 1218768745930474927⟩, true⟩

def words08 : List Nat := [360582693050704051, 360582692993461421, 360582692945126797, 360582692745328493, 360582692545378858, 360582692232895250, 360582692054516975, 360582691908755192, 360582691762913673, 360582691459096295]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607291007985102, 360607322121686057⟩, ⟨(-1713305585920470971), (-1711844950799342911)⟩, true⟩

def words09 : List Nat := [360582691207502563, 360582691162803943, 360582691278631959, 360582691279615475, 360582691234437470, 360582691005802271, 360582690776965493, 360582690902863789, 360582691258065193, 360582691613480430]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk694
