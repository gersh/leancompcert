import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481645830743168, 362481755743871170⟩, ⟨295517099513415255, 301855045787768073⟩, true⟩

def state01 : KState := ⟨⟨362467524054595671, 362467633994526509⟩, ⟨1501543947073487605, 1507884182443173417⟩, true⟩

def words00 : List Nat := [371285290307133797, 371285290267415186, 371285290044014431, 371285289925950895, 371285289806438495, 371285289711251149, 371285289432648106, 371285289132203345, 371285288830506508, 371285288650684374]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464324622024077, 362464434588605509⟩, ⟨1774883167733417096, 1781225679472207780⟩, true⟩

def words01 : List Nat := [371285288445994758, 371285288379453231, 371285288311937823, 371285288239388594, 371285288052226546, 371285287872166616, 371285287690544985, 371285287631699780, 371285287389469491, 371285287148655524]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474029785391705, 362474139778601441⟩, ⟨945814825065436000, 952159611526580166⟩, true⟩

def words02 : List Nat := [371285286906588559, 371285286722344494, 371285286479099900, 371285286328239031, 371285286176420560, 371285285982702601, 371285285667768260, 371285285491354801, 371285285313339713, 371285285273293313]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472970881446322, 362473080901709292⟩, ⟨1036298064485208014, 1042645162237565480⟩, true⟩

def words03 : List Nat := [371285285145050289, 371285285017757964, 371285284889234042, 371285284868521213, 371285284792555406, 371285284725065062, 371285284656618001, 371285284562448404, 371285284284754844, 371285284145649339]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473812120033559, 362473922166783944⟩, ⟨964456840281766609, 970806201255196285⟩, true⟩

def words04 : List Nat := [371285284004836947, 371285283977502573, 371285283861739785, 371285283742669375, 371285283622492724, 371285283520487130, 371285283359433481, 371285283336489016, 371285283312543336, 371285283269197698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486341010598424, 362486451084136774⟩, ⟨(-106160588915902969), (-99808938773310033)⟩, true⟩

def words05 : List Nat := [371285283142141786, 371285283149548246, 371285283292279999, 371285283295249434, 371285283255775391, 371285283193688858, 371285283179029371, 371285283182301953, 371285283178432278, 371285283195406555]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479576807422737, 362479686907802308⟩, ⟨471894541087142097, 478248485214447603⟩, true⟩

def words06 : List Nat := [371285283205899397, 371285283208889907, 371285283124234775, 371285283070785543, 371285283015808261, 371285283003586046, 371285282822705279, 371285282643399369, 371285282462910926, 371285282420674830]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467474137660389, 362467584264770238⟩, ⟨1506427888173282194, 1512784117076714086⟩, true⟩

def words07 : List Nat := [371285282416758537, 371285282479558836, 371285282541697563, 371285282544668240, 371285282424234189, 371285282329469195, 371285282233223578, 371285282194429655, 371285281989701924, 371285281786027570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473196780762788, 362473306934475024⟩, ⟨1017228335254123058, 1023586838261614460⟩, true⟩

def words08 : List Nat := [371285281581025884, 371285281421300880, 371285281192834583, 371285281088960263, 371285280984133760, 371285280849872129, 371285280532285404, 371285280353025873, 371285280172172397, 371285280110732617]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476684984161166, 362476795164972179⟩, ⟨718974963769767128, 725335783583194646⟩, true⟩

def words09 : List Nat := [371285279972965586, 371285279802209015, 371285279630254976, 371285279523754770, 371285279347837834, 371285279214985243, 371285279081105515, 371285278947945929, 371285278719957301, 371285278624429293]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk854
