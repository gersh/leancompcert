import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876A

def state06 : KState := ⟨⟨360572321292609536, 360572371699760311⟩, ⟨852594760268173325, 855578709348477569⟩, true⟩

def words05 : List Nat := [360582131680650158, 360582131716817001, 360582131753847588, 360582131891651096, 360582131976387181, 360582132061327008, 360582132070777491, 360582132072040081, 360582132004828187, 360582131894938825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566848836155988, 360566899255205494⟩, ⟨1332276269189414114, 1335261261371465654⟩, true⟩

def words06 : List Nat := [360582131784636847, 360582131671034815, 360582131469442965, 360582131202861083, 360582130936079431, 360582130620163038, 360582130382853377, 360582130216970700, 360582130050945741, 360582129793147453]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592775176085680, 360592825607038060⟩, ⟨(-940839026406572167), (-937852990640047629)⟩, true⟩

def words07 : List Nat := [360582129620443883, 360582129578070488, 360582129588665904, 360582129589928443, 360582129558236508, 360582129402660020, 360582129246843634, 360582129174602205, 360582129289688307, 360582129412986441]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588438779596230, 360588489222584088⟩, ⟨(-560652360732881226), (-557665269636439048)⟩, true⟩

def words08 : List Nat := [360582129436706827, 360582129464034089, 360582129621011944, 360582129778357187, 360582129839064188, 360582129857086115, 360582129858221374, 360582129811378967, 360582129764313258, 360582129786956300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582283439329585, 360582333894210247⟩, ⟨(-20814059698607894), (-17825925662892792)⟩, true⟩

def words09 : List Nat := [360582129990386637, 360582130194063051, 360582130332494013, 360582130373569265, 360582130381810781, 360582130390427200, 360582130528502629, 360582130629186141, 360582130632631649, 360582130636258082]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876B
