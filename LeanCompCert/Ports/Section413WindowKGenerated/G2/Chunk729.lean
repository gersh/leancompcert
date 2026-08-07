import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607166096185422, 360607200458834380⟩, ⟨(-1810155144069855706), (-1808463136586876992)⟩, true⟩

def state01 : KState := ⟨⟨360612110307688952, 360612144680087001⟩, ⟨(-2170662231408775113), (-2168969513167077709)⟩, true⟩

def words00 : List Nat := [360582393877636874, 360582394219055855, 360582394444563750, 360582394670181206, 360582394765782074, 360582394980283861, 360582395382285129, 360582395784480649, 360582396091533248, 360582396500619334]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604335361074983, 360604369743264928⟩, ⟨(-1603693102380206934), (-1601999670162211398)⟩, true⟩

def words01 : List Nat := [360582397097252796, 360582397694194874, 360582398355519983, 360582398829347800, 360582399142194157, 360582399455112357, 360582399762053198, 360582400163170160, 360582400465311542, 360582400767658968]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619382653782907, 360619417045843280⟩, ⟨(-2701129308022430987), (-2699435156007091731)⟩, true⟩

def words02 : List Nat := [360582400962594749, 360582401106071469, 360582401437092774, 360582401768409237, 360582402052441019, 360582402342008671, 360582402505969457, 360582402670029133, 360582402987932649, 360582403496652853]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592831124363312, 360592865526185464⟩, ⟨(-764526901017077890), (-762832037024760636)⟩, true⟩

def words03 : List Nat := [360582404192706257, 360582404888938997, 360582405427535096, 360582405778633169, 360582406044669356, 360582406310982777, 360582406764657327, 360582407030949376, 360582407175258167, 360582407319730593]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581749010437919, 360581783422038727⟩, ⟨43815310937293789, 45510888234041339⟩, true⟩

def words04 : List Nat := [360582407414170818, 360582407603496196, 360582407786457675, 360582407969608352, 360582407994976101, 360582407996012636, 360582407833739833, 360582407588785335, 360582407343533469, 360582407286168050]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360588412607733576, 360588447029208862⟩, ⟨(-442316636963557254), (-440620339274740880)⟩, true⟩

def words05 : List Nat := [360582407278539947, 360582407177383496, 360582407161454295, 360582407392977634, 360582407576607904, 360582407760408730, 360582407843987739, 360582407845024439, 360582407823812337, 360582407907770358]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573371593590729, 360573406024840747⟩, ⟨655078476053989021, 656775486956824511⟩, true⟩

def words06 : List Nat := [360582407983934331, 360582407984971062, 360582407896159403, 360582407652352853, 360582407408379796, 360582407117139111, 360582406920115786, 360582406869241152, 360582406818241397, 360582406648205923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604992829777124, 360605027270809675⟩, ⟨(-1652462141737057158), (-1650764416954872606)⟩, true⟩

def words07 : List Nat := [360582406525699418, 360582406524510130, 360582406708184185, 360582406924452433, 360582406963618095, 360582407002845376, 360582407229378216, 360582407550660910, 360582407861446455, 360582408172455928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592243766309683, 360592278217239218⟩, ⟨(-722007069791147102), (-720308622678196162)⟩, true⟩

def words08 : List Nat := [360582408345967062, 360582408599618078, 360582408979857711, 360582409360391005, 360582409619648940, 360582409691724554, 360582409692648642, 360582409671148205, 360582409649464358, 360582409759173454]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580831550662700, 360580866011362335⟩, ⟨111027766054082716, 112726926334265734⟩, true⟩

def words09 : List Nat := [360582410023374074, 360582410287765728, 360582410435395562, 360582410436432708, 360582410396698190, 360582410255952475, 360582410160375245, 360582410234978468, 360582410235911364, 360582410215832668]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729
