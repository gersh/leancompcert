import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320A

def state06 : KState := ⟨⟨360571264126414826, 360571270343413899⟩, ⟨341753372587537057, 341888151602882369⟩, true⟩

def words05 : List Nat := [360581952093353733, 360581950134632349, 360581948175915124, 360581945858331944, 360581943771494496, 360581940853369324, 360581937935344670, 360581935986306472, 360581934685320861, 360581934353133266]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576784213563413, 360576790434624569⟩, ⟨164604730338218506, 164739639604568306⟩, true⟩

def words06 : List Nat := [360581934020897501, 360581933203245390, 360581933150303959, 360581933608311416, 360581933608671370, 360581933381040195, 360581932182700202, 360581930236139205, 360581928289618039, 360581927311444169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561676798643466, 360561683023728257⟩, ⟨649286169888512023, 649421208212425001⟩, true⟩

def words07 : List Nat := [360581927280325623, 360581927409451966, 360581927409832534, 360581927069114014, 360581927069471976, 360581926826096985, 360581927306342247, 360581927457213875, 360581927457595664, 360581926826976774]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603625747458191, 360603631976579630⟩, ⟨(-696694587070957871), (-696559419231338417)⟩, true⟩

def words08 : List Nat := [360581926196306686, 360581925540468645, 360581926179942335, 360581926983493928, 360581926983892258, 360581926909058239, 360581926211786062, 360581925666953284, 360581925543627969, 360581926220472581]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605354713218169, 360605360946407940⟩, ⟨(-752276324784987554), (-752141026372539748)⟩, true⟩

def words09 : List Nat := [360581926288010346, 360581926355589817, 360581927099753965, 360581928328383961, 360581928850224834, 360581929372097809, 360581929372480377, 360581929267368471, 360581929761298116, 360581930491706450]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk320B
