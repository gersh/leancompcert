import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175A

def state06 : KState := ⟨⟨360508311327615931, 360508313096459912⟩, ⟨1329174309030088053, 1329195334760470231⟩, true⟩

def words05 : List Nat := [360584014007309958, 360584016804698221, 360584017976799292, 360584017977022038, 360584017213933755, 360584015607155407, 360584014558431245, 360584014558654000, 360584011902241249, 360584007591605725]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360530777786714664, 360530779557663802⟩, ⟨934268530966804198, 934289593674511834⟩, true⟩

def words06 : List Nat := [360584003281411503, 360584000027320847, 360583998383410966, 360583995311623852, 360583992240169020, 360583986402347376, 360583977353399947, 360583968769504925, 360583960186520032, 360583954833342488]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599965181548474, 360599966954620318⟩, ⟨(-281876869505896966), (-281855769492041348)⟩, true⟩

def words07 : List Nat := [360583951807232044, 360583947159746518, 360583942512747134, 360583941865644734, 360583941865832098, 360583940599324018, 360583939332940166, 360583935604540415, 360583934202973354, 360583935115163402]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609020067708270, 360609021842879169⟩, ⟨(-440998411084948862), (-440977274159004724)⟩, true⟩

def words08 : List Nat := [360583939252374941, 360583941598693459, 360583942325464914, 360583943052181951, 360583943052368691, 360583944490681606, 360583947976679039, 360583951462322615, 360583952071519295, 360583953496897758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360719840988414366, 360719842765694507⟩, ⟨(-2391327527656601696), (-2391306353618708714)⟩, true⟩

def words09 : List Nat := [360583954712369503, 360583955927764909, 360583959350790183, 360583961441671491, 360583961441879824, 360583960175984197, 360583960862533531, 360583965365791445, 360583973086278909, 360583980805941158]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175B
