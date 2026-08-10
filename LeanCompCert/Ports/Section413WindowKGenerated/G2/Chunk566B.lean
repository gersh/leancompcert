import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566A

def state06 : KState := ⟨⟨360605210007170991, 360605230352527832⟩, ⟨(-1329673388260956945), (-1328894549689287327)⟩, true⟩

def words05 : List Nat := [360581777555995020, 360581777286408090, 360581777016599335, 360581777001022180, 360581776895621347, 360581776523544626, 360581776151330112, 360581776097561819, 360581776512147144, 360581776926896635]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590477925238629, 360590498278107784⟩, ⟨(-495035629442526389), (-494256365185506799)⟩, true⟩

def words06 : List Nat := [360581777043569980, 360581777044359604, 360581777226602654, 360581777473817393, 360581777509509590, 360581777510299629, 360581777382715418, 360581777056402086, 360581776729948642, 360581776773896009]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569834377287567, 360569854737603837⟩, ⟨675039148018080949, 675818834340964821⟩, true⟩

def words07 : List Nat := [360581777239440960, 360581777705140925, 360581778013633485, 360581778127003776, 360581778159400814, 360581778192005130, 360581778326270836, 360581778355650237, 360581778356365709, 360581778146819451]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360622813417433897, 360622833785194817⟩, ⟨(-2328080972189094660), (-2327300863865762348)⟩, true⟩

def words08 : List Nat := [360581778037666135, 360581778340169466, 360581778689505739, 360581779038977047, 360581779124839787, 360581779218627082, 360581779623108893, 360581780027808050, 360581780673355036, 360581781398328017]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582354963745262, 360582375339049171⟩, ⟨(-34283220571721082), (-33502684602115914)⟩, true⟩

def words09 : List Nat := [360581781967401794, 360581782536535189, 360581782953395320, 360581783608204907, 360581783974431306, 360581784340772100, 360581784550734747, 360581784551524534, 360581784461850925, 360581784473198444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk566B
