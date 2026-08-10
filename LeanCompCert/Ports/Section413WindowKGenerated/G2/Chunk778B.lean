import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778A

def state06 : KState := ⟨⟨360577916172034427, 360577955573950307⟩, ⟨329398933254280799, 331470947817185951⟩, true⟩

def words05 : List Nat := [360582212146135981, 360582212343617907, 360582212458507920, 360582212618744819, 360582212693257086, 360582212768060639, 360582212843867222, 360582212895263328, 360582212896263535, 360582212842738096]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595319223572608, 360595358635998321⟩, ⟨(-1025704451513057168), (-1023631618603661036)⟩, true⟩

def words06 : List Nat := [360582212788974977, 360582212746146728, 360582212939200364, 360582213132461888, 360582213182283304, 360582213183394963, 360582213117480459, 360582213167695274, 360582213243566793, 360582213413532915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586763855965862, 360586803278971701⟩, ⟨(-359463257849702911), (-357389601014123247)⟩, true⟩

def words07 : List Nat := [360582213485291336, 360582213557169833, 360582213734727758, 360582213995046747, 360582214132512789, 360582214270139088, 360582214293302876, 360582214294416274, 360582214299766866, 360582214359966885]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587474911629461, 360587514345113418⟩, ⟨(-414839044902898404), (-412764571977144218)⟩, true⟩

def words08 : List Nat := [360582214492992233, 360582214630526281, 360582214662346177, 360582214694281663, 360582214695212866, 360582214680843504, 360582214835159204, 360582214989683738, 360582215017065661, 360582215086251969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617236905262080, 360617276349245460⟩, ⟨(-2733219453406565658), (-2731144162629867640)⟩, true⟩

def words09 : List Nat := [360582215129065825, 360582215172198693, 360582215379618230, 360582215611950605, 360582215700636716, 360582215789421052, 360582215993437890, 360582216280147058, 360582216731111328, 360582217182320391]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778B
