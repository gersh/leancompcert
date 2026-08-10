import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597A

def state06 : KState := ⟨⟨360588035775527011, 360588058504675569⟩, ⟨(-354352648315590788), (-353435014227209764)⟩, true⟩

def words05 : List Nat := [360582140946271097, 360582141254105624, 360582141842051408, 360582142612091940, 360582143140130023, 360582143668283279, 360582144055348126, 360582144163525242, 360582144263180816, 360582144363107871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580607274909136, 360580630011925055⟩, ⟨89524849482814795, 90442953764579503⟩, true⟩

def words06 : List Nat := [360582144544827475, 360582144545663403, 360582144448499976, 360582144140440827, 360582143832255332, 360582143452684916, 360582143321075208, 360582143348648269, 360582143349400451, 360582143195023007]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360625085428355558, 360625108173278216⟩, ⟨(-2569192337524800621), (-2568273760619789671)⟩, true⟩

def words07 : List Nat := [360582143425168228, 360582143680869213, 360582143928034192, 360582144331175337, 360582144493820220, 360582144656524140, 360582144923097795, 360582145362698042, 360582146082055795, 360582146801594575]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601561493005859, 360601584245883681⟩, ⟨(-1162910082709422771), (-1161991030204810873)⟩, true⟩

def words08 : List Nat := [360582147380147100, 360582147767960538, 360582148379042152, 360582148990349325, 360582149420455337, 360582149639295458, 360582149640063903, 360582149631705978, 360582149706876748, 360582150032871609]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602896168230947, 360602918928985430⟩, ⟨(-1242639902675449714), (-1241720379186125228)⟩, true⟩

def words09 : List Nat := [360582150638484334, 360582151244237701, 360582151681816725, 360582152125605100, 360582152497706122, 360582152870031354, 360582153521942348, 360582154025292813, 360582154373277460, 360582154721377094]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597B
