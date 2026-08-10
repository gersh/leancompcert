import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272A

def state06 : KState := ⟨⟨360662055679823621, 360662060112540917⟩, ⟨(-2159426997509976809), (-2159345264743143835)⟩, true⟩

def words05 : List Nat := [360582840774308433, 360582841344095750, 360582843256508013, 360582843829025539, 360582843829356420, 360582843134322470, 360582842682523695, 360582844246853559, 360582847153081441, 360582850059177389]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574016715757305, 360574021151891117⟩, ⟨240811960043230828, 240893785960922368⟩, true⟩

def words06 : List Nat := [360582852088406803, 360582853318857580, 360582855576900449, 360582857834882453, 360582858886760688, 360582858887119321, 360582858600401812, 360582857466005571, 360582856331625275, 360582854807408570]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564729485525534, 360564733925041932⟩, ⟨494307924633352304, 494389842811403278⟩, true⟩

def words07 : List Nat := [360582855500919666, 360582856518351972, 360582856860022506, 360582856860382925, 360582856822635944, 360582856434757217, 360582856999059658, 360582857383514026, 360582857383842156, 360582856719866397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360661503342471845, 360661507785373037⟩, ⟨(-2146037932235695817), (-2145955921703297695)⟩, true⟩

def words08 : List Nat := [360582856731783185, 360582858082772171, 360582860773639117, 360582863464378090, 360582864865819613, 360582866316773040, 360582868156152611, 360582869995504464, 360582872536863014, 360582875418596324]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613349249163815, 360613353695487994⟩, ⟨(-831769076453141205), (-831686972490780623)⟩, true⟩

def words09 : List Nat := [360582877269251885, 360582879119808854, 360582880882888803, 360582883319220318, 360582885141808476, 360582886964321486, 360582888076752657, 360582888077111736, 360582888970802554, 360582890087104024]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272B
