import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515A

def state06 : KState := ⟨⟨360583419171938449, 360583435891146929⟩, ⟨(-79478118042130256), (-78895646261325320)⟩, true⟩

def words05 : List Nat := [360581906983926897, 360581906983694521, 360581907210438650, 360581907211151865, 360581907166859584, 360581906770624511, 360581906374272397, 360581905915653209, 360581905718836419, 360581905749251673]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596725454916617, 360596742180932968⟩, ⟨(-765659211089976895), (-765076388262539837)⟩, true⟩

def words06 : List Nat := [360581905749894773, 360581905510610109, 360581905689917906, 360581905967718813, 360581906151764903, 360581906401615850, 360581906463194207, 360581906524852917, 360581906525439899, 360581906781420403]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582421289732588, 360582438022466353⟩, ⟨(-27926344915206510), (-27343175636549828)⟩, true⟩

def words07 : List Nat := [360581907181127817, 360581907580953673, 360581907792592122, 360581907793305728, 360581907726186752, 360581907559112240, 360581907599052574, 360581907898829894, 360581907909753437, 360581907920769284]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618250483504401, 360618267222984301⟩, ⟨(-1876208819854713965), (-1875625302576885785)⟩, true⟩

def words08 : List Nat := [360581908306671787, 360581908882847234, 360581909449084107, 360581910015429672, 360581910278839218, 360581910279552961, 360581910336424734, 360581910505775269, 360581910848849501, 360581911554309981]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607528829366024, 360607545575636256⟩, ⟨(-1323014382994687157), (-1322430515370140241)⟩, true⟩

def words09 : List Nat := [360581912019609137, 360581912484967728, 360581913325021281, 360581914355161954, 360581915157129596, 360581915959181110, 360581916456581817, 360581916579197911, 360581917076461071, 360581917573943070]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515B
