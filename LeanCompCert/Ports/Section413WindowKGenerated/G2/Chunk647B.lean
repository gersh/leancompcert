import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647A

def state06 : KState := ⟨⟨360576918199261687, 360576945062085271⟩, ⟨389833773548405184, 391008920205241940⟩, true⟩

def words05 : List Nat := [360582983524347271, 360582983796978481, 360582984025565004, 360582984026476541, 360582984017516783, 360582983803031513, 360582983588396953, 360582983205865241, 360582982969698157, 360582982877406538]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586513738011749, 360586540609518269⟩, ⟨(-231778773066939873), (-230603064060667613)⟩, true⟩

def words06 : List Nat := [360582982784986474, 360582982573153796, 360582982123541216, 360582981912242221, 360582981700681370, 360582981429454335, 360582981181844729, 360582980814878065, 360582980447740787, 360582980326921727]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557820401707412, 360557847281809891⟩, ⟨1626809504685258968, 1627985770494750818⟩, true⟩

def words07 : List Nat := [360582980327673363, 360582980304376323, 360582980280988892, 360582980138519663, 360582979814527672, 360582979428231618, 360582979041680078, 360582978847799036, 360582978662493731, 360582978275488415]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597406956856912, 360597433845564631⟩, ⟨(-937775472512976301), (-936598649214437529)⟩, true⟩

def words08 : List Nat := [360582977888288007, 360582977749063805, 360582977997480525, 360582978246064205, 360582978268560718, 360582978269473551, 360582978163346075, 360582978030504806, 360582977930902310, 360582978154971579]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586529883779010, 360586556781186560⟩, ⟨(-232944210399931037), (-231766823396002123)⟩, true⟩

def words09 : List Nat := [360582978225330546, 360582978295798442, 360582978603846927, 360582979031085599, 360582979398326421, 360582979765704799, 360582980013678716, 360582980075678649, 360582980131625111, 360582980187871704]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647B
