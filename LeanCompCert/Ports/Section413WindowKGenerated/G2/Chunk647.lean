import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360601368320634737, 360601395131706225⟩, ⟨(-1192983914499775564), (-1191812117749743640)⟩, true⟩

def state01 : KState := ⟨⟨360607631250921014, 360607658070686485⟩, ⟨(-1598334320789650835), (-1597161961496183381)⟩, true⟩

def words00 : List Nat := [360582974919264488, 360582975097089880, 360582975454668225, 360582975812502627, 360582976110095395, 360582976169883844, 360582976170695477, 360582976110746363, 360582976228168413, 360582976610633385]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586069818186140, 360586096646527918⟩, ⟨(-202901751823533283), (-201728837515194511)⟩, true⟩

def words01 : List Nat := [360582977179030607, 360582977747584656, 360582978108919282, 360582978516404705, 360582978739815023, 360582978963446214, 360582979425171264, 360582979649173362, 360582979698157269, 360582979747260058]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599881167402065, 360599908004358523⟩, ⟨(-1096746034207014965), (-1095572562314987197)⟩, true⟩

def words02 : List Nat := [360582979964484501, 360582980393809754, 360582980984892480, 360582981576137416, 360582981964030297, 360582982114151213, 360582982323825920, 360582982533768874, 360582982735961105, 360582982998375069]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582122033906015, 360582148879537549⟩, ⟨52906135905631235, 54080169378589619⟩, true⟩

def words03 : List Nat := [360582983141033630, 360582983283787186, 360582983529990300, 360582983895647225, 360582984099518688, 360582984303545610, 360582984387915370, 360582984388826637, 360582984235378295, 360582984223519301]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589047871849016, 360589074726073315⟩, ⟨(-395603629009937323), (-394429039199337941)⟩, true⟩

def words04 : List Nat := [360582984375484054, 360582984376395374, 360582984303628594, 360582984047424021, 360582983791079873, 360582983403691835, 360582983224000650, 360582983253762193, 360582983254574313, 360582983251977173]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk647
