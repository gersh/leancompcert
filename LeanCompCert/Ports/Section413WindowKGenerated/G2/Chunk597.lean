import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614662549343210, 360614685231059728⟩, ⟨(-1944976971976457501), (-1944062171004219241)⟩, true⟩

def state01 : KState := ⟨⟨360621410281860115, 360621432971452024⟩, ⟨(-2347933825012857737), (-2347018553840061161)⟩, true⟩

def words00 : List Nat := [360582122685429103, 360582123170539588, 360582123441646748, 360582123712825545, 360582123912084920, 360582124270823239, 360582124909969548, 360582125549261543, 360582126011037573, 360582126670203677]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617643059276201, 360617665756739850⟩, ⟨(-2122947076347506624), (-2122031335113366106)⟩, true⟩

def words01 : List Nat := [360582127425942548, 360582128181900595, 360582129169133849, 360582129955927016, 360582130504913245, 360582131053939195, 360582131508857076, 360582132150561883, 360582132746245142, 360582133342093187]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360620053227936224, 360620075933355238⟩, ⟨(-2267033668272599466), (-2266117451905611340)⟩, true⟩

def words02 : List Nat := [360582133742748357, 360582134061989952, 360582134661610204, 360582135261481204, 360582135790182360, 360582136039810742, 360582136126737259, 360582136213751987, 360582136581116985, 360582137217246256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579159413754615, 360579182127047137⟩, ⟨175703106944324960, 176619793634939940⟩, true⟩

def words03 : List Nat := [360582137731629383, 360582138246142502, 360582138620033129, 360582138714871699, 360582138715573971, 360582138656456469, 360582138597094716, 360582138649544452, 360582138650288584, 360582138601664395]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608931078622815, 360608953799797007⟩, ⟨(-1603030356424255596), (-1602113198843339842)⟩, true⟩

def words04 : List Nat := [360582138552856086, 360582138682071434, 360582139099164031, 360582139516402941, 360582139662416895, 360582139663252598, 360582139676649349, 360582139824111626, 360582140188908453, 360582140638530362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk597
