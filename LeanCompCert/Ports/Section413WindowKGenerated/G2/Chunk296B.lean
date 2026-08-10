import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296A

def state06 : KState := ⟨⟨360595722215904405, 360595727501758900⟩, ⟨(-363760387736959847), (-363654359170110939)⟩, true⟩

def words05 : List Nat := [360583462691661735, 360583463981333682, 360583465599680912, 360583466086145365, 360583466086510881, 360583465625248321, 360583465454826507, 360583466320301752, 360583466734016926, 360583467147786677]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612031399493521, 360612036689090345⟩, ⟨(-847927692343266266), (-847821552760582008)⟩, true⟩

def words06 : List Nat := [360583467148136851, 360583466997661014, 360583465715845298, 360583465566712692, 360583465417483332, 360583464561727309, 360583464245948626, 360583463001579897, 360583461757220066, 360583462608245056]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603514074788118, 360603519368093004⟩, ⟨(-595109048720861422), (-595002799101484022)⟩, true⟩

def words07 : List Nat := [360583464703592571, 360583466798873939, 360583467970401118, 360583468525705774, 360583468779243954, 360583469032868531, 360583470029140481, 360583471427736703, 360583472103558419, 360583472779396482]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636778032140846, 360636783329154267⟩, ⟨(-1582338194976006037), (-1582231835268488291)⟩, true⟩

def words08 : List Nat := [360583474237549423, 360583476582454091, 360583480058176367, 360583483533739750, 360583486030055748, 360583487396617901, 360583488736569522, 360583490076540376, 360583491586232314, 360583493381517998]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360624792698041512, 360624797998807497⟩, ⟨(-1226389849322580649), (-1226283378184088285)⟩, true⟩

def words09 : List Nat := [360583494593992630, 360583495806427059, 360583497537628332, 360583500191798540, 360583502561412131, 360583504930930568, 360583506595650956, 360583507605150565, 360583508995718742, 360583510386330339]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk296B
