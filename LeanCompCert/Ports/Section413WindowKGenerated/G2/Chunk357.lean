import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598484122942364, 360598491900799200⟩, ⟨(-584972655208232733), (-584784939652633217)⟩, true⟩

def state01 : KState := ⟨⟨360569206162925080, 360569213945289651⟩, ⟨460333874482001025, 460521750987258543⟩, true⟩

def words00 : List Nat := [360582112628490024, 360582112646809666, 360582112647240606, 360582112273353938, 360582111899410279, 360582111140866480, 360582110995774486, 360582110829441181, 360582110663064817, 360582110101856083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578545363829511, 360578553150719820⟩, ⟨126732875445643587, 126920913587659001⟩, true⟩

def words01 : List Nat := [360582109741120224, 360582109257241641, 360582108838869201, 360582108929448187, 360582108929890200, 360582108354678037, 360582107779410028, 360582106927545998, 360582106466765015, 360582106367785544]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562811719021373, 360562819510489197⟩, ⟨688546186473030686, 688734388146170206⟩, true⟩

def words02 : List Nat := [360582106268753357, 360582105567310698, 360582104370704293, 360582103773047421, 360582103175295183, 360582102362739676, 360582100770265673, 360582098783492844, 360582096796727610, 360582095591881478]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360511364339409491, 360511372135391691⟩, ⟨2527221344449105156, 2527409707443935524⟩, true⟩

def words03 : List Nat := [360582095294944474, 360582095537563469, 360582095537990977, 360582095315556739, 360582094836746696, 360582093818557206, 360582092800286150, 360582092013315382, 360582090669477681, 360582088691279882]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580535004537134, 360580542805056677⟩, ⟨54754962081227972, 54943487262075004⟩, true⟩

def words04 : List Nat := [360582086713084387, 360582085297792752, 360582084576321653, 360582084320779727, 360582084065214577, 360582083145920440, 360582081700360174, 360582081035936370, 360582080371410636, 360582079685819253]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598503567866147, 360598511372950431⟩, ⟨(-587754891444206103), (-587566203051064951)⟩, true⟩

def words05 : List Nat := [360582079643259518, 360582079055796666, 360582078661081392, 360582079373631199, 360582079888578128, 360582080403582858, 360582080410772832, 360582080411253941, 360582080550170313, 360582081010179506]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575553290982714, 360575561100595527⟩, ⟨232849649614375225, 233038499970487113⟩, true⟩

def words06 : List Nat := [360582081583140164, 360582081583620311, 360582081378492690, 360582080523394455, 360582079668266302, 360582078381176892, 360582077496215013, 360582077133761236, 360582076771274050, 360582076015327719]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607226528879439, 360607234343024371⟩, ⟨(-900218684127965062), (-900029671636108158)⟩, true⟩

def words07 : List Nat := [360582076431312009, 360582077029535334, 360582078207013489, 360582078940459343, 360582078998883250, 360582079057338779, 360582079057734814, 360582079092644754, 360582079796086870, 360582080499598081]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553961410088314, 360553969228808048⟩, ⟨1005636112404786942, 1005825288605957856⟩, true⟩

def words08 : List Nat := [360582080809842719, 360582080810323196, 360582080343214004, 360582079989854161, 360582079636374016, 360582078808135235, 360582077578144613, 360582075893987237, 360582074209833223, 360582072757408383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536730818526574, 360536738641775488⟩, ⟨1622356196597072182, 1622545534920596780⟩, true⟩

def words09 : List Nat := [360582071972591641, 360582071167046954, 360582070361498979, 360582069003365568, 360582067525779526, 360582065851399418, 360582064176971100, 360582063281319613, 360582062408279907, 360582061142750924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357
