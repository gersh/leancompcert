import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk357B
