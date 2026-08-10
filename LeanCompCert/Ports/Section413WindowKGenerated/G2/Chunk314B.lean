import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314A

def state06 : KState := ⟨⟨360594288122822338, 360594294099821304⟩, ⟨(-360202174450081023), (-360075018065787117)⟩, true⟩

def words05 : List Nat := [360582856245569384, 360582855497796154, 360582854749948248, 360582854707455044, 360582853656761254, 360582851734080756, 360582849811442627, 360582848635211778, 360582848612477371, 360582848976714417]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547230883052164, 360547236864031468⟩, ⟨1120156077726948707, 1120283359352633417⟩, true⟩

def words06 : List Nat := [360582848977087249, 360582848837816259, 360582847690683901, 360582847263949353, 360582846837132158, 360582845564173316, 360582843283588261, 360582840293043013, 360582837302607907, 360582835318411914]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360466968901413886, 360466974886339331⟩, ⟨3646479255142589661, 3646606660973456877⟩, true⟩

def words07 : List Nat := [360582834187601806, 360582833214392161, 360582832241196788, 360582830618545620, 360582827988571007, 360582825091604378, 360582822194699218, 360582820303462991, 360582817405076722, 360582813725633279]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575359712551629, 360575365701431781⟩, ⟨233797922969163851, 233925453313470285⟩, true⟩

def words08 : List Nat := [360582810046329112, 360582807372644466, 360582805481304342, 360582804031205227, 360582802581164498, 360582800270062145, 360582798402089297, 360582796687929055, 360582794973755107, 360582794264572889]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360515455647732380, 360515461640610263⟩, ⟨2120486132336070588, 2120613788587971450⟩, true⟩

def words09 : List Nat := [360582794029054757, 360582793281666680, 360582792534254178, 360582791244108979, 360582790571061098, 360582789643661969, 360582788716275760, 360582787286330229, 360582784850018004, 360582782713263850]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk314B
