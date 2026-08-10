import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446A

def state06 : KState := ⟨⟨360610595695322766, 360610608092126993⟩, ⟨(-1224861465390850680), (-1224487328371183650)⟩, true⟩

def words05 : List Nat := [360583186705246805, 360583187441805322, 360583188166787167, 360583188535870777, 360583188536436419, 360583188459728733, 360583188806419977, 360583189489394460, 360583190103830869, 360583190718392165]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594318307477098, 360594330710089747⟩, ⟨(-497984092110575444), (-497609695657040876)⟩, true⟩

def words06 : List Nat := [360583191081302651, 360583191094628424, 360583191438601331, 360583191782737661, 360583191998892178, 360583191999503881, 360583191991375984, 360583191596946748, 360583191202416449, 360583191275206780]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560445009803859, 360560457418166037⟩, ⟨1015337886184947404, 1015712539498855000⟩, true⟩

def words07 : List Nat := [360583191443268061, 360583191611435090, 360583191611979310, 360583191528908067, 360583191462413928, 360583191268675775, 360583191197848007, 360583191198459060, 360583190973331601, 360583190465155716]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579936377105266, 360579948791244389⟩, ⟨144353890690088095, 144728802146040013⟩, true⟩

def words08 : List Nat := [360583189956875188, 360583189241952564, 360583189059352770, 360583189218527878, 360583189219097035, 360583188941873989, 360583188164858409, 360583187888223509, 360583187611410036, 360583187296550857]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547208183788905, 360547220603745623⟩, ⟨1607097684006204133, 1607472855479421573⟩, true⟩

def words09 : List Nat := [360583187224630908, 360583186901697329, 360583186578665882, 360583186081792493, 360583185911867743, 360583185394710283, 360583184877509058, 360583184073040709, 360583182768990737, 360583181965165745]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446B
