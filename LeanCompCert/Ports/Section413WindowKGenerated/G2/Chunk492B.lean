import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492A

def state06 : KState := ⟨⟨360567755720834325, 360567770925027346⟩, ⟨695410876389933724, 695916961959988978⟩, true⟩

def words05 : List Nat := [360581899010550614, 360581898649787280, 360581898338421690, 360581898597105805, 360581898753540464, 360581898910079826, 360581898910692860, 360581898802663347, 360581898636183429, 360581898350158487]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571617496605397, 360571632707192422⟩, ⟨505128459146934908, 505634859716645830⟩, true⟩

def words06 : List Nat := [360581898187977137, 360581898188655965, 360581897901747932, 360581897409517777, 360581896917196962, 360581896230933434, 360581895927001242, 360581895801748146, 360581895676429937, 360581895237326716]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604378626659227, 360604393843659488⟩, ⟨(-1109304709079146949), (-1108797992497433569)⟩, true⟩

def words07 : List Nat := [360581895045560490, 360581895062279657, 360581895070369880, 360581895071049004, 360581894807180169, 360581894194763117, 360581893582240779, 360581893426544334, 360581893883676413, 360581894340960732]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575333170868181, 360575348394330069⟩, ⟨322031989920319353, 322539024962622967⟩, true⟩

def words08 : List Nat := [360581894592857509, 360581894615678958, 360581894616232036, 360581894538578322, 360581894460740598, 360581894281069695, 360581893925939886, 360581893251340259, 360581892576638505, 360581892095384292]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556839815375125, 360556855045231454⟩, ⟨1233706542728921188, 1234213892985361474⟩, true⟩

def words09 : List Nat := [360581891963180593, 360581891893954343, 360581891824662223, 360581891547680748, 360581891289230085, 360581890929166583, 360581890618331518, 360581890619010890, 360581890316903460, 360581889809795052]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk492B
