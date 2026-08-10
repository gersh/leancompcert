import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759A

def state06 : KState := ⟨⟨360571983349995927, 360572020779439272⟩, ⟨770801166531386442, 772721469950961926⟩, true⟩

def words05 : List Nat := [360582193505273145, 360582193471611481, 360582193542310784, 360582193734911022, 360582193813562682, 360582193892385468, 360582193893366635, 360582193838695519, 360582193653954534, 360582193521276436]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584173116289311, 360584210555918547⟩, ⟨(-155224894258446887), (-153303817066579119)⟩, true⟩

def words06 : List Nat := [360582193388231466, 360582193355026775, 360582193247866398, 360582193054112183, 360582192860167904, 360582192622760282, 360582192581876848, 360582192648615297, 360582192649590242, 360582192630432947]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585102888604122, 360585140338469463⟩, ⟨(-225971153154917432), (-224049298276717842)⟩, true⟩

def words07 : List Nat := [360582192653730073, 360582192677334536, 360582192691264882, 360582192692347369, 360582192533478888, 360582192226299426, 360582191918926792, 360582191638791325, 360582191544267096, 360582191584198307]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571483410280966, 360571520870452293⟩, ⟨808764051428543406, 810686689405693038⟩, true⟩

def words08 : List Nat := [360582191585166168, 360582191508055554, 360582191257847013, 360582191180963200, 360582191103814944, 360582190880018313, 360582190483235045, 360582189999275864, 360582189515114852, 360582189204304191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563502388970111, 360563539859357069⟩, ⟨1415322361272858651, 1417245775585106177⟩, true⟩

def words09 : List Nat := [360582189097374714, 360582189131061729, 360582189132026733, 360582189066934066, 360582188828815645, 360582188547312358, 360582188265487724, 360582188156830639, 360582188074334997, 360582187830088452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759B
