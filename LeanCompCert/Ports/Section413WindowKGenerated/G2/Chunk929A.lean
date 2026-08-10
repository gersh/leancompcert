import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602711888923836, 360602768758356362⟩, ⟨(-1931587129147521928), (-1928019587781465182)⟩, true⟩

def state01 : KState := ⟨⟨360599595476038707, 360599652358268738⟩, ⟨(-1642161955484079461), (-1638593225169113853)⟩, true⟩

def words00 : List Nat := [360582015434804785, 360582015481684884, 360582015610401270, 360582015739535927, 360582015800485475, 360582015891260755, 360582015902843352, 360582015914558342, 360582016007305843, 360582016198662566]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572200797524565, 360572257692427571⟩, ⟨903194141972116998, 906764049797599962⟩, true⟩

def words01 : List Nat := [360582016341751937, 360582016485071712, 360582016570081435, 360582016571425787, 360582016540835554, 360582016481643821, 360582016422050543, 360582016380421793, 360582016341576561, 360582016237948424]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593549035441594, 360593605943034921⟩, ⟨(-1080543677812546398), (-1076972590740229392)⟩, true⟩

def words02 : List Nat := [360582016144729153, 360582016238679502, 360582016406689381, 360582016574959424, 360582016628938838, 360582016630283454, 360582016685321399, 360582016771645562, 360582016868246423, 360582016994344600]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577832524280561, 360577889444693867⟩, ⟨380141269451389989, 383713547948753355⟩, true⟩

def words03 : List Nat := [360582017062108004, 360582017130040217, 360582017298766122, 360582017525828529, 360582017723564935, 360582017921516557, 360582018046520539, 360582018102217415, 360582018103334098, 360582018060445414]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584195015482933, 360584251948562654⟩, ⟨(-211268435929493719), (-207694980153261481)⟩, true⟩

def words04 : List Nat := [360582018088369455, 360582018089714277, 360582018046736514, 360582017929254070, 360582017811554993, 360582017641651226, 360582017560981109, 360582017549342509, 360582017537554486, 360582017491911803]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929A
