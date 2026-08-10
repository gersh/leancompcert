import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571A

def state06 : KState := ⟨⟨360571077746010132, 360571098466590041⟩, ⟨617373017162788275, 618173209803386115⟩, true⟩

def words05 : List Nat := [360581911629019210, 360581912168313346, 360581912553216932, 360581912926673205, 360581913025021145, 360581913123570078, 360581913434725826, 360581913440988195, 360581913441706118, 360581913253325580]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584356314622715, 360584377042733371⟩, ⟨(-141612942523987699), (-140812319388107577)⟩, true⟩

def words06 : List Nat := [360581913064774262, 360581913106278314, 360581913552619327, 360581913999097943, 360581914150262420, 360581914151059512, 360581914080291113, 360581914055564105, 360581914030607289, 360581914040172841]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607136902446648, 360607157638148769⟩, ⟨(-1444172064799836571), (-1443371007621983979)⟩, true⟩

def words07 : List Nat := [360581914040886595, 360581913828819619, 360581913709636505, 360581913998307418, 360581914207576298, 360581914416980965, 360581914473726153, 360581914610175868, 360581915052286481, 360581915494646173]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595522740900084, 360595543484124082⟩, ⟨(-780067597252055772), (-779266109936908748)⟩, true⟩

def words08 : List Nat := [360581916181543915, 360581916563761337, 360581916708436584, 360581916853181266, 360581916919857014, 360581917147380812, 360581917363963147, 360581917580690177, 360581917581405354, 360581917806833304]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617581619407564, 360617602370153303⟩, ⟨(-2041710243768292391), (-2040908326247437249)⟩, true⟩

def words09 : List Nat := [360581918351427168, 360581918896235900, 360581919746485694, 360581920292170501, 360581920567662720, 360581920843199873, 360581921109959217, 360581921529387726, 360581922153823616, 360581922778428553]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571B
