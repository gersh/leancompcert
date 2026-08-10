import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974A

def state06 : KState := ⟨⟨360609366108742629, 360609428931015634⟩, ⟨(-2639199113359549862), (-2635064865253456768)⟩, true⟩

def words05 : List Nat := [360582390602405858, 360582390627794877, 360582390758012518, 360582390890807908, 360582390932480164, 360582390974261457, 360582391078655348, 360582391252397306, 360582391530964374, 360582391809856879]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594098680651141, 360594161516428499⟩, ⟨(-1151249470606795523), (-1147113906304831413)⟩, true⟩

def words06 : List Nat := [360582391995620810, 360582392076585457, 360582392262515854, 360582392448859435, 360582392592356753, 360582392631180542, 360582392632441492, 360582392610854587, 360582392622762434, 360582392745139554]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588981869222136, 360589044718318940⟩, ⟨(-652489788551261822), (-648352925935896604)⟩, true⟩

def words07 : List Nat := [360582392883191642, 360582393021504429, 360582393106862691, 360582393212125831, 360582393242332220, 360582393272891288, 360582393387062784, 360582393509414344, 360582393578918443, 360582393648613707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597105009330301, 360597167871806276⟩, ⟨(-1444303165608635010), (-1440164998726159748)⟩, true⟩

def words08 : List Nat := [360582393785317556, 360582394020264402, 360582394330372558, 360582394640745636, 360582394849591797, 360582394980959441, 360582395143074965, 360582395305612200, 360582395432155110, 360582395585146727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591146673130678, 360591209549087800⟩, ⟨(-863429172898046252), (-859289691674600486)⟩, true⟩

def words09 : List Nat := [360582395685164875, 360582395785335598, 360582395901427712, 360582396070237305, 360582396150903022, 360582396231818168, 360582396241656275, 360582396243073863, 360582396319856137, 360582396411872032]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk974B
