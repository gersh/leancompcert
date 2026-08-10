import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228A

def state06 : KState := ⟨⟨360594294038936312, 360594297108271790⟩, ⟨(-318305801428367932), (-318258329739288424)⟩, true⟩

def words05 : List Nat := [360580378124236219, 360580376457265558, 360580375032915470, 360580376480791810, 360580376622348528, 360580376763936800, 360580376764201286, 360580375736968165, 360580375046263015, 360580375655590837]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621412329589450, 360621415401718772⟩, ⟨(-938126270736434946), (-938078735166174990)⟩, true⟩

def words06 : List Nat := [360580378173510791, 360580381533319862, 360580383933592495, 360580386333687453, 360580387548580507, 360580390070128797, 360580393150329507, 360580396230316236, 360580397529301733, 360580399323052944]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360717057375749368, 360717060450676348⟩, ⟨(-3126112504887190298), (-3126064905320925426)⟩, true⟩

def words07 : List Nat := [360580403023675677, 360580406724061217, 360580411765458267, 360580414908493291, 360580416358380881, 360580417808170294, 360580421163868095, 360580425767433899, 360580431739469397, 360580437711053040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360653769339892273, 360653772417643234⟩, ⟨(-1678148429220938749), (-1678100765028011935)⟩, true⟩

def words08 : List Nat := [360580442475541716, 360580446622320289, 360580450701061986, 360580454779529475, 360580457848316278, 360580459020875765, 360580459226918481, 360580459432973090, 360580460894144341, 360580464097123030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360497866780907689, 360497869861451519⟩, ⟨1891399887717742524, 1891447615853673186⟩, true⟩

def words09 : List Nat := [360580467569185801, 360580471041000325, 360580473266510277, 360580473597021997, 360580473597270941, 360580472988153788, 360580472379004161, 360580471704243675, 360580469433870183, 360580465827209322]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228B
