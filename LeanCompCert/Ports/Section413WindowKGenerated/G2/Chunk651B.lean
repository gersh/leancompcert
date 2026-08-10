import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651A

def state06 : KState := ⟨⟨360556684101504469, 360556711310687154⟩, ⟨1708998238659331247, 1710195884866563385⟩, true⟩

def words05 : List Nat := [360582959396290115, 360582959211319023, 360582959026182946, 360582958878229703, 360582958848009049, 360582958726174641, 360582958604223940, 360582958325917613, 360582957812567643, 360582957410823228]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560472790227323, 360560500008068300⟩, ⟨1462018496992691539, 1463216707417150685⟩, true⟩

def words06 : List Nat := [360582957008778908, 360582956687008167, 360582956224593977, 360582955561845716, 360582954898961957, 360582954177364627, 360582953573404844, 360582953204692213, 360582952835902357, 360582952312923558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587014610790861, 360587041837289997⟩, ⟨(-267863439222299960), (-266664664502696920)⟩, true⟩

def words07 : List Nat := [360582951969152101, 360582951860691667, 360582951877524147, 360582951878442188, 360582951770098607, 360582951429087762, 360582951087924601, 360582950741234319, 360582950632527197, 360582950696244253]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598330901022531, 360598358136264209⟩, ⟨(-1005566928630260451), (-1004367584028993135)⟩, true⟩

def words08 : List Nat := [360582950697062240, 360582950642886367, 360582950840096297, 360582951056830307, 360582951214351311, 360582951335778698, 360582951339099051, 360582951342512180, 360582951361416272, 360582951598796937]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558055048966054, 360558082292868151⟩, ⟨1620204206070379924, 1621404115287608146⟩, true⟩

def words09 : List Nat := [360582951775151925, 360582951951665105, 360582951996467399, 360582951997386227, 360582951909889423, 360582951621153200, 360582951332152120, 360582951080272718, 360582950834613108, 360582950454145569]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651B
