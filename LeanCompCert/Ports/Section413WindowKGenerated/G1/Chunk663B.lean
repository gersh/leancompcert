import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663A

def state06 : KState := ⟨⟨362483165554480674, 362483230635930741⟩, ⟨148747289896246946, 151664233679547488⟩, true⟩

def words05 : List Nat := [371285516039018425, 371285516086679911, 371285516228437636, 371285516257502930, 371285516307669324, 371285516358678358, 371285516401631212, 371285516403893569, 371285516144197725, 371285516112628746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464920260973340, 362464985362567413⟩, ⟨1359636259636637891, 1362554540280434519⟩, true⟩

def words06 : List Nat := [371285516272058979, 371285516274321387, 371285516165906773, 371285516013591780, 371285515860442284, 371285515749791877, 371285515524643178, 371285515362583145, 371285515199724649, 371285515037726076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502649544227523, 362502714666241352⟩, ⟨(-1144636113638829838), (-1141716477630552890)⟩, true⟩

def words07 : List Nat := [371285514729945171, 371285514613328024, 371285514602976221, 371285514605294055, 371285514588827523, 371285514521597865, 371285514610406870, 371285514697171067, 371285514957820601, 371285515219447382]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486399535191713, 362486464677652974⟩, ⟨(-65946672033380366), (-63025678619920346)⟩, true⟩

def words08 : List Nat := [371285515424845488, 371285515427108871, 371285515458077660, 371285515588872393, 371285515685998002, 371285515688266415, 371285515551302539, 371285515415357224, 371285515350193502, 371285515367074433]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471517645953203, 362471582808801161⟩, ⟨922191431092909572, 925113778081859044⟩, true⟩

def words09 : List Nat := [371285515533035576, 371285515699926493, 371285515866973656, 371285515869237706, 371285515760989536, 371285515664386910, 371285515658621637, 371285515660885662, 371285515452467736, 371285515245218057]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663B
