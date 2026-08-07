import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489376776583800, 362489441735757776⟩, ⟨(-263133791317002222), (-260224958123818256)⟩, true⟩

def state01 : KState := ⟨⟨362484875432346835, 362484940411652702⟩, ⟨35347173800735039, 38257341839911491⟩, true⟩

def words00 : List Nat := [371285517121214100, 371285517123474590, 371285517108560150, 371285517092659016, 371285517098245109, 371285517100737093, 371285517136358913, 371285517252949858, 371285517356100401, 371285517358445643]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490399817854707, 362490464817648283⟩, ⟨(-331006140190000315), (-328094613507099833)⟩, true⟩

def words01 : List Nat := [371285517437683661, 371285517526812415, 371285517765287613, 371285517767548867, 371285517734148342, 371285517664856881, 371285517634073070, 371285517636608045, 371285517670724539, 371285517747888975]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477008735521887, 362477073755712955⟩, ⟨557097254032313950, 560010133583010514⟩, true⟩

def words02 : List Nat := [371285517823585216, 371285517825846514, 371285517598561536, 371285517541265074, 371285517482906915, 371285517435711915, 371285517170636487, 371285516906594526, 371285516641623923, 371285516543796523]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475113941462794, 362475178982018735⟩, ⟨682858414760311857, 685772645215490809⟩, true⟩

def words03 : List Nat := [371285516497534958, 371285516579499172, 371285516660952263, 371285516663220076, 371285516512003262, 371285516431788612, 371285516494319208, 371285516496581968, 371285516377486679, 371285516224183576]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490359627753599, 362490424688536096⟩, ⟨(-328612484640307015), (-325696912250953717)⟩, true⟩

def words04 : List Nat := [371285516069909287, 371285515984618145, 371285515810101728, 371285515837991491, 371285515839741959, 371285515830912889, 371285515665083956, 371285515697547538, 371285515915848907, 371285515992175063]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk663
