import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk149

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360914629549128106, 360914630803513594⟩, ⟨(-4989375444439351267), (-4989362788702220171)⟩, true⟩

def state01 : KState := ⟨⟨360786669927324575, 360786671183484628⟩, ⟨(-3082782474218619456), (-3082769792031719694)⟩, true⟩

def words00 : List Nat := [360579816913529326, 360579832660000785, 360579848256164070, 360579863850288540, 360579876397797182, 360579886805874207, 360579894947914860, 360579903088883554, 360579912645909508, 360579926512300153]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360533836268693289, 360533837526606867⟩, ⟨688372279115410105, 688384987456368223⟩, true⟩

def words01 : List Nat := [360579939303829213, 360579952093677423, 360579962635327023, 360579968731581007, 360579972487856164, 360579976243677797, 360579979854889174, 360579979855075581, 360579979022992687, 360579975930591879]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360656998683531572, 360656999943205147⟩, ⟨(-1149718815870566450), (-1149706081261742654)⟩, true⟩

def words02 : List Nat := [360579972838563827, 360579974132771520, 360579980401384250, 360579986669196517, 360579989239186656, 360579990447368966, 360579990447521198, 360579989978911754, 360579993507562700, 360579998665242403]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360726694268057633, 360726695529511990⟩, ⟨(-2191000047754565421), (-2190987286550183529)⟩, true⟩

def words03 : List Nat := [360580000356315847, 360580002047178642, 360580006906047087, 360580014645295399, 360580020032002440, 360580025418018478, 360580027926789036, 360580033283577792, 360580043100478994, 360580052916129340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360741581792987362, 360741583056199916⟩, ⟨(-2413742639591423458), (-2413729852111020978)⟩, true⟩

def words04 : List Nat := [360580065483228015, 360580075641747065, 360580082707901060, 360580089773129407, 360580093532814393, 360580100082739341, 360580111088263602, 360580122092351151, 360580129554191936, 360580140353229478]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360811320316122639, 360811321581100988⟩, ⟨(-3456654540134482942), (-3456641726246587952)⟩, true⟩

def words05 : List Nat := [360580155605523597, 360580170855835503, 360580187957703613, 360580200635284693, 360580209477029721, 360580218317607187, 360580231608542030, 360580247195683082, 360580262641985705, 360580278086264641]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360786719660800427, 360786720927556801⟩, ⟨(-3089288137468463345), (-3089275296972249947)⟩, true⟩

def words06 : List Nat := [360580291277542574, 360580300048575412, 360580310072529906, 360580320095198691, 360580327713012120, 360580335472158718, 360580341004862577, 360580346536846083, 360580356512048536, 360580370296538683]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578252475702405, 360578253744224483⟩, ⟨32661392492846885, 32674259430620301⟩, true⟩

def words07 : List Nat := [360580384687982061, 360580399077538160, 360580409876714432, 360580416262148943, 360580421368228542, 360580426473678172, 360580432983679329, 360580435081695744, 360580435081862600, 360580434936442816]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360676143298749671, 360676144569037998⟩, ⟨(-1433886722053606759), (-1433873828648475415)⟩, true⟩

def words08 : List Nat := [360580437541962549, 360580443858129740, 360580454607187956, 360580465354847198, 360580471924926982, 360580476029719445, 360580480004086198, 360580483977974586, 360580489210028482, 360580495591074655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600558168349367, 360600559440422277⟩, ⟨(-300545956823012663), (-300533036658253685)⟩, true⟩

def words09 : List Nat := [360580499201579916, 360580502811623663, 360580505022039218, 360580511211808445, 360580516270165501, 360580521327878748, 360580524147985407, 360580524148172894, 360580523904431474, 360580525240258405]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk149
