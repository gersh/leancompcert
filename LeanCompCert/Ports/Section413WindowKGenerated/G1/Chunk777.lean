import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494121836609044, 362494212164114329⟩, ⟨(-703978614175446289), (-699239157653001605)⟩, true⟩

def state01 : KState := ⟨⟨362476393558077880, 362476483909441654⟩, ⟨673601323036171982, 678342633488214734⟩, true⟩

def words00 : List Nat := [371285213266607153, 371285213269287883, 371285213252415892, 371285213224711371, 371285213215961275, 371285213218945909, 371285213157650997, 371285213126894862, 371285213095258558, 371285213064421557]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504549848425087, 362504640224042189⟩, ⟨(-1514542976974093978), (-1509799781674203956)⟩, true⟩

def words01 : List Nat := [371285213007071716, 371285213063475194, 371285213283932509, 371285213415509724, 371285213492553394, 371285213570371735, 371285213739458700, 371285213826902769, 371285214078674900, 371285214331662084]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496080732573096, 362496171132427004⟩, ⟨(-856328478431215269), (-851583399322411459)⟩, true⟩

def words02 : List Nat := [371285214551236792, 371285214553918059, 371285214715099021, 371285214880720887, 371285215094322653, 371285215159944152, 371285215222216088, 371285215285471633, 371285215470043208, 371285215614045375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481953891849396, 362482044315791853⟩, ⟨241889925217178181, 246636876851840167⟩, true⟩

def words03 : List Nat := [371285215922227178, 371285216231468064, 371285216541407472, 371285216631483001, 371285216727326921, 371285216824487208, 371285216976233632, 371285216978916263, 371285216940126363, 371285216902321978]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486808661552925, 362486899109541842⟩, ⟨(-135483565104157558), (-130734743980527054)⟩, true⟩

def words04 : List Nat := [371285216921071800, 371285216924106727, 371285217086767669, 371285217252821536, 371285217397887454, 371285217400569392, 371285217412829312, 371285217503940814, 371285217630954889, 371285217655361439]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485647190777917, 362485737663256358⟩, ⟨(-45154562981655164), (-40403837678572182)⟩, true⟩

def words05 : List Nat := [371285217670335483, 371285217686219502, 371285217810459217, 371285217853135405, 371285217945347020, 371285218038609724, 371285218130938260, 371285218133627994, 371285218063179015, 371285218073260363]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484085090813063, 362484175587207434⟩, ⟨76323018282418539, 81075603413114195⟩, true⟩

def words06 : List Nat := [371285218247062064, 371285218249745118, 371285218224536188, 371285218164120821, 371285218102704023, 371285218076817198, 371285218020652633, 371285218055816414, 371285218089228035, 371285218092073233]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494425557262633, 362494516077854719⟩, ⟨(-727869896190165451), (-723115429077768935)⟩, true⟩

def words07 : List Nat := [371285218215360615, 371285218353411027, 371285218655347799, 371285218766823076, 371285218828625763, 371285218891289088, 371285218988508306, 371285219020757910, 371285219142118149, 371285219264634553]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487297035009476, 362487387579792449⟩, ⟨(-173432469830708487), (-168676121026725751)⟩, true⟩

def words08 : List Nat := [371285219354077225, 371285219356760637, 371285219258152372, 371285219293842479, 371285219364195245, 371285219366888747, 371285219308155063, 371285219232041997, 371285219224487372, 371285219255422963]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483030962981597, 362483121531998609⟩, ⟨158456703688648235, 163214937779123977⟩, true⟩

def words09 : List Nat := [371285219353728102, 371285219453171467, 371285219551617214, 371285219554301318, 371285219450828518, 371285219399209364, 371285219456526405, 371285219459257201, 371285219434297854, 371285219410376233]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777
