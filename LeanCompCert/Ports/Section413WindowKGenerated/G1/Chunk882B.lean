import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882A

def state06 : KState := ⟨⟨362471892257571350, 362472009954643537⟩, ⟨1156753533261828343, 1163767425984678247⟩, true⟩

def words05 : List Nat := [371285196844223300, 371285196716415051, 371285196587400088, 371285196512999304, 371285196373052086, 371285196262841468, 371285196151504419, 371285196047989021, 371285195772438480, 371285195626816489]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470374839519228, 362470492564010841⟩, ⟨1290684371423068090, 1297700684323913838⟩, true⟩

def words06 : List Nat := [371285195479507435, 371285195461420832, 371285195271586358, 371285195061044123, 371285194849267980, 371285194669202686, 371285194434009279, 371285194308286033, 371285194181554370, 371285194055846391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484873310304314, 362484991062608642⟩, ⟨10848019160057218, 17866787230063422⟩, true⟩

def words07 : List Nat := [371285193891382467, 371285193842127630, 371285193836156568, 371285193839243761, 371285193783628337, 371285193689953383, 371285193595089396, 371285193554817989, 371285193449128957, 371285193450320809]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479663980565704, 362479781760656073⟩, ⟨470698025786580680, 477719246948935170⟩, true⟩

def words08 : List Nat := [371285193450355253, 371285193432434927, 371285193264632422, 371285193183780947, 371285193101378891, 371285193059159260, 371285192901096148, 371285192744205304, 371285192586018796, 371285192557427496]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470103122248974, 362470220930037507⟩, ⟨1314888999840609942, 1321912666615966748⟩, true⟩

def words09 : List Nat := [371285192498266195, 371285192493622596, 371285192487972448, 371285192478852067, 371285192310425990, 371285192182816606, 371285192053586055, 371285191962132876, 371285191794527277, 371285191628413679]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk882B
