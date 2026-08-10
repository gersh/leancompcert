import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474321527994407, 362474386080452282⟩, ⟨732581943747208141, 735463852266299403⟩, true⟩

def state01 : KState := ⟨⟨362490165404756823, 362490229977397033⟩, ⟨(-314795366842418130), (-311912124166477144)⟩, true⟩

def words00 : List Nat := [371285512447002221, 371285512332785597, 371285512140300005, 371285512160098807, 371285512168308116, 371285512170561116, 371285511873656859, 371285511806602364, 371285511897236705, 371285511970950807]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490334058427252, 362490398651601518⟩, ⟨(-325939526954448482), (-323054926669188928)⟩, true⟩

def words01 : List Nat := [371285512043984422, 371285512117808693, 371285512336006467, 371285512441311779, 371285512556550066, 371285512672599683, 371285512787923219, 371285512790187417, 371285512760598216, 371285512837311517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482701542664985, 362482766155929778⟩, ⟨178786147747311966, 181672076522579448⟩, true⟩

def words02 : List Nat := [371285513030078698, 371285513033300645, 371285513039313336, 371285513046047808, 371285513081375020, 371285513083858716, 371285513146290657, 371285513280026240, 371285513349666574, 371285513352006031]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501602298452221, 362501666932065110⟩, ⟨(-1071216364579316250), (-1068329090080827010)⟩, true⟩

def words03 : List Nat := [371285513421931034, 371285513534573865, 371285513821681452, 371285513843818469, 371285513845562977, 371285513831683938, 371285514028853268, 371285514142371509, 371285514388125549, 371285514634850360]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473617584181853, 362473682238196574⟩, ⟨779769280615120681, 782657904588358071⟩, true⟩

def words04 : List Nat := [371285514880249257, 371285514882503673, 371285514823235231, 371285514790269843, 371285514790381143, 371285514792635653, 371285514524072994, 371285514226855570, 371285513928748321, 371285513801380072]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk661A
