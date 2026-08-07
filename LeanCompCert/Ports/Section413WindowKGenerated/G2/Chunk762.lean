import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk762

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571938703903662, 360571976379588485⟩, ⟨775429385019847015, 777368422501623899⟩, true⟩

def state01 : KState := ⟨⟨360587335054660846, 360587372740584911⟩, ⟨(-397827692594395943), (-395887874829708837)⟩, true⟩

def words00 : List Nat := [360582177939784239, 360582177953525452, 360582177954502147, 360582177881500553, 360582177808323884, 360582177692049003, 360582177850634830, 360582178016559946, 360582178042244653, 360582178111530973]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595879660692028, 360595917356866556⟩, ⟨(-1049035916654369821), (-1047095317650756953)⟩, true⟩

def words01 : List Nat := [360582178238952338, 360582178366699073, 360582178666046051, 360582178849055253, 360582178885484539, 360582178922016168, 360582179103725983, 360582179371965861, 360582179553095846, 360582179734457368]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581331734407950, 360581369440955004⟩, ⟨59758987441054784, 61700377086957902⟩, true⟩

def words02 : List Nat := [360582179827038248, 360582179839415288, 360582179847620167, 360582179856128247, 360582179857038495, 360582179821417808, 360582179613967262, 360582179320495115, 360582179026817886, 360582178838529279]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553156347455151, 360553194064215548⟩, ⟨2207809605832902548, 2209751774094748354⟩, true⟩

def words03 : List Nat := [360582178990017084, 360582179152331514, 360582179228394236, 360582179229480937, 360582179191479338, 360582179087549887, 360582178983319794, 360582178875343111, 360582178595601775, 360582178216551524]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573606654570159, 360573644381591001⟩, ⟨648536040336548562, 650478990903254448⟩, true⟩

def words04 : List Nat := [360582177837271779, 360582177421438839, 360582177114700241, 360582176979992362, 360582176845193482, 360582176540743091, 360582176118994825, 360582175773402914, 360582175427488962, 360582175253602847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360588682164960404, 360588719902343049⟩, ⟨(-501106182667802812), (-499162441963587830)⟩, true⟩

def words05 : List Nat := [360582175142709294, 360582174899535902, 360582174656153537, 360582174613698188, 360582174614607986, 360582174570519853, 360582174526324118, 360582174366050173, 360582174366851068, 360582174453922971]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595824144480587, 360595861892093997⟩, ⟨(-1045802441368618486), (-1043857920414665240)⟩, true⟩

def words06 : List Nat := [360582174712367278, 360582174914190353, 360582174985266364, 360582175056452428, 360582175057378120, 360582175075806630, 360582175259426798, 360582175443251629, 360582175540890163, 360582175721460144]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607938818233750, 360607976576123473⟩, ⟨(-1969833663588808329), (-1967888358809679233)⟩, true⟩

def words07 : List Nat := [360582175953269387, 360582176185408162, 360582176546841429, 360582176883357748, 360582177078364172, 360582177273438329, 360582177600571108, 360582178014093741, 360582178353199274, 360582178692524547]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360611029946564861, 360611067714806509⟩, ⟨(-2205763396834272247), (-2203817302359284985)⟩, true⟩

def words08 : List Nat := [360582178929722228, 360582179058997214, 360582179359695310, 360582179660721488, 360582179822866957, 360582179989923561, 360582180051269312, 360582180112731783, 360582180345597112, 360582180725484581]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573664826010555, 360573702604512461⟩, ⟨645046768927848147, 646993646207951715⟩, true⟩

def words09 : List Nat := [360582181115266836, 360582181505245108, 360582181762408843, 360582181921501753, 360582182037037906, 360582182152870475, 360582182319877341, 360582182320964908, 360582182316680471, 360582182206690809]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk762
