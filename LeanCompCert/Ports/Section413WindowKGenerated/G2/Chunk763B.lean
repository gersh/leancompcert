import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763A

def state06 : KState := ⟨⟨360566108481246591, 360566146321521652⟩, ⟨1222837583776851035, 1224789176199447851⟩, true⟩

def words05 : List Nat := [360582186206779333, 360582186427970480, 360582186551198401, 360582186552286818, 360582186504327046, 360582186413484826, 360582186322309242, 360582186323397848, 360582186200121804, 360582185991194249]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593619739217751, 360593657589784908⟩, ⟨(-878115108754760269), (-876162730377962833)⟩, true⟩

def words06 : List Nat := [360582185782025740, 360582185659070475, 360582185666072006, 360582185673269389, 360582185674282880, 360582185536598130, 360582185227642948, 360582185090235304, 360582184985124241, 360582185136492717]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573895827858300, 360573933688788089⟩, ⟨628282153757064908, 630235323579139836⟩, true⟩

def words07 : List Nat := [360582185201915731, 360582185267455881, 360582185312832791, 360582185444101651, 360582185468718303, 360582185493506041, 360582185494493044, 360582185387390177, 360582185109054278, 360582185002267785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573189951275853, 360573227822459286⟩, ⟨682142788456954075, 684096741503686629⟩, true⟩

def words08 : List Nat := [360582184895122140, 360582184846284849, 360582184661850782, 360582184353202559, 360582184044357700, 360582183692663912, 360582183447545070, 360582183373784791, 360582183299902576, 360582183140452528]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585137977742716, 360585175859218858⟩, ⟨(-230703178068449192), (-228748438711461906)⟩, true⟩

def words09 : List Nat := [360582183024118516, 360582182902353474, 360582182784674233, 360582182785763132, 360582182620232461, 360582182287861959, 360582181955291551, 360582181765136438, 360582181768578239, 360582181808896069]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk763B
