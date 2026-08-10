import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915A

def state06 : KState := ⟨⟨360568672887299846, 360568728065415386⟩, ⟨1210717982168787197, 1214129530528461119⟩, true⟩

def words05 : List Nat := [360581988851132560, 360581988926394179, 360581988927491267, 360581988926925564, 360581988928032937, 360581988928418576, 360581988928671562, 360581988868261032, 360581988688509560, 360581988545215828]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555768666918093, 360555823857487973⟩, ⟨2392280769682954686, 2395693458425392058⟩, true⟩

def words06 : List Nat := [360581988401461404, 360581988266783845, 360581988092082406, 360581987842459198, 360581987592616489, 360581987313313283, 360581987093473834, 360581986846468026, 360581986599322925, 360581986284684931]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588920199545639, 360588975402609841⟩, ⟨(-643556627127663789), (-640142794219711203)⟩, true⟩

def words07 : List Nat := [360581986000048309, 360581985834935059, 360581985669429607, 360581985623324388, 360581985608026944, 360581985466665234, 360581985325052852, 360581985339186638, 360581985416586834, 360581985494285847]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593942001489406, 360593997217178015⟩, ⟨(-1103581734498364703), (-1100166745386013367)⟩, true⟩

def words08 : List Nat := [360581985495486081, 360581985478714764, 360581985434980508, 360581985473600461, 360581985474713441, 360581985445999564, 360581985446057015, 360581985386448920, 360581985350338968, 360581985482996862]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577643767980561, 360577698996130099⟩, ⟨389311295121240020, 392727425593039570⟩, true⟩

def words09 : List Nat := [360581985734285511, 360581985985822642, 360581986177868556, 360581986299217853, 360581986337997963, 360581986377113177, 360581986431387431, 360581986457692216, 360581986458874174, 360581986413440067]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk915B
