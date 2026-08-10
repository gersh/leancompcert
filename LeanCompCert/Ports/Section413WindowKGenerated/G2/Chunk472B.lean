import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472A

def state06 : KState := ⟨⟨360520504695153892, 360520518642283820⟩, ⟨2945935115078489297, 2946380525612903071⟩, true⟩

def words05 : List Nat := [360582865979034399, 360582866502578162, 360582866749462185, 360582866750111654, 360582866550171810, 360582866100425670, 360582865650512821, 360582865061697586, 360582864026099719, 360582862707573979]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558348052578477, 360558362005837988⟩, ⟨1157278639207538421, 1157724339456308489⟩, true⟩

def words06 : List Nat := [360582861388955196, 360582860430680693, 360582859696974713, 360582859311461592, 360582858925903790, 360582858114645959, 360582856856701236, 360582855669659686, 360582854482467984, 360582853741388154]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571374861936584, 360571388821390814⟩, ⟨541318245858973254, 541764238962526106⟩, true⟩

def words07 : List Nat := [360582853223863615, 360582852358717367, 360582851493482189, 360582850892260682, 360582850515435553, 360582849915392126, 360582849315310450, 360582848385111636, 360582847697507773, 360582847455886638]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563344551609560, 360563358517179172⟩, ⟨920975272904087358, 921421555174134968⟩, true⟩

def words08 : List Nat := [360582847214062807, 360582847105542091, 360582846703333828, 360582846078797729, 360582845454191616, 360582844516908821, 360582843891972939, 360582843712763422, 360582843533493452, 360582843007667101]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602406382135387, 360602420353850502⟩, ⟨(-926424192428022487), (-925977619507459937)⟩, true⟩

def words09 : List Nat := [360582842596181137, 360582842327392721, 360582842234412326, 360582842514617427, 360582842515222252, 360582842419066738, 360582842671430408, 360582843244886146, 360582843659313649, 360582844073866835]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472B
