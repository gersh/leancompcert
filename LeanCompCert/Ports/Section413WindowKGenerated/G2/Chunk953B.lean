import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953A

def state06 : KState := ⟨⟨360609718339336316, 360609778382270794⟩, ⟨(-2636015123803366916), (-2632148842895764002)⟩, true⟩

def words05 : List Nat := [360582174533598463, 360582174735253961, 360582174936103725, 360582175148029318, 360582175263694443, 360582175379447742, 360582175583757452, 360582175858265617, 360582176148846302, 360582176439727241]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605052106910315, 360605112163033450⟩, ⟨(-2191153789569908986), (-2187286250929108922)⟩, true⟩

def words06 : List Nat := [360582176639809756, 360582176730376589, 360582176895591296, 360582177061224167, 360582177198482486, 360582177271469002, 360582177284444711, 360582177297602024, 360582177420422834, 360582177662494197]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589743494436553, 360589803563553613⟩, ⟨(-731049737199356865), (-727180959261826147)⟩, true⟩

def words07 : List Nat := [360582177996503021, 360582178330770117, 360582178610035588, 360582178818900768, 360582178951358044, 360582179084157699, 360582179304125246, 360582179440701287, 360582179521866935, 360582179603233824]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587733777676532, 360587793859864118⟩, ⟨(-539346915360759080), (-535476890691437910)⟩, true⟩

def words08 : List Nat := [360582179604366878, 360582179682526682, 360582179874211765, 360582180066158054, 360582180165105202, 360582180201256024, 360582180236495976, 360582180272137604, 360582180304698529, 360582180364977898]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585830170330920, 360585890265697437⟩, ⟨(-357723673567935071), (-353852391695478299)⟩, true⟩

def words09 : List Nat := [360582180369468775, 360582180374107330, 360582180488373697, 360582180673179244, 360582180829638190, 360582180986343823, 360582181087635846, 360582181089018729, 360582181119535701, 360582181160009913]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953B
