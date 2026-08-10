import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk702A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk702B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk702A

def state06 : KState := ⟨⟨362480148320076852, 362480221602397289⟩, ⟨355021752814477871, 358499063037839421⟩, true⟩

def words05 : List Nat := [371285323561363569, 371285323576528510, 371285323769766087, 371285323863870303, 371285324018610650, 371285324174299950, 371285324288552195, 371285324290958236, 371285324135248018, 371285324065577447]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469896036339184, 362469969340087367⟩, ⟨1075425937598371894, 1078904753446657120⟩, true⟩

def words06 : List Nat := [371285324051121180, 371285324053533508, 371285323927031597, 371285323780723120, 371285323633486720, 371285323487922344, 371285323266577938, 371285323198943746, 371285323130503530, 371285323043708353]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486082419117383, 362486155744686623⟩, ⟨(-62062340145276515), (-58581990825499581)⟩, true⟩

def words07 : List Nat := [371285322826847777, 371285322813440928, 371285322867136089, 371285322869543652, 371285322704018266, 371285322503623137, 371285322302277449, 371285322270315692, 371285322190535581, 371285322205169179]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475195617838203, 362475268965121727⟩, ⟨703055550423054208, 706537425933769676⟩, true⟩

def words08 : List Nat := [371285322210095695, 371285322212502632, 371285321947632663, 371285321856635529, 371285321764476951, 371285321734687245, 371285321459839803, 371285321144154698, 371285320827463523, 371285320713961303]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469156423862617, 362469229792774813⟩, ⟨1127633272762264937, 1131116668662097981⟩, true⟩

def words09 : List Nat := [371285320572599855, 371285320565630966, 371285320557871236, 371285320551160501, 371285320375140676, 371285320216445400, 371285320096871720, 371285320099279105, 371285319871999455, 371285319645814104]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk702B
