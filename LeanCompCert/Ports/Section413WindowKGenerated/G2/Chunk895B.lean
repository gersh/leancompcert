import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895A

def state06 : KState := ⟨⟨360550779889359427, 360550832592658469⟩, ⟨2792415851471372341, 2795603270581868473⟩, true⟩

def words05 : List Nat := [360582049534581105, 360582049453447081, 360582049372172785, 360582049228447793, 360582048959957551, 360582048660350379, 360582048360371555, 360582048081029243, 360582047804427416, 360582047457225038]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592917827213518, 360592970542705619⟩, ⟨(-981653863464538447), (-978465352284475257)⟩, true⟩

def words06 : List Nat := [360582047109737245, 360582046887175339, 360582046789309692, 360582046803409486, 360582046804621638, 360582046699067461, 360582046539058684, 360582046503960411, 360582046511526787, 360582046634830476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564676542171506, 360564729269974197⟩, ⟨1548092261554751000, 1551281875456157262⟩, true⟩

def words07 : List Nat := [360582046689787838, 360582046744907744, 360582046761381735, 360582046840757626, 360582046888026334, 360582046935503683, 360582046936666244, 360582046901222245, 360582046741071214, 360582046549226890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566169127555051, 360566221867534292⟩, ⟨1414324459015083002, 1417515163750273546⟩, true⟩

def words08 : List Nat := [360582046356958013, 360582046232824270, 360582046025513481, 360582045739595138, 360582045453467894, 360582045065035150, 360582044772471642, 360582044574236087, 360582044375863996, 360582044115148427]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583629752239388, 360583682504429377⟩, ⟨(-150113643735580007), (-146921844977708617)⟩, true⟩

def words09 : List Nat := [360582043939587698, 360582043888857074, 360582043837766100, 360582043783926469, 360582043605572802, 360582043307979641, 360582043010139195, 360582042837115435, 360582042750332428, 360582042769995859]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895B
