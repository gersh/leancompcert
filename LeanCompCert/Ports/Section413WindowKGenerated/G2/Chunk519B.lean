import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519A

def state06 : KState := ⟨⟨360590853566620605, 360590870556994723⟩, ⟨(-462275037668391915), (-461678530291448011)⟩, true⟩

def words05 : List Nat := [360581983405809461, 360581983560041686, 360581983770231018, 360581984265135779, 360581984667413979, 360581985069794653, 360581985228414682, 360581985229134008, 360581985288078099, 360581985459897065]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560056808792152, 360560073805949474⟩, ⟨1137958620791435394, 1138555480658560352⟩, true⟩

def words06 : List Nat := [360581985474346631, 360581985475065964, 360581985119965860, 360581984579308360, 360581984038550766, 360581983314312797, 360581982773450425, 360581982516141454, 360581982258752497, 360581981742848812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614756589436825, 360614773593382086⟩, ⟨(-1705071565808975117), (-1704474353140435109)⟩, true⟩

def words07 : List Nat := [360581981321888899, 360581981270826660, 360581981537359977, 360581981751832180, 360581981752519238, 360581981582047711, 360581981609880112, 360581981996349614, 360581982627781672, 360581983259353491]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624946751792744, 360624963762601640⟩, ⟨(-2234859400875050598), (-2234261831401649340)⟩, true⟩

def words08 : List Nat := [360581983705253186, 360581984251645994, 360581985079411225, 360581985907364706, 360581986562298072, 360581987350968421, 360581987879506179, 360581988408098860, 360581988923708181, 360581989751111159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575624272573135, 360575641290157105⟩, ⟨329804278273138664, 330402200017120654⟩, true⟩

def words09 : List Nat := [360581990947635411, 360581992144251725, 360581993131899620, 360581993750418021, 360581994276475638, 360581994802717446, 360581995235578491, 360581995299420725, 360581995300061965, 360581995178618973]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519B
