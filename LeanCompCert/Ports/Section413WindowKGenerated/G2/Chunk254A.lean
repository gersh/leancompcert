import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk254A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629632646270937, 360629636471091705⟩, ⟨(-1171960900224464000), (-1171895180513062764)⟩, true⟩

def state01 : KState := ⟨⟨360594689639275946, 360594693467264102⟩, ⟨(-284657483284023097), (-284591683105686723)⟩, true⟩

def words00 : List Nat := [360583501717960419, 360583502328351294, 360583502348389944, 360583502368519087, 360583502368797260, 360583501994134556, 360583500077397675, 360583497363206764, 360583494649166228, 360583493920488860]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360497471161234318, 360497474992348756⟩, ⟨2186421181271303815, 2186487060904259545⟩, true⟩

def words01 : List Nat := [360583495905632945, 360583497890684105, 360583498980396292, 360583499113580411, 360583499113861114, 360583497807461153, 360583496501068416, 360583495153582913, 360583492815715243, 360583489432195502]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557504974104663, 360557508808356389⟩, ⟨660078205602059122, 660144165000444634⟩, true⟩

def words02 : List Nat := [360583486048868568, 360583482893474814, 360583480759667078, 360583480168791027, 360583479577933109, 360583477714389311, 360583474311344962, 360583471904564492, 360583469497874794, 360583468075560497]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590481824191625, 360590485661614257⟩, ⟨(-178903291944419342), (-178837251894434138)⟩, true⟩

def words03 : List Nat := [360583467055089465, 360583464840353531, 360583462625725603, 360583461216424170, 360583460658382348, 360583459707757493, 360583458757171376, 360583456882707199, 360583455895044496, 360583456171739864]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360527229244023689, 360527233084577925⟩, ⟨1430305999701342486, 1430372119435408686⟩, true⟩

def words04 : List Nat := [360583456172010963, 360583456128988959, 360583454548049041, 360583451761556273, 360583448975233293, 360583445116113638, 360583442028599255, 360583440481247204, 360583438933981461, 360583436311274798]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk254A
