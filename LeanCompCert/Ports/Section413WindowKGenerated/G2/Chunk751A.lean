import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554485628652323, 360554522182425929⟩, ⟨2084278934842709985, 2086133098214727857⟩, true⟩

def state01 : KState := ⟨⟨360573788967542481, 360573825531426376⟩, ⟨634408520678939124, 636263443382268774⟩, true⟩

def words00 : List Nat := [360582299883967562, 360582299518031850, 360582299241011933, 360582298960051641, 360582298679025146, 360582298248785364, 360582297796118098, 360582297345090619, 360582296893753559, 360582296619741944]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567169397191803, 360567205971257107⟩, ⟨1131657977935428366, 1133513665413324718⟩, true⟩

def words01 : List Nat := [360582296507913977, 360582296307528745, 360582296106944374, 360582296034838707, 360582296035734030, 360582295993666039, 360582295951499608, 360582295770852013, 360582295543452853, 360582295343799883]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562523960531042, 360562560544667982⟩, ⟨1480592802037461548, 1482449246147972968⟩, true⟩

def words02 : List Nat := [360582295143797487, 360582295058261515, 360582294795557295, 360582294410928864, 360582294026118883, 360582293591248865, 360582293261800477, 360582292984974832, 360582292708040225, 360582292332850439]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578601290393881, 360578637884637555⟩, ⟨272554020669551890, 274411224149399386⟩, true⟩

def words03 : List Nat := [360582292071098661, 360582291805566739, 360582291539717091, 360582291451003034, 360582291185175992, 360582290768634294, 360582290351898971, 360582290074330735, 360582289931381815, 360582289883894268]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557721287734124, 360557757892169164⟩, ⟨1841437509935097204, 1843295479242806864⟩, true⟩

def words04 : List Nat := [360582289836263363, 360582289641241400, 360582289269009578, 360582289038091028, 360582288806911923, 360582288440876934, 360582287897734811, 360582287242469616, 360582286587017093, 360582286108792489]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk751A
