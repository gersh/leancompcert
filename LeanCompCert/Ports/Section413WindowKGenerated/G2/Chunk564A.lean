import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569069640477395, 360569089792161831⟩, ⟨714076060750439401, 714843951010578951⟩, true⟩

def state01 : KState := ⟨⟨360568798731551341, 360568818890631235⟩, ⟨729342509326813051, 730110816727718335⟩, true⟩

def words00 : List Nat := [360581764195328905, 360581764196114353, 360581763972473971, 360581763589915806, 360581763207243489, 360581762682065605, 360581762436463791, 360581762284434660, 360581762132319869, 360581761823032011]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570779315874080, 360570799482379815⟩, ⟨617583929269272860, 618352655598830596⟩, true⟩

def words01 : List Nat := [360581761594228601, 360581761504774886, 360581761415096966, 360581761317428964, 360581761008208561, 360581760432269456, 360581759856199655, 360581759594020171, 360581759488914219, 360581759295488621]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360543460170074132, 360543480344066063⟩, ⟨2158894088690262132, 2159663237426112286⟩, true⟩

def words02 : List Nat := [360581759101944466, 360581758750809046, 360581758086348491, 360581757525854343, 360581756965173110, 360581756231192726, 360581755269059998, 360581754064712688, 360581752860257640, 360581751888234522]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360542841700303792, 360542861881688059⟩, ⟨2193904606724575792, 2194674172648132586⟩, true⟩

def words03 : List Nat := [360581751210669152, 360581750846768859, 360581750482798984, 360581749917425396, 360581749465521329, 360581748934376085, 360581748403019164, 360581748185265106, 360581747654409179, 360581746966249508]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567511709455136, 360567531898271087⟩, ⟨801363951032001889, 802133936436478267⟩, true⟩

def words04 : List Nat := [360581746277949342, 360581745425812530, 360581744775210293, 360581744438168643, 360581744101077860, 360581743484267940, 360581742803088498, 360581742333781220, 360581741864237974, 360581741533991840]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk564A
