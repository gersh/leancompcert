import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502065059212296, 362502203097362278⟩, ⟨(-1628061470599554380), (-1619179682964435470)⟩, true⟩

def state01 : KState := ⟨⟨362491873780522668, 362492011848819537⟩, ⟨(-656814777444568191), (-647930116660036587)⟩, true⟩

def words00 : List Nat := [371285213113784992, 371285213183028034, 371285213323791149, 371285213466339976, 371285213611912695, 371285213615253591, 371285213614136142, 371285213613757872, 371285213711334307, 371285213786511304]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482290976304525, 362482429074752336⟩, ⟨256628875075434291, 265516409697187269⟩, true⟩

def words01 : List Nat := [371285213970303106, 371285214155567114, 371285214339230071, 371285214376963620, 371285214419785708, 371285214464228501, 371285214617142090, 371285214624368064, 371285214626939761, 371285214601501153]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495841447818467, 362495979576184000⟩, ⟨(-1035046243981191613), (-1026155857449355005)⟩, true⟩

def words02 : List Nat := [371285214651921714, 371285214678140484, 371285214760165417, 371285214843512105, 371285214908101928, 371285214911646851, 371285215024200989, 371285215138573563, 371285215323721659, 371285215440095537]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491761967961672, 362491900126748805⟩, ⟨(-646129858631311146), (-637236571852873742)⟩, true⟩

def words03 : List Nat := [371285215552248692, 371285215665497542, 371285215822992350, 371285215927040075, 371285216043331262, 371285216160937195, 371285216254595692, 371285216257937910, 371285216290270209, 371285216364549407]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486001785587537, 362486139974131766⟩, ⟨(-96880949783695984), (-87984825810372454)⟩, true⟩

def words04 : List Nat := [371285216528710274, 371285216615672245, 371285216695102556, 371285216775705278, 371285216888058155, 371285216946740562, 371285217038715291, 371285217132003458, 371285217214235202, 371285217227377035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk953A
