import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574311974809152, 360574330883104885⟩, ⟨404060339147320438, 404759153437001320⟩, true⟩

def state01 : KState := ⟨⟨360608252156281482, 360608271071751297⟩, ⟨(-1452690399152681417), (-1451991192405298321)⟩, true⟩

def words00 : List Nat := [360581730380073629, 360581730564651916, 360581730799736543, 360581731034957697, 360581731035670767, 360581730953936140, 360581730826791363, 360581730893829036, 360581731294097129, 360581731779974410]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595046159909916, 360595065082636997⟩, ⟨(-730039752554828923), (-729340148725961185)⟩, true⟩

def words01 : List Nat := [360581732097669266, 360581732415442467, 360581733066464852, 360581733973266566, 360581734734345054, 360581735495519402, 360581736000366035, 360581736252962722, 360581736497170650, 360581736741621191]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600230775348798, 360600249705237595⟩, ⟨(-1013847599345872632), (-1013147603591558860)⟩, true⟩

def words02 : List Nat := [360581737319126104, 360581737563727964, 360581737564408277, 360581737510831160, 360581737457136919, 360581737187051370, 360581737492862963, 360581737812838781, 360581737963105583, 360581738302127995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601850820281677, 360601869757360304⟩, ⟨(-1102538913475109803), (-1101838524186596555)⟩, true⟩

def words03 : List Nat := [360581738901015574, 360581739500104429, 360581740088755990, 360581740344580047, 360581740345281822, 360581740290429746, 360581740437361768, 360581740807215369, 360581741175551331, 360581741544061560]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579351849759637, 360579370794078361⟩, ⟨129012481987645175, 129713267634443605⟩, true⟩

def words04 : List Nat := [360581741712144895, 360581741712905894, 360581741681493210, 360581741715970723, 360581741716607530, 360581741667115327, 360581741421863093, 360581740866477641, 360581740310966890, 360581739986181274]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk547A
