import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564828593355462, 360564876106438761⟩, ⟨1490935290538231703, 1493669087312143277⟩, true⟩

def state01 : KState := ⟨⟨360584259454009314, 360584306978618831⟩, ⟨(-164653373274920887), (-161918594408420013)⟩, true⟩

def words00 : List Nat := [360582407228979928, 360582407162087332, 360582407106804152, 360582406983029924, 360582406859034090, 360582406700718052, 360582406702463849, 360582406759548327, 360582406760639068, 360582406770964791]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586647392405089, 360586694928592217⟩, ⟨(-368199266285976109), (-365463500836156137)⟩, true⟩

def words01 : List Nat := [360582406771972930, 360582406741090141, 360582406815181564, 360582406817180139, 360582406818318879, 360582406697890892, 360582406577238010, 360582406438655794, 360582406456298381, 360582406507887976]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578671017732738, 360578718565588635⟩, ⟨311462409700795345, 314199169620067269⟩, true⟩

def words02 : List Nat := [360582406508992284, 360582406460973871, 360582406275061356, 360582406227077661, 360582406178788888, 360582406035913584, 360582405807050776, 360582405509274634, 360582405211256520, 360582405051211304]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572728833708650, 360572776393112816⟩, ⟨817971458794177677, 820709203029276521⟩, true⟩

def words03 : List Nat := [360582405041148958, 360582405074593962, 360582405075685100, 360582405040063366, 360582404945035980, 360582404815724199, 360582404692915072, 360582404720505751, 360582404721635507, 360582404609947979]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610181689398786, 360610229260362087⟩, ⟨(-2374759217961850366), (-2372020488367966508)⟩, true⟩

def words04 : List Nat := [360582404497990136, 360582404387878326, 360582404441915198, 360582404538412648, 360582404539542332, 360582404518930950, 360582404621290889, 360582404742083491, 360582404971829235, 360582405299489277]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk852A
