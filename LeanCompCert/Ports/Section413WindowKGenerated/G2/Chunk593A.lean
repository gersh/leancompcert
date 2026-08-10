import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603769589219357, 360603791956005047⟩, ⟨(-1290515105781160513), (-1289619043252415617)⟩, true⟩

def state01 : KState := ⟨⟨360592991702527190, 360593014077209933⟩, ⟨(-651503147571096291), (-650606616708164975)⟩, true⟩

def words00 : List Nat := [360582045098338198, 360582045099167070, 360582045128447096, 360582045229161995, 360582045229856084, 360582045200406917, 360582045088642291, 360582044811542521, 360582044534293225, 360582044668218209]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564233632015895, 360564256014516599⟩, ⟨1054231718110264855, 1055128712695665069⟩, true⟩

def words01 : List Nat := [360582044761808713, 360582044855548571, 360582044856288971, 360582044752909066, 360582044461273125, 360582044097041125, 360582043732579049, 360582043499282191, 360582043378797664, 360582043079801422]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588901981281369, 360588924371601352⟩, ⟨(-409241006991028773), (-408343548526671553)⟩, true⟩

def words02 : List Nat := [360582042780627318, 360582042766642230, 360582042872254260, 360582042978017203, 360582042978795808, 360582042826633080, 360582042391192567, 360582042120765018, 360582041850094757, 360582041906304515]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577794782512793, 360577817180740190⟩, ⟨249895243435493596, 250793171084276530⟩, true⟩

def words03 : List Nat := [360582041907043088, 360582041880911684, 360582042111738193, 360582042601952039, 360582043019203652, 360582043436576738, 360582043673096537, 360582043673925918, 360582043627341272, 360582043557064496]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568143098033672, 360568165504071257⟩, ⟨822661495883649707, 823559887027290063⟩, true⟩

def words04 : List Nat := [360582043699330224, 360582043700159621, 360582043630695826, 360582043396711234, 360582043162607140, 360582042686118660, 360582042440278077, 360582042288887805, 360582042137411588, 360582041829042231]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593A
