import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360542825406426736, 360542857837629390⟩, ⟨2801028220042863355, 2802581346971716707⟩, true⟩

def state01 : KState := ⟨⟨360566652955120524, 360566685395829020⟩, ⟨1111548213780983206, 1113102014719266670⟩, true⟩

def words00 : List Nat := [360582385931797080, 360582385573878760, 360582385352226157, 360582385121755993, 360582384891215246, 360582384482564416, 360582384049889577, 360582383597901129, 360582383145629434, 360582382787095686]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566416835063788, 360566449285345858⟩, ⟨1128297781532071922, 1129852261380760746⟩, true⟩

def words01 : List Nat := [360582382566632223, 360582382246479036, 360582381926142508, 360582381804505815, 360582381804767092, 360582381696529587, 360582381588207477, 360582381294003177, 360582380871793824, 360582380648309490]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565316606927221, 360565349066679106⟩, ⟨1206313148907602311, 1207868300402538683⟩, true⟩

def words02 : List Nat := [360582380424487037, 360582380399226401, 360582380175299413, 360582379837364678, 360582379499256340, 360582379111386868, 360582378823556480, 360582378623837416, 360582378424011985, 360582378085435663]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583595844781223, 360583628314032530⟩, ⟨(-90383027755962078), (-88827202419088036)⟩, true⟩

def words03 : List Nat := [360582377846184167, 360582377602920542, 360582377359367334, 360582377265821933, 360582377067318093, 360582376699589647, 360582376331679122, 360582376162374775, 360582376167482516, 360582376186173900]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578230718219520, 360578263197045570⟩, ⟨290084672467860316, 291641177083156228⟩, true⟩

def words04 : List Nat := [360582376187076757, 360582376056851130, 360582375782192050, 360582375647917550, 360582375513395144, 360582375241713304, 360582374884855016, 360582374428500623, 360582373971966627, 360582373713988251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk709A
