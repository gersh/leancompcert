import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480022690118209, 362480170528750170⟩, ⟨500250882671993588, 510082429834444962⟩, true⟩

def state01 : KState := ⟨⟨362485730103760952, 362485877973321314⟩, ⟨(-61934664746799973), (-52100070973827521)⟩, true⟩

def words00 : List Nat := [371285348995939029, 371285348999752071, 371285349023328273, 371285349084286293, 371285349118100836, 371285349121560687, 371285349017638536, 371285349018569566, 371285349088702030, 371285349097652873]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488753657216013, 362488901558392261⟩, ⟨(-359823060927728771), (-349985352515526511)⟩, true⟩

def words01 : List Nat := [371285349100283720, 371285349089374967, 371285349119712449, 371285349127832000, 371285349134683248, 371285349142842585, 371285349149673896, 371285349153197513, 371285349124590812, 371285349164968367]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475246181956992, 362475394113915632⟩, ⟨971020877297209961, 980861618553925733⟩, true⟩

def words02 : List Nat := [371285349297451326, 371285349300911794, 371285349296343221, 371285349281847952, 371285349266103133, 371285349253323606, 371285349187675083, 371285349148291004, 371285349107688993, 371285349067925111]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491191521016532, 362491339484285598⟩, ⟨(-600139813867195276), (-590295987441289228)⟩, true⟩

def words03 : List Nat := [371285348969238875, 371285348951888741, 371285349014103210, 371285349017571533, 371285348995090821, 371285348957871290, 371285348974594870, 371285348997223560, 371285349060404214, 371285349125070233]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484519076635860, 362484667071147051⟩, ⟨57392638330503518, 67239543513326890⟩, true⟩

def words04 : List Nat := [371285349188595641, 371285349192059936, 371285349196319901, 371285349252974105, 371285349338900892, 371285349342422664, 371285349342885616, 371285349341846114, 371285349355771796, 371285349359767177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985A
