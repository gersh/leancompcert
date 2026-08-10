import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602036082558797, 360602049206903136⟩, ⟨(-864369576377936224), (-863962494119843272)⟩, true⟩

def state01 : KState := ⟨⟨360605055213314412, 360605068343585191⟩, ⟨(-1002994813805708099), (-1002587459493938605)⟩, true⟩

def words00 : List Nat := [360583227697468226, 360583228186067004, 360583228282474040, 360583228378940504, 360583228379467411, 360583228693700110, 360583229287600960, 360583229881596845, 360583230236649735, 360583230712963033]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360618218534987231, 360618231671209569⟩, ⟨(-1607428331265093455), (-1607020703687237959)⟩, true⟩

def words01 : List Nat := [360583231469863298, 360583232226914616, 360583232963080439, 360583233631204143, 360583233896218853, 360583234161274091, 360583234366936569, 360583234812446687, 360583235575082771, 360583236337839494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566773237751652, 360566786379966224⟩, ⟨755044008032519552, 755451910803682096⟩, true⟩

def words02 : List Nat := [360583236863138159, 360583236915490717, 360583237176761446, 360583237438204470, 360583237438735749, 360583237375738696, 360583236839740446, 360583235939367369, 360583235038915460, 360583234277000923]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557482014691014, 360557495162834634⟩, ⟨1181915738039201499, 1182323913161830929⟩, true⟩

def words03 : List Nat := [360583233919410823, 360583233778126564, 360583233636779904, 360583233205755973, 360583232986944702, 360583232648171972, 360583232309217937, 360583232307828556, 360583231985212340, 360583231425637461]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584570822323226, 360584583976421509⟩, ⟨(-62694071056081874), (-62285622346898998)⟩, true⟩

def words04 : List Nat := [360583230865953232, 360583230294356850, 360583230285950987, 360583230518463089, 360583230519049374, 360583230348190158, 360583229704648224, 360583229134892780, 360583228564965644, 360583228497273136]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459A
