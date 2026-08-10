import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598133878283773, 360598190493696106⟩, ⟨(-1504611486062987237), (-1501067517769400087)⟩, true⟩

def state01 : KState := ⟨⟨360584422218225893, 360584478846282771⟩, ⟨(-233582016522731911), (-230036876016868617)⟩, true⟩

def words00 : List Nat := [360581998004364310, 360581998005705318, 360581997971309939, 360581997863510521, 360581997755494600, 360581997618763479, 360581997575869816, 360581997613372122, 360581997614578087, 360581997621012665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594985946373454, 360595042587091669⟩, ⟨(-1213026025417743961), (-1209479711017994385)⟩, true⟩

def words01 : List Nat := [360581997740347878, 360581997860074460, 360581997979642536, 360581998010087981, 360581998011346482, 360581997931915671, 360581997887656723, 360581998012179573, 360581998153958921, 360581998296035512]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593224210804797, 360593280864309544⟩, ⟨(-1049678465032118326), (-1046130965001815708)⟩, true⟩

def words02 : List Nat := [360581998372360139, 360581998485956017, 360581998715463857, 360581998945360846, 360581999145034064, 360581999261819960, 360581999320670235, 360581999379654651, 360581999390052257, 360581999513251087]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576363991095254, 360576420657222043⟩, ⟨513890488186029609, 517439158722701515⟩, true⟩

def words03 : List Nat := [360581999714785057, 360581999916571684, 360582000059837752, 360582000108367003, 360582000109492671, 360582000089879692, 360582000164861111, 360582000175211593, 360582000176409369, 360582000117635271]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594089704708335, 360594146383515468⟩, ⟨(-1130135224260959815), (-1126585377689434311)⟩, true⟩

def words04 : List Nat := [360582000058565336, 360582000065080323, 360582000111108411, 360582000157373873, 360582000158624138, 360582000102375914, 360581999961991813, 360581999913426411, 360581999909025303, 360582000041398516]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk927A
