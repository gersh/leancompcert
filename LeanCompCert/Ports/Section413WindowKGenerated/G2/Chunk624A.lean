import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571894237682848, 360571919104505809⟩, ⟨671504733655765455, 672552958845108183⟩, true⟩

def state01 : KState := ⟨⟨360564431107575935, 360564455982638292⟩, ⟨1137240728010777250, 1138289467380202968⟩, true⟩

def words00 : List Nat := [360582697108714580, 360582697109590679, 360582697045281947, 360582696769564504, 360582696493725807, 360582696043542092, 360582695723964387, 360582695491044908, 360582695258036587, 360582694878125878]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587453531699738, 360587478415040223⟩, ⟨(-299687820613502161), (-298638564565826437)⟩, true⟩

def words01 : List Nat := [360582694586595590, 360582694501026142, 360582694415189175, 360582694405091381, 360582694355105682, 360582694097539533, 360582693839813510, 360582693995774150, 360582694073143929, 360582694150697040]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604934062422571, 360604958954105883⟩, ⟨(-1391030728328046191), (-1389980951480458519)⟩, true⟩

def words02 : List Nat := [360582694151477440, 360582694099874675, 360582694132325154, 360582694277407055, 360582694278146033, 360582694308842726, 360582694309623163, 360582694247404654, 360582694321495667, 360582694679122615]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583771631020726, 360583796530966993⟩, ⟨(-69659661149508068), (-68609368405133442)⟩, true⟩

def words03 : List Nat := [360582695232470324, 360582695785968155, 360582696138878152, 360582696500308761, 360582696796299231, 360582697092519292, 360582697527405666, 360582697706914808, 360582697725297150, 360582697743817442]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585140123401310, 360585165031611952⟩, ⟨(-155092351153813898), (-154041542340221850)⟩, true⟩

def words04 : List Nat := [360582697848674177, 360582698084281499, 360582698470787957, 360582698857449770, 360582699006638503, 360582699007514955, 360582698901133974, 360582698660881962, 360582698420380604, 360582698433121292]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624A
