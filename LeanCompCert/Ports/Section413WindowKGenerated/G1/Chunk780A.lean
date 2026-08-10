import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492506822531546, 362492597875955131⟩, ⟨(-579680922936222057), (-574884953500177769)⟩, true⟩

def state01 : KState := ⟨⟨362482891426009428, 362482982503407568⟩, ⟨170337443027067514, 175135282604551106⟩, true⟩

def words00 : List Nat := [371285227764174145, 371285227766866896, 371285227688764354, 371285227608522749, 371285227527276641, 371285227497420640, 371285227433438379, 371285227485653229, 371285227536929042, 371285227539718356]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500719365043948, 362500810466755457⟩, ⟨(-1220516609516687185), (-1215716873133047587)⟩, true⟩

def words01 : List Nat := [371285227635825295, 371285227762125644, 371285227952221565, 371285227972747777, 371285227974867701, 371285227956590791, 371285228080132684, 371285228143862956, 371285228345411596, 371285228548129279]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486484604434819, 362486575730484496⟩, ⟨(-109865489184552220), (-105063853812802052)⟩, true⟩

def words02 : List Nat := [371285228748988354, 371285228813972551, 371285228925933865, 371285229039299023, 371285229200377414, 371285229205151067, 371285229211252630, 371285229218237392, 371285229272754972, 371285229293122258]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482938989654260, 362483030139973887⟩, ⟨166886776739510903, 171690306021357613⟩, true⟩

def words03 : List Nat := [371285229476361201, 371285229660726718, 371285229825352717, 371285229843114337, 371285229910334643, 371285229978911130, 371285230194727705, 371285230197420688, 371285230194664280, 371285230169523110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489106347085385, 362489197521540177⟩, ⟨(-314427151736030983), (-309621738823862301)⟩, true⟩

def words04 : List Nat := [371285230279080837, 371285230335848801, 371285230459702465, 371285230584592894, 371285230657701294, 371285230660394455, 371285230514490651, 371285230473939539, 371285230552155289, 371285230605820663]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk780A
