import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536907737551243, 360536910989119877⟩, ⟨1042276425772331849, 1042328121926797855⟩, true⟩

def state01 : KState := ⟨⟨360645631695765315, 360645634950217985⟩, ⟨(-1513321973584435732), (-1513270209640544868)⟩, true⟩

def words00 : List Nat := [360581263490193870, 360581263014839542, 360581264003464060, 360581264992063631, 360581264992345422, 360581264643742899, 360581265115515822, 360581265587339163, 360581267863145445, 360581270601205160]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360610972931372215, 360610976188740464⟩, ⟨(-698430901442254110), (-698379068938480868)⟩, true⟩

def words01 : List Nat := [360581272080951826, 360581273560605209, 360581274979340494, 360581277300477076, 360581279160401180, 360581281020216849, 360581281610264048, 360581281938002853, 360581283200761244, 360581284463518812]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595234638276494, 360595237898525298⟩, ⟨(-328180832171237022), (-328128931902204448)⟩, true⟩

def words02 : List Nat := [360581286807685876, 360581288400479870, 360581289086810853, 360581289773116803, 360581289974887375, 360581291088283152, 360581292142378586, 360581293196439331, 360581293196714374, 360581293360175793]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360748393656526726, 360748396919661607⟩, ⟨(-3932856157260646205), (-3932804189067633469)⟩, true⟩

def words03 : List Nat := [360581295753099002, 360581298145908306, 360581301785216354, 360581305924478258, 360581308525241233, 360581311125804536, 360581315525270916, 360581320824568264, 360581327922356147, 360581335019612008]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360699108936005040, 360699112202059376⟩, ⟨(-2772926857015164061), (-2772874820084137765)⟩, true⟩

def words04 : List Nat := [360581340573945638, 360581344982310050, 360581349912541923, 360581354842446507, 360581358690583940, 360581361393779021, 360581363012765500, 360581364631653200, 360581368047991060, 360581373047879760]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk235A
