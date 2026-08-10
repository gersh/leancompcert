import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587012073817911, 360587063368875359⟩, ⟨(-437217279151142483), (-434155167186805387)⟩, true⟩

def state01 : KState := ⟨⟨360563331629871011, 360563382937067994⟩, ⟨1656126023453622799, 1659189208612413349⟩, true⟩

def words00 : List Nat := [360582152168019510, 360582152151830324, 360582152007585709, 360582151836848387, 360582151665776650, 360582151462775940, 360582151131838164, 360582150693935674, 360582150255798461, 360582149922800518]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360541126326779334, 360541177645967911⟩, ⟨3619463763507215962, 3622528008904788700⟩, true⟩

def words01 : List Nat := [360582149711560414, 360582149628296584, 360582149544898323, 360582149380473206, 360582149088040389, 360582148763844716, 360582148439289772, 360582148060715256, 360582147662506019, 360582147200468079]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574654157846048, 360574705489058325⟩, ⟨654769201521746514, 657834510114045640⟩, true⟩

def words02 : List Nat := [360582146738152414, 360582146345938379, 360582146017614458, 360582145817254138, 360582145616790698, 360582145303974217, 360582145009951797, 360582144843991460, 360582144677667540, 360582144531352955]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573747933106313, 360573799276472698⟩, ⟨734901813724065588, 737968197163572242⟩, true⟩

def words03 : List Nat := [360582144448385374, 360582144267328592, 360582144086031661, 360582144023741941, 360582144024809786, 360582143970566904, 360582143916186758, 360582143781744181, 360582143650195739, 360582143557309012]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570636654176151, 360570688009523106⟩, ⟨1010029508625417866, 1013096951687019088⟩, true⟩

def words04 : List Nat := [360582143463990744, 360582143457645924, 360582143323450337, 360582143117355364, 360582142911078349, 360582142607709947, 360582142368185209, 360582142234752665, 360582142101184142, 360582141903832739]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884A
