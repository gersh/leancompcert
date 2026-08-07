import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884

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

def state06 : KState := ⟨⟨360572591775203241, 360572643142601492⟩, ⟨837041609788624710, 840110118845037484⟩, true⟩

def words05 : List Nat := [360582141775378945, 360582141586001762, 360582141396208265, 360582141315079017, 360582141148541247, 360582140873781760, 360582140598784442, 360582140414174073, 360582140310805093, 360582140204763431]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587066421792809, 360587117801340432⟩, ⟨(-443546141887445882), (-440476558038142220)⟩, true⟩

def words06 : List Nat := [360582140098550911, 360582139928829564, 360582139739319479, 360582139677755181, 360582139615856104, 360582139483559634, 360582139387513516, 360582139208291214, 360582139028825128, 360582139033630809]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581262501608813, 360581313893177946⟩, ⟨69978380265040975, 73049027716646633⟩, true⟩

def words07 : List Nat := [360582139218487115, 360582139403583656, 360582139468583077, 360582139469858913, 360582139460267766, 360582139418178858, 360582139430390114, 360582139499336076, 360582139500484697, 360582139492496625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588760198754328, 360588811602349050⟩, ⟨(-593449005998726659), (-590377294462028397)⟩, true⟩

def words08 : List Nat := [360582139535109843, 360582139651568437, 360582139824000137, 360582139996678838, 360582140042667947, 360582140043943053, 360582139989238341, 360582139931991769, 360582139917285520, 360582139993999478]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589233117945588, 360589284533677859⟩, ⟨(-635297867076638357), (-632225081428686273)⟩, true⟩

def words09 : List Nat := [360582139995140951, 360582139990884164, 360582140108326506, 360582140336682050, 360582140482118404, 360582140627752367, 360582140709704797, 360582140710980027, 360582140745990091, 360582140828166863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884
