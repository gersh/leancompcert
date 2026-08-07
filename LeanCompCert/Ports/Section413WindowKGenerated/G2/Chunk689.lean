import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603515385596237, 360603545943311213⟩, ⟨(-1432727229132437709), (-1431305068451590773)⟩, true⟩

def state01 : KState := ⟨⟨360599033437609754, 360599064004618213⟩, ⟨(-1124041649841666617), (-1122618848794658279)⟩, true⟩

def words00 : List Nat := [360582772702202824, 360582772703177696, 360582772865276686, 360582773052124967, 360582773185804749, 360582773186779399, 360582773163041684, 360582773010987740, 360582772915873548, 360582773153392797]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575116290271048, 360575146866453954⟩, ⟨524233621807929304, 525657055112248422⟩, true⟩

def words01 : List Nat := [360582773558209286, 360582773963200930, 360582774220771086, 360582774268146179, 360582774268981893, 360582774123364090, 360582774040906889, 360582774041884354, 360582774037271392, 360582773927613447]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615632524838406, 360615663110236725⟩, ⟨(-2268301081252020921), (-2266877012776255221)⟩, true⟩

def words02 : List Nat := [360582773836260724, 360582774023067275, 360582774377400236, 360582774731909525, 360582774905757517, 360582775151453907, 360582775607005520, 360582776062829889, 360582776455915583, 360582776934020273]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590066500957981, 360590097095650975⟩, ⟨(-505879565487789544), (-504454856284391592)⟩, true⟩

def words03 : List Nat := [360582777255438770, 360582777576945602, 360582778012362321, 360582778553946713, 360582778969178498, 360582779384571948, 360582779639699847, 360582779684776399, 360582779791710319, 360582779898971432]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592765918286011, 360592796522169673⟩, ⟨(-692068462076926845), (-690643119222801653)⟩, true⟩

def words04 : List Nat := [360582780156173575, 360582780203422619, 360582780204307015, 360582780072849964, 360582779941237061, 360582779757108658, 360582779809119990, 360582779940678499, 360582779942182485, 360582780088481652]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598247048808501, 360598277661896664⟩, ⟨(-1070017489168591512), (-1068591511618287050)⟩, true⟩

def words05 : List Nat := [360582780307967080, 360582780527738502, 360582780892888330, 360582781161610792, 360582781250972828, 360582781340408052, 360582781425543022, 360582781618798773, 360582781844303297, 360582782070016931]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588445659935822, 360588476282314369⟩, ⟨(-394132820212845461), (-392706201953717719)⟩, true⟩

def words06 : List Nat := [360582782180043099, 360582782243567694, 360582782516738589, 360582782790206301, 360582782948301907, 360582782949277335, 360582782897448084, 360582782711860780, 360582782526093818, 360582782495042129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560777733596752, 360560808365168561⟩, ⟨1514212750389211465, 1515640002754332463⟩, true⟩

def words07 : List Nat := [360582782521237275, 360582782547604844, 360582782548474213, 360582782460760308, 360582782162950807, 360582781762827844, 360582781362421530, 360582781061237414, 360582780848577899, 360582780531053663]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584535651728620, 360584566292502546⟩, ⟨(-124737215420780787), (-123309328247476605)⟩, true⟩

def words08 : List Nat := [360582780213323000, 360582779928466575, 360582779749042144, 360582779728808507, 360582779708524890, 360582779491933734, 360582779206203847, 360582779087244730, 360582778968004655, 360582778967659488]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569233788524218, 360569264438604422⟩, ⟨931066888273182597, 932495417532300869⟩, true⟩

def words09 : List Nat := [360582778968534048, 360582778837712074, 360582778784499628, 360582778968513786, 360582779099580083, 360582779230801910, 360582779249686486, 360582779250662401, 360582779059693594, 360582778864945470]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk689
