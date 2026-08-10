import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946A

def state06 : KState := ⟨⟨360577415310246653, 360577474441146295⟩, ⟨435149430708734269, 438929058862435377⟩, true⟩

def words05 : List Nat := [360582111414662083, 360582111487738427, 360582111488977298, 360582111491747970, 360582111492903218, 360582111424778162, 360582111372405927, 360582111388598034, 360582111389819692, 360582111342254075]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603573937578900, 360603633081443213⟩, ⟨(-2041184949876467748), (-2037404094423288366)⟩, true⟩

def words06 : List Nat := [360582111294397615, 360582111248140069, 360582111346717924, 360582111445556642, 360582111449787116, 360582111494179554, 360582111628340413, 360582111762930335, 360582111963572284, 360582112192317470]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582484770311031, 360582543927243758⟩, ⟨(-44546349753155518), (-40764257049020136)⟩, true⟩

def words07 : List Nat := [360582112349162495, 360582112506142623, 360582112700753367, 360582112958424825, 360582113136914486, 360582113315602855, 360582113399464253, 360582113400835920, 360582113377955621, 360582113384082522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594250087372904, 360594309257236330⟩, ⟨(-1158554575965651718), (-1154771258918739776)⟩, true⟩

def words08 : List Nat := [360582113473463412, 360582113565683916, 360582113585097250, 360582113604659328, 360582113605808250, 360582113613106935, 360582113762621733, 360582113912405756, 360582113973745324, 360582114103959686]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606629098367192, 360606688281179152⟩, ⟨(-2330797412932196595), (-2327012869725340323)⟩, true⟩

def words09 : List Nat := [360582114276325571, 360582114449096452, 360582114732937656, 360582114929273504, 360582115023658506, 360582115118175064, 360582115305404137, 360582115549575621, 360582115810171843, 360582116071068115]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946B
