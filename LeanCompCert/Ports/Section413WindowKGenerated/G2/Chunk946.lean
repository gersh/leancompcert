import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583853883419247, 360583912936500211⟩, ⟨(-174466827102265135), (-170694562925967721)⟩, true⟩

def state01 : KState := ⟨⟨360593849542372856, 360593908608378898⟩, ⟨(-1120119516636202573), (-1116346029683783561)⟩, true⟩

def words00 : List Nat := [360582108578926092, 360582108640510997, 360582108813386546, 360582108986521497, 360582109045042582, 360582109046413120, 360582109025111891, 360582109058335602, 360582109156271027, 360582109282405346]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581571710413784, 360581630789487275⟩, ⟨41581217697744016, 45355941024596762⟩, true⟩

def words01 : List Nat := [360582109311420411, 360582109340600762, 360582109481160939, 360582109693910093, 360582109861000320, 360582110028310740, 360582110139848985, 360582110141219754, 360582110141337561, 360582110137838835]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594432543768521, 360594491635753682⟩, ⟨(-1175325422050143932), (-1171549476956760824)⟩, true⟩

def words02 : List Nat := [360582110240468620, 360582110410662461, 360582110524590711, 360582110638666279, 360582110722117253, 360582110891707478, 360582111051880877, 360582111212308079, 360582111316497052, 360582111448743540]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590160276125550, 360590219381067844⟩, ⟨(-771034884413072414), (-767257713121608320)⟩, true⟩

def words03 : List Nat := [360582111671560372, 360582111894775276, 360582112059862480, 360582112113905740, 360582112115183082, 360582112074538959, 360582112075375574, 360582112174146487, 360582112260923675, 360582112348036477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578277237711857, 360578336355701156⟩, ⟨353527807577870656, 357306213702500350⟩, true⟩

def words04 : List Nat := [360582112378855000, 360582112380226204, 360582112330180781, 360582112294824736, 360582112259082917, 360582112163747387, 360582112004654186, 360582111759833239, 360582111514754583, 360582111381730766]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946
