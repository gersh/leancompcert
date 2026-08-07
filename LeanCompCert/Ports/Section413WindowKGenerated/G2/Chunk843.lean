import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk843

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599509053822702, 360599555530109205⟩, ⟨(-1445235616812527343), (-1442589689420560541)⟩, true⟩

def state01 : KState := ⟨⟨360588725732564275, 360588772220262366⟩, ⟨(-536212237069101541), (-533565347622957927)⟩, true⟩

def words00 : List Nat := [360582443363004034, 360582443465474338, 360582443466568965, 360582443452721214, 360582443438673039, 360582443347781407, 360582443445974185, 360582443566083731, 360582443606180270, 360582443682495966]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617332069986901, 360617378569111151⟩, ⟨(-2948211549674371089), (-2945563696833849887)⟩, true⟩

def words01 : List Nat := [360582443851925430, 360582444021718622, 360582444331669460, 360582444501372107, 360582444527991274, 360582444554676791, 360582444721650883, 360582444996779901, 360582445412056131, 360582445827601517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615084480662278, 360615130991338131⟩, ⟨(-2758731685815719114), (-2756082858887304398)⟩, true⟩

def words02 : List Nat := [360582446167523295, 360582446556035977, 360582446955996409, 360582447356301786, 360582447719850123, 360582448062197111, 360582448334017218, 360582448605963166, 360582448873747082, 360582449262686896]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574234965967148, 360574281488040608⟩, ⟨686374194204175254, 689023982351018378⟩, true⟩

def words03 : List Nat := [360582449688394471, 360582450114320361, 360582450469744545, 360582450716399800, 360582450903847681, 360582451091635355, 360582451206700090, 360582451207910936, 360582451182685232, 360582451087072515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592005937387745, 360592052470910950⟩, ⟨(-812607856050591724), (-809957102176862910)⟩, true⟩

def words04 : List Nat := [360582450991190978, 360582450890047970, 360582450859015864, 360582450824554633, 360582450789994379, 360582450635767421, 360582450369767448, 360582450244583438, 360582450132915815, 360582450248030642]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360579242931437915, 360579289476489574⟩, ⟨264060908358463272, 266712634714307640⟩, true⟩

def words05 : List Nat := [360582450283427755, 360582450318955354, 360582450454368560, 360582450689377146, 360582450888590806, 360582451087997336, 360582451170257659, 360582451171468770, 360582451113278158, 360582451077185572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583775711870686, 360583822268327162⟩, ⟨(-118428898974659881), (-115776210453285573)⟩, true⟩

def words06 : List Nat := [360582451080421553, 360582451081632712, 360582450982129591, 360582450800445464, 360582450618545518, 360582450379297686, 360582450222305476, 360582450179841491, 360582450137246451, 360582450040779151]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593636259243441, 360593682827140785⟩, ⟨(-950501612528685770), (-947847958686156516)⟩, true⟩

def words07 : List Nat := [360582450041778190, 360582449999846516, 360582450027139174, 360582450028350579, 360582449958781675, 360582449769942802, 360582449580875961, 360582449603858749, 360582449737966733, 360582449872344254]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360576789258899610, 360576835838329932⟩, ⟨471005222880225922, 473659849932014778⟩, true⟩

def words08 : List Nat := [360582449900107229, 360582449901319648, 360582449845874341, 360582449832743671, 360582449819297293, 360582449710737093, 360582449461811925, 360582449123417820, 360582448784796137, 360582448586877533]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360560558056963064, 360560604647819767⟩, ⟨1840898067421268023, 1843553658803139295⟩, true⟩

def words09 : List Nat := [360582448595128506, 360582448670148298, 360582448674634229, 360582448675845908, 360582448540043052, 360582448369127374, 360582448197854098, 360582448108244288, 360582447958200259, 360582447700649189]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk843
