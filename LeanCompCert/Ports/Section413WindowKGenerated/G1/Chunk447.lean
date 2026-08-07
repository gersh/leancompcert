import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk447

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467232679696948, 362467261289691889⟩, ⟨815918671772821970, 816782745668155366⟩, true⟩

def state01 : KState := ⟨⟨362464977086302414, 362465005709488966⟩, ⟨916860356402865925, 917725020032047953⟩, true⟩

def words00 : List Nat := [371285533518077255, 371285533519582962, 371285533272574107, 371285533023924629, 371285532774689418, 371285532677253066, 371285532329666317, 371285532213297673, 371285532096468185, 371285531878579372]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502774619526853, 362502803256105263⟩, ⟨(-773246769230125767), (-772381506786237513)⟩, true⟩

def words01 : List Nat := [371285531461497142, 371285531504297254, 371285531967988764, 371285531969468290, 371285531841125504, 371285531563850001, 371285531425293068, 371285531426924355, 371285531753816560, 371285532141711886]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492655475829521, 362492684125779271⟩, ⟨(-320776484350421458), (-319910623871363574)⟩, true⟩

def words02 : List Nat := [371285532527055343, 371285532528535404, 371285532317638466, 371285532316727739, 371285532466184596, 371285532467677747, 371285532294116298, 371285532059224908, 371285532086848441, 371285532248471110]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362453926529053020, 362453955192303691⟩, ⟨1411881003206696156, 1412747458704406036⟩, true⟩

def words03 : List Nat := [371285532791137362, 371285533334367098, 371285533837823016, 371285533839303269, 371285533676778824, 371285533577184159, 371285533476831579, 371285533435657804, 371285532728345242, 371285532024192480]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483182371471760, 362483211047979045⟩, ⟨102898770365865161, 103765819030685889⟩, true⟩

def words04 : List Nat := [371285531319427724, 371285531114633628, 371285530660127795, 371285530637442321, 371285530614254354, 371285530528275312, 371285529967567185, 371285529776638811, 371285529835696694, 371285529837231128]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488431086184810, 362488459776203607⟩, ⟨(-131974825884905041), (-131107172510216199)⟩, true⟩

def words05 : List Nat := [371285529786542165, 371285529635042245, 371285529828845493, 371285529927398840, 371285530176363106, 371285530425869220, 371285530672958856, 371285530674467634, 371285530659689938, 371285530726975257]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472895851433356, 362472924554639377⟩, ⟨563433187702556979, 564301431406105887⟩, true⟩

def words06 : List Nat := [371285531104504764, 371285531105985880, 371285530818560437, 371285530500560321, 371285530182035099, 371285529884529097, 371285529337078587, 371285529227986412, 371285529118379348, 371285529009216239]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362511134674257933, 362511163390846874⟩, ⟨(-1148657880835286788), (-1147789037910809028)⟩, true⟩

def words07 : List Nat := [371285528945777498, 371285529164650212, 371285529881308092, 371285530008365643, 371285530078235723, 371285530148565707, 371285530716808586, 371285531082005649, 371285531655433947, 371285532229463457]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492735956258426, 362492764686215184⟩, ⟨(-324796816054320765), (-323927374449891773)⟩, true⟩

def words08 : List Nat := [371285532657163775, 371285532658645672, 371285532550102030, 371285532680251329, 371285532878387136, 371285532879895157, 371285532672543433, 371285532465836626, 371285532548458305, 371285532711612030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480080138101536, 362480108881439885⟩, ⟨242177626693404596, 243047667725418500⟩, true⟩

def words09 : List Nat := [371285533288546676, 371285533866081089, 371285534361158095, 371285534362640255, 371285534193519636, 371285534057838200, 371285534281975484, 371285534283464791, 371285534171977517, 371285534052594471]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk447
