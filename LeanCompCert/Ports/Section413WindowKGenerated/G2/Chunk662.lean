import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk662

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613922716996955, 360613950837211076⟩, ⟨(-2053455481664491609), (-2052197997629606835)⟩, true⟩

def state01 : KState := ⟨⟨360603353515285931, 360603381644384467⟩, ⟨(-1353786844206540413), (-1352528771978594665)⟩, true⟩

def words00 : List Nat := [360582951690706726, 360582951884085346, 360582952262771472, 360582952641730551, 360582952963252684, 360582953291309811, 360582953478841801, 360582953666469179, 360582953780882345, 360582954090473809]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562489471427601, 360562517609330138⟩, ⟨1352083587958888593, 1353342243143103093⟩, true⟩

def words01 : List Nat := [360582954568045109, 360582955045780682, 360582955349167556, 360582955425001882, 360582955425787444, 360582955305537471, 360582955185017452, 360582955172717846, 360582954978930493, 360582954671292432]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587829231908651, 360587857378614312⟩, ⟨(-326001604715766943), (-324742366544631467)⟩, true⟩

def words02 : List Nat := [360582954363428393, 360582954345128664, 360582954559485796, 360582954774015026, 360582954794578818, 360582954795512642, 360582954588441322, 360582954376577510, 360582954164446223, 360582954200849450]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583613300488131, 360583641456099245⟩, ⟨(-46773052526034758), (-45513224503976496)⟩, true⟩

def words03 : List Nat := [360582954201695745, 360582954091853052, 360582954051787728, 360582954302863094, 360582954427923756, 360582954553130118, 360582954564308440, 360582954565242473, 360582954359242013, 360582954370691356]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581226074592000, 360581254239011424⟩, ⟨111329539403394138, 112589950932005246⟩, true⟩

def words04 : List Nat := [360582954376828552, 360582954377768902, 360582954349512980, 360582954186179041, 360582954022697722, 360582953802446587, 360582953766468565, 360582953817992115, 360582953818834472, 360582953709968889]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360593291126376791, 360593319299607267⟩, ⟨(-688108082974213404), (-686847087669658974)⟩, true⟩

def words05 : List Nat := [360582953827186523, 360582953970325916, 360582954056896608, 360582954057830894, 360582953973091574, 360582953674100976, 360582953374940222, 360582953230902617, 360582953360099963, 360582953517508149]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575759660831860, 360575787842973652⟩, ⟨473537263384644929, 474798849197156973⟩, true⟩

def words06 : List Nat := [360582953531935189, 360582953552704758, 360582953574581519, 360582953596737225, 360582953597520054, 360582953515014889, 360582953358135876, 360582953058783158, 360582952759273761, 360582952455154083]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564240316827435, 360564268507770608⟩, ⟨1237055353821014074, 1238317522945275334⟩, true⟩

def words07 : List Nat := [360582952466952803, 360582952587039725, 360582952593256921, 360582952594195969, 360582952534622120, 360582952323656575, 360582952112395649, 360582952081000550, 360582951913658179, 360582951632739608]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594504340127823, 360594532539905798⟩, ⟨(-769055209161872103), (-767792454423279645)⟩, true⟩

def words08 : List Nat := [360582951351617891, 360582951241234099, 360582951242005134, 360582951142278127, 360582951042490204, 360582950749743886, 360582950519711710, 360582950357275929, 360582950211957677, 360582950387661553]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588080928552659, 360588109137234412⟩, ⟨(-343185088505170853), (-341921743493861491)⟩, true⟩

def words09 : List Nat := [360582950424978215, 360582950462393921, 360582950726720515, 360582951137925063, 360582951491996195, 360582951846209129, 360582951970033924, 360582951970968851, 360582951945457711, 360582952024317656]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk662
