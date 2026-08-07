import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530724105491967, 360530729112750158⟩, ⟨1506595964135887982, 1506693834906385338⟩, true⟩

def state01 : KState := ⟨⟨360615592516411257, 360615597527276891⟩, ⟨(-946640937128536360), (-946542962085271246)⟩, true⟩

def words00 : List Nat := [360582862043923292, 360582861435204207, 360582861426323360, 360582861386977342, 360582861347604554, 360582860198568441, 360582858310752591, 360582857310766946, 360582856504319047, 360582857637197501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581323493365746, 360581328507868473⟩, ⟨44308292741050237, 44406372950490097⟩, true⟩

def words01 : List Nat := [360582857987198446, 360582858337218123, 360582859311686489, 360582861032025412, 360582862447415992, 360582863862770901, 360582864208004098, 360582864208387001, 360582864050603776, 360582863997942833]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598722724971843, 360598727743071872⟩, ⟨(-459104764124036825), (-459006579862303873)⟩, true⟩

def words02 : List Nat := [360582865084934597, 360582865085316717, 360582865037680616, 360582864307283894, 360582863576870836, 360582862111994856, 360582861574142576, 360582861901707184, 360582861902047745, 360582862180876915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360679211407075672, 360679216428787613⟩, ⟨(-2788170363378958897), (-2788072074606910133)⟩, true⟩

def words03 : List Nat := [360582862699647304, 360582863218488192, 360582864929147249, 360582867021518341, 360582868103938745, 360582869186310988, 360582870779479936, 360582873359054385, 360582876688426327, 360582880017654380]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360664117843121991, 360664122868471805⟩, ⟨(-2351625472434653346), (-2351527078364362512)⟩, true⟩

def words04 : List Nat := [360582882436107525, 360582884241194068, 360582886924831898, 360582889608400337, 360582891460545146, 360582892665098826, 360582893273431641, 360582893881764172, 360582895680527266, 360582898486641666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564518571395925, 360564523600354061⟩, ⟨532357469776421127, 532455968325471237⟩, true⟩

def words05 : List Nat := [360582901001252537, 360582903515769753, 360582905422399027, 360582906629986999, 360582907533840963, 360582908437734446, 360582909883678243, 360582910145014303, 360582910145361161, 360582909510862538]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360649043986306388, 360649049018875493⟩, ⟨(-1915906531300160504), (-1915807928159139370)⟩, true⟩

def words06 : List Nat := [360582909431080404, 360582910583383875, 360582911905285515, 360582913227168722, 360582913529136209, 360582913870386972, 360582915075049326, 360582916279741475, 360582918265004868, 360582920548054357]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608422220110377, 360608427256334502⟩, ⟨(-738959604519802501), (-738860895475550557)⟩, true⟩

def words07 : List Nat := [360582921949566261, 360582923351019271, 360582924723175323, 360582927008732209, 360582928636092834, 360582930263402425, 360582931138550128, 360582931138932998, 360582931710838764, 360582932591020140]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571208406677642, 360571213446505422⟩, ⟨339661243977257122, 339760057473809868⟩, true⟩

def words08 : List Nat := [360582934315494133, 360582935352261096, 360582935794090375, 360582936235930959, 360582936236254774, 360582935588083264, 360582935536709534, 360582935009997903, 360582934483283991, 360582933351902932]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668020180586048, 360668025224029065⟩, ⟨(-2467439879389801491), (-2467340961069747781)⟩, true⟩

def words09 : List Nat := [360582933322056146, 360582933696555534, 360582934917262094, 360582936582495588, 360582937230561694, 360582937878615629, 360582939414773795, 360582941566606877, 360582944500836227, 360582947434950422]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289
