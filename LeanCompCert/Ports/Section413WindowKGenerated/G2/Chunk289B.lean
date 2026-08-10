import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk289B
