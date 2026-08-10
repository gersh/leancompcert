import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381A

def state06 : KState := ⟨⟨360577543109998462, 360577552045278494⟩, ⟨165994156421443204, 166224632617449658⟩, true⟩

def words05 : List Nat := [360581902927072903, 360581903324521924, 360581904407227178, 360581905832102371, 360581906864029439, 360581907895984506, 360581908364287344, 360581908364802515, 360581908150260358, 360581908036699287]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582426211200919, 360582435151330878⟩, ⟨(-20514729006497350), (-20284067712390510)⟩, true⟩

def words06 : List Nat := [360581908216900871, 360581908217416087, 360581907829090624, 360581907097130340, 360581906365116069, 360581905223831917, 360581904424209783, 360581904309579511, 360581904194900730, 360581903751375090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604003154387342, 360604012099383715⟩, ⟨(-844453957815030926), (-844223110746571952)⟩, true⟩

def words07 : List Nat := [360581903751800151, 360581903400605733, 360581903152980480, 360581903153495835, 360581902575322435, 360581901414980085, 360581900254599896, 360581899861057609, 360581900440632000, 360581901020293420]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599543386497433, 360599552336399249⟩, ⟨(-674392861258384534), (-674161826876225728)⟩, true⟩

def words08 : List Nat := [360581901022632729, 360581901023149580, 360581901255475721, 360581901714107304, 360581901714546161, 360581901702669659, 360581901237565604, 360581900430267855, 360581899622913741, 360581899962099644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577043393220309, 360577052347985645⟩, ⟨185132680631385384, 185363900775474862⟩, true⟩

def words09 : List Nat := [360581900966675613, 360581901971310459, 360581902548284698, 360581902980266469, 360581903238769422, 360581903497400469, 360581904439672447, 360581904932149208, 360581904932617731, 360581904806121129]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381B
