import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640A

def state06 : KState := ⟨⟨360576987981161760, 360577014243544819⟩, ⟨372364947071878741, 373501418990396473⟩, true⟩

def words05 : List Nat := [360582841882053033, 360582842747494591, 360582843428090793, 360582843866198780, 360582844170006097, 360582844474044273, 360582844771420971, 360582844826410971, 360582844827213761, 360582844737128809]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615434919206467, 360615461190094224⟩, ⟨(-2090768268491016188), (-2089631251719204548)⟩, true⟩

def words06 : List Nat := [360582844646843505, 360582844739523223, 360582845091010985, 360582845442686491, 360582845588390050, 360582845589291216, 360582845769018770, 360582845981241036, 360582846373307863, 360582846883282731]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614472111328272, 360614498390819863⟩, ⟨(-2029147294990623255), (-2028009726930771549)⟩, true⟩

def words07 : List Nat := [360582847209394728, 360582847535572429, 360582847944357412, 360582848501147191, 360582848893349732, 360582849285681182, 360582849504702395, 360582849803293370, 360582850297913939, 360582850792827779]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620078905156689, 360620105193134501⟩, ⟨(-2388518874214066965), (-2387380762314541251)⟩, true⟩

def words08 : List Nat := [360582851530759291, 360582852053888698, 360582852423226351, 360582852792650979, 360582852995158842, 360582853385312360, 360582853880987177, 360582854376817596, 360582854751215112, 360582855333367693]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360633212937526583, 360633239234021260⟩, ⟨(-3230296816881057950), (-3229158159093203600)⟩, true⟩

def words09 : List Nat := [360582856158567504, 360582856984023578, 360582857997675958, 360582858835839092, 360582859468358009, 360582860100927494, 360582860770731254, 360582861564065035, 360582862350729785, 360582863137562653]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk640B
