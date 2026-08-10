import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796A

def state06 : KState := ⟨⟨360567333143037670, 360567374461659468⟩, ⟨1180335244815814541, 1182558225936873307⟩, true⟩

def words05 : List Nat := [360582219576015638, 360582219825410629, 360582219953702144, 360582219954840916, 360582219925824845, 360582219834199871, 360582219806742732, 360582219807881565, 360582219716186821, 360582219531028498]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581031914185796, 360581073243560005⟩, ⟨89026912205013627, 91250749915027133⟩, true⟩

def words06 : List Nat := [360582219345596747, 360582219305376678, 360582219362812436, 360582219420468976, 360582219421519966, 360582219347688220, 360582219163603101, 360582218924276193, 360582218684609276, 360582218602539735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562105755554490, 360562147095776340⟩, ⟨1597011208546425575, 1599235910542286911⟩, true⟩

def words07 : List Nat := [360582218589178663, 360582218497091386, 360582218404792914, 360582218391416273, 360582218405280330, 360582218419328641, 360582218420359088, 360582218327946239, 360582218078180609, 360582217827585355]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559844428360775, 360559885779325333⟩, ⟨1777114360759201163, 1779339918788693519⟩, true⟩

def words08 : List Nat := [360582217576633961, 360582217321886234, 360582216909888765, 360582216419219358, 360582215928368892, 360582215398582942, 360582214966715003, 360582214692348338, 360582214417844745, 360582214050360453]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592439231508863, 360592480593222310⟩, ⟨(-820566659131550707), (-818340244471470259)⟩, true⟩

def words09 : List Nat := [360582213771096065, 360582213649417721, 360582213561717693, 360582213562857080, 360582213441156305, 360582213152902207, 360582212864434107, 360582212733536139, 360582212834896252, 360582212964905583]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796B
