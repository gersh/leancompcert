import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967A

def state06 : KState := ⟨⟨360596556259149513, 360596618147742090⟩, ⟨(-1386181412371294035), (-1382137834317724503)⟩, true⟩

def words05 : List Nat := [360582332147277867, 360582332438723722, 360582332676296045, 360582332916472931, 360582333106483948, 360582333296873232, 360582333593666908, 360582333811424114, 360582333960319123, 360582334109396913]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600013725545224, 360600075627408108⟩, ⟨(-1720761484702630509), (-1716716622546083369)⟩, true⟩

def words06 : List Nat := [360582334222020022, 360582334388167162, 360582334660720468, 360582334933541110, 360582335115937714, 360582335191995446, 360582335242952842, 360582335294354597, 360582335452113926, 360582335636888779]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600889510783329, 360600951426008379⟩, ⟨(-1805564921396197005), (-1801518766116384285)⟩, true⟩

def words07 : List Nat := [360582335767759354, 360582335898787213, 360582336042700216, 360582336244671246, 360582336369777405, 360582336495087639, 360582336566925829, 360582336653888252, 360582336847364449, 360582337041303568]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605892161512653, 360605954089985119⟩, ⟨(-2289735416682501082), (-2285687979251458902)⟩, true⟩

def words08 : List Nat := [360582337271002368, 360582337532625098, 360582337740379112, 360582337948284184, 360582338097938149, 360582338311395435, 360582338631195250, 360582338951257663, 360582339169848910, 360582339415281361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629995793652962, 360630057735384015⟩, ⟨(-4622896890189522664), (-4618848169395591044)⟩, true⟩

def words09 : List Nat := [360582339746299640, 360582340077724468, 360582340476912832, 360582340769974317, 360582340970570503, 360582341171282774, 360582341478448927, 360582341866199587, 360582342360267463, 360582342854655556]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk967B
