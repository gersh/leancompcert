import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855A

def state06 : KState := ⟨⟨360580435343722031, 360580483274835400⟩, ⟨158255661977107475, 161025150198404919⟩, true⟩

def words05 : List Nat := [360582365792033515, 360582365680776679, 360582365569291519, 360582365543308349, 360582365544337367, 360582365534499435, 360582365524529879, 360582365427553456, 360582365309804450, 360582365289213596]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566380136344250, 360566428079050756⟩, ⟨1360819795848904947, 1363590276037085985⟩, true⟩

def words06 : List Nat := [360582365268231443, 360582365189497975, 360582365004599458, 360582364750272412, 360582364495750741, 360582364192491995, 360582363973578669, 360582363836020108, 360582363698316554, 360582363456823774]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582703249356162, 360582751203671532⟩, ⟨(-36021223999353248), (-33249750383244278)⟩, true⟩

def words07 : List Nat := [360582363271593779, 360582363223194298, 360582363230902164, 360582363232132031, 360582363153177414, 360582362941763698, 360582362730116510, 360582362674410294, 360582362679949998, 360582362685771727]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566648871694636, 360566696837733811⟩, ⟨1337944716379550311, 1340717193377277715⟩, true⟩

def words08 : List Nat := [360582362686878293, 360582362601950099, 360582362520520248, 360582362476618824, 360582362432392167, 360582362353967623, 360582362138855314, 360582361844355864, 360582361549644857, 360582361251723498]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360534723033280227, 360534771010903480⟩, ⟨4070630504706987084, 4073403973243799156⟩, true⟩

def words09 : List Nat := [360582361069710555, 360582360868465932, 360582360667085976, 360582360389225990, 360582359974640530, 360582359453599812, 360582358932186336, 360582358547396049, 360582358060566339, 360582357505918011]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk855B
