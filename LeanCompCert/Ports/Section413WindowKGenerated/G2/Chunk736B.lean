import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736A

def state06 : KState := ⟨⟨360568243721637624, 360568278833343709⟩, ⟨1039146386361486781, 1040893285238330877⟩, true⟩

def words05 : List Nat := [360582410790711302, 360582410762860702, 360582410734896879, 360582410615183074, 360582410500785760, 360582410340086339, 360582410179063667, 360582410154869053, 360582410076033857, 360582409885274721]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559967269326555, 360560002390929316⟩, ⟨1648803614429164700, 1650551242344606198⟩, true⟩

def words06 : List Nat := [360582409694299693, 360582409424073451, 360582409246359868, 360582409150086061, 360582409053742677, 360582408802890758, 360582408367846440, 360582407900190996, 360582407432222205, 360582407050116837]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571389127136479, 360571424258710706⟩, ⟨807246948717132942, 808995311280261314⟩, true⟩

def words07 : List Nat := [360582406746936932, 360582406327651913, 360582405908177824, 360582405672980398, 360582405529182174, 360582405255162039, 360582404981035669, 360582404588150875, 360582404256040228, 360582404108212339]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584504695763123, 360584539837216868⟩, ⟨(-159106465555300263), (-157357375019747397)⟩, true⟩

def words08 : List Nat := [360582403994946905, 360582404094739297, 360582404102480342, 360582404110330740, 360582404111207645, 360582404125649938, 360582404291004454, 360582404456554608, 360582404457511704, 360582404469600474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606166801035892, 360606201952380891⟩, ⟨(-1755532136699712771), (-1753782317229716579)⟩, true⟩

def words09 : List Nat := [360582404623700345, 360582404778115775, 360582405116059277, 360582405270309797, 360582405271278824, 360582405248163023, 360582405255080814, 360582405395300838, 360582405719032086, 360582406043000697]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk736B
