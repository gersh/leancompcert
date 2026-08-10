import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk649A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk649B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk649A

def state06 : KState := ⟨⟨362475055876018437, 362475118135976570⟩, ⟨673532527537314862, 676264204342215560⟩, true⟩

def words05 : List Nat := [371285528014683125, 371285528352138960, 371285528642439991, 371285528662106882, 371285528690726141, 371285528720403079, 371285528899256436, 371285528901468077, 371285528764802010, 371285528607102528]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485104884160536, 362485167163895351⟩, ⟨20710688663968583, 23443650264225697⟩, true⟩

def words06 : List Nat := [371285528448356146, 371285528398118495, 371285528276049769, 371285528322769515, 371285528324481718, 371285528324189840, 371285528110221602, 371285527995758309, 371285527999688388, 371285528001978532]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489493859615756, 362489556159515762⟩, ⟨(-264438590763390669), (-261704318934080247)⟩, true⟩

def words07 : List Nat := [371285527998093982, 371285527994812330, 371285528180757348, 371285528318056352, 371285528488555410, 371285528659922939, 371285528786412684, 371285528788625479, 371285528697260244, 371285528761985191]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470798588432339, 362470860908048534⟩, ⟨950469432881090093, 953204985972018649⟩, true⟩

def words08 : List Nat := [371285528923881978, 371285528926094320, 371285528772695991, 371285528620012989, 371285528466468815, 371285528349004918, 371285528112312907, 371285528032973951, 371285527952871690, 371285527856594034]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483972288491515, 362484034628131722⟩, ⟨94257286568673242, 96994141119598768⟩, true⟩

def words09 : List Nat := [371285527632422591, 371285527559723217, 371285527619297800, 371285527621510629, 371285527441411994, 371285527204141519, 371285526965998488, 371285526965253228, 371285526866124168, 371285526845687409]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk649B
