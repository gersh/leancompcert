import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793A

def state06 : KState := ⟨⟨362471551867777072, 362471646249287218⟩, ⟨1070460694279555506, 1075518524901890216⟩, true⟩

def words05 : List Nat := [371285199095126859, 371285199126589830, 371285199158076841, 371285199160836485, 371285199049704932, 371285198966038116, 371285198952696536, 371285198955437750, 371285198817704562, 371285198650054631]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487047710995793, 362487142117027413⟩, ⟨(-159346112914116176), (-154286336138829930)⟩, true⟩

def words06 : List Nat := [371285198481144969, 371285198448327094, 371285198338057921, 371285198343689311, 371285198345836470, 371285198304526130, 371285198130430321, 371285198116392227, 371285198226874746, 371285198254204231]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485941579078415, 362486036010141168⟩, ⟨(-71578800637149913), (-66517037022608241)⟩, true⟩

def words07 : List Nat := [371285198280291690, 371285198307260639, 371285198319886475, 371285198322908009, 371285198256200016, 371285198232929410, 371285198208675150, 371285198185135020, 371285198049549157, 371285198063566766]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476726457085086, 362476820912527597⟩, ⟨659999096648610187, 665062795656895269⟩, true⟩

def words08 : List Nat := [371285198217988020, 371285198220736044, 371285198210618070, 371285198191585759, 371285198198159614, 371285198201181929, 371285198155035388, 371285198128271983, 371285198100626757, 371285198073324384]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506027306692088, 362506121786961786⟩, ⟨(-1666362228626192458), (-1661296558462953552)⟩, true⟩

def words09 : List Nat := [371285197969677057, 371285197955202112, 371285198079971699, 371285198111191427, 371285198114409345, 371285198118460388, 371285198279902294, 371285198388012677, 371285198653391775, 371285198920014734]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793B
