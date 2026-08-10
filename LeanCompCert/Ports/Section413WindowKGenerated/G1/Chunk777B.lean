import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777A

def state06 : KState := ⟨⟨362485647190777917, 362485737663256358⟩, ⟨(-45154562981655164), (-40403837678572182)⟩, true⟩

def words05 : List Nat := [371285217670335483, 371285217686219502, 371285217810459217, 371285217853135405, 371285217945347020, 371285218038609724, 371285218130938260, 371285218133627994, 371285218063179015, 371285218073260363]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484085090813063, 362484175587207434⟩, ⟨76323018282418539, 81075603413114195⟩, true⟩

def words06 : List Nat := [371285218247062064, 371285218249745118, 371285218224536188, 371285218164120821, 371285218102704023, 371285218076817198, 371285218020652633, 371285218055816414, 371285218089228035, 371285218092073233]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494425557262633, 362494516077854719⟩, ⟨(-727869896190165451), (-723115429077768935)⟩, true⟩

def words07 : List Nat := [371285218215360615, 371285218353411027, 371285218655347799, 371285218766823076, 371285218828625763, 371285218891289088, 371285218988508306, 371285219020757910, 371285219142118149, 371285219264634553]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487297035009476, 362487387579792449⟩, ⟨(-173432469830708487), (-168676121026725751)⟩, true⟩

def words08 : List Nat := [371285219354077225, 371285219356760637, 371285219258152372, 371285219293842479, 371285219364195245, 371285219366888747, 371285219308155063, 371285219232041997, 371285219224487372, 371285219255422963]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483030962981597, 362483121531998609⟩, ⟨158456703688648235, 163214937779123977⟩, true⟩

def words09 : List Nat := [371285219353728102, 371285219453171467, 371285219551617214, 371285219554301318, 371285219450828518, 371285219399209364, 371285219456526405, 371285219459257201, 371285219434297854, 371285219410376233]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk777B
