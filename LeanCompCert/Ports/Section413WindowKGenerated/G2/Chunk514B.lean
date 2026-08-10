import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514A

def state06 : KState := ⟨⟨360571948367675216, 360571965019474722⟩, ⟨510533263416440439, 511112262964551451⟩, true⟩

def words05 : List Nat := [360581895580617497, 360581896202466217, 360581896634673312, 360581896960792050, 360581897097616316, 360581897234623669, 360581897361965523, 360581897435423417, 360581897436059169, 360581897243784177]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584662132581336, 360584678791096739⟩, ⟨(-143660298490973296), (-143080953309156202)⟩, true⟩

def words06 : List Nat := [360581897235072693, 360581897614740104, 360581898251709698, 360581898888803056, 360581899203562311, 360581899204274284, 360581899142268635, 360581899042606783, 360581898942743985, 360581898954813995]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600395143713904, 360600411809030147⟩, ⟨(-953590441803431104), (-953010746550674444)⟩, true⟩

def words07 : List Nat := [360581898955466880, 360581898695775531, 360581898552105542, 360581898914236076, 360581899076357771, 360581899238589974, 360581899239224325, 360581899212593207, 360581899555937328, 360581899916360023]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605277533602987, 360605294205612450⟩, ⟨(-1205019455788460604), (-1204439415934016728)⟩, true⟩

def words08 : List Nat := [360581900652947766, 360581901013202380, 360581901168549333, 360581901323968143, 360581901324574436, 360581901300390140, 360581901760206961, 360581902220142340, 360581902489668169, 360581902944694348]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579690335540157, 360579707014283315⟩, ⟨112507843566009794, 113088230171913138⟩, true⟩

def words09 : List Nat := [360581903334981694, 360581903725471963, 360581904035165512, 360581904035877841, 360581903969340068, 360581903579245078, 360581903189029351, 360581902973269092, 360581902944148984, 360581902902247819]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514B
