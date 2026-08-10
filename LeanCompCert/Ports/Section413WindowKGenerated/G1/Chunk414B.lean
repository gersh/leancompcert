import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414A

def state06 : KState := ⟨⟨362497506278707938, 362497530741442483⟩, ⟨(-515722676180069910), (-515037358089247224)⟩, true⟩

def words05 : List Nat := [371285105059728928, 371285105083793876, 371285105688763916, 371285106117294270, 371285106720784342, 371285107324784186, 371285107925269326, 371285107926951118, 371285108227515982, 371285108528806772]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485636881526484, 362485661356412685⟩, ⟨(-23628950619041864), (-22943128657424962)⟩, true⟩

def words06 : List Nat := [371285109071242339, 371285109072605355, 371285108840541693, 371285108535887069, 371285108230713508, 371285108101745729, 371285107841417848, 371285108002795372, 371285108108573302, 371285108123342409]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518033105750476, 362518057592966165⟩, ⟨(-1367248633822377288), (-1366562300497611648)⟩, true⟩

def words07 : List Nat := [371285108668426640, 371285109214226904, 371285110251612691, 371285110586621846, 371285110806947062, 371285111027654037, 371285111491967252, 371285111707021260, 371285112502206309, 371285113297975746]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488123646702653, 362488148146239026⟩, ⟨(-126481308212855360), (-125794463761250368)⟩, true⟩

def words08 : List Nat := [371285113975578033, 371285114170032938, 371285114745324586, 371285115321274881, 371285116071958242, 371285116073322262, 371285116050381102, 371285116027774984, 371285116222187906, 371285116296831655]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467408879549430, 362467433391363480⟩, ⟨733214965119225837, 733902319030888281⟩, true⟩

def words09 : List Nat := [371285116951142164, 371285117605975709, 371285118260219816, 371285118261584032, 371285118166300655, 371285118191873981, 371285118586405940, 371285118587770252, 371285118209212029, 371285117784593140]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk414B
