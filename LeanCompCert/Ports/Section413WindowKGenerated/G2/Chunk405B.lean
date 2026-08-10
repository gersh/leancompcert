import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405A

def state06 : KState := ⟨⟨360589100624635880, 360589110769384214⟩, ⟨(-266961083089720524), (-266682986394886434)⟩, true⟩

def words05 : List Nat := [360582537688409621, 360582537074505598, 360582536460526370, 360582536472570054, 360582536478248691, 360582536484016763, 360582536484510118, 360582536026274665, 360582535744434793, 360582535907166940]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590934762728375, 360590944912652786⟩, ⟨(-341378676949022907), (-341100370285749655)⟩, true⟩

def words06 : List Nat := [360582536476797144, 360582536849405646, 360582536916259382, 360582536983165331, 360582536983634873, 360582536560214063, 360582536799007876, 360582537157861881, 360582537212544533, 360582537420348289]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581406788668307, 360581416943796027⟩, ⟨45255840054429714, 45534357841156958⟩, true⟩

def words07 : List Nat := [360582537945306440, 360582538470416619, 360582539172304937, 360582539269603041, 360582539270111059, 360582538838649467, 360582538580951122, 360582539059081274, 360582539059538711, 360582539032456480]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605977585032998, 360605987745407794⟩, ⟨(-952175266060130422), (-951896535322604278)⟩, true⟩

def words08 : List Nat := [360582539005301375, 360582538651597563, 360582537861179629, 360582537676608654, 360582537491899894, 360582537153270158, 360582537103186147, 360582536699123724, 360582536294976052, 360582536819455672]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565721218459618, 360565731384025020⟩, ⟨682131177798780123, 682410119248828061⟩, true⟩

def words09 : List Nat := [360582538003028541, 360582539186648762, 360582539900557192, 360582540010414543, 360582540010876143, 360582539786402901, 360582539942017689, 360582539942568575, 360582539928463621, 360582539515041001]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk405B
