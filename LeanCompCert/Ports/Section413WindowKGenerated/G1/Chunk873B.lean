import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873A

def state06 : KState := ⟨⟨362482183428248087, 362482298646190779⟩, ⟨245459699786836863, 252255897693896219⟩, true⟩

def words05 : List Nat := [371285186504288260, 371285186463829996, 371285186432605131, 371285186435992792, 371285186394971354, 371285186395223100, 371285186394476242, 371285186381864613, 371285186219961454, 371285186190807239]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477552939263951, 362477668184247405⟩, ⟨650049571147431117, 656848131478540825⟩, true⟩

def words06 : List Nat := [371285186253641934, 371285186258690297, 371285186260991021, 371285186246809512, 371285186239908018, 371285186243259596, 371285186188347637, 371285186189188259, 371285186188973662, 371285186189643749]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486735643501324, 362486850915953132⟩, ⟨(-152290258704062953), (-145489298324853489)⟩, true⟩

def words07 : List Nat := [371285186119152461, 371285186136288672, 371285186182630208, 371285186185725079, 371285186132174296, 371285186056232283, 371285185979017236, 371285185960465064, 371285185894263460, 371285185916716172]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480406803201356, 362480522103153484⟩, ⟨400709109758915275, 407512473256550707⟩, true⟩

def words08 : List Nat := [371285185919056439, 371285185919549138, 371285185744558117, 371285185702036777, 371285185657959477, 371285185654898923, 371285185525635692, 371285185397440194, 371285185267981160, 371285185250804893]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466549208289991, 362466664535645547⟩, ⟨1611853404012528312, 1618659162434239188⟩, true⟩

def words09 : List Nat := [371285185267964802, 371285185339764385, 371285185410508672, 371285185413552307, 371285185332577129, 371285185230991263, 371285185127869172, 371285185079713271, 371285184871802762, 371285184663362186]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873B
