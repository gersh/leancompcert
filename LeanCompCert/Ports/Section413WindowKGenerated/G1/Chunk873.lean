import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483001848725244, 362483116902306529⟩, ⟨174182766422533366, 180964610631518400⟩, true⟩

def state01 : KState := ⟨⟨362472705843510265, 362472820924140362⟩, ⟨1073097819014210591, 1079882024726193807⟩, true⟩

def words00 : List Nat := [371285189873688337, 371285189876727316, 371285189792185802, 371285189708809968, 371285189624191227, 371285189570331965, 371285189449668500, 371285189397761528, 371285189344857513, 371285189290017423]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489843685413757, 362489958793591516⟩, ⟨(-423315490746471640), (-416528879717144750)⟩, true⟩

def words01 : List Nat := [371285189150455804, 371285189066776256, 371285189025145365, 371285189028184868, 371285188912347660, 371285188776273305, 371285188638991841, 371285188634154255, 371285188647226678, 371285188705299844]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473855010286377, 362473970145863686⟩, ⟨972883242771835118, 979672246470329666⟩, true⟩

def words02 : List Nat := [371285188759892582, 371285188762932206, 371285188651130230, 371285188663320479, 371285188681133842, 371285188684174606, 371285188551661646, 371285188422257555, 371285188291595619, 371285188195176298]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468386750321653, 362468501913280112⟩, ⟨1450504438392405418, 1457295833428975536⟩, true⟩

def words03 : List Nat := [371285188068786480, 371285188037798808, 371285188005756187, 371285187971887708, 371285187811584044, 371285187692971397, 371285187581397276, 371285187584437665, 371285187420734515, 371285187233104122]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483517887330132, 362483633077483326⟩, ⟨128899414589350643, 135693184954029705⟩, true⟩

def words04 : List Nat := [371285187044129448, 371285186974751567, 371285186838625412, 371285186800254256, 371285186760920293, 371285186703335651, 371285186560813930, 371285186506971630, 371285186516631998, 371285186519783888]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk873
