import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk595

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487516452294864, 362487568325335059⟩, ⟨(-150280517389586093), (-148195664301362621)⟩, true⟩

def state01 : KState := ⟨⟨362495347562635166, 362495399453685494⟩, ⟨(-616258590375058147), (-614172665593028381)⟩, true⟩

def words00 : List Nat := [371285077854005406, 371285077907571709, 371285078212742407, 371285078518747539, 371285078781702972, 371285078783715936, 371285078669820784, 371285078672210865, 371285078956450989, 371285079131970299]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502767185592472, 362502819094994834⟩, ⟨(-1057796266872427738), (-1055709249871113242)⟩, true⟩

def words01 : List Nat := [371285079302412332, 371285079473546438, 371285079926742139, 371285080313042775, 371285080782963421, 371285081253620729, 371285081686100099, 371285081742526776, 371285082041899709, 371285082342422278]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475929744585336, 362475981671938094⟩, ⟨539688810025314420, 541776895529114598⟩, true⟩

def words02 : List Nat := [371285082675813801, 371285082677827470, 371285082634837523, 371285082591095741, 371285082587133794, 371285082589373473, 371285082517801208, 371285082547561431, 371285082575204425, 371285082577288827]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502962253098425, 362503014198630130⟩, ⟨(-1069695525820191334), (-1067606358032707506)⟩, true⟩

def words03 : List Nat := [371285082500215541, 371285082577054673, 371285082873327271, 371285082896582420, 371285082898185010, 371285082851806618, 371285082963482868, 371285082984240231, 371285083286769051, 371285083590174903]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484342908251424, 362484394871964102⟩, ⟨38980541439328682, 41070791816019346⟩, true⟩

def words04 : List Nat := [371285083871555376, 371285083920214960, 371285084111361679, 371285084303576479, 371285084579152156, 371285084581170835, 371285084566298532, 371285084532460707, 371285084555504755, 371285084557804842]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478152011004227, 362478203992872317⟩, ⟨407724955720869747, 409816287346424733⟩, true⟩

def words05 : List Nat := [371285084678724745, 371285084812064037, 371285084942433259, 371285084944461423, 371285084823163931, 371285084771386633, 371285084946847021, 371285084948861962, 371285084836262775, 371285084723015810]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501591823547317, 362501643823489336⟩, ⟨(-988470232458929162), (-986377824260410464)⟩, true⟩

def words06 : List Nat := [371285084775811506, 371285084805817424, 371285084913611947, 371285085022179737, 371285085064471330, 371285085066497933, 371285085030504882, 371285085155482191, 371285085523154863, 371285085803240215]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496725627833201, 362496777646108805⟩, ⟨(-698521575200380428), (-696428074775670442)⟩, true⟩

def words07 : List Nat := [371285086083854071, 371285086365106735, 371285086857186010, 371285087209953959, 371285087648603077, 371285088088039910, 371285088476057374, 371285088488765637, 371285088686332181, 371285088885014234]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486294524562706, 362486346560785151⟩, ⟨(-76935121982610122), (-74840552192964674)⟩, true⟩

def words08 : List Nat := [371285089364847566, 371285089524578957, 371285089682331815, 371285089840832153, 371285090026012536, 371285090071898782, 371285090259874125, 371285090448635202, 371285090634009500, 371285090657172308]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505735138813568, 362505787193314006⟩, ⟨(-1235542516297255170), (-1233446857232691466)⟩, true⟩

def words09 : List Nat := [371285090794287959, 371285090932448635, 371285091268483771, 371285091270500004, 371285091269430540, 371285091209443785, 371285091322437550, 371285091425339915, 371285091773952253, 371285092123479059]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk595
