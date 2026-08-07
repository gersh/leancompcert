import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360564100170055637, 360564143717602424⟩, ⟨1478593311332335137, 1480996132247184343⟩, true⟩

def state01 : KState := ⟨⟨360599052516286841, 360599096074879764⟩, ⟨(-1377153254284002154), (-1374749530845611240)⟩, true⟩

def words00 : List Nat := [360582270744316119, 360582270709797158, 360582270896780766, 360582271084004428, 360582271141385510, 360582271142555840, 360582271106879021, 360582271164717748, 360582271333356818, 360582271540473802]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586965010707496, 360587008580474911⟩, ⟨(-389405816927072759), (-387001180366650121)⟩, true⟩

def words01 : List Nat := [360582271631867011, 360582271723357549, 360582271902425288, 360582272156873488, 360582272345070281, 360582272533454131, 360582272646669246, 360582272822954001, 360582272881863726, 360582272941161067]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596108392522867, 360596151973301202⟩, ⟨(-1136692123119985583), (-1134286586691217859)⟩, true⟩

def words02 : List Nat := [360582273107876564, 360582273196822898, 360582273210629658, 360582273224563797, 360582273225561726, 360582273138690002, 360582273288030730, 360582273438204073, 360582273511458474, 360582273682485096]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600795726675385, 360600839318515992⟩, ⟨(-1519847964205320059), (-1517441523603242473)⟩, true⟩

def words03 : List Nat := [360582273897753659, 360582274113379023, 360582274378759856, 360582274494994677, 360582274496074372, 360582274484674636, 360582274610058814, 360582274842544737, 360582275070623850, 360582275298946826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606484040457454, 360606527643443903⟩, ⟨(-1984964276892110778), (-1982556925173264986)⟩, true⟩

def words04 : List Nat := [360582275414622313, 360582275460510325, 360582275602031115, 360582275743898040, 360582275847937905, 360582275955875424, 360582275981151387, 360582276006543983, 360582276181248186, 360582276479235842]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570243732211031, 360570287346245019⟩, ⟨977923086466529365, 980331341377023713⟩, true⟩

def words05 : List Nat := [360582276858730828, 360582277238448009, 360582277479244730, 360582277633587747, 360582277734962629, 360582277836658703, 360582277915153734, 360582277916324867, 360582277845645939, 360582277700224680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589475781565357, 360589519406647389⟩, ⟨(-594605709398395934), (-592196551144959260)⟩, true⟩

def words06 : List Nat := [360582277557366610, 360582277636439904, 360582277737733659, 360582277839242925, 360582277840334898, 360582277801003863, 360582277612231178, 360582277419778061, 360582277226985814, 360582277272502705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598106880615327, 360598150516850035⟩, ⟨(-1300407168510538669), (-1297997098250734157)⟩, true⟩

def words07 : List Nat := [360582277273546329, 360582277273398421, 360582277421160622, 360582277717373286, 360582277973985507, 360582278230783936, 360582278412534919, 360582278504657253, 360582278699686224, 360582278895101087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580305754837844, 360580349402116622⟩, ⟨155408763793959784, 157819737292509278⟩, true⟩

def words08 : List Nat := [360582279086577950, 360582279167671619, 360582279168731036, 360582279152419641, 360582279135924221, 360582279022132495, 360582279014780994, 360582279034079712, 360582279035123451, 360582278974647403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603881693134781, 360603925351470571⟩, ⟨(-1773027916428929691), (-1770616038523206895)⟩, true⟩

def words09 : List Nat := [360582279041649550, 360582279132597190, 360582279345389656, 360582279409281742, 360582279410383963, 360582279332753612, 360582279295284091, 360582279411845999, 360582279677413554, 360582279943241782]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817
