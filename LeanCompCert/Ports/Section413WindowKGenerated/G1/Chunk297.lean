import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk297

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506182272249749, 362506194484516598⟩, ⟨(-610992549655544397), (-610747378396268137)⟩, true⟩

def state01 : KState := ⟨⟨362471613499427119, 362471625720165190⟩, ⟨415864136128087661, 416109559027684727⟩, true⟩

def words00 : List Nat := [371285632459359143, 371285632460310380, 371285632119064760, 371285631783706707, 371285631448002633, 371285631328163894, 371285630905909130, 371285631173972869, 371285631426317207, 371285631427301767]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 29700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 29700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515672335983328, 362515684565334284⟩, ⟨(-893437001443971561), (-893191322612406371)⟩, true⟩

def words01 : List Nat := [371285630956554844, 371285630854136901, 371285631589125989, 371285631590077724, 371285631097151215, 371285630362426818, 371285630021678217, 371285630022741427, 371285631020427898, 371285632032693646]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 29710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 29700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495217873838224, 362495230111783838⟩, ⟨(-285375836442999026), (-285129902133131672)⟩, true⟩

def words02 : List Nat := [371285633049969121, 371285633452918282, 371285634984924742, 371285636517309413, 371285638116023528, 371285638380771213, 371285638622050700, 371285638863640064, 371285639464814394, 371285639788480447]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 29720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 29700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452019973894911, 362452032220409879⟩, ⟨999227793261255745, 999473982381526113⟩, true⟩

def words03 : List Nat := [371285640853956943, 371285641919736233, 371285642683064983, 371285642684017502, 371285641942100688, 371285641456096195, 371285641441355391, 371285641442308014, 371285640410021124, 371285639281014504]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 29730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 29700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484438670705766, 362484450925762638⟩, ⟨34966636866874055, 35213080065743037⟩, true⟩

def words04 : List Nat := [371285638151670732, 371285638150828345, 371285637581800627, 371285637458396157, 371285637334687119, 371285637060975015, 371285635434927796, 371285634824309542, 371285634557699088, 371285634558706025]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 29740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 29700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491553959415982, 362491566223163812⟩, ⟨(-176690826945448445), (-176444125147987483)⟩, true⟩

def words05 : List Nat := [371285634519634786, 371285634418178549, 371285635341032869, 371285636029864890, 371285636750140453, 371285637470718809, 371285638046680721, 371285638047634008, 371285637319914676, 371285637520326274]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 29750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 29700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491981433611532, 362491993705849627⟩, ⟨(-189342290729758026), (-189095336217589124)⟩, true⟩

def words06 : List Nat := [371285638846867743, 371285638966104103, 371285639069766642, 371285639173745225, 371285639621761628, 371285639706274384, 371285640412029421, 371285641118130278, 371285641829271563, 371285642043620694]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 29760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 29700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362513240180953097, 362513252461809627⟩, ⟨(-822369755090650476), (-822122543962677836)⟩, true⟩

def words07 : List Nat := [371285642730227891, 371285643417270250, 371285644929332172, 371285644940491139, 371285644941230470, 371285644764873135, 371285644989808650, 371285645000347758, 371285645928042773, 371285646856089112]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 29770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 29700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464827127930111, 362464839417396488⟩, ⟨619458431560312282, 619705899133598516⟩, true⟩

def words08 : List Nat := [371285647798758562, 371285647799712505, 371285647242045701, 371285647163653039, 371285647084797252, 371285646862566838, 371285645335568094, 371285643815028473, 371285642294205996, 371285641898065626]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 29780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 29700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362431095029721174, 362431107327803278⟩, ⟨1624681201822984218, 1624928926101249992⟩, true⟩

def words09 : List Nat := [371285641452414035, 371285641705446239, 371285641964217817, 371285641965172099, 371285640724902623, 371285639608136168, 371285638490957111, 371285638370003525, 371285636972888178, 371285635144115401]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 29790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 29700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 29700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk297
