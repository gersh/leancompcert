import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk116

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362599674731549986, 362599676448406729⟩, ⟨(-1318357302563930041), (-1318343823289017373)⟩, true⟩

def state01 : KState := ⟨⟨362493664706012963, 362493666425967210⟩, ⟨(-88288804036297458), (-88275288814245698)⟩, true⟩

def words00 : List Nat := [371286045658819445, 371286045659162614, 371286051008702802, 371286056482191584, 371286062134302968, 371286062134652150, 371286061636226015, 371286061130693994, 371286063041522833, 371286063696760919]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362413943706686224, 362413945429735462⟩, ⟨837867927039398083, 837881478210007519⟩, true⟩

def words01 : List Nat := [371286069097285308, 371286074497014434, 371286078676729822, 371286078677073330, 371286073009864836, 371286067760103532, 371286064639437410, 371286064639781205, 371286058475065847, 371286052269512572]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362427628369108374, 362427630095234733⟩, ⟨679296026630540501, 679309613572846285⟩, true⟩

def words02 : List Nat := [371286047234832217, 371286047235212237, 371286050050816985, 371286054458120491, 371286058100024952, 371286058100368890, 371286051914209000, 371286046235951469, 371286040558492491, 371286040208181668]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510309105270595, 362510310834535210⟩, ⟨(-282660733449243353), (-282647109993088523)⟩, true⟩

def words03 : List Nat := [371286035186505539, 371286030180026189, 371286027525824777, 371286027526209925, 371286028443955228, 371286029554769309, 371286030615657875, 371286030616004925, 371286028436341343, 371286030522706924]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362383857532137517, 362383859264477335⟩, ⟨1189931135793545933, 1189944795060758371⟩, true⟩

def words04 : List Nat := [371286035700744340, 371286035701088729, 371286031078683963, 371286026478096677, 371286021878172329, 371286017623189815, 371286009731764700, 371286007155929302, 371286004580409556, 371286000448602722]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507928543236497, 362507930278684725⟩, ⟨(-256172364481968344), (-256158668985903666)⟩, true⟩

def words05 : List Nat := [371285991682106245, 371285988988807886, 371285989500608221, 371285989500952920, 371285982927922036, 371285974047551997, 371285965168563233, 371285963612575764, 371285961267236313, 371285963151595633]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472857126695725, 362472858865261282⟩, ⟨152938386395462370, 152952118255310886⟩, true⟩

def words06 : List Nat := [371285964443626334, 371285964443978216, 371285963768386305, 371285966607966563, 371285971657454457, 371285971657800241, 371285969274668056, 371285966919213845, 371285965301736845, 371285965302129775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362418851435917680, 362418853177596703⟩, ⟨783777402789219984, 783791170999190348⟩, true⟩

def words07 : List Nat := [371285966814472534, 371285969449496313, 371285972032980074, 371285972033327028, 371285967703227524, 371285965648200854, 371285968829881180, 371285968830226706, 371285964331498232, 371285958586072662]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467891888176357, 362467893632954398⟩, ⟨210943517835706987, 210957322258012813⟩, true⟩

def words08 : List Nat := [371285954385207490, 371285954385593807, 371285955612511647, 371285957772252744, 371285958722105490, 371285958722451265, 371285949950594927, 371285944072775295, 371285939596855473, 371285939597219412]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362446962433291500, 362446964181221270⟩, ⟨455795981740232900, 455809823021882204⟩, true⟩

def words09 : List Nat := [371285938053903706, 371285936481633552, 371285937092712129, 371285937093092952, 371285936363292271, 371285937104004124, 371285937104267844, 371285936210907727, 371285925615360302, 371285922285753055]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk116
