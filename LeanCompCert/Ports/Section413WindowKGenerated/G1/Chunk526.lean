import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk526

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473281607695876, 362473321749810195⟩, ⟨615226875242152210, 616653316782951082⟩, true⟩

def state01 : KState := ⟨⟨362491589243096634, 362491629400974399⟩, ⟨(-347811004480466746), (-346383733701491200)⟩, true⟩

def words00 : List Nat := [371285045009145373, 371285045011100257, 371285045099681541, 371285045281889718, 371285045365497939, 371285045367262043, 371285045059517538, 371285045056669580, 371285045408773591, 371285045535742766]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476587264693256, 362476627438626234⟩, ⟨441570796872732723, 442998912399759627⟩, true⟩

def words01 : List Nat := [371285045652560819, 371285045769976216, 371285046070812839, 371285046214066930, 371285046386976208, 371285046560565175, 371285046733960091, 371285046735723029, 371285046427937846, 371285046270104755]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478216546361254, 362478256736006702⟩, ⟨355840406789178695, 357269349185043805⟩, true⟩

def words02 : List Nat := [371285046257870673, 371285046259633978, 371285045975117963, 371285045689230503, 371285045402633243, 371285045220684279, 371285044962761410, 371285045015403032, 371285045055461791, 371285045057290857]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495412589203801, 362495452794837454⟩, ⟨(-549288731953562546), (-547858948022116024)⟩, true⟩

def words03 : List Nat := [371285045161095368, 371285045394825064, 371285045740983198, 371285045742746668, 371285045608253718, 371285045359747699, 371285045110556467, 371285045101831676, 371285045138008439, 371285045337759851]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474326894067812, 362474367115621492⟩, ⟨560738551717725636, 562169173758898272⟩, true⟩

def words04 : List Nat := [371285045536094476, 371285045537858174, 371285045277549699, 371285045301789317, 371285045436262302, 371285045438038088, 371285045250168241, 371285044987013623, 371285044723142801, 371285044592805897]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465644654699238, 362465684892102693⟩, ⟨1017992600672075632, 1019424057288084234⟩, true⟩

def words05 : List Nat := [371285044462756216, 371285044536201081, 371285044609538308, 371285044611333092, 371285044385560164, 371285044271806540, 371285044225110318, 371285044226874706, 371285043861202574, 371285043495545308]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480656425835633, 362480696679064588⟩, ⟨227394175463382677, 228826465528078611⟩, true⟩

def words06 : List Nat := [371285043129155627, 371285042912264069, 371285042538237258, 371285042404668840, 371285042270539884, 371285042076314571, 371285041513426539, 371285041311542068, 371285041208572513, 371285041210401746]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473015933257145, 362473056202566210⟩, ⟨629915650991361645, 631348788078045093⟩, true⟩

def words07 : List Nat := [371285041129237460, 371285041018530393, 371285041154381478, 371285041223478080, 371285041295158789, 371285041367480818, 371285041437403419, 371285041439168450, 371285041029007776, 371285040803706644]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467239601912031, 362467279886972847⟩, ⟨934303303932817214, 935737270903311078⟩, true⟩

def words08 : List Nat := [371285040678387649, 371285040680184114, 371285040532021802, 371285040340809277, 371285040148945591, 371285040007492172, 371285039685369202, 371285039533233740, 371285039380514385, 371285039182302195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492221337081288, 362492261638062995⟩, ⟨(-382118644553796704), (-380683838630099622)⟩, true⟩

def words09 : List Nat := [371285038869105252, 371285038893848054, 371285039073826036, 371285039075591765, 371285038776062817, 371285038421790747, 371285038070175375, 371285038072120972, 371285038033836487, 371285038172879601]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk526
