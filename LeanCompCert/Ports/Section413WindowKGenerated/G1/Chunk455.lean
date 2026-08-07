import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk455

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488055379190194, 362488085064915319⟩, ⟨(-115901697591416141), (-114989106798507893)⟩, true⟩

def state01 : KState := ⟨⟨362460277990277589, 362460307689596354⟩, ⟨1148067148737852036, 1148980358108597692⟩, true⟩

def words00 : List Nat := [371285557908724126, 371285557910231339, 371285557288042541, 371285557149332264, 371285557009847763, 371285556983492974, 371285556384640520, 371285555641376337, 371285554897547998, 371285554456419220]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463082898130207, 362463112611030148⟩, ⟨1020486103607453739, 1021399931128974933⟩, true⟩

def words01 : List Nat := [371285553902702990, 371285553765815606, 371285553628429058, 371285553483719464, 371285552937613529, 371285552538499098, 371285552138640394, 371285552080472213, 371285551589327897, 371285551098093615]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483775277741392, 362483805004165220⟩, ⟨78497019042445635, 79411462239069557⟩, true⟩

def words02 : List Nat := [371285550606209296, 371285550306360792, 371285549774778248, 371285549726007847, 371285549676782649, 371285549545638277, 371285549079404593, 371285549023948455, 371285549159471398, 371285549161034078]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477502354231841, 362477532094388772⟩, ⟨364208557873118799, 365123626406793227⟩, true⟩

def words03 : List Nat := [371285549123865703, 371285549087352113, 371285549494040566, 371285549698940970, 371285549924859839, 371285550151347997, 371285550353772001, 371285550355280649, 371285549915172424, 371285549740994104]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471921964770267, 362471951718365460⟩, ⟨618457377147301379, 619373057730246613⟩, true⟩

def words04 : List Nat := [371285549871749624, 371285549873284487, 371285549779925415, 371285549609075460, 371285549437643306, 371285549413001164, 371285549253749700, 371285549361787007, 371285549369002154, 371285549370565905]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493441388621293, 362493471155876738⟩, ⟨(-361902516363672552), (-360986213488001964)⟩, true⟩

def words05 : List Nat := [371285549073082827, 371285548884878820, 371285548987440162, 371285548988949270, 371285548639679197, 371285548215773013, 371285547847260843, 371285547848938930, 371285547839556734, 371285548015175525]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476660367819418, 362476690148711401⟩, ⟨402658962990905859, 403575887215349815⟩, true⟩

def words06 : List Nat := [371285548189395019, 371285548190917835, 371285548057238549, 371285548052387110, 371285548133551966, 371285548135061526, 371285547581261486, 371285547001757165, 371285546421643834, 371285546323546059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362452410931686387, 362452440726147070⟩, ⟨1507923937926298511, 1508841480546186859⟩, true⟩

def words07 : List Nat := [371285546375012494, 371285546621405351, 371285546771020910, 371285546772530610, 371285546280605322, 371285545935377621, 371285545589373372, 371285545323039214, 371285544598629338, 371285543874030927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483600260353866, 362483630068327332⟩, ⟨86179436261383669, 87097594860924773⟩, true⟩

def words08 : List Nat := [371285543148809280, 371285542779862063, 371285542195418267, 371285542032972927, 371285541870016044, 371285541627503602, 371285540869978459, 371285540594112360, 371285540520697618, 371285540522261549]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494506016843216, 362494535838618313⟩, ⟨(-411088441463217285), (-410169653580104481)⟩, true⟩

def words09 : List Nat := [371285540481512079, 371285540354341536, 371285540519790095, 371285540619229204, 371285540736726980, 371285540854776146, 371285540971718593, 371285540973255467, 371285540888176247, 371285541087328208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk455
