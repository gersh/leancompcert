import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482795573276342, 362482941547878048⟩, ⟨225852392135917734, 235500890812924164⟩, true⟩

def state01 : KState := ⟨⟨362481064505586844, 362481210510990860⟩, ⟨395378443760985923, 405029958136893661⟩, true⟩

def words00 : List Nat := [371285347113574480, 371285347143359504, 371285347216241703, 371285347290553541, 371285347343037307, 371285347346475141, 371285347259579682, 371285347251171745, 371285347265251347, 371285347268810663]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483043474032599, 362483189510836581⟩, ⟨201604645468706502, 211259234363501950⟩, true⟩

def words01 : List Nat := [371285347229176604, 371285347163621452, 371285347121659206, 371285347125448444, 371285347105289297, 371285347113556710, 371285347116786801, 371285347120225261, 371285346996174932, 371285346978507777]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486499507085481, 362486645574539703⟩, ⟨(-136819350532793073), (-127161760203827773)⟩, true⟩

def words02 : List Nat := [371285347032868207, 371285347036330116, 371285347019547394, 371285346983623489, 371285346946416320, 371285346942605960, 371285346953482325, 371285347013681903, 371285347074438296, 371285347091319846]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491735720319582, 362491881818786474⟩, ⟨(-649614484879160051), (-639953857317390361)⟩, true⟩

def words03 : List Nat := [371285347211233309, 371285347332891529, 371285347485008283, 371285347525330151, 371285347548685688, 371285347573157564, 371285347613888033, 371285347617713915, 371285347673057402, 371285347743605321]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486203914925665, 362486350044417678⟩, ⟨(-107818495752715312), (-98154829436871364)⟩, true⟩

def words04 : List Nat := [371285347812707059, 371285347816162873, 371285347856616117, 371285347932076848, 371285348030193926, 371285348033633339, 371285347992977922, 371285347953525780, 371285347949325572, 371285347963484999]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480086184316321, 362480232344855566⟩, ⟨491459391318926779, 501126098867976419⟩, true⟩

def words05 : List Nat := [371285348018488938, 371285348074899899, 371285348127903657, 371285348131354563, 371285348098670025, 371285348062319772, 371285348058773835, 371285348062273771, 371285348012806646, 371285347964484680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499412680471575, 362499558871790243⟩, ⟨(-1401840299958385377), (-1392170577102355879)⟩, true⟩

def words06 : List Nat := [371285347966637858, 371285347980168106, 371285348083610938, 371285348188429633, 371285348267333967, 371285348271480421, 371285348378741374, 371285348487852308, 371285348695960005, 371285348844566857]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495367758650991, 362495513981293463⟩, ⟨(-1005503263845078387), (-995830472036616777)⟩, true⟩

def words07 : List Nat := [371285348981639829, 371285349119899079, 371285349360955865, 371285349551465427, 371285349772619813, 371285349995118560, 371285350197223478, 371285350261321214, 371285350367427220, 371285350475388884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491877297447144, 362492023550742748⟩, ⟨(-663494791107449285), (-653818995746022435)⟩, true⟩

def words08 : List Nat := [371285350650112276, 371285350687087998, 371285350721318978, 371285350756729527, 371285350822255398, 371285350851363097, 371285350983144138, 371285351116328607, 371285351243925726, 371285351315580886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496245617051734, 362496391901537409⟩, ⟨(-1091560677667158976), (-1081881825837498618)⟩, true⟩

def words09 : List Nat := [371285351448114704, 371285351582497496, 371285351758149942, 371285351835338076, 371285351894565081, 371285351954831323, 371285352088714206, 371285352172081774, 371285352287081771, 371285352403717617]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk979
