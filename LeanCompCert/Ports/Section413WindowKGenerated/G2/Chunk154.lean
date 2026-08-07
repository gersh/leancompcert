import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk154

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360521436517882174, 360521437861991541⟩, ⟨908741501555184822, 908755516741413144⟩, true⟩

def state01 : KState := ⟨⟨360600055623751967, 360600056969681959⟩, ⟨(-302091640036218148), (-302077596803243414)⟩, true⟩

def words00 : List Nat := [360580444501887132, 360580447922077617, 360580454188709342, 360580460454564232, 360580463082708580, 360580463082901674, 360580461521226395, 360580458526431999, 360580455531968616, 360580455542337644]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620828300735814, 360620829648505306⟩, ⟨(-622279990420294011), (-622265918831407195)⟩, true⟩

def words01 : List Nat := [360580455542510945, 360580453689538922, 360580454181456520, 360580459814078846, 360580464363863628, 360580468913089770, 360580471260409473, 360580472561493019, 360580475178841023, 360580477795912647]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360623059717071403, 360623061066663612⟩, ⟨(-656897627159581244), (-656883527455156696)⟩, true⟩

def words02 : List Nat := [360580480254910132, 360580482173833490, 360580482174005847, 360580481367923899, 360580480561915211, 360580478805918210, 360580483193073100, 360580487579699951, 360580489224113890, 360580491983165773]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360633140581556960, 360633141932974852⟩, ⟨(-812977140890584767), (-812963013006874149)⟩, true⟩

def words03 : List Nat := [360580495918713287, 360580499853806326, 360580502359300249, 360580502359493779, 360580500690668145, 360580495052288330, 360580489414601774, 360580486250167217, 360580488887890779, 360580492298041437]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600513176569350, 360600514529833562⟩, ⟨(-309171131957785151), (-309156975557910749)⟩, true⟩

def words04 : List Nat := [360580493591432598, 360580495030335724, 360580500650099084, 360580506269195509, 360580510809726746, 360580511181247992, 360580511181420922, 360580508962034798, 360580506742901795, 360580505664675456]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360424493111291850, 360424494466380514⟩, ⟨2411587299781605008, 2411601484378493244⟩, true⟩

def words05 : List Nat := [360580511136496453, 360580516607646158, 360580518924913882, 360580518925107629, 360580517076841004, 360580512514275507, 360580507952241133, 360580502283933523, 360580494303451404, 360580484213106161]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360648655110632552, 360648656467554481⟩, ⟨(-1055362832797008157), (-1055348619848922447)⟩, true⟩

def words06 : List Nat := [360580474124022687, 360580468208682918, 360580464423493806, 360580459915922850, 360580455408919671, 360580447354599191, 360580441144456872, 360580439105196054, 360580437422756350, 360580441832440467]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619450944954338, 360619452303723647⟩, ⟨(-603271020507853664), (-603256778971678728)⟩, true⟩

def words07 : List Nat := [360580444041730073, 360580446250753566, 360580452626261406, 360580461125995284, 360580468499020569, 360580475871124577, 360580479072184896, 360580479709572912, 360580482227339715, 360580484744846852]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572676297732791, 360572677658330729⟩, ⟨120904500003225353, 120918769855917505⟩, true⟩

def words08 : List Nat := [360580490221732711, 360580491549387371, 360580491549561187, 360580490205952761, 360580488862483309, 360580485360116224, 360580485019406033, 360580485505114503, 360580485505289189, 360580483905577722]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360670826840745791, 360670828203180757⟩, ⟨(-1400184508345057998), (-1400170210027815988)⟩, true⟩

def words09 : List Nat := [360580483401816237, 360580482749333630, 360580485599401004, 360580486680317918, 360580486680497021, 360580484239321647, 360580483511461367, 360580488812535805, 360580494641042007, 360580500468839243]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk154
