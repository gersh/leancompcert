import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk124

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360410323113001621, 360410323967022580⟩, ⟨2123013556528836030, 2123020730580796322⟩, true⟩

def state01 : KState := ⟨⟨360614428947229219, 360614429802690118⟩, ⟨(-408902406005853975), (-408895214091548969)⟩, true⟩

def words00 : List Nat := [360581521510133014, 360581514159963490, 360581512466594410, 360581513728995205, 360581513729135793, 360581509385700238, 360581498607727362, 360581490573475958, 360581482540474156, 360581483608661309]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602697881475297, 360602698738392713⟩, ⟨(-263279709990134803), (-263272499993253495)⟩, true⟩

def words01 : List Nat := [360581483608800852, 360581481386264322, 360581483384026104, 360581490890642222, 360581494612755201, 360581498334292894, 360581498824733099, 360581499567467413, 360581501274449461, 360581502981207845]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360555102461995383, 360555103320351267⟩, ⟨327899389590043058, 327906617459928884⟩, true⟩

def words02 : List Nat := [360581511121396013, 360581512841339152, 360581512841475381, 360581510131190068, 360581507421318575, 360581499867641001, 360581496214034133, 360581493108161462, 360581490002772507, 360581483579197601]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360649783889579765, 360649784749378880⟩, ⟨(-849473707385007866), (-849466461568367902)⟩, true⟩

def words03 : List Nat := [360581483008164782, 360581484559064505, 360581492531801876, 360581494091578518, 360581494091719439, 360581490089916589, 360581488507752274, 360581494174163592, 360581499663885615, 360581505152757357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576910848978185, 360576911710235095⟩, ⟨56520983783729620, 56528247742243078⟩, true⟩

def words04 : List Nat := [360581505152895324, 360581505025316460, 360581498492186720, 360581494719415477, 360581490947210259, 360581483752276107, 360581477319761591, 360581467622428549, 360581457926624418, 360581452131740497]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360492360932587640, 360492361795289345⟩, ⟨1109999439414906136, 1110006721368428308⟩, true⟩

def words05 : List Nat := [360581457806160636, 360581463844304144, 360581464754029484, 360581464754183372, 360581463932353046, 360581459985213645, 360581458492558332, 360581458492711596, 360581454557096882, 360581447406956154]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360518494095890155, 360518494960038949⟩, ⟨784218353996590406, 784225653987924586⟩, true⟩

def words06 : List Nat := [360581440257926389, 360581435133101358, 360581434069029341, 360581433086025623, 360581432103168575, 360581425678531548, 360581416673708049, 360581404654302049, 360581392636779559, 360581383945924108]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627606428254487, 360627607293864840⟩, ⟨(-577053265890510082), (-577045947666300138)⟩, true⟩

def words07 : List Nat := [360581378903242659, 360581370658264430, 360581362414579129, 360581364678764907, 360581367053221173, 360581369427321582, 360581369427458373, 360581368603451835, 360581369637626445, 360581373342445379]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546861874987684, 360546862742044950⟩, ⟨430646997586094014, 430654333875240148⟩, true⟩

def words08 : List Nat := [360581376868249263, 360581376868402798, 360581375371439808, 360581369909632034, 360581364448675179, 360581354481746626, 360581347778774025, 360581347445646345, 360581347112552997, 360581342672699493]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360626261270113890, 360626262138621385⟩, ⟨(-561644749498614599), (-561637395088938433)⟩, true⟩

def words09 : List Nat := [360581343518923434, 360581347124998018, 360581350934561326, 360581350934714985, 360581348393196346, 360581339187744077, 360581329983734869, 360581327551963613, 360581331146855128, 360581334741206064]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk124
