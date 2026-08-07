import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk433

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485818102304488, 362485844878743109⟩, ⟨(-15871636996420476), (-15088247139695384)⟩, true⟩

def state01 : KState := ⟨⟨362476141997600220, 362476168786842080⟩, ⟨403254504929707113, 404038449232526131⟩, true⟩

def words00 : List Nat := [371285496720272324, 371285496820156246, 371285497266495705, 371285497713403122, 371285498081321294, 371285498082750797, 371285497815566278, 371285497759534863, 371285497772876157, 371285497774356108]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497873790474627, 362497900592754787⟩, ⟨(-538057277488205769), (-537272768431899379)⟩, true⟩

def words01 : List Nat := [371285497560029504, 371285497344371578, 371285497444458382, 371285497497300385, 371285497708574062, 371285497920410439, 371285498130894534, 371285498132333801, 371285498172491580, 371285498460568737]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486879607021575, 362486906422052962⟩, ⟨(-61700496278483318), (-60915434772409620)⟩, true⟩

def words02 : List Nat := [371285499281202061, 371285499391908401, 371285499396232550, 371285499401007288, 371285499570687445, 371285499572278420, 371285499925793005, 371285500309674941, 371285500571602717, 371285500605552711]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505405482791677, 362505432310717667⟩, ⟨(-864469683761583980), (-863684063466461794)⟩, true⟩

def words03 : List Nat := [371285501172078096, 371285501739303843, 371285502640676419, 371285502937414461, 371285503147918265, 371285503358858206, 371285503669735473, 371285503743489068, 371285504204281136, 371285504665682563]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494299316699691, 362494326157532773⟩, ⟨(-383121794420771796), (-382335614668811704)⟩, true⟩

def words04 : List Nat := [371285505124656594, 371285505126093906, 371285505497822760, 371285505917874176, 371285506496023479, 371285506497454081, 371285506366137589, 371285506233533169, 371285506418532870, 371285506623619627]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470956268171990, 362470983121910647⟩, ⟨628911928670279259, 629698667945477163⟩, true⟩

def words05 : List Nat := [371285506877472218, 371285507131883383, 371285507385171992, 371285507386603114, 371285507018938136, 371285506621890118, 371285506289390437, 371285506290849362, 371285506025976168, 371285505692665848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485117509042206, 362485144375586016⟩, ⟨14907613039181488, 15694907610623042⟩, true⟩

def words06 : List Nat := [371285505491814306, 371285505493417657, 371285505885565396, 371285506312830075, 371285506580695018, 371285506582126276, 371285506141039586, 371285506035682173, 371285506258070654, 371285506259552136]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477461272349682, 362477488151941055⟩, ⟨347033021242730127, 347820881753471449⟩, true⟩

def words07 : List Nat := [371285506252288671, 371285506218492157, 371285506422771601, 371285506424348312, 371285506515787200, 371285506633565699, 371285506737464322, 371285506738898549, 371285506335967550, 371285506152903561]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464109751456862, 362464136643795872⟩, ⟨926294592974779144, 927083006544442022⟩, true⟩

def words08 : List Nat := [371285506047062757, 371285506048494537, 371285505493864687, 371285504938003004, 371285504381590858, 371285503984669393, 371285503394707918, 371285503237985390, 371285503080811116, 371285502926500285]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502155833457465, 362502182738778585⟩, ⟨(-724730191703664081), (-723941214777161121)⟩, true⟩

def words09 : List Nat := [371285502474068784, 371285502514809990, 371285502773973144, 371285502775412040, 371285502530364067, 371285502118489188, 371285501823936985, 371285501825529244, 371285502063974664, 371285502449965490]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk433
