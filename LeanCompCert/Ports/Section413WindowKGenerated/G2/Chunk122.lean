import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk122

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360686122075774882, 360686122901200339⟩, ⟨(-1276359819308018766), (-1276352996988098654)⟩, true⟩

def state01 : KState := ⟨⟨360653988055758179, 360653988882611946⟩, ⟨(-884962320350900682), (-884955480598617768)⟩, true⟩

def words00 : List Nat := [360581515823590561, 360581515823740281, 360581516049251428, 360581519493318555, 360581521249455245, 360581521249605393, 360581521084229165, 360581516599770544, 360581512116015701, 360581516891734982]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529056370903069, 360529057199167072⟩, ⟨641453316480350312, 641460173458752554⟩, true⟩

def words01 : List Nat := [360581529480518972, 360581542067270011, 360581549901094826, 360581554120598078, 360581554120725751, 360581553519998899, 360581555101011142, 360581555101161174, 360581554144216115, 360581549848386283]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572103826785626, 360572104656466793⟩, ⟨115275888998333393, 115282763301490559⟩, true⟩

def words02 : List Nat := [360581545553225901, 360581542599513834, 360581546084296052, 360581549568536396, 360581549568674832, 360581547190119079, 360581538179144578, 360581535805457352, 360581533432116849, 360581530884046637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573889564625183, 360573890395737008⟩, ⟨93208533124950828, 93215424932039080⟩, true⟩

def words03 : List Nat := [360581530113498403, 360581525729257190, 360581521345703842, 360581519672141021, 360581519672266747, 360581518856195512, 360581518040238333, 360581513900567568, 360581506657099617, 360581506035028842]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569870468710482, 360569871301239231⟩, ⟨142103952265893911, 142110861423086009⟩, true⟩

def words04 : List Nat := [360581511410057892, 360581511410208061, 360581510794328556, 360581504054954840, 360581497316657636, 360581487341502312, 360581481820989109, 360581479747910230, 360581477675154716, 360581472187886014]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360632115354299079, 360632116188247686⟩, ⟨(-620176262415457151), (-620169335857964553)⟩, true⟩

def words05 : List Nat := [360581476902840514, 360581482563848368, 360581494831364514, 360581506369530967, 360581512371367640, 360581518372236480, 360581520991375304, 360581527287091684, 360581531413552163, 360581535539372557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360535034932547182, 360535035767928990⟩, ⟨569732855925615968, 569739800061418290⟩, true⟩

def words06 : List Nat := [360581535539506857, 360581535195551183, 360581528259398508, 360581527924202088, 360581527589018901, 360581522513774652, 360581510849249740, 360581494808299058, 360581478769934669, 360581469329466188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360519700287943696, 360519701124747916⟩, ⟨757870594387669218, 757877555983574888⟩, true⟩

def words07 : List Nat := [360581465545582403, 360581461589179262, 360581457633403826, 360581450372925484, 360581443559009297, 360581434939546984, 360581426321442451, 360581424290738332, 360581422564121512, 360581417538101628]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360665760005445401, 360665760843672796⟩, ⟨(-1036258668437792835), (-1036251689358206359)⟩, true⟩

def words08 : List Nat := [360581414070273799, 360581420013404105, 360581430192508689, 360581440369984869, 360581444487565705, 360581444487716573, 360581442032797879, 360581440560412469, 360581444188564881, 360581451048753082]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360651985712688910, 360651986552356494⟩, ⟨(-867032373794602432), (-867025377008116096)⟩, true⟩

def words09 : List Nat := [360581453168102963, 360581455287126643, 360581460183002307, 360581468369060211, 360581474887971652, 360581481405847520, 360581484634137762, 360581490952660950, 360581496684134950, 360581502414724748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk122
