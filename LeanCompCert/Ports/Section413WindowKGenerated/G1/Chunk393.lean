import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk393

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488874741722358, 362488896626873236⟩, ⟨(-148264897321998052), (-147683689155452094)⟩, true⟩

def state01 : KState := ⟨⟨362470573032355954, 362470594928949322⟩, ⟨571143484458488964, 571725142375736444⟩, true⟩

def words00 : List Nat := [371285139611471226, 371285139612758634, 371285139609701541, 371285139471941387, 371285139333696714, 371285139235014872, 371285138854263203, 371285138897549033, 371285138940396930, 371285138941729168]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505567166992972, 362505589075258261⟩, ⟨(-804582845635187251), (-804000728838738265)⟩, true⟩

def words01 : List Nat := [371285138673444013, 371285138775858258, 371285139524345431, 371285139694956222, 371285139759736169, 371285139824901639, 371285140536305885, 371285140924971902, 371285141445905728, 371285141967381078]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491015463876226, 362491037383769264⟩, ⟨(-232445689110760848), (-231863115053063210)⟩, true⟩

def words02 : List Nat := [371285142400665056, 371285142401952589, 371285142191242347, 371285142410282924, 371285142623339680, 371285142624649888, 371285142350646695, 371285142077033964, 371285142057719720, 371285142209096537]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489544911279821, 362489566842771640⟩, ⟨(-174556685576899594), (-173973655279805040)⟩, true⟩

def words03 : List Nat := [371285142862026527, 371285143515434400, 371285144043033988, 371285144044321986, 371285143811948310, 371285143775662900, 371285144296500816, 371285144418434654, 371285144531824069, 371285144645692771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498295085695116, 362498317028703661⟩, ⟨(-518677928308484738), (-518094444883750470)⟩, true⟩

def words04 : List Nat := [371285145404898784, 371285145886584739, 371285147013580325, 371285148141058828, 371285149150529779, 371285149383406635, 371285149676710886, 371285149970645304, 371285150713648520, 371285151049570126]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502926457930363, 362502948412691253⟩, ⟨(-700972156002885646), (-700388210064071998)⟩, true⟩

def words05 : List Nat := [371285151372939227, 371285151696733274, 371285152255526274, 371285152580775492, 371285152965035025, 371285153349753822, 371285153734269504, 371285153735566950, 371285153995169827, 371285154448867568]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482007320626525, 362482029286881556⟩, ⟨122495878534664167, 123080276941921599⟩, true⟩

def words06 : List Nat := [371285155166451598, 371285155167740472, 371285155025692552, 371285154884072945, 371285154794284752, 371285154795719194, 371285154901089902, 371285155277334034, 371285155530833089, 371285155532168372]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362517324455600212, 362517346433489993⟩, ⟨(-1268078090629026160), (-1267493234102858304)⟩, true⟩

def words07 : List Nat := [371285156019285382, 371285156586435370, 371285157797914481, 371285158150555015, 371285158343285359, 371285158536397992, 371285159127345140, 371285159396605047, 371285160214825046, 371285161033573718]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503598912394889, 362503620901926392⟩, ⟨(-727456178940135489), (-726870863903657699)⟩, true⟩

def words08 : List Nat := [371285161851734026, 371285162256828442, 371285163306104075, 371285164356019271, 371285165600538920, 371285166113846057, 371285166614826122, 371285167116202786, 371285167717815978, 371285168187755550]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479223745865767, 362479245747017978⟩, ⟨232881191616689659, 233466964451963825⟩, true⟩

def words09 : List Nat := [371285168985161527, 371285169783063390, 371285170574509664, 371285170575799906, 371285170636268246, 371285170765246753, 371285171537730467, 371285171539020778, 371285171453427725, 371285171304491379]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk393
