import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498252086500000, 362498358815794479⟩, ⟨(-1104604868668206467), (-1098536916606857117)⟩, true⟩

def state01 : KState := ⟨⟨362478841020551806, 362478947776251084⟩, ⟨529839938245400713, 535910113726652235⟩, true⟩

def words00 : List Nat := [371285312358735580, 371285312361657862, 371285312318235928, 371285312312466574, 371285312305265024, 371285312304490909, 371285312133263662, 371285311963077900, 371285311791661184, 371285311748626416]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475374164923114, 362475480946891809⟩, ⟨821870954919185965, 827943342680721763⟩, true⟩

def words01 : List Nat := [371285311740399768, 371285311808908416, 371285311875853982, 371285311878792481, 371285311837045450, 371285311839947661, 371285311881001220, 371285311883932334, 371285311781601335, 371285311668130004]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485165039209914, 362485271847346473⟩, ⟨(-2715374149883998), 3359217601223554⟩, true⟩

def words02 : List Nat := [371285311577570038, 371285311580821651, 371285311631485857, 371285311729547845, 371285311806481340, 371285311809408868, 371285311733917864, 371285311685901571, 371285311725806342, 371285311728832894]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493983951057238, 362494090785930704⟩, ⟨(-745598227241168408), (-739521383313053612)⟩, true⟩

def words03 : List Nat := [371285311730604386, 371285311707890585, 371285311786327865, 371285311823957303, 371285311871986255, 371285311921102237, 371285311965798306, 371285311968793411, 371285312038345150, 371285312146274088]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485958743229067, 362486065604102951⟩, ⟨(-69486876358642412), (-63407842018710602)⟩, true⟩

def words04 : List Nat := [371285312371363344, 371285312429669481, 371285312487228662, 371285312545747807, 371285312599702304, 371285312602931741, 371285312742880262, 371285312885471365, 371285312985736300, 371285312997700432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498111803722927, 362498218691053997⟩, ⟨(-1093426214673470828), (-1087344951183686704)⟩, true⟩

def words05 : List Nat := [371285313138704172, 371285313281260120, 371285313516020525, 371285313579692171, 371285313607901131, 371285313637060746, 371285313794589966, 371285313892781444, 371285314047954002, 371285314204385388]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494597910674831, 362494704824359080⟩, ⟨(-797362861542121907), (-791279377394794505)⟩, true⟩

def words06 : List Nat := [371285314359732147, 371285314362657050, 371285314436333029, 371285314546082112, 371285314686446656, 371285314745992089, 371285314804205487, 371285314863356584, 371285315009968762, 371285315124730563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481494113210755, 362481601053300934⟩, ⟨306983746129908306, 313069455637973442⟩, true⟩

def words07 : List Nat := [371285315287315672, 371285315451116781, 371285315586717724, 371285315589645627, 371285315593659570, 371285315618998782, 371285315766349925, 371285315769275283, 371285315729214480, 371285315688512586]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494453858611646, 362494560824870430⟩, ⟨(-785280961817429950), (-779193046684600212)⟩, true⟩

def words08 : List Nat := [371285315731943877, 371285315771252483, 371285315932459009, 371285316094832894, 371285316234382127, 371285316259954293, 371285316342820620, 371285316427211289, 371285316628619438, 371285316741318395]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493208808535609, 362493315801412218⟩, ⟨(-680332177993790140), (-674242019109936536)⟩, true⟩

def words09 : List Nat := [371285316853201411, 371285316966058793, 371285317125956282, 371285317236804385, 371285317363373306, 371285317491084935, 371285317617812145, 371285317620738430, 371285317671847779, 371285317770319943]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842
