import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554362270294022, 360554410597848936⟩, ⟨2394855807883527736, 2397659283070963536⟩, true⟩

def state01 : KState := ⟨⟨360579383539375057, 360579431878585815⟩, ⟨245346844798211846, 248151321278683356⟩, true⟩

def words00 : List Nat := [360582322489085602, 360582322158382544, 360582321904087703, 360582321785425141, 360582321666653959, 360582321423335268, 360582321044224628, 360582320778480818, 360582320512380321, 360582320381918125]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593129548389157, 360593177899375205⟩, ⟨(-935697418253119996), (-932891930101323220)⟩, true⟩

def words01 : List Nat := [360582320349415583, 360582320213316834, 360582320076984716, 360582320090912126, 360582320112363283, 360582320134015970, 360582320135121627, 360582320089845643, 360582320217215233, 360582320344992676]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579280629010128, 360579328991619511⟩, ⟨254192903562228804, 256999390450838264⟩, true⟩

def words02 : List Nat := [360582320460295691, 360582320461530994, 360582320441420066, 360582320353884801, 360582320266169280, 360582320085644662, 360582319973084511, 360582319935032240, 360582319896844286, 360582319790996340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590169878856134, 360590218253142974⟩, ⟨(-681544381207930287), (-678736890818862583)⟩, true⟩

def words03 : List Nat := [360582319857655894, 360582319959527946, 360582320196253878, 360582320297725911, 360582320298868405, 360582320267345480, 360582320262680625, 360582320359426889, 360582320452343077, 360582320545520084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581923400926574, 360581971786984833⟩, ⟨27071345282037505, 29879847365060787⟩, true⟩

def words04 : List Nat := [360582320570433997, 360582320571669640, 360582320500094210, 360582320383640984, 360582320266862729, 360582320116271140, 360582319971726263, 360582319759519086, 360582319547080183, 360582319429188034]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360558206934810374, 360558255332527815⟩, ⟨2065642626580791112, 2068452130827426700⟩, true⟩

def words05 : List Nat := [360582319426144230, 360582319422242149, 360582319418221069, 360582319310749435, 360582319182865409, 360582319021307252, 360582318859379605, 360582318783550513, 360582318572199493, 360582318293565827]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555075406283756, 360555123815661501⟩, ⟨2334899157632094012, 2337709664257754764⟩, true⟩

def words06 : List Nat := [360582318014636100, 360582317832514797, 360582317718267409, 360582317621336402, 360582317524319385, 360582317293762803, 360582316971960769, 360582316647060285, 360582316321797793, 360582315971811993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552735174186803, 360552783595329617⟩, ⟨2536116549850595349, 2538928067976797961⟩, true⟩

def words07 : List Nat := [360582315656618702, 360582315273810785, 360582314890774899, 360582314613958534, 360582314449879030, 360582314220910205, 360582313991814258, 360582313675702146, 360582313224038005, 360582312882000667]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360542473073349450, 360542521506149718⟩, ⟨3418466651979171458, 3421279172471993052⟩, true⟩

def words08 : List Nat := [360582312539577850, 360582312166390828, 360582311754620626, 360582311275275978, 360582310795741697, 360582310252203307, 360582309802320599, 360582309373648126, 360582308944828402, 360582308448497340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578645364090393, 360578693808561100⟩, ⟨307811023071020933, 310624547159546739⟩, true⟩

def words09 : List Nat := [360582307986809431, 360582307660555974, 360582307333946982, 360582307118880276, 360582306900562134, 360582306558661462, 360582306216533188, 360582305938654077, 360582305762617545, 360582305721900165]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859
