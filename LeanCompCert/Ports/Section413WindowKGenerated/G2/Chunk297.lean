import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360624792698041512, 360624797998807497⟩, ⟨(-1226389849322580649), (-1226283378184088285)⟩, true⟩

def state01 : KState := ⟨⟨360586313697863551, 360586319002336309⟩, ⟨(-83544753981097955), (-83438172732041525)⟩, true⟩

def words00 : List Nat := [360583511751022528, 360583511987414845, 360583511987765575, 360583511661313669, 360583511334821075, 360583510375572938, 360583510379123632, 360583510770945050, 360583510771299086, 360583510676371783]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360626427178995874, 360626432487185822⟩, ⟨(-1275769909544168902), (-1275663217839335984)⟩, true⟩

def words01 : List Nat := [360583510676692638, 360583510483619935, 360583510806605036, 360583510806998832, 360583510533957610, 360583509229174344, 360583507924401347, 360583508322865947, 360583509767470135, 360583511212065896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619750305450550, 360619755617393863⟩, ⟨(-1077291388970269469), (-1077184585696720187)⟩, true⟩

def words02 : List Nat := [360583512094600919, 360583513595138238, 360583516223131768, 360583518851063553, 360583520785944869, 360583521961427549, 360583522543545875, 360583523125664377, 360583523373901061, 360583524593018743]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360518131687900683, 360518137003556148⟩, ⟨1944422584235684130, 1944529497890249440⟩, true⟩

def words03 : List Nat := [360583526138797308, 360583527684545654, 360583528213617721, 360583528214011849, 360583527617345517, 360583526464981109, 360583525312567621, 360583524976926592, 360583523515737454, 360583521317540353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593535040882407, 360593540360264739⟩, ⟨(-298538844599859163), (-298431820090283831)⟩, true⟩

def words04 : List Nat := [360583519119402236, 360583518047864666, 360583517545917051, 360583516976526496, 360583516407142396, 360583514897909668, 360583512594518451, 360583511154022734, 360583509713508482, 360583509375756982]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580923161512600, 360580928484649806⟩, ⟨76756431552736641, 76863567788246535⟩, true⟩

def words05 : List Nat := [360583509376108543, 360583509042988490, 360583509501756919, 360583511058147741, 360583511854582918, 360583512651026768, 360583512651386043, 360583512563762790, 360583511352165616, 360583511265825487]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611628993677290, 360611634320529677⟩, ⟨(-837222267372579273), (-837115020554570407)⟩, true⟩

def words06 : List Nat := [360583512217552186, 360583512750405129, 360583512750760012, 360583512704303155, 360583512657778519, 360583512952167574, 360583513789473436, 360583514626797526, 360583514903910109, 360583515848843991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617289308583897, 360617294639164730⟩, ⟨(-1005945536275306271), (-1005838178442644287)⟩, true⟩

def words07 : List Nat := [360583516768303456, 360583517687814922, 360583519092941385, 360583519375227796, 360583519375592129, 360583518699037341, 360583518022454836, 360583517877013011, 360583519011542029, 360583520146083818]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360555209577467539, 360555214911810464⟩, ⟨842696769972774938, 842804239858830734⟩, true⟩

def words08 : List Nat := [360583520720590418, 360583520720985143, 360583520172951220, 360583519449689276, 360583518726376889, 360583516961866562, 360583514466495854, 360583511412329548, 360583508358290399, 360583506427079307]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360478478745365950, 360478484083433837⟩, ⟨3129056120995215635, 3129163701866174591⟩, true⟩

def words09 : List Nat := [360583505477732601, 360583505227526577, 360583504977286745, 360583504168493232, 360583502238122693, 360583499718131424, 360583497198192041, 360583495507695176, 360583493100168420, 360583489576785051]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297
