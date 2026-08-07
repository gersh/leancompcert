import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360610921484120039, 360610934078283703⟩, ⟨(-1246389582550405141), (-1246006597865473623)⟩, true⟩

def state01 : KState := ⟨⟨360610159027293818, 360610171627263132⟩, ⟨(-1212253229506091631), (-1211869983537114203)⟩, true⟩

def words00 : List Nat := [360583246350010263, 360583246549462456, 360583246550020566, 360583246369598998, 360583246189085138, 360583245895131077, 360583246400559908, 360583246906084703, 360583247165749624, 360583247764573188]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612190519173862, 360612203124957107⟩, ⟨(-1303739970800217602), (-1303356463117885750)⟩, true⟩

def words01 : List Nat := [360583248317118005, 360583248869821956, 360583249915272091, 360583250625358433, 360583250917369350, 360583251209417020, 360583251369096161, 360583251870723082, 360583252514299064, 360583253157983520]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579555592176233, 360579568203822619⟩, ⟨165427279983847171, 165811051654131619⟩, true⟩

def words02 : List Nat := [360583253499995342, 360583253500611506, 360583253350367083, 360583253276568542, 360583253202599206, 360583253002293790, 360583252477382044, 360583251704626063, 360583250931786823, 360583250439035902]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565661469096863, 360565674086556142⟩, ⟨791139101025004273, 791523134478783589⟩, true⟩

def words03 : List Nat := [360583250357771884, 360583250253793323, 360583250149750698, 360583249702758548, 360583249404952471, 360583248981889927, 360583248558659153, 360583248399958085, 360583248257957482, 360583247868405139]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610727393213041, 360610740016489892⟩, ⟨(-1238862814924419704), (-1238478519419252356)⟩, true⟩

def words04 : List Nat := [360583247478730681, 360583247666759647, 360583248176580773, 360583248686496873, 360583248702886644, 360583248703503162, 360583248464083212, 360583248533654746, 360583248816750026, 360583249427614634]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598804443666428, 360598817072820765⟩, ⟨(-701584245492532944), (-701199685176750590)⟩, true⟩

def words05 : List Nat := [360583249791005739, 360583250154458608, 360583251009714754, 360583252112480978, 360583253089907423, 360583254067395129, 360583254735297053, 360583255259648646, 360583255605513728, 360583255951558993]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588986759513199, 360588999394472738⟩, ⟨(-259136609079730948), (-258751787152332564)⟩, true⟩

def words06 : List Nat := [360583256789195797, 360583257135734596, 360583257237543405, 360583257339409620, 360583257339925812, 360583257750630565, 360583258016504611, 360583258282481541, 360583258284733977, 360583258412751624]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611739414933997, 360611752055724930⟩, ⟨(-1284866804815040174), (-1284481720038023366)⟩, true⟩

def words07 : List Nat := [360583258682822667, 360583258953066398, 360583259098111906, 360583259098729310, 360583258958117347, 360583258390669758, 360583257823129186, 360583258039179245, 360583258671754902, 360583259304454151]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574046627237678, 360574059273908408⟩, ⟨414392931547124517, 414778281413667239⟩, true⟩

def words08 : List Nat := [360583259689663881, 360583259690280882, 360583259970006506, 360583260355974076, 360583260527664157, 360583260528281216, 360583260209339874, 360583259504582647, 360583258799741975, 360583258171256239]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360542001347156881, 360542013999636892⟩, ⟨1859613934300290282, 1859999546136888594⟩, true⟩

def words09 : List Nat := [360583258112034617, 360583258256932004, 360583258257481883, 360583258155401257, 360583258069393370, 360583257750700021, 360583257431842410, 360583257255426072, 360583256588543209, 360583255674717533]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk450
