import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk478

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362458844504656617, 362458877399503296⟩, ⟨1260440143027085049, 1261502472671527617⟩, true⟩

def state01 : KState := ⟨⟨362487130197507918, 362487163106620247⟩, ⟨(-91778954703529642), (-90715943090216772)⟩, true⟩

def words00 : List Nat := [371285268113599250, 371285267853371833, 371285267402861498, 371285267135934972, 371285266868530533, 371285266528511145, 371285265879700531, 371285265668200187, 371285265678819334, 371285265720180093]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488591624345564, 362488624547911896⟩, ⟨(-161614387900752965), (-160550685166911787)⟩, true⟩

def words01 : List Nat := [371285265762197594, 371285265804735216, 371285266229357500, 371285266491918656, 371285266858359150, 371285267225407081, 371285267442897573, 371285267444488452, 371285267149783841, 371285267221942826]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461096117869517, 362461129055614251⟩, ⟨1153353271916181139, 1154417652734619055⟩, true⟩

def words02 : List Nat := [371285267424828692, 371285267426419752, 371285267047236231, 371285266653499431, 371285266259120401, 371285265997001309, 371285265517510908, 371285265323165616, 371285265128295089, 371285264904511066]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481778828286599, 362481811780452150⟩, ⟨163970373487904662, 165035444126264508⟩, true⟩

def words03 : List Nat := [371285264401002959, 371285264081210444, 371285263802377172, 371285263803968515, 371285263265119337, 371285262659972856, 371285262054219687, 371285261885076009, 371285261588286760, 371285261517996596]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469010827839419, 362469043794351122⟩, ⟨774792266404476181, 775858023435780759⟩, true⟩

def words04 : List Nat := [371285261447079053, 371285261333044566, 371285260768072949, 371285260639750254, 371285260510664906, 371285260396632535, 371285259783621560, 371285259129300248, 371285258474346040, 371285258173106311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452785939075779, 362452818919915118⟩, ⟨1551343722449774575, 1552410165133348043⟩, true⟩

def words05 : List Nat := [371285257899086436, 371285257964577157, 371285258022679573, 371285258024271893, 371285257557705075, 371285257116451026, 371285256674370653, 371285256668412352, 371285256080747504, 371285255404769555]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473976373115611, 362474009368199869⟩, ⟨537044042459171874, 538111166979023550⟩, true⟩

def words06 : List Nat := [371285254728137296, 371285254180149221, 371285253415258731, 371285252960209825, 371285252504669771, 371285251976927074, 371285251197010980, 371285250807269923, 371285250460492794, 371285250462141357]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463933317090107, 362463966326750433⟩, ⟨1017901994956171501, 1018969817299497011⟩, true⟩

def words07 : List Nat := [371285250228524218, 371285250008332179, 371285249787482451, 371285249741508794, 371285249495504530, 371285249374813257, 371285249253604566, 371285249133936319, 371285248511412831, 371285248068966380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362444079734731685, 362444112758563019⟩, ⟨1968657726987394062, 1969726227913085308⟩, true⟩

def words08 : List Nat := [371285247625576065, 371285247617882000, 371285247088296041, 371285246470931866, 371285245852999134, 371285245325818828, 371285244614462300, 371285244086158129, 371285243557331851, 371285242978398331]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489112889698912, 362489145927918013⟩, ⟨(-188174507202984950), (-187105317173697192)⟩, true⟩

def words09 : List Nat := [371285242120650151, 371285241650005799, 371285241178565582, 371285241072893981, 371285240726248949, 371285240330385990, 371285239933878414, 371285239915967049, 371285239760855760, 371285239844179183]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk478
