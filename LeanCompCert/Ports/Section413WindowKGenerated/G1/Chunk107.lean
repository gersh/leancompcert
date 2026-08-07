import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk107

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362591116473413098, 362591117923712158⟩, ⟨(-1129331281106335235), (-1129320775704845713)⟩, true⟩

def state01 : KState := ⟨⟨362457351365492253, 362457352818636272⟩, ⟨302041036670531732, 302051572527419996⟩, true⟩

def words00 : List Nat := [371285592302112730, 371285592302427285, 371285589203046859, 371285587053835627, 371285585380350353, 371285585380665111, 371285575914752382, 371285566229373123, 371285556545678694, 371285555579843315]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362433676743075006, 362433678199056743⟩, ⟨556232689175291474, 556243255438606582⟩, true⟩

def words01 : List Nat := [371285559028688124, 371285565109593952, 371285571148813207, 371285571149130125, 371285570531477455, 371285571534438205, 371285576072635419, 371285576072950928, 371285571402863464, 371285566562437211]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362544770012770434, 362544771471574590⟩, ⟨(-635079638865213303), (-635069042331150085)⟩, true⟩

def words02 : List Nat := [371285563899164877, 371285563899511763, 371285568296159090, 371285574840527897, 371285579436032692, 371285579436348210, 371285575279031486, 371285575880726312, 371285585167209611, 371285590682987213]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362640337389914089, 362640338851593573⟩, ⟨(-1661138751103550519), (-1661128123702435539)⟩, true⟩

def words03 : List Nat := [371285594687406563, 371285598691178346, 371285611373448070, 371285619740011377, 371285630255435930, 371285640769027549, 371285651294232556, 371285657025524154, 371285671428143696, 371285685828252876]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362553992245642454, 362553993710134157⟩, ⟨(-733187354358009667), (-733176696738971383)⟩, true⟩

def words04 : List Nat := [371285706372445313, 371285717323065649, 371285728224084082, 371285739123182943, 371285750336977813, 371285757347489683, 371285768656636921, 371285779963803226, 371285791226389137, 371285797570543517]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362656726442036776, 362656727909394696⟩, ⟨(-1837881505626302249), (-1837870817181179441)⟩, true⟩

def words05 : List Nat := [371285809510814509, 371285821449036898, 371285842031703329, 371285853952570114, 371285864334328058, 371285874714248426, 371285891917817628, 371285906195165959, 371285922071009165, 371285937944040066]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362547546771776684, 362547548241991528⟩, ⟨(-662777736140007712), (-662767016939784834)⟩, true⟩

def words06 : List Nat := [371285952693072674, 371285955956462876, 371285965954147446, 371285975950139158, 371285988537959598, 371285994042669211, 371285998078756692, 371286002114204468, 371286009985647717, 371286015699336270]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491994270801098, 362491995743870588⟩, ⟨(-63829267390145752), (-63818517430841718)⟩, true⟩

def words07 : List Nat := [371286030030039825, 371286044358207824, 371286056948985411, 371286058080171214, 371286061698222506, 371286065315760023, 371286074522923425, 371286075108943392, 371286075658404900, 371286076207887763]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362539589410702042, 362539590886607513⟩, ⟨(-576864906924056826), (-576854126378270002)⟩, true⟩

def words08 : List Nat := [371286085358222139, 371286090265557180, 371286101387460075, 371286112507432595, 371286122265911874, 371286122266228979, 371286120592112562, 371286120520156695, 371286128965390084, 371286133920026263]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362525686780329822, 362525688259134461⟩, ⟨(-426719736591142221), (-426708924749237361)⟩, true⟩

def words09 : List Nat := [371286137289533773, 371286140658522869, 371286150796450149, 371286157830467575, 371286165384011599, 371286172936273683, 371286179429740125, 371286179430057823, 371286178173108683, 371286181831512090]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk107
