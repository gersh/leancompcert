import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk146

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362529375422529488, 362529378197871117⟩, ⟨(-668666307112686764), (-668638895751957808)⟩, true⟩

def state01 : KState := ⟨⟨362454630665119831, 362454633444439261⟩, ⟨422950844840395939, 422978314297681609⟩, true⟩

def words00 : List Nat := [371283587237823353, 371283587238271495, 371283588780394403, 371283591012500306, 371283593654272366, 371283593654713128, 371283591017043922, 371283588281699045, 371283585546546789, 371283584732207754]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362376952276233913, 362376955059522087⟩, ⟨1558537143899661499, 1558564671360050461⟩, true⟩

def words01 : List Nat := [371283584172693247, 371283585594632104, 371283586991565604, 371283586992006590, 371283582166408534, 371283578091298262, 371283574016500660, 371283573778674993, 371283567321931551, 371283560030203350]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476050921056477, 362476053708300701⟩, ⟨109188261634007713, 109215846951812025⟩, true⟩

def words02 : List Nat := [371283552739280327, 371283550110512885, 371283545161736917, 371283542135663992, 371283539109867396, 371283535651692707, 371283526806107475, 371283522619920208, 371283518905846446, 371283518906315179]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362509571176736108, 362509573968005843⟩, ⟨(-381304729801073276), (-381277085569663388)⟩, true⟩

def words03 : List Nat := [371283518396414244, 371283517860207805, 371283521442563412, 371283523322814340, 371283526651790534, 371283529980476294, 371283531543741385, 371283531544185453, 371283530450679754, 371283532230039198]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362437539099221916, 362437541894425486⟩, ⟨673620842276729294, 673648544120422132⟩, true⟩

def words04 : List Nat := [371283536416869841, 371283536417311923, 371283534404013356, 371283532444927883, 371283530485937764, 371283529044245599, 371283525289609528, 371283525161571734, 371283525033399887, 371283524730201625]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362535108639677434, 362535111438883025⟩, ⟨(-756451666348450646), (-756423905855172942)⟩, true⟩

def words05 : List Nat := [371283521591963457, 371283519042813146, 371283518588286533, 371283518588730076, 371283515989079419, 371283512618983711, 371283510521891493, 371283510522386976, 371283513627622893, 371283517147507596]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362429651599984311, 362429654403184062⟩, ⟨789750268238851359, 789778087306796503⟩, true⟩

def words06 : List Nat := [371283520686436121, 371283520686878810, 371283518041688273, 371283516924607545, 371283515807460734, 371283514814890243, 371283507641436793, 371283500439823265, 371283493239015504, 371283490673620790]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362402309702054646, 362402312509253228⟩, ⟨1191318103545162258, 1191345981296318556⟩, true⟩

def words07 : List Nat := [371283487004352019, 371283486238486112, 371283485472562157, 371283484487196084, 371283480867789161, 371283478504782966, 371283476874979233, 371283476875422642, 371283472395753669, 371283466867652160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488320265808234, 362488323076978906⟩, ⟨(-71593514945936943), (-71565578864565961)⟩, true⟩

def words08 : List Nat := [371283461340104020, 371283459690209925, 371283456415169570, 371283457090677433, 371283457091023100, 371283456294917042, 371283451670509847, 371283450410228127, 371283451355696475, 371283451687770237]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474753056800848, 362474755872012978⟩, ⟨127802472584533167, 127830468055292287⟩, true⟩

def words09 : List Nat := [371283451719900240, 371283451752170821, 371283453690399711, 371283453726355634, 371283455198184432, 371283456669989082, 371283457617590155, 371283457618034150, 371283452413268609, 371283451822220822]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk146
