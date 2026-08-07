import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk100

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362439131937343880, 362439133196204314⟩, ⟨454109518161339849, 454118041343282001⟩, true⟩

def state01 : KState := ⟨⟨362537175058448572, 362537176319932878⟩, ⟨(-526937400851649185), (-526928851417704607)⟩, true⟩

def words00 : List Nat := [371284544273728312, 371284544274050410, 371284545999960643, 371284548840805331, 371284548929584265, 371284548929877122, 371284535728585437, 371284532515641074, 371284536074724408, 371284541333276430]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475814915300718, 362475816179449289⟩, ⟨87711909324812667, 87720485441903781⟩, true⟩

def words01 : List Nat := [371284546028344748, 371284550722570897, 371284559170395736, 371284562702666279, 371284569170257006, 371284575636671981, 371284580245773455, 371284580246066851, 371284571592349282, 371284570718914549]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362397582958844880, 362397584225608249⟩, ⟨871921816234941556, 871930418565952626⟩, true⟩

def words02 : List Nat := [371284573941181983, 371284573941475543, 371284564787776004, 371284555518618751, 371284546251191307, 371284539858161035, 371284528469620040, 371284524504627076, 371284520540328572, 371284516470729481]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362558055055121225, 362558056324548196⟩, ⟨(-738681554861281633), (-738672925801077255)⟩, true⟩

def words03 : List Nat := [371284507804573942, 371284503086582505, 371284501917342084, 371284501917636264, 371284495220008614, 371284486366170492, 371284478584754751, 371284478585083925, 371284483323638058, 371284490651228699]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362364437196232052, 362364438468312048⟩, ⟨1205902954749925768, 1205911610460014244⟩, true⟩

def words04 : List Nat := [371284497883983973, 371284497884278197, 371284491921647388, 371284490599206912, 371284489276888622, 371284487117462029, 371284471774968159, 371284455596447838, 371284439421025517, 371284429673332945]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362316780621604286, 362316781896333605⟩, ⟨1685431733087039373, 1685440415436653273⟩, true⟩

def words05 : List Nat := [371284417735298309, 371284410788496046, 371284403842976394, 371284397034136907, 371284381544233138, 371284368983295536, 371284356424702216, 371284352271968421, 371284337360310289, 371284320705025122]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490239322621772, 362490240599990410⟩, ⟨(-60287523495850881), (-60278814581284389)⟩, true⟩

def words06 : List Nat := [371284304052923664, 371284297277125071, 371284287148932709, 371284283933546467, 371284280718704814, 371284274039762818, 371284259321221742, 371284254466960660, 371284254620083705, 371284255214767366]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472535984471813, 362472537264539341⟩, ⟨118107237188496917, 118115973294051803⟩, true⟩

def words07 : List Nat := [371284255601583581, 371284255988422291, 371284260299884387, 371284260796001944, 371284262989323230, 371284265182319689, 371284267280782726, 371284267281078020, 371284256281255279, 371284255119032799]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362331212944171863, 362331214226867015⟩, ⟨1543599746687596211, 1543608509293508199⟩, true⟩

def words08 : List Nat := [371284258657093424, 371284258657388798, 371284251314169654, 371284243885357733, 371284236457909338, 371284231970981903, 371284223018124264, 371284215108105508, 371284207199554276, 371284198221841595]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362576153972277652, 362576155257641384⟩, ⟨(-929011931947636936), (-929003142402267406)⟩, true⟩

def words09 : List Nat := [371284183061603068, 371284177716040645, 371284176837174505, 371284176837475185, 371284173518463222, 371284168822904732, 371284166331227718, 371284166331559259, 371284174748163595, 371284183854572157]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk100
