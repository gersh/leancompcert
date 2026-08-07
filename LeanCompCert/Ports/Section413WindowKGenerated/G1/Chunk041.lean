import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk041

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362753060664876991, 362753060859043008⟩, ⟨(-1124121260131914267), (-1124120720340855093)⟩, true⟩

def state01 : KState := ⟨⟨362427119997511894, 362427120192676952⟩, ⟨213808583615360858, 213809127507616820⟩, true⟩

def words00 : List Nat := [371279017848205552, 371279036253105463, 371279083380002667, 371279130483997512, 371279194466613221, 371279194466723794, 371279179719949267, 371279159595697669, 371279141878075998, 371279141878201920]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492057827961806, 362492058024126035⟩, ⟨(-52187477929050801), (-52186929925101709)⟩, true⟩

def words01 : List Nat := [371279175683678111, 371279222120873959, 371279268934046536, 371279275150085781, 371279298410169960, 371279321659009594, 371279384374730799, 371279388218157644, 371279391293436526, 371279394367264812]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362580674832509355, 362580675029669616⟩, ⟨(-417971676566901059), (-417971124454184571)⟩, true⟩

def words02 : List Nat := [371279435154104363, 371279446984967402, 371279474165093349, 371279501332083131, 371279510755244804, 371279510755355854, 371279442284612465, 371279432449508315, 371279471367457329, 371279495866160978]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362661495299182391, 362661495497356908⟩, ⟨(-751811359609358841), (-751810803302603385)⟩, true⟩

def words03 : List Nat := [371279513206008049, 371279530537499149, 371279606336104272, 371279661576871823, 371279733879943049, 371279806148103737, 371279869240139473, 371279869240250956, 371279898684827412, 371279942538336719]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362435162377247770, 362435162576418066⟩, ⟨187003711400694380, 187004271835138274⟩, true⟩

def words04 : List Nat := [371280024278559381, 371280049839220383, 371280074715650570, 371280099580118181, 371280141581894852, 371280154991602851, 371280177818273517, 371280200633983963, 371280223846624073, 371280223846739787]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362899768450089247, 362899768650274527⟩, ⟨(-1744083643171617786), (-1744083078519883576)⟩, true⟩

def words05 : List Nat := [371280224201994477, 371280235407428612, 371280304499548363, 371280313953936477, 371280314719684538, 371280315485097547, 371280374093799658, 371280417104381745, 371280517910118221, 371280618667453118]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454836658722655, 362454836859918467⟩, ⟨108583340249672604, 108583909110513242⟩, true⟩

def words06 : List Nat := [371280719584549997, 371280743802106750, 371280807145340999, 371280870458214191, 371280926784286038, 371280926784398193, 371280906597000483, 371280887082103892, 371280876166531916, 371280876166659598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362250608130582482, 362250608332792722⟩, ⟨962197685730921287, 962198258827068461⟩, true⟩

def words07 : List Nat := [371280903704584576, 371280937469306320, 371280970589181844, 371280970589294318, 371280927521526731, 371280899615534766, 371280901083736945, 371280901083849464, 371280854386465879, 371280799303803983]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362586131547423959, 362586131750644279⟩, ⟨(-441376290874857095), (-441375713551355193)⟩, true⟩

def words08 : List Nat := [371280744247441980, 371280731694153222, 371280705870846222, 371280714520104840, 371280717266930457, 371280717267045896, 371280711453421321, 371280730932000535, 371280791484763303, 371280816619756340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362330393265159705, 362330393469414623⟩, ⟨632007748326466816, 632008329990137664⟩, true⟩

def words09 : List Nat := [371280830593051899, 371280844559721045, 371280880489372030, 371280887847692491, 371280911996275765, 371280936133393289, 371280959427879193, 371280959427992490, 371280907479747898, 371280871643221799]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk041
