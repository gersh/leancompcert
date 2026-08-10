import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk747A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578042974251826, 360578079124455717⟩, ⟨313496222002932310, 315320157942385668⟩, true⟩

def state01 : KState := ⟨⟨360577203428807552, 360577239589018272⟩, ⟨376146257382807636, 377970940882817726⟩, true⟩

def words00 : List Nat := [360582300222199950, 360582300194619558, 360582300063536090, 360582299818583200, 360582299573442736, 360582299249905850, 360582299016356834, 360582298961910695, 360582298907357669, 360582298763705501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596187164985332, 360596223335248700⟩, ⟨(-1042345838449284034), (-1040520403865542696)⟩, true⟩

def words01 : List Nat := [360582298696867826, 360582298554232379, 360582298446344236, 360582298447407590, 360582298304478798, 360582297991754383, 360582297678834794, 360582297552644952, 360582297739877719, 360582297927346430]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570693506793745, 360570729687179443⟩, ⟨862524002651707802, 864350193625520996⟩, true⟩

def words02 : List Nat := [360582298025087969, 360582298026151461, 360582297944862601, 360582297891763740, 360582297838396013, 360582297652996190, 360582297288561447, 360582296797825156, 360582296306898441, 360582295995136429]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555580412931791, 360555616603350845⟩, ⟨1992113554470717279, 1993940495286852715⟩, true⟩

def words03 : List Nat := [360582295865248344, 360582295890357278, 360582295891305824, 360582295805686976, 360582295758431703, 360582295666399833, 360582295574050420, 360582295535244206, 360582295317448455, 360582294961596589]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597394992025897, 360597431192488427⟩, ⟨(-1133348396136140729), (-1131520704622415219)⟩, true⟩

def words04 : List Nat := [360582294605513271, 360582294359130152, 360582294202616372, 360582294152754519, 360582294102827300, 360582293872973804, 360582293711467433, 360582293720813565, 360582293790648325, 360582293994262017]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk747A
