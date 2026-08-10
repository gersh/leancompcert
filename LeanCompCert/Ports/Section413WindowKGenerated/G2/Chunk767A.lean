import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589779063653717, 360589817255004582⟩, ⟨(-587476231495716573), (-585497771222223349)⟩, true⟩

def state01 : KState := ⟨⟨360570618188247681, 360570656390008664⟩, ⟨882097401359660090, 884076660141071604⟩, true⟩

def words00 : List Nat := [360582183747013277, 360582183738937663, 360582183561041059, 360582183339219075, 360582183117111600, 360582182779170689, 360582182445774252, 360582182025079988, 360582181604187332, 360582181310620593]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557155965191122, 360557194177266383⟩, ⟨1914891506694387076, 1916871556734877382⟩, true⟩

def words01 : List Nat := [360582181161267091, 360582181112936664, 360582181064509660, 360582180880442999, 360582180677030759, 360582180402434972, 360582180127514149, 360582180022435031, 360582179793193900, 360582179468673251]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576578391173688, 360576616613573906⟩, ⟨424710448791938056, 426691291012828012⟩, true⟩

def words02 : List Nat := [360582179143895858, 360582178877135460, 360582178711936732, 360582178674561978, 360582178637121582, 360582178442573961, 360582178213345592, 360582177943161462, 360582177672661634, 360582177558328407]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587932750496630, 360587970983318539⟩, ⟨(-446564935847834588), (-444583293920343204)⟩, true⟩

def words03 : List Nat := [360582177486830049, 360582177330523624, 360582177186173376, 360582177342820679, 360582177426517325, 360582177510397541, 360582177511372521, 360582177534642975, 360582177611026403, 360582177687767005]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566383982481482, 360566422225613832⟩, ⟨1207120403327400711, 1209102836531681897⟩, true⟩

def words04 : List Nat := [360582177704570725, 360582177705665000, 360582177553102566, 360582177314887319, 360582177076499652, 360582176795808923, 360582176599959933, 360582176431132315, 360582176262170855, 360582176008500239]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk767A
