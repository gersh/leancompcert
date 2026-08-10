import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk834A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570280818017243, 360570326269459759⟩, ⟨1006665590922071377, 1009225584291261715⟩, true⟩

def state01 : KState := ⟨⟨360590295200603193, 360590340663308814⟩, ⟨(-662619829537670445), (-660058896768624089)⟩, true⟩

def words00 : List Nat := [360582427151522905, 360582427204500114, 360582427205576987, 360582427187788463, 360582427169821570, 360582427054141296, 360582427108445225, 360582427208138656, 360582427235658598, 360582427331772583]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594795111928670, 360594840585939096⟩, ⟨(-1037969611891997254), (-1035407736133264290)⟩, true⟩

def words01 : List Nat := [360582427543688876, 360582427755987063, 360582427990161549, 360582428111977902, 360582428113081722, 360582428108023158, 360582428240087515, 360582428450552031, 360582428600329820, 360582428750356530]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597593727389118, 360597639212808884⟩, ⟨(-1271547057607984088), (-1268984230028124332)⟩, true⟩

def words02 : List Nat := [360582428791939411, 360582428793136466, 360582428824040015, 360582428912131030, 360582428931748273, 360582428998216396, 360582428999282603, 360582428993733909, 360582429044462632, 360582429228150567]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577854151930037, 360577899648636971⟩, ⟨375486617478255996, 378050386802446978⟩, true⟩

def words03 : List Nat := [360582429554984738, 360582429882040501, 360582430085229695, 360582430247063630, 360582430275694875, 360582430304638822, 360582430476767832, 360582430505811289, 360582430506887948, 360582430453847931]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603184033767057, 360603229541769578⟩, ⟨(-1738133904401033021), (-1735569192516403849)⟩, true⟩

def words04 : List Nat := [360582430466913198, 360582430606362601, 360582430888977363, 360582431171816529, 360582431332361493, 360582431471026280, 360582431541748880, 360582431612814989, 360582431827017562, 360582432077478960]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk834A
