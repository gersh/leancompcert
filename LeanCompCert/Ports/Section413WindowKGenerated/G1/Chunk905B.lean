import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905A

def state06 : KState := ⟨⟨362502028676156250, 362502152833211975⟩, ⟨(-1549760524608728571), (-1542169009875197047)⟩, true⟩

def words05 : List Nat := [371285122312423276, 371285122446471228, 371285122690439397, 371285122809247146, 371285122907818639, 371285123007343460, 371285123217653385, 371285123387946975, 371285123578179842, 371285123769819619]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488755861722121, 362488880047241437⟩, ⟨(-347746365900474875), (-340152273351798431)⟩, true⟩

def words06 : List Nat := [371285123960122254, 371285123988731114, 371285124078620263, 371285124170098074, 371285124280576280, 371285124290648491, 371285124293035697, 371285124290882247, 371285124359927779, 371285124405001076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483965388621846, 362484089602644444⟩, ⟨86189495874018400, 93786170106121848⟩, true⟩

def words07 : List Nat := [371285124529806808, 371285124655857694, 371285124750384725, 371285124762140321, 371285124809879029, 371285124859269537, 371285125012407276, 371285125015568652, 371285125006496372, 371285124998649149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489098091406054, 362489222333680990⟩, ⟨(-378709528278273207), (-371110294803426833)⟩, true⟩

def words08 : List Nat := [371285125088911119, 371285125139484070, 371285125310512875, 371285125482870354, 371285125611457815, 371285125614619532, 371285125594885922, 371285125613023218, 371285125738125845, 371285125786619986]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491068060007889, 362491192331146309⟩, ⟨(-557173755313407576), (-549571906955919586)⟩, true⟩

def words09 : List Nat := [371285125834138691, 371285125882776585, 371285125999539876, 371285126074667576, 371285126185665461, 371285126297870399, 371285126394644144, 371285126397806533, 371285126412106574, 371285126483010462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905B
