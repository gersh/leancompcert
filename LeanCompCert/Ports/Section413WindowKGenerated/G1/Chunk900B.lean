import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900A

def state06 : KState := ⟨⟨362484787955073069, 362484910692708134⟩, ⟨10382982897763328, 17846309257561994⟩, true⟩

def words05 : List Nat := [371285108795284893, 371285108767500742, 371285108830531075, 371285108864331293, 371285108907195997, 371285108951251115, 371285108971407552, 371285108974551204, 371285108851260253, 371285108852926406]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486679121158880, 362486801886824547⟩, ⟨(-159907125842704959), (-152441274901627491)⟩, true⟩

def words06 : List Nat := [371285108965345086, 371285108979461023, 371285108993048452, 371285109007732851, 371285109058860532, 371285109062333094, 371285109183597237, 371285109308167873, 371285109407997643, 371285109430041547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498624393005362, 362498747187116786⟩, ⟨(-1235834348380285485), (-1228365935187247039)⟩, true⟩

def words07 : List Nat := [371285109574150863, 371285109719955002, 371285109987243540, 371285110122042981, 371285110236947511, 371285110352855963, 371285110526926899, 371285110640850669, 371285110794383630, 371285110949339816]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487565640793193, 362487688463319719⟩, ⟨(-239673001793684063), (-232202028827547977)⟩, true⟩

def words08 : List Nat := [371285111103415909, 371285111111660919, 371285111140183963, 371285111170259518, 371285111225785046, 371285111228930603, 371285111145006206, 371285111062031448, 371285111014496697, 371285111046831640]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474577026050037, 362474699876812208⟩, ⟨930580402337442027, 938053919195999165⟩, true⟩

def words09 : List Nat := [371285111166057193, 371285111286528606, 371285111397580523, 371285111400724030, 371285111360937963, 371285111344451879, 371285111345201373, 371285111348351671, 371285111242114046, 371285111130077425]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk900B
