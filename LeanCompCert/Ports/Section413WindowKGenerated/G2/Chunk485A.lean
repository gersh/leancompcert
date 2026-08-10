import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590237632477830, 360590252352429016⟩, ⟨(-391185811237412294), (-390703395895414856)⟩, true⟩

def state01 : KState := ⟨⟨360541940677842776, 360541955404169903⟩, ⟨1951188880252577135, 1951671604855781001⟩, true⟩

def words00 : List Nat := [360582196779003536, 360582196650813524, 360582196097178715, 360582195291811883, 360582194486301035, 360582193514287489, 360582192246620352, 360582190638831802, 360582189030981529, 360582187760485215]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360497190105417043, 360497204838025562⟩, ⟨4122364547573985493, 4122847576919306003⟩, true⟩

def words01 : List Nat := [360582186931680117, 360582186433169278, 360582185934606057, 360582185180360887, 360582184121055826, 360582182878884517, 360582181636575003, 360582180241851987, 360582178715132963, 360582176964507824]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360542664915648475, 360542679654560033⟩, ⟨1915667061338535977, 1916150396538995835⟩, true⟩

def words02 : List Nat := [360582175213807192, 360582173512620316, 360582172026229288, 360582170963369564, 360582169900490616, 360582168480364677, 360582166882857910, 360582165708897901, 360582164534786212, 360582163487169533]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555853802855378, 360555868548132235⟩, ⟨1275468320649367020, 1275951964790629304⟩, true⟩

def words03 : List Nat := [360582162674195206, 360582161532309138, 360582160390337670, 360582159671795478, 360582159167813764, 360582158404157630, 360582157640465434, 360582156661352711, 360582155697183786, 360582155156389150]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560150010428969, 360560164761997770⟩, ⟨1066915648010218317, 1067399597592846735⟩, true⟩

def words04 : List Nat := [360582154615395228, 360582154497650359, 360582154260321954, 360582153697144222, 360582153133890957, 360582152233553874, 360582151607426175, 360582151253877802, 360582150900270762, 360582150335583617]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485A
