import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578339455780742, 360578384680987999⟩, ⟨335029647978704581, 337570795953313029⟩, true⟩

def state01 : KState := ⟨⟨360593769404612123, 360593814641095128⟩, ⟨(-948805869991107215), (-946263783818914209)⟩, true⟩

def words00 : List Nat := [360582441974487649, 360582441986301068, 360582442191302402, 360582442396536721, 360582442475438791, 360582442476632202, 360582442489351077, 360582442568714455, 360582442643899507, 360582442781799856]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578049329782986, 360578094577633810⟩, ⟨359321622557889974, 361864654700765774⟩, true⟩

def words01 : List Nat := [360582442847059011, 360582442912446951, 360582442965893306, 360582443121768186, 360582443142722708, 360582443163882698, 360582443164946191, 360582443113639848, 360582442918050357, 360582442867163981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593631788320488, 360593677047428278⟩, ⟨(-937602687653325051), (-935058718650814097)⟩, true⟩

def words02 : List Nat := [360582442907925522, 360582442909119208, 360582442858206873, 360582442696342844, 360582442534289031, 360582442334630255, 360582442336037933, 360582442409591025, 360582442410654589, 360582442546837744]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590786196902831, 360590831467276346⟩, ⟨(-700683216998578212), (-698138310293124608)⟩, true⟩

def words03 : List Nat := [360582442827045689, 360582443107613497, 360582443532069344, 360582443812738748, 360582443974262008, 360582444135873413, 360582444187215277, 360582444311086479, 360582444412817135, 360582444514809496]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577610973443953, 360577656255196313⟩, ⟨396016505628608893, 398562359563471115⟩, true⟩

def words04 : List Nat := [360582444544134076, 360582444545328155, 360582444459064603, 360582444488903967, 360582444489903252, 360582444483326456, 360582444364612042, 360582444173668701, 360582443982495485, 360582443791046926]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk832A
