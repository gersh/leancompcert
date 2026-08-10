import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589720175274729, 360589752511498878⟩, ⟨(-521156546454581941), (-519610148751006433)⟩, true⟩

def state01 : KState := ⟨⟨360570114981263784, 360570147326926269⟩, ⟨866968129067961825, 868515195053790411⟩, true⟩

def words00 : List Nat := [360582413742540349, 360582413797291049, 360582413798193555, 360582413752777039, 360582413707214720, 360582413483155408, 360582413359606904, 360582413192389227, 360582413025066755, 360582412758292655]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569629343101381, 360569661698252945⟩, ⟨901332720013265914, 902880457966507764⟩, true⟩

def words01 : List Nat := [360582412585894283, 360582412462689264, 360582412339165344, 360582412303802126, 360582412069205652, 360582411664684838, 360582411259984513, 360582410949133476, 360582410824679321, 360582410645696697]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569704188388868, 360569736553107047⟩, ⟨895969580526002244, 897517996034335510⟩, true⟩

def words02 : List Nat := [360582410466584275, 360582410156966941, 360582409781753166, 360582409605732255, 360582409429446105, 360582409202984688, 360582408981844863, 360582408661273210, 360582408340524223, 360582407991706996]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360534199763148202, 360534232137335934⟩, ⟨3411011411085781922, 3412560497369389866⟩, true⟩

def words03 : List Nat := [360582407813621824, 360582407798566572, 360582407783415846, 360582407613703917, 360582407295069975, 360582406893441832, 360582406491534375, 360582406148839109, 360582405607061126, 360582404928094960]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560266419148413, 360560298802802400⟩, ⟨1564353340231787934, 1565903097152852010⟩, true⟩

def words04 : List Nat := [360582404248893832, 360582403768791744, 360582403389015353, 360582403208221690, 360582403027355147, 360582402676823915, 360582402127173539, 360582401508526003, 360582400889589536, 360582400469664120]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk708A
