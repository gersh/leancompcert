import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550066462752615, 360550092334418445⟩, ⟨2071716460247953971, 2072827992589630031⟩, true⟩

def state01 : KState := ⟨⟨360575755289529953, 360575781169624129⟩, ⟨437843933966204862, 438956002393133956⟩, true⟩

def words00 : List Nat := [360582683457805943, 360582683193297590, 360582683086931458, 360582682816356822, 360582682545644862, 360582682212824809, 360582682039582057, 360582682076972058, 360582682077786430, 360582681908539286]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360613599249777399, 360613625138311299⟩, ⟨(-1969649275972222920), (-1968536670652512332)⟩, true⟩

def words01 : List Nat := [360582681939223947, 360582682078662906, 360582682255478970, 360582682350707482, 360582682351532171, 360582682237627191, 360582682255615085, 360582682546073813, 360582683033162784, 360582683520439017]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606370685481992, 360606396582554031⟩, ⟨(-1509899167259245037), (-1508786018702363553)⟩, true⟩

def words02 : List Nat := [360582683884677461, 360582684175485007, 360582684401493683, 360582684627751518, 360582684787429388, 360582684814290090, 360582684815087075, 360582684700055381, 360582684715740393, 360582685089434289]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360548140501909544, 360548166407401699⟩, ⟨2195603558094071359, 2196717242465463025⟩, true⟩

def words03 : List Nat := [360582685433088932, 360582685776901025, 360582685996414494, 360582685997309123, 360582685970843878, 360582685727945554, 360582685484805095, 360582685235383372, 360582684818807867, 360582684277333589]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598030214833627, 360598056128775685⟩, ⟨(-979691203014638699), (-978576980849600757)⟩, true⟩

def words04 : List Nat := [360582683735673928, 360582683310718795, 360582683008688497, 360582682854234080, 360582682699699320, 360582682336404429, 360582681951773270, 360582681814083495, 360582681784078032, 360582682026548704]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636A
