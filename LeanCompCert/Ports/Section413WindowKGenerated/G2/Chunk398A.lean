import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360625734034114003, 360625743787257233⟩, ⟨(-1721674877578591495), (-1721412516075310101)⟩, true⟩

def state01 : KState := ⟨⟨360604796552580564, 360604806310860641⟩, ⟨(-888286456508528418), (-888023890532938568)⟩, true⟩

def words00 : List Nat := [360582494075110968, 360582494862435811, 360582496077901910, 360582497293465185, 360582498196283146, 360582498919791159, 360582499325361572, 360582499730966072, 360582499756854240, 360582500317780012]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570411743412021, 360570421506770197⟩, ⟨480845540276727066, 481108308436832634⟩, true⟩

def words01 : List Nat := [360582501244180024, 360582502170636823, 360582502685099058, 360582502996600212, 360582503149302321, 360582503302155240, 360582503788495257, 360582503886208388, 360582503886690962, 360582503583827878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360627385745271003, 360627395513719448⟩, ⟨(-1788221938810054290), (-1787958967929758306)⟩, true⟩

def words02 : List Nat := [360582503606538614, 360582504248969631, 360582504874641754, 360582505500379336, 360582505550587253, 360582505551126558, 360582505025124058, 360582505076957347, 360582505757491879, 360582506885065140]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603641907245101, 360603651680828383⟩, ⟨(-842418463905845106), (-842155288479164486)⟩, true⟩

def words03 : List Nat := [360582507423336041, 360582507961636891, 360582508940019686, 360582510237456131, 360582511259197345, 360582512280975696, 360582512810645447, 360582512811184956, 360582513244257569, 360582513775442495]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360626845042061284, 360626854820724919⟩, ⟨(-1766924139905625968), (-1766660762052331948)⟩, true⟩

def words04 : List Nat := [360582514934942397, 360582516001477843, 360582516674893615, 360582517348338351, 360582517667760707, 360582518396756738, 360582519753944793, 360582521111169484, 360582522053238476, 360582523166260732]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398A
