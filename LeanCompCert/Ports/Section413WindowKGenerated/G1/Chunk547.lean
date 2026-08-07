import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk547

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477220562842249, 362477264111021435⟩, ⟨415964209935875456, 417573412286104976⟩, true⟩

def state01 : KState := ⟨⟨362490467307589617, 362490510872222942⟩, ⟨(-308681825061495988), (-307071722585423634)⟩, true⟩

def words00 : List Nat := [371284897964678693, 371284897966725364, 371284898026185342, 371284898142697534, 371284898176235222, 371284898178079123, 371284897870931036, 371284897854996453, 371284898153766970, 371284898258258924]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490194336210500, 362490237917664243⟩, ⟨(-293677726681214324), (-292066703879328582)⟩, true⟩

def words01 : List Nat := [371284898361337552, 371284898465070855, 371284898901723355, 371284899221023611, 371284899618504418, 371284900016656596, 371284900379379690, 371284900381219273, 371284900439018833, 371284900538890476]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484084640505117, 362484128238336506⟩, ⟨40675590324241716, 42287509397482988⟩, true⟩

def words02 : List Nat := [371284900971304605, 371284900973144155, 371284900960848253, 371284900860414804, 371284900759308480, 371284900682924402, 371284900621016988, 371284900758223460, 371284900893273044, 371284900895186451]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495197688054303, 362495241302526562⟩, ⟨(-567585623158964115), (-565972793247620903)⟩, true⟩

def words03 : List Nat := [371284901158351697, 371284901436556502, 371284901854237233, 371284901856077312, 371284901829270137, 371284901721003270, 371284901797596749, 371284901819226027, 371284902009361732, 371284902200331725]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475013894467866, 362475057525519671⟩, ⟨537319087775380056, 538932825337031988⟩, true⟩

def words04 : List Nat := [371284902375256275, 371284902377096928, 371284902143972125, 371284902133348462, 371284902211091486, 371284902212933523, 371284901927492283, 371284901539017847, 371284901149826716, 371284901047443636]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481661854167867, 362481705501823646⟩, ⟨173379749131890430, 174994395843297602⟩, true⟩

def words05 : List Nat := [371284901022348657, 371284901177811060, 371284901333150398, 371284901335023169, 371284901213250602, 371284901165190903, 371284901274782985, 371284901276640444, 371284901219087639, 371284901162814211]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479656109933708, 362479699774086188⟩, ⟨283275908270202229, 284891458426057735⟩, true⟩

def words06 : List Nat := [371284901185758037, 371284901187786550, 371284901254013370, 371284901407807078, 371284901507887502, 371284901509728810, 371284901224541804, 371284901250100673, 371284901369011215, 371284901370917046]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488375020802588, 362488418701696026⟩, ⟨(-194282350304611992), (-192665883162806624)⟩, true⟩

def words07 : List Nat := [371284901277324100, 371284901184930943, 371284901330402593, 371284901438947506, 371284901563166404, 371284901688078147, 371284901816441945, 371284901818283762, 371284901615026244, 371284901681503573]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493356078471530, 362493399775780659⟩, ⟨(-467100691332066067), (-465483324852901259)⟩, true⟩

def words08 : List Nat := [371284901996368481, 371284902136822625, 371284902275587416, 371284902414980596, 371284902655622288, 371284902759939936, 371284903196266075, 371284903633308131, 371284904002294422, 371284904159258733]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511657896265915, 362511701610250126⟩, ⟨(-1469996512663847236), (-1468378232473819996)⟩, true⟩

def words09 : List Nat := [371284904402226274, 371284904646163454, 371284905182288466, 371284905275351163, 371284905343426009, 371284905412086655, 371284905736355380, 371284905894710542, 371284906384933605, 371284906875984806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk547
