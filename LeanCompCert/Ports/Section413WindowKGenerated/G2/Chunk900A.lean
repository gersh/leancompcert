import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546609792078762, 360546663034772729⟩, ⟨3175740702632015018, 3178976548694957342⟩, true⟩

def state01 : KState := ⟨⟨360560785848345777, 360560839103259906⟩, ⟨1899830273181920007, 1903067219122682623⟩, true⟩

def words00 : List Nat := [360581984605012688, 360581984337182058, 360581984050168145, 360581983688493774, 360581983326615846, 360581982914862002, 360581982597678087, 360581982404055803, 360581982210307188, 360581981945378812]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571433877051016, 360571487144243432⟩, ⟨941284586706506399, 944522637876815761⟩, true⟩

def words01 : List Nat := [360581981711536836, 360581981601385885, 360581981490874844, 360581981311735232, 360581981009239139, 360581980585945470, 360581980162410942, 360581979862564309, 360581979623772403, 360581979508583322]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569111844102195, 360569165123661115⟩, ⟨1150264721451194641, 1153503885914320293⟩, true⟩

def words02 : List Nat := [360581979393186577, 360581979197489185, 360581979013068387, 360581978952317338, 360581978891218601, 360581978761534751, 360581978508502923, 360581978158385425, 360581977808026501, 360581977562691598]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570968323523571, 360571021615313096⟩, ⟨983165094953279935, 986405360599075381⟩, true⟩

def words03 : List Nat := [360581977421430159, 360581977403675690, 360581977385776370, 360581977306149899, 360581977259359151, 360581977133787081, 360581977007821750, 360581976984868440, 360581976926228323, 360581976805901714]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584902329196553, 360584955633267948⟩, ⟨(-271543079858507884), (-268301708293734624)⟩, true⟩

def words04 : List Nat := [360581976685303575, 360581976524907133, 360581976451292383, 360581976464362146, 360581976465575638, 360581976359204942, 360581976233516125, 360581976194767919, 360581976157092868, 360581976191526116]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk900A
