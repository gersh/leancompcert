import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk677

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491884474604001, 362491952316709747⟩, ⟨(-441590506850289688), (-438488509412706516)⟩, true⟩

def state01 : KState := ⟨⟨362479027477641220, 362479095340590598⟩, ⟨428835766137249599, 431939174791942499⟩, true⟩

def words00 : List Nat := [371285475574845415, 371285475577157173, 371285475384353057, 371285475387627537, 371285475398344988, 371285475400657036, 371285475144526086, 371285474888275348, 371285474631112287, 371285474592913622]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362462180323969355, 362462248207801698⟩, ⟨1569645106711653408, 1572749929454606314⟩, true⟩

def words01 : List Nat := [371285474500300669, 371285474440865034, 371285474380613316, 371285474321151942, 371285473970426717, 371285473664268802, 371285473356901127, 371285473194518375, 371285472853057984, 371285472512725718]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471789877091359, 362471857781610299⟩, ⟨918888104931776026, 921994328675920072⟩, true⟩

def words02 : List Nat := [371285472171353180, 371285472031625423, 371285471781908212, 371285471750910779, 371285471719266167, 371285471634387107, 371285471258306108, 371285470966231890, 371285470672928838, 371285470572525343]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472420650061210, 362472488575639859⟩, ⟨876200228393583967, 879307878619536371⟩, true⟩

def words03 : List Nat := [371285470373270990, 371285470167797264, 371285469971100004, 371285469973673286, 371285469890841422, 371285469825986340, 371285469760331710, 371285469675461774, 371285469394463833, 371285469205675577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462933523886199, 362463001470068492⟩, ⟨1518943822581865047, 1522052868605032077⟩, true⟩

def words04 : List Nat := [371285469041691436, 371285469044004745, 371285468781485552, 371285468521253106, 371285468260111483, 371285468017129203, 371285467694732811, 371285467542978816, 371285467390480632, 371285467195066353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489613649172267, 362489681616332248⟩, ⟨(-288783584832494367), (-285673117467551521)⟩, true⟩

def words05 : List Nat := [371285466865043003, 371285466753897598, 371285466641537325, 371285466620880878, 371285466374442257, 371285466094088622, 371285465812810855, 371285465750118177, 371285465658539372, 371285465723451867]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480138099962877, 362480206087979343⟩, ⟨353312543498108838, 356424424207307924⟩, true⟩

def words06 : List Nat := [371285465786703826, 371285465789024088, 371285465685926782, 371285465745121743, 371285465869542269, 371285465871858167, 371285465751397417, 371285465592602128, 371285465432855773, 371285465412521284]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470153994186448, 362470222003009231⟩, ⟨1030022891922525692, 1033136182783470526⟩, true⟩

def words07 : List Nat := [371285465336497527, 371285465325602364, 371285465313952984, 371285465270285255, 371285465077455574, 371285464952160071, 371285464915024223, 371285464917338706, 371285464718423131, 371285464496116099]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480894978125431, 362480963007693685⟩, ⟨301959756896705455, 305074453990859121⟩, true⟩

def words08 : List Nat := [371285464272837125, 371285464102183286, 371285463880384353, 371285463877008978, 371285463872890852, 371285463834798015, 371285463505966262, 371285463363614646, 371285463292271677, 371285463294668031]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475198528256241, 362475266578923879⟩, ⟨688151740921472626, 691267868448109636⟩, true⟩

def words09 : List Nat := [371285463230014055, 371285463147645272, 371285463091259781, 371285463093810727, 371285463013717310, 371285462929292701, 371285462844122356, 371285462762940673, 371285462417687745, 371285462270198925]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk677
