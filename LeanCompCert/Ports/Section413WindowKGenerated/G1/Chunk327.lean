import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk327

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469149218915205, 362469164142588385⟩, ⟨509266937192823383, 509596774749527047⟩, true⟩

def state01 : KState := ⟨⟨362459004051550541, 362459018984630094⟩, ⟨841095062087356158, 841425207280098086⟩, true⟩

def words00 : List Nat := [371284747981515462, 371284747982570808, 371284747193859880, 371284746214388806, 371284745234540093, 371284744475913813, 371284743350710998, 371284743158887927, 371284742966721671, 371284742775742296]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362522854538219356, 362522869480860082⟩, ⟨(-1247848231420050554), (-1247517773433242208)⟩, true⟩

def words01 : List Nat := [371284741990075676, 371284741593806976, 371284741732050694, 371284741733113397, 371284741431145763, 371284740979860301, 371284741008218601, 371284741242339830, 371284742408345267, 371284743574762065]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471761374167581, 362471776326325573⟩, ⟨424096149300756714, 424426918741697110⟩, true⟩

def words02 : List Nat := [371284744729380929, 371284744730436991, 371284745320026832, 371284745999889122, 371284746432823113, 371284746433879230, 371284745623632988, 371284744814657204, 371284744005294075, 371284743845993820]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362454405246634568, 362454420208310937⟩, ⟨992426922390142275, 992758003415496901⟩, true⟩

def words03 : List Nat := [371284743865441563, 371284744281487550, 371284744696536236, 371284744697597605, 371284744225493820, 371284744039100434, 371284744352996727, 371284744354053203, 371284743613573919, 371284742688561869]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477551209433087, 362477566180562698⟩, ⟨234600738770586074, 234932129344012376⟩, true⟩

def words04 : List Nat := [371284741763148195, 371284741541362009, 371284741176588128, 371284741399721813, 371284741400540428, 371284741348852571, 371284740523571382, 371284739932701366, 371284739679600231, 371284739680695340]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467188112611928, 362467203093414065⟩, ⟨574098845165039329, 574430552559505439⟩, true⟩

def words05 : List Nat := [371284739462462551, 371284739238904203, 371284739177875693, 371284739179040170, 371284738972146463, 371284739012155237, 371284739012946195, 371284738993041868, 371284738137464298, 371284737603565455]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362438011058695688, 362438026048902924⟩, ⟨1530159818928518000, 1530491834483399938⟩, true⟩

def words06 : List Nat := [371284737423519163, 371284737424576474, 371284736539530782, 371284735549212297, 371284734558559920, 371284733853755063, 371284732748800007, 371284731930167565, 371284731111226716, 371284730102442241]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500417085253535, 362500432085012518⟩, ⟨(-515192997589220802), (-514860668974610110)⟩, true⟩

def words07 : List Nat := [371284728677996415, 371284728183247205, 371284727804047083, 371284727805123171, 371284727150139025, 371284726323216982, 371284725503452503, 371284725504629469, 371284725535047817, 371284726015369292]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491721517964204, 362491736527273213⟩, ⟨(-230238719005321176), (-229906077291435374)⟩, true⟩

def words08 : List Nat := [371284726267760838, 371284726268819458, 371284725567212024, 371284725681580927, 371284726043070960, 371284726044134215, 371284725565539787, 371284725087051969, 371284725056799317, 371284725271828383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472488735335292, 362472503754183265⟩, ⟨400551146272475023, 400884100817044197⟩, true⟩

def words09 : List Nat := [371284725934435397, 371284726597435954, 371284727144733699, 371284727145794370, 371284726732754064, 371284726353352492, 371284726520736741, 371284726521797581, 371284726201857883, 371284725830427688]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk327
