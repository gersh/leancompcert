import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk186

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362526658206511010, 362526662809079074⟩, ⟨(-749914924177588289), (-749857020849390387)⟩, true⟩

def state01 : KState := ⟨⟨362474858868947279, 362474863476624827⟩, ⟨213799214218949680, 213857212610556146⟩, true⟩

def words00 : List Nat := [371286353074874075, 371286353075448065, 371286352735977539, 371286352301650019, 371286352131853174, 371286352132495833, 371286352563940551, 371286353784235839, 371286354997396246, 371286354997990252]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362541822348063432, 362541826960934430⟩, ⟨(-1032798158213392083), (-1032740063146073627)⟩, true⟩

def words01 : List Nat := [371286355979819111, 371286357579235067, 371286360343445581, 371286360344020116, 371286359842521092, 371286358705875799, 371286359317734203, 371286359960421701, 371286362939705782, 371286365918930990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460920004423027, 362460924622478466⟩, ⟨473851279996400219, 473909471624161559⟩, true⟩

def words02 : List Nat := [371286368878762196, 371286368879336798, 371286368593541086, 371286369189136197, 371286370495880299, 371286370496455070, 371286368473470770, 371286365896834801, 371286363320249822, 371286362597337520]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471309427044963, 362471314050276673⟩, ⟨280498187894761649, 280556475983219931⟩, true⟩

def words03 : List Nat := [371286362196123401, 371286363160402356, 371286364119125456, 371286364119714006, 371286363645969984, 371286363846418607, 371286366924719419, 371286366925294363, 371286366170230652, 371286365363365902]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473396573764758, 362473401202152013⟩, ⟨241724835226195799, 241783219439692205⟩, true⟩

def words04 : List Nat := [371286364912499325, 371286364913135349, 371286365910451212, 371286367645187203, 371286368636171103, 371286368636746399, 371286365798276049, 371286365073526465, 371286365449247265, 371286365449843150]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467939454472275, 362467944088090965⟩, ⟨343563925724494470, 343622407531177360⟩, true⟩

def words05 : List Nat := [371286364755176800, 371286364059520723, 371286364676793877, 371286364677427367, 371286364558936484, 371286364134450075, 371286363709807859, 371286363315182105, 371286359994322728, 371286359008108713]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464638945887450, 362464643584640405⟩, ⟨405460324669044686, 405518902307751626⟩, true⟩

def words06 : List Nat := [371286359903482767, 371286359941276933, 371286359978317823, 371286360015553457, 371286360929715352, 371286360930356973, 371286361997907105, 371286363270680294, 371286363932320168, 371286363932916129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362558355403214883, 362558360047178335⟩, ⟨(-1344699074957681555), (-1344640400012595185)⟩, true⟩

def words07 : List Nat := [371286364471763861, 371286366174053629, 371286370279296894, 371286370567848150, 371286370568298584, 371286370460393096, 371286372309124963, 371286373301662117, 371286377155733738, 371286381009652904]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362445921674694815, 362445926323865606⟩, ⟨755942158324639117, 756000930569354533⟩, true⟩

def words08 : List Nat := [371286384867677194, 371286384912109904, 371286385358491221, 371286385805114688, 371286386559781451, 371286386560358080, 371286383502948116, 371286380446020809, 371286377389181687, 371286375811857546]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362409175983711704, 362409180638068687⟩, ⟨1443248548019646182, 1443307417220731250⟩, true⟩

def words09 : List Nat := [371286374342672582, 371286375037757486, 371286375600612070, 371286375601191819, 371286373474273357, 371286372221055870, 371286370967675293, 371286370877156761, 371286366979856554, 371286362852893326]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk186
