import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk044

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361255798410775407, 361255798507411364⟩, ⟨(-2988544149748422336), (-2988543860989631396)⟩, true⟩

def state01 : KState := ⟨⟨360916901882190746, 360916901979294918⟩, ⟨(-1498226106137955292), (-1498225815316758576)⟩, true⟩

def words00 : List Nat := [360576863887218509, 360576968416150057, 360577042090221836, 360577115730856791, 360577175424116270, 360577184829995015, 360577184830039000, 360577162321753194, 360577168234267953, 360577245253990734]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360261843550672755, 360261843648240069⟩, ⟨1394461231973623383, 1394461524839672207⟩, true⟩

def words01 : List Nat := [360577328196733423, 360577411101894967, 360577467688213516, 360577474124062140, 360577474124103386, 360577466821531115, 360577459522251905, 360577449815903564, 360577404074719678, 360577332681009226]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360722027881783946, 360722027979816348⟩, ⟨(-640641556448255557), (-640641261524215133)⟩, true⟩

def words02 : List Nat := [360577261319585105, 360577262022939127, 360577334023156165, 360577405990840844, 360577431323045674, 360577431323094962, 360577406712947177, 360577400778758037, 360577413699511610, 360577446336502375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360421547313823941, 360421547412327668⟩, ⟨691161670780679239, 691161967795044595⟩, true⟩

def words03 : List Nat := [360577446336547108, 360577439401106027, 360577432468785137, 360577402203053164, 360577397829382314, 360577380017660319, 360577362213962247, 360577304417366457, 360577249590193288, 360577214522191417]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360487769303035941, 360487769402006404⟩, ⟨396270174309963380, 396270473398978816⟩, true⟩

def words04 : List Nat := [360577194541846933, 360577194541896455, 360577160101456588, 360577099780237513, 360577039486151992, 360576942435504316, 360576880488747414, 360576868565266449, 360576856647140235, 360576818946590445]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360802329067381355, 360802329166821261⟩, ⟨(-1004444336381340312), (-1004444035200964522)⟩, true⟩

def words05 : List Nat := [360576828853633679, 360576858753894510, 360576915242097383, 360576960293821183, 360576960293867675, 360576955745149273, 360576996431460860, 360577066992429368, 360577117499684520, 360577167984305914]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361071671586737218, 361071671686650787⟩, ⟨(-2208621364370677483), (-2208621061075391225)⟩, true⟩

def words06 : List Nat := [360577192847169869, 360577203239749859, 360577263277264383, 360577323287901209, 360577355420742758, 360577422886000879, 360577464828012863, 360577506751260071, 360577573015212699, 360577683527161771]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360305325558735262, 360305325659119247⟩, ⟨1221598381071407469, 1221598686471855035⟩, true⟩

def words07 : List Nat := [360577807520325045, 360577931458057171, 360578014556828735, 360578048829135134, 360578068131199053, 360578087424653191, 360578100496880920, 360578100496930816, 360578064816573401, 360578003937349572]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360653863449859988, 360653863550715973⟩, ⟨(-340642001596011614), (-340641694078667158)⟩, true⟩

def words08 : List Nat := [360577943085286031, 360577946179356374, 360578010070098976, 360578073932360267, 360578091488332642, 360578091488382682, 360578060419124503, 360578026942990134, 360577996803653407, 360578013696768374]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360675003137958967, 360675003239292654⟩, ⟨(-435234950799038519), (-435234641134436539)⟩, true⟩

def words09 : List Nat := [360578013696813438, 360578005326890096, 360578037563552253, 360578116837783206, 360578168581109558, 360578220301431626, 360578247002932603, 360578262932207130, 360578284430094120, 360578305918445190]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk044
