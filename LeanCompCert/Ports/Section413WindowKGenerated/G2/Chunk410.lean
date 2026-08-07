import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk410

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566664743221222, 360566675118363760⟩, ⟨643251954724432493, 643539446985396889⟩, true⟩

def state01 : KState := ⟨⟨360595138064097983, 360595148444542969⟩, ⟨(-524436099401686174), (-524148389714811596)⟩, true⟩

def words00 : List Nat := [360582370820110594, 360582370101547302, 360582369501316339, 360582369356427152, 360582369211390536, 360582368785898080, 360582368607433478, 360582368130732032, 360582367653944297, 360582367766439173]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360545066739846358, 360545077125540287⟩, ⟨1529372344134634851, 1529660269107175749⟩, true⟩

def words01 : List Nat := [360582368671663917, 360582369576951054, 360582370029895504, 360582370030452337, 360582369891517165, 360582369427768203, 360582369092581407, 360582369093138298, 360582368630576011, 360582367722056796]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575825722266962, 360575836113216826⟩, ⟨267426766725187485, 267714907321959473⟩, true⟩

def words02 : List Nat := [360582366813448232, 360582365799248914, 360582365162108279, 360582365118006218, 360582365073863465, 360582364509672757, 360582363524798320, 360582362526099005, 360582361527282506, 360582360970816679]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590581611955519, 360590592008211258⟩, ⟨(-338159588113205581), (-337871229790293799)⟩, true⟩

def words03 : List Nat := [360582360812295082, 360582360264255836, 360582359716136216, 360582359771423774, 360582359771890439, 360582359770046213, 360582359768141321, 360582359468538480, 360582359277797701, 360582359479038229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557085871804877, 360557096273312184⟩, ⟨1036442550027294747, 1036731123901577375⟩, true⟩

def words04 : List Nat := [360582359479502042, 360582359148666677, 360582358226637457, 360582357007121890, 360582355787574523, 360582354416523128, 360582353342439990, 360582352860643805, 360582352378805333, 360582351599107594]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360612526626563819, 360612537033332735⟩, ⟨(-1239681427601352018), (-1239392637712208816)⟩, true⟩

def words05 : List Nat := [360582350984340014, 360582350961801585, 360582351332002011, 360582351555561508, 360582351556086465, 360582351141540644, 360582350903719233, 360582351381466895, 360582352117078343, 360582352852779115]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577656688836969, 360577667100920460⟩, ⟨192159264434890964, 192448272566443898⟩, true⟩

def words06 : List Nat := [360582353290991554, 360582353772786240, 360582354345325829, 360582354917998394, 360582355225092331, 360582355225649986, 360582354942347056, 360582354286428590, 360582353630443281, 360582352960978080]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582355438834460, 360582365856173252⟩, ⟨(-814110577462113), (-524886585093793)⟩, true⟩

def words07 : List Nat := [360582353142264145, 360582353437735601, 360582353438232538, 360582353436622426, 360582353350508623, 360582352963457716, 360582352779801296, 360582353077604458, 360582353078412473, 360582353079303529]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618603439854836, 360618613862462152⟩, ⟨(-1490052835121160921), (-1489763394671258755)⟩, true⟩

def words08 : List Nat := [360582353671156746, 360582354649796703, 360582355614767724, 360582356579790667, 360582356972318353, 360582356972876187, 360582357034796849, 360582357294825145, 360582357755895989, 360582358638820205]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583834265765311, 360583844693684518⟩, ⟨(-61211489061396844), (-60921830319539286)⟩, true⟩

def words09 : List Nat := [360582359224943520, 360582359811099152, 360582360348744551, 360582361186191681, 360582361872246020, 360582362558361621, 360582362760786042, 360582362761344134, 360582362410071434, 360582362446772776]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk410
