import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360548159437647598, 360548171742167216⟩, ⟨1558294949171269776, 1558664972144754084⟩, true⟩

def state01 : KState := ⟨⟨360638648932289636, 360638661242547952⟩, ⟨(-2468932433177066022), (-2468562154802975156)⟩, true⟩

def words00 : List Nat := [360583197134721020, 360583196852512558, 360583197190199789, 360583197555956240, 360583197556523415, 360583197720010427, 360583198500282571, 360583199280697943, 360583200398179603, 360583201644812494]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605044916610108, 360605057232672350⟩, ⟨(-973081954004268049), (-972711417268959585)⟩, true⟩

def words01 : List Nat := [360583202565318723, 360583203485852705, 360583204394451802, 360583205554663544, 360583206476428031, 360583207398250390, 360583207889260409, 360583207889869123, 360583208368146257, 360583208859606405]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589022354791758, 360589034676583538⟩, ⟨(-259703161431934523), (-259332369589282467)⟩, true⟩

def words02 : List Nat := [360583209801545761, 360583210355643426, 360583210515550142, 360583210675509111, 360583210676021618, 360583210695945776, 360583210850982522, 360583211006125315, 360583211006667630, 360583211039800415]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360655947360171515, 360655959687709459⟩, ⟨(-3240175216326112079), (-3239804168577554181)⟩, true⟩

def words03 : List Nat := [360583211674548101, 360583212309451891, 360583213447601255, 360583214602740645, 360583215331387020, 360583216060049514, 360583217291966460, 360583218848920964, 360583220482574184, 360583222116290372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360636810209041454, 360636822542390469⟩, ⟨(-2387959631933649878), (-2387588325333323500)⟩, true⟩

def words04 : List Nat := [360583223339647765, 360583224060050228, 360583225283575067, 360583226507223994, 360583227491149679, 360583227972223627, 360583228176689645, 360583228381223686, 360583229088814098, 360583230292489607]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360554393801358259, 360554406140436573⟩, ⟨1284139490441978807, 1284511052311763339⟩, true⟩

def words05 : List Nat := [360583231404001409, 360583232515576920, 360583233374356249, 360583233730392132, 360583233730911986, 360583233674779463, 360583233728215070, 360583233728824346, 360583233336383790, 360583232690084504]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574425722329784, 360574438067165411⟩, ⟨391496163105232681, 391867981550260341⟩, true⟩

def words06 : List Nat := [360583232043679619, 360583231474567530, 360583231608941463, 360583231927906738, 360583231928468562, 360583231822029764, 360583231212858587, 360583230898710088, 360583230584399520, 360583230258808900]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577129244130965, 360577141594771628⟩, ⟨270950153224575664, 271322230427861950⟩, true⟩

def words07 : List Nat := [360583230062089265, 360583229591520063, 360583229120851825, 360583228925676635, 360583228926187356, 360583228914341514, 360583228902427268, 360583228556473534, 360583227917915949, 360583227782084950]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579855469118502, 360579867825507032⟩, ⟨149266596400696072, 149638929872194014⟩, true⟩

def words08 : List Nat := [360583227907210144, 360583227907819717, 360583227667321359, 360583226960569272, 360583226253749797, 360583225302011156, 360583224600195991, 360583224400849701, 360583224201445776, 360583223710904480]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585276052197299, 360585288414337102⟩, ⟨(-92543089753715147), (-92170499803799937)⟩, true⟩

def words09 : List Nat := [360583223636139901, 360583223509726543, 360583223474135044, 360583223494946556, 360583223495514059, 360583223084860945, 360583222674118804, 360583222092147897, 360583221810570492, 360583221857537842]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445
