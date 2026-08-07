import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk083

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362659867452932342, 362659868304900297⟩, ⟨(-1466787813249592247), (-1466783024867758929)⟩, true⟩

def state01 : KState := ⟨⟨362482258064059802, 362482258918185862⟩, ⟨8191875385217625, 8196681690558927⟩, true⟩

def words00 : List Nat := [371283190121418259, 371283199577089646, 371283216340614874, 371283233100228058, 371283249922527351, 371283249922766407, 371283247502575452, 371283244753613110, 371283245281534618, 371283245281806868]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362405404127866985, 362405404984151984⟩, ⟨647805919269799226, 647810743526556538⟩, true⟩

def words01 : List Nat := [371283259435372817, 371283273704285127, 371283285548378071, 371283285548617428, 371283278186473447, 371283275303633733, 371283283910308518, 371283283910547939, 371283276211613969, 371283266852364311]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362455285626311969, 362455286484744328⟩, ⟨232552340752187929, 232557182885901143⟩, true⟩

def words02 : List Nat := [371283259740535237, 371283259740799437, 371283257023050401, 371283255354201129, 371283253685683089, 371283248620047125, 371283228533667509, 371283215747440308, 371283204513649353, 371283204513902300]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477274493404799, 362477275354018215⟩, ⟨49359751859429068, 49364612172784746⟩, true⟩

def words03 : List Nat := [371283201162980176, 371283197911411888, 371283200751943592, 371283200752209943, 371283203376410783, 371283206925306889, 371283207328876712, 371283207329118242, 371283195081770353, 371283194372264353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362398213571122700, 362398214433876361⟩, ⟨709432573709354756, 709437451883477480⟩, true⟩

def words04 : List Nat := [371283203428006640, 371283203428246940, 371283197256831895, 371283190719602632, 371283184183842673, 371283182130953232, 371283176770212010, 371283178586129765, 371283178586311269, 371283177002964203]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516305630575319, 362516306495509254⟩, ⟨(-277325193932251220), (-277320297542081114)⟩, true⟩

def words05 : List Nat := [371283166829191107, 371283162609924061, 371283168405762662, 371283168406003152, 371283159408581809, 371283147699899325, 371283135993924397, 371283135637786182, 371283134210840164, 371283138178616289]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468108175928405, 362468109043034322⟩, ⟨125476125967890652, 125481040526958912⟩, true⟩

def words06 : List Nat := [371283141909266192, 371283141909507096, 371283132528380451, 371283134936467601, 371283137565069279, 371283137565310351, 371283124743250481, 371283112033736280, 371283100803871433, 371283100804148655]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362387728103919671, 362387728973197006⟩, ⟨799032930355733856, 799037863100688090⟩, true⟩

def words07 : List Nat := [371283104489425802, 371283109964411118, 371283115557245442, 371283115557486738, 371283105356292839, 371283098667273595, 371283099446892524, 371283099447133890, 371283090932959893, 371283079553519284]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362552155821914970, 362552156693354885⟩, ⟨(-579644724316817497), (-579639773438377023)⟩, true⟩

def words08 : List Nat := [371283068176690824, 371283062962123346, 371283054693079401, 371283056284169410, 371283057014985070, 371283057015230806, 371283049244525158, 371283052420092029, 371283069711765348, 371283077945477591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362535697171763664, 362535698045413290⟩, ⟨(-441646660575202408), (-441641691146363300)⟩, true⟩

def words09 : List Nat := [371283086308583876, 371283094669780273, 371283104391215814, 371283106990519594, 371283111076074911, 371283115160746552, 371283119215434380, 371283119215678661, 371283121653302924, 371283127911959373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk083
