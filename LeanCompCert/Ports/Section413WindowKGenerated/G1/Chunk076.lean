import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk076

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362391677666138301, 362391678374409215⟩, ⟨704278919773623678, 704282564934995654⟩, true⟩

def state01 : KState := ⟨⟨362459269840741454, 362459270550954440⟩, ⟨190740975554025505, 190744635485300639⟩, true⟩

def words00 : List Nat := [371284334941448275, 371284331631484888, 371284329940834733, 371284337720631916, 371284343897510596, 371284343897727535, 371284327542231444, 371284327984215430, 371284335548822657, 371284335549047121]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489340170395326, 362489340882585939⟩, ⟨(-38182170433464281), (-38178495442541103)⟩, true⟩

def words01 : List Nat := [371284332255950348, 371284327260010822, 371284328947814537, 371284328948055946, 371284332665043288, 371284337090638691, 371284341455320429, 371284341455538662, 371284330581081093, 371284331238780331]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451118217428140, 362451118931556903⟩, ⟨253388896481781582, 253392586251554758⟩, true⟩

def words02 : List Nat := [371284349061208741, 371284349061426302, 371284347955290661, 371284341010647459, 371284334067741768, 371284331291254781, 371284324058801009, 371284326533500948, 371284328968844500, 371284328969073490]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362618834321745860, 362618835037846091⟩, ⟨(-1027239477454251066), (-1027235772632242518)⟩, true⟩

def words03 : List Nat := [371284331041634203, 371284337464617842, 371284354614047947, 371284356632425401, 371284356632594258, 371284356032064640, 371284361961524669, 371284362492270986, 371284380093537980, 371284397690295739]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362508523797263369, 362508524515335111⟩, ⟨(-184377200014866209), (-184373480120679653)⟩, true⟩

def words04 : List Nat := [371284415450931427, 371284415451149651, 371284422532044970, 371284434597369259, 371284447146869770, 371284447147088084, 371284436968562097, 371284426768950943, 371284423406571014, 371284426556882533]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362387017076317684, 362387017796356168⟩, ⟨746121847082066638, 746125582031966198⟩, true⟩

def words05 : List Nat := [371284436837088116, 371284447114690590, 371284457378708901, 371284457378927462, 371284448936824293, 371284445593715811, 371284446112859494, 371284446113081769, 371284435942350576, 371284423224819872]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362409576204626410, 362409576926623080⟩, ⟨573525598508984866, 573529348468716122⟩, true⟩

def words06 : List Nat := [371284410968564293, 371284410968804950, 371284408134160583, 371284413299479452, 371284414926356992, 371284414926575904, 371284393958028503, 371284374519047433, 371284355085023695, 371284352591351727]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362450483018512119, 362450483742509318⟩, ⟨259888728355556172, 259892493669473700⟩, true⟩

def words07 : List Nat := [371284342843677974, 371284333111261262, 371284330570117219, 371284330570358363, 371284332881686390, 371284336449019548, 371284339833415681, 371284339833636434, 371284328317527908, 371284323910955865]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362444336036820103, 362444336762773002⟩, ⟨307553268785445373, 307557049129308307⟩, true⟩

def words08 : List Nat := [371284331987509675, 371284331987729419, 371284327019700195, 371284322405887093, 371284317793193125, 371284315782453338, 371284316805576400, 371284325753026139, 371284331177257004, 371284331177484226]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362602340779671621, 362602341507611859⟩, ⟨(-908381699398834367), (-908377903762379113)⟩, true⟩

def words09 : List Nat := [371284337645008853, 371284349309768185, 371284367109215318, 371284367109435122, 371284362454696374, 371284356065554178, 371284356535891380, 371284356536133278, 371284370351028840, 371284385670219004]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk076
