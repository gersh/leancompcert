import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835A

def state06 : KState := ⟨⟨360553358925661159, 360553404558394614⟩, ⟨2423680824400583484, 2426255951934198598⟩, true⟩

def words05 : List Nat := [360582442200442929, 360582442211479401, 360582442212547242, 360582442151815424, 360582441947979463, 360582441659977444, 360582441371608931, 360582441226575700, 360582440997895359, 360582440651644186]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591292490217828, 360591338134262509⟩, ⟨(-746211074015869342), (-743635001260584792)⟩, true⟩

def words06 : List Nat := [360582440305129433, 360582440102063626, 360582440012124850, 360582440039417351, 360582440040534366, 360582439946094174, 360582439889155348, 360582439815335284, 360582439784316361, 360582439892034218]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594463817777644, 360594509473259398⟩, ⟨(-1011318421265614662), (-1008741392658235542)⟩, true⟩

def words07 : List Nat := [360582439919510061, 360582439947119245, 360582439970780974, 360582440066965900, 360582440125293230, 360582440183814548, 360582440184887838, 360582440154531267, 360582440299904875, 360582440445697414]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580121040847811, 360580166707616761⟩, ⟨187506242418809368, 190084214466719448⟩, true⟩

def words08 : List Nat := [360582440603942937, 360582440719720433, 360582440740046301, 360582440760491881, 360582440761495480, 360582440756981245, 360582440787104432, 360582440817439790, 360582440818518405, 360582440714249932]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617587496036863, 360617633174122143⟩, ⟨(-2944504703626984696), (-2941925785591009350)⟩, true⟩

def words09 : List Nat := [360582440803807766, 360582440920933270, 360582441157982869, 360582441402588403, 360582441525320219, 360582441648142344, 360582441913709040, 360582442251126366, 360582442673040356, 360582443095228458]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835B
