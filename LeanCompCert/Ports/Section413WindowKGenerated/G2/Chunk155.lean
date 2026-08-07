import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk155

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360670826840745791, 360670828203180757⟩, ⟨(-1400184508345057998), (-1400170210027815988)⟩, true⟩

def state01 : KState := ⟨⟨360587543902186555, 360587545266472830⟩, ⟨(-109285058606117276), (-109270731584465166)⟩, true⟩

def words00 : List Nat := [360580504193796530, 360580506252618993, 360580510501850540, 360580514750591446, 360580516138671920, 360580516138866468, 360580513392171497, 360580508569947257, 360580503748308577, 360580500541336832]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360449441831138203, 360449443197257402⟩, ⟨2033808955332924230, 2033823310792689086⟩, true⟩

def words01 : List Nat := [360580505140940010, 360580509739990574, 360580512240085624, 360580512240280272, 360580510609229493, 360580506963627218, 360580503318436347, 360580502202861953, 360580496957658616, 360580488513674457]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360541855090938233, 360541856458896067⟩, ⟨598756041007649957, 598770425012006385⟩, true⟩

def words02 : List Nat := [360580480070736082, 360580470081879585, 360580462630486547, 360580455948918459, 360580449268198013, 360580438717987088, 360580428302295810, 360580422025607386, 360580415749670748, 360580412184911007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360479403110106026, 360479404479922481⟩, ⟨1568805232410666740, 1568819645288531122⟩, true⟩

def words03 : List Nat := [360580409702583558, 360580404805954780, 360580399909920788, 360580394774257485, 360580391732885140, 360580386311675793, 360580380891143029, 360580373377542155, 360580364621616352, 360580358125050444]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360460459102157312, 360460460473809514⟩, ⟨1863400282194576478, 1863414723609236898⟩, true⟩

def words04 : List Nat := [360580351629252773, 360580349264371199, 360580345268606180, 360580337961959437, 360580330656220832, 360580322272270939, 360580315994855340, 360580309565119072, 360580303136187463, 360580294218093067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360678872705648167, 360678874079141910⟩, ⟨(-1534075530545066984), (-1534061060485153272)⟩, true⟩

def words05 : List Nat := [360580286512396478, 360580282932494338, 360580279352993717, 360580280222052794, 360580280222233169, 360580277793495392, 360580275482463778, 360580277699805901, 360580284036492245, 360580290372408079]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360646087721877337, 360646089097235274⟩, ⟨(-1024430412533146000), (-1024415913457362188)⟩, true⟩

def words06 : List Nat := [360580293328138720, 360580294103538949, 360580297738887389, 360580301373825561, 360580302366874661, 360580302367070172, 360580301029668852, 360580297608921178, 360580294882915956, 360580299108573187]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360508127832539628, 360508129209738930⟩, ⟨1124572729625850520, 1124587257380853196⟩, true⟩

def words07 : List Nat := [360580305204496718, 360580311299674921, 360580314833277692, 360580317322786438, 360580317322953118, 360580316748091801, 360580317787588313, 360580317787783897, 360580315309887959, 360580310676836546]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360532925330938756, 360532926709986714⟩, ⟨738785622800214855, 738800179366523167⟩, true⟩

def words08 : List Nat := [360580306044335418, 360580308242083771, 360580315070961223, 360580321898999612, 360580325249174268, 360580325249369922, 360580324510030742, 360580322346529852, 360580320183250826, 360580316073640757]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546635012079377, 360546636392991267⟩, ⟨524951570700399865, 524966156334841647⟩, true⟩

def words09 : List Nat := [360580313034281902, 360580307915859948, 360580302798057365, 360580300042553237, 360580299862034697, 360580298611318761, 360580297360740170, 360580294058651489, 360580290226752309, 360580288069679398]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk155
