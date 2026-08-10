import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360629045232732990, 360629049444442690⟩, ⟨(-1233792892249618168), (-1233717111517894348)⟩, true⟩

def state01 : KState := ⟨⟨360552091636039128, 360552095851072121⟩, ⟨813421836471999278, 813497705620015262⟩, true⟩

def words00 : List Nat := [360582671879584120, 360582672006798068, 360582672924918149, 360582673843074593, 360582673908514303, 360582673908863737, 360582673099235557, 360582671211532108, 360582669323905971, 360582666978679037]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360480714095139071, 360480718313461971⟩, ⟨2713222263323496207, 2713298220032980537⟩, true⟩

def words01 : List Nat := [360582665830148087, 360582664388607259, 360582662947139616, 360582660801327418, 360582658703103692, 360582656242072582, 360582653781124469, 360582652192604498, 360582649197805544, 360582645369060506]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360534338124477162, 360534342346103957⟩, ⟨1285444923062911590, 1285520967738099502⟩, true⟩

def words02 : List Nat := [360582641540526792, 360582637676207602, 360582634923417031, 360582633151956132, 360582631380599917, 360582628371738049, 360582623957307525, 360582620949594275, 360582617941998533, 360582615758335955]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360514266983443750, 360514271208402744⟩, ⟨1820066015168605296, 1820142148596768010⟩, true⟩

def words03 : List Nat := [360582613945975097, 360582611037163580, 360582608128503814, 360582606625812092, 360582606030826743, 360582604464634249, 360582602898522801, 360582600454446422, 360582597427025009, 360582594862629350]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591179174335446, 360591183402593506⟩, ⟨(-229195617664931557), (-229119396333336165)⟩, true⟩

def words04 : List Nat := [360582592298306959, 360582591139211615, 360582590750549838, 360582589578518316, 360582588406517892, 360582586747502550, 360582586252660861, 360582586707704954, 360582586708025420, 360582586374476988]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266A
