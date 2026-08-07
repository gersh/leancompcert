import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266

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

def state06 : KState := ⟨⟨360586801764542387, 360586805996103121⟩, ⟨(-112611612721908791), (-112535303357237469)⟩, true⟩

def words05 : List Nat := [360582587432126671, 360582588489798964, 360582589762203085, 360582589762553042, 360582589632127173, 360582588313587934, 360582586995074927, 360582585491918044, 360582584866582351, 360582585025270923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360534987866249202, 360534992101147527⟩, ⟨1268520476200976261, 1268596874562516919⟩, true⟩

def words06 : List Nat := [360582585025582947, 360582584477050705, 360582582526357427, 360582579989707787, 360582577453153507, 360582574554865394, 360582570725364011, 360582566195260931, 360582561665430724, 360582558538138998]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360400561847826803, 360400566086024318⟩, ⟨4854568212244637107, 4854644698611630453⟩, true⟩

def words07 : List Nat := [360582556754970833, 360582555993951154, 360582555232951289, 360582553485683338, 360582550337721563, 360582546134048418, 360582541930586733, 360582537216935320, 360582531103038400, 360582524283123705]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528000358766919, 360528004600270318⟩, ⟨1453922271019714714, 1453998845604327272⟩, true⟩

def words08 : List Nat := [360582517463640459, 360582512045671875, 360582507335379080, 360582504026308626, 360582500717455874, 360582496180104412, 360582491457126515, 360582488135086724, 360582484813194866, 360582481889352534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545143571269057, 360545147816114178⟩, ⟨996156006098787883, 996232669890496695⟩, true⟩

def words09 : List Nat := [360582479848634703, 360582476623287399, 360582473398114884, 360582471573084506, 360582470464557068, 360582468701568035, 360582466938674908, 360582464095097668, 360582461298237531, 360582459901128804]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk266
