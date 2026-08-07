import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk268

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362454890169062254, 362454900027409306⟩, ⟨812616966273198259, 812795575747056285⟩, true⟩

def state01 : KState := ⟨⟨362465602425570125, 362465612291543311⟩, ⟨525611875233831007, 525790689127876309⟩, true⟩

def words00 : List Nat := [371285227349261369, 371285227350207382, 371285227015626927, 371285227119051399, 371285227119710418, 371285227011784301, 371285225586542514, 371285224878828618, 371285224170723739, 371285224029295191]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488636849895986, 362488646723622123⟩, ⟨(-92010459795312544), (-91831438005116182)⟩, true⟩

def words01 : List Nat := [371285223298457805, 371285222545746345, 371285222429451425, 371285222482862606, 371285222874842952, 371285223267130654, 371285223380458887, 371285223381317733, 371285222731591457, 371285222860305874]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466836527844546, 362466846409154243⟩, ⟨492877663513981575, 493056888735052381⟩, true⟩

def words02 : List Nat := [371285224377968153, 371285224378820018, 371285224044844086, 371285223707127141, 371285223369088468, 371285223139010554, 371285222815548100, 371285223287367016, 371285223482023344, 371285223482905084]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362518802503959287, 362518812392994592⟩, ⟨(-901713438924138728), (-901534006387036572)⟩, true⟩

def words03 : List Nat := [371285222798574515, 371285222690397855, 371285223860540225, 371285223861392444, 371285223290907201, 371285222510953763, 371285222079347444, 371285222080312086, 371285223196554768, 371285224448939340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471918423983705, 362471928320700683⟩, ⟨356717254530023675, 356896893283060795⟩, true⟩

def words04 : List Nat := [371285225590685309, 371285225591537718, 371285225048054983, 371285225212775627, 371285225295199851, 371285225296053100, 371285223833420860, 371285222283495189, 371285220733327669, 371285220569984969]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362445798349378413, 362445808253777122⟩, ⟨1058279393234773661, 1058459238281337367⟩, true⟩

def words05 : List Nat := [371285220296980760, 371285220519347413, 371285220737911383, 371285220738764850, 371285219477941229, 371285218393775087, 371285217432632215, 371285217433489068, 371285216244123453, 371285214777912690]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362517370536762279, 362517380448794215⟩, ⟨(-864365080667733384), (-864185030553795036)⟩, true⟩

def words06 : List Nat := [371285213311438718, 371285213230628737, 371285213501742005, 371285214330448106, 371285215000883694, 371285215001753375, 371285215731028986, 371285216668601206, 371285218742270958, 371285219940046726]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499392207021153, 362499402126850095⟩, ⟨(-381224575821914022), (-381044316164374582)⟩, true⟩

def words07 : List Nat := [371285221091922881, 371285222244004627, 371285223513960101, 371285224090882666, 371285225003056516, 371285225915479504, 371285226697288073, 371285226698141629, 371285226369953626, 371285226898392658]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458924621119822, 362458934548544657⟩, ⟨706859086489294644, 707039550364564708⟩, true⟩

def words08 : List Nat := [371285228809669754, 371285228877696698, 371285228878341937, 371285228811784089, 371285229026728288, 371285229027668529, 371285228622144502, 371285228523215797, 371285228423999895, 371285228321336200]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362533019770859209, 362533029705997049⟩, ⟨(-1285836358818895680), (-1285655687502300096)⟩, true⟩

def words09 : List Nat := [371285227748995537, 371285228154857330, 371285229942732614, 371285230902039577, 371285231406252649, 371285231910700259, 371285233316980334, 371285234035945188, 371285235813316527, 371285237590926892]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk268
