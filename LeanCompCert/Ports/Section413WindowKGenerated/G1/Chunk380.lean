import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk380

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362533814641582855, 362533835046657502⟩, ⟨(-1857378143572447359), (-1856854146238577661)⟩, true⟩

def state01 : KState := ⟨⟨362493681464619714, 362493701880887854⟩, ⟨(-332247788430827931), (-331723365685547295)⟩, true⟩

def words00 : List Nat := [371284973010961647, 371284973349988316, 371284973885206180, 371284974421009611, 371284974994825244, 371284974996067519, 371284974795634207, 371284974518123102, 371284974613842279, 371284974844880237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468420641950206, 362468441069392976⟩, ⟨628215282570902014, 628740130118257094⟩, true⟩

def words01 : List Nat := [371284975767605311, 371284976690785642, 371284977612422603, 371284977710916797, 371284978019188475, 371284978328100426, 371284978920303819, 371284978921545746, 371284978592145848, 371284978158559685]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477235084708443, 362477255523257335⟩, ⟨293175992170405306, 293701262030168482⟩, true⟩

def words02 : List Nat := [371284977942006004, 371284977943374082, 371284978260939933, 371284978706894224, 371284979088379242, 371284979089621454, 371284978549763466, 371284978359169894, 371284978405537993, 371284978406823735]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362509304186232136, 362509324636127541⟩, ⟨(-926642355456785977), (-926116654031833695)⟩, true⟩

def words03 : List Nat := [371284978204700330, 371284977870728472, 371284977813326463, 371284977814707570, 371284977889234160, 371284978032487767, 371284978179814386, 371284978181095751, 371284978770907774, 371284979412446991]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499539232911308, 362499559693866644⟩, ⟨(-555067332439699009), (-554541210237740011)⟩, true⟩

def words04 : List Nat := [371284980667416747, 371284981179078093, 371284981679067654, 371284982179429649, 371284982715959200, 371284982970598211, 371284983915513300, 371284984860902931, 371284985679168864, 371284986063469605]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362523582304715784, 362523602776908774⟩, ⟨(-1469977008179693853), (-1469450458328869721)⟩, true⟩

def words05 : List Nat := [371284986907304528, 371284987751759850, 371284989286130449, 371284990012164518, 371284990587416739, 371284991163036492, 371284992239902332, 371284992972551004, 371284993987855179, 371284995003641418]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506901714463117, 362506922197881221⟩, ⟨(-835160246584233255), (-834633269449581135)⟩, true⟩

def words06 : List Nat := [371284996020021748, 371284996117253681, 371284996643802235, 371284997170987999, 371284997766122135, 371284997790208344, 371284997812934219, 371284997836068424, 371284998548708752, 371284999126003688]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464627865095573, 362464648359741449⟩, ⟨774494475816697452, 775021880448087208⟩, true⟩

def words07 : List Nat := [371285000050390718, 371285000975239863, 371285001718548972, 371285001719792895, 371285001573183075, 371285001603652016, 371285001891797870, 371285001893042128, 371285001358126121, 371285000825089351]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488289009666606, 362488309515439547⟩, ⟨(-126532811804554876), (-126004983397544360)⟩, true⟩

def words08 : List Nat := [371285000378498912, 371285000379878468, 371285000757157410, 371285001291428400, 371285001714816733, 371285001716061237, 371285001303671029, 371285001174824289, 371285001428469455, 371285001516610492]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486548782064197, 362486569299156471⟩, ⟨(-60213208271036888), (-59684948652764230)⟩, true⟩

def words09 : List Nat := [371285001603383670, 371285001690561297, 371285002125177129, 371285002309375322, 371285002646466226, 371285002984029958, 371285003250945951, 371285003252191379, 371285002763542774, 371285002806186398]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk380
