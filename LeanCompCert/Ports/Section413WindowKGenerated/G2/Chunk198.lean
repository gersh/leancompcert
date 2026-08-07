import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360518267651071097, 360518269924614799⟩, ⟨1277970823176476623, 1278001288928193545⟩, true⟩

def state01 : KState := ⟨⟨360497155126145964, 360497157402078956⟩, ⟨1695939270386009548, 1695969783457932644⟩, true⟩

def words00 : List Nat := [360582812184752708, 360582811463239601, 360582808195299557, 360582802645366641, 360582797095953460, 360582789972148006, 360582784156787319, 360582779691917774, 360582775227473561, 360582769203364062]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360517649085235484, 360517651363562505⟩, ⟨1289692355024961927, 1289722915534726745⟩, true⟩

def words01 : List Nat := [360582764882143199, 360582760940254772, 360582756998688996, 360582755591927921, 360582751641393630, 360582745524515695, 360582739408210584, 360582732255645922, 360582726438507197, 360582723155466377]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360543078095222202, 360543080375966884⟩, ⟨785310852444385374, 785341460884133592⟩, true⟩

def words02 : List Nat := [360582719872720374, 360582715317944859, 360582711829506930, 360582709899309075, 360582707969235534, 360582704468869129, 360582699906915206, 360582694049415091, 360582688192457334, 360582684080499619]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360481680636330231, 360481682919471387⟩, ⟨2003020534390073256, 2003051190363772610⟩, true⟩

def words03 : List Nat := [360582682083648240, 360582680025718874, 360582677967970613, 360582673935035835, 360582668372014228, 360582662167499542, 360582655963533016, 360582651557226559, 360582648249636343, 360582643160921174]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580203557685624, 360580205843223912⟩, ⟨48033895555627473, 48064599100252305⟩, true⟩

def words04 : List Nat := [360582638072661483, 360582635512057030, 360582635524669057, 360582636794471046, 360582636794711713, 360582635662876706, 360582631995101693, 360582630026236227, 360582628057495310, 360582627233606797]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360507921989385940, 360507924277348352⟩, ⟨1483387901057691958, 1483418652733259560⟩, true⟩

def words05 : List Nat := [360582627111856089, 360582625380845214, 360582624443242105, 360582626496498190, 360582626597019098, 360582626697570198, 360582626697796750, 360582625529301087, 360582621827425477, 360582618066509141]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360537108514066435, 360537110804423835⟩, ⟨903508933948761913, 903539733200853191⟩, true⟩

def words06 : List Nat := [360582614305887766, 360582613067708181, 360582609296684791, 360582604238050723, 360582599179883551, 360582592824802502, 360582588981381055, 360582587659345662, 360582586337415645, 360582583362712756]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360521424099227430, 360521426391991888⟩, ⟨1215103792900396053, 1215134639992661907⟩, true⟩

def words07 : List Nat := [360582581074530840, 360582580252726682, 360582579430931896, 360582577411699611, 360582574380808826, 360582569163459629, 360582563946589106, 360582557793925990, 360582552939336588, 360582549864828542]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360472116205967999, 360472118501159342⟩, ⟨2195066513286318306, 2195097408636716628⟩, true⟩

def words08 : List Nat := [360582546790590805, 360582542285835788, 360582535254714328, 360582529782407040, 360582524310583142, 360582517386239100, 360582508977343175, 360582498599175744, 360582488222001593, 360582480361824839]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360420561384135988, 360420563681726048⟩, ⟨3221147491126581661, 3221178434199578979⟩, true⟩

def words09 : List Nat := [360582474813699603, 360582471781794376, 360582468750166583, 360582464128088756, 360582460246952403, 360582454951262440, 360582449656030513, 360582446128699964, 360582440078979418, 360582431944751153]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198
