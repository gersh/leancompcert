import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611946632076504, 360611964547118104⟩, ⟨(-1597965239960959313), (-1597320064555953943)⟩, true⟩

def state01 : KState := ⟨⟨360615497091170948, 360615515013243052⟩, ⟨(-1787397862533920292), (-1786752312366718570)⟩, true⟩

def words00 : List Nat := [360581996992416215, 360581997173339962, 360581997627028471, 360581998080916738, 360581998291519247, 360581998448499860, 360581998449164699, 360581998430409972, 360581998743175216, 360581999372711704]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583974029870926, 360583991958920070⟩, ⟨(-106608926359593918), (-105963004211652278)⟩, true⟩

def words01 : List Nat := [360582000260580906, 360582001148573409, 360582001811146687, 360582002519988299, 360582003140485730, 360582003761163315, 360582004306833136, 360582004617056572, 360582004654998828, 360582004693035866]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360646937312022268, 360646955248052480⟩, ⟨(-3464101690322732342), (-3463455395909621968)⟩, true⟩

def words02 : List Nat := [360582004980888572, 360582005445749724, 360582006261351513, 360582007077064389, 360582007590357607, 360582008250250931, 360582009260896958, 360582010271727514, 360582011399622973, 360582012618139116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596309481599610, 360596327424684923⟩, ⟨(-763812021247379414), (-763165350550894738)⟩, true⟩

def words03 : List Nat := [360582013616867415, 360582014615638680, 360582015490966473, 360582016541708617, 360582017504110940, 360582018466598087, 360582019205088506, 360582019593105491, 360582019861948984, 360582020131035556]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593450385701477, 360593468335748456⟩, ⟨(-611354386560710297), (-610707344493803129)⟩, true⟩

def words04 : List Nat := [360582020607180796, 360582020827957924, 360582020873393665, 360582020918902424, 360582020919521996, 360582020943767768, 360582021070974249, 360582021198307333, 360582021198966645, 360582021364848308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360657149126521753, 360657167083552289⟩, ⟨(-4010043951463168043), (-4009396536789391029)⟩, true⟩

def words05 : List Nat := [360582021792604033, 360582022220574190, 360582022998885495, 360582023904966699, 360582024511495084, 360582025118058542, 360582025999748470, 360582027058257482, 360582028467027392, 360582029875913951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611789366656295, 360611807330751572⟩, ⟨(-1589651047907952269), (-1589003256225076457)⟩, true⟩

def words06 : List Nat := [360582030957584493, 360582031689041125, 360582032395827957, 360582033102803443, 360582033611857739, 360582033770805152, 360582033771464688, 360582033754484964, 360582033988017865, 360582034546726070]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578222938151213, 360578240909216658⟩, ⟨201952134970029934, 202600298686068684⟩, true⟩

def words07 : List Nat := [360582035185144647, 360582035823684636, 360582036286269605, 360582036398791134, 360582036399422421, 360582036252924269, 360582036309195462, 360582036413480385, 360582036414146775, 360582036343811752]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591023016521879, 360591040994584882⟩, ⟨(-481297256981715991), (-480648719701647493)⟩, true⟩

def words08 : List Nat := [360582036552455854, 360582037128631753, 360582037617841865, 360582038107170619, 360582038297511949, 360582038298252580, 360582038263869354, 360582038390009859, 360582038395582832, 360582038564967500]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578677539574029, 360578695524688799⟩, ⟨177907566902816956, 178556480711419108⟩, true⟩

def words09 : List Nat := [360582038565630742, 360582038472033914, 360582038560088983, 360582039012913813, 360582039308626422, 360582039604461545, 360582039647217915, 360582039647958731, 360582039340781815, 360582039279009238]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533
