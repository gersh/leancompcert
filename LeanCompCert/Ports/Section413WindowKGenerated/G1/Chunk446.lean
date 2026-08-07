import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk446

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489711270225697, 362489739747101335⟩, ⟨(-187590616478356289), (-186732486373736119)⟩, true⟩

def state01 : KState := ⟨⟨362460719586316924, 362460748076509143⟩, ⟨1105518655523841128, 1106377379613858066⟩, true⟩

def words00 : List Nat := [371285553108975035, 371285553110451655, 371285552664346314, 371285552478421119, 371285552291750719, 371285552123116415, 371285551284463302, 371285550446488906, 371285549607927682, 371285549183427186]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362450383742072554, 362450412245551314⟩, ⟨1566671544615864849, 1567530861485619449⟩, true⟩

def words01 : List Nat := [371285548628504556, 371285548284856814, 371285547940747262, 371285547594493599, 371285546578441408, 371285545715117537, 371285544851035942, 371285544489409189, 371285543709457928, 371285542923755833]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463227665776476, 362463256182456390⟩, ⟨993632021989595757, 994491927963166433⟩, true⟩

def words02 : List Nat := [371285542137444845, 371285541853688147, 371285541352298248, 371285541353405558, 371285541354059154, 371285541177462282, 371285540411355699, 371285539905017214, 371285539397958797, 371285539219157335]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469822613992760, 362469851144166211⟩, ⟨699318901284027851, 700179409539349495⟩, true⟩

def words03 : List Nat := [371285538721003271, 371285538187141330, 371285537652662854, 371285537620472824, 371285537371536693, 371285537270353529, 371285537168690468, 371285537067507402, 371285536516288194, 371285536166781340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480714984282598, 362480743527606914⟩, ⟨213100718835426935, 213961814213890693⟩, true⟩

def words04 : List Nat := [371285535966567235, 371285535968054987, 371285535765495790, 371285535528375802, 371285535290715202, 371285535205240644, 371285535171533711, 371285535406464090, 371285535503994629, 371285535505528838]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502858572002526, 362502887128685052⟩, ⟨(-775686391081048172), (-774824699191345964)⟩, true⟩

def words05 : List Nat := [371285535793175778, 371285536188873949, 371285536793998800, 371285536805832177, 371285536806980785, 371285536749487948, 371285537133420761, 371285537326418749, 371285537715911014, 371285538106065959]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483176487180804, 362483205057166570⟩, ⟨103364266863586049, 104226552946074983⟩, true⟩

def words06 : List Nat := [371285538495743362, 371285538497220904, 371285538471571463, 371285538663436940, 371285539006065540, 371285539007545214, 371285538813523596, 371285538524418867, 371285538311648087, 371285538313332814]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471658346660050, 362471686929960589⟩, ⟨617999303186403344, 618862184107094680⟩, true⟩

def words07 : List Nat := [371285538411461469, 371285538562429207, 371285538713150861, 371285538714654360, 371285538448431184, 371285538336676057, 371285538525790145, 371285538527268286, 371285538227200016, 371285537918861823]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477798003025174, 362477826599580698⟩, ⟨343698789426616297, 344562262645866593⟩, true⟩

def words08 : List Nat := [371285537609889880, 371285537425429817, 371285537206255752, 371285537348051739, 371285537401853745, 371285537403332072, 371285536789704744, 371285536677427271, 371285536650917147, 371285536652448138]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467232679696948, 362467261289691889⟩, ⟨815918671772821970, 816782745668155366⟩, true⟩

def words09 : List Nat := [371285536481034404, 371285536310389045, 371285536139173699, 371285536079447745, 371285535836052359, 371285535613330561, 371285535390106798, 371285535149426153, 371285534241312900, 371285533834337710]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk446
