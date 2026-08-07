import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk338

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362532029572918523, 362532045561217343⟩, ⟨(-1601864587628648529), (-1601499347649485937)⟩, true⟩

def state01 : KState := ⟨⟨362486221663261412, 362486237661441642⟩, ⟨(-53493087028035899), (-53127513006583925)⟩, true⟩

def words00 : List Nat := [371284666680670235, 371284666869811833, 371284667162815037, 371284667456349561, 371284668016241037, 371284668017335357, 371284667411292789, 371284666751440638, 371284666305157266, 371284666352902807]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482165510908962, 362482181518923456⟩, ⟨83838061957531032, 84203968526439752⟩, true⟩

def words01 : List Nat := [371284667275029112, 371284668197535390, 371284669062584997, 371284669364641698, 371284669933298052, 371284670502469790, 371284671430159648, 371284671431254887, 371284671359759059, 371284671287360075]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362522494558658350, 362522510576474883⟩, ⟨(-1280268187332939062), (-1279901949209143336)⟩, true⟩

def words02 : List Nat := [371284671872790685, 371284672096135548, 371284673038143275, 371284673980575676, 371284674595403725, 371284674596503785, 371284675040564991, 371284675700459906, 371284677233653375, 371284678353093690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362515856616669151, 362515872644496494⟩, ⟨(-1055647835646880977), (-1055281258807309289)⟩, true⟩

def words03 : List Nat := [371284679298903431, 371284680245013298, 371284681804940266, 371284682930356540, 371284684200658390, 371284685471301651, 371284686740323200, 371284687286449565, 371284688208751408, 371284689131633183]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473277487150871, 362473293524717123⟩, ⟨385509684701859703, 385876591158247669⟩, true⟩

def words04 : List Nat := [371284690766809922, 371284691238793400, 371284691643404888, 371284692048351151, 371284692486404788, 371284692490317700, 371284692702552056, 371284692915221210, 371284693127456500, 371284693128591813]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362513343397490677, 362513359444974972⟩, ⟨(-970880054075159063), (-970512811844921111)⟩, true⟩

def words05 : List Nat := [371284693328734674, 371284693866187893, 371284695105143397, 371284695181674240, 371284695182522921, 371284695030764209, 371284695598127324, 371284696079878553, 371284696927161512, 371284697774857583]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494809981372620, 362494826038736159⟩, ⟨(-343305364787507210), (-342937787994822460)⟩, true⟩

def words06 : List Nat := [371284698620767278, 371284698621863460, 371284698860613327, 371284699417011975, 371284700134185610, 371284700248570212, 371284700323249999, 371284700398277269, 371284700918266184, 371284701218447570]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479783379075712, 362479799446342098⟩, ⟨165836740460502559, 166204652712698115⟩, true⟩

def words07 : List Nat := [371284702389879055, 371284703561701959, 371284704569226635, 371284704570323293, 371284704516944331, 371284704618873197, 371284705359883394, 371284705360985294, 371284705276196859, 371284705132667739]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483260662827621, 362483276739893685⟩, ⟨48085377402794693, 48453621719213125⟩, true⟩

def words08 : List Nat := [371284705385203199, 371284705386411071, 371284706043856094, 371284706738700794, 371284707287311243, 371284707288408215, 371284706676377364, 371284706318209817, 371284706470883405, 371284706472018773]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503341954454038, 362503358041502337⟩, ⟨(-632557493103609225), (-632188910438520035)⟩, true⟩

def words09 : List Nat := [371284706430662416, 371284706246743280, 371284706748017268, 371284707132708639, 371284707782430883, 371284708432546357, 371284709080952301, 371284709082052570, 371284709399729558, 371284709951167583]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk338
