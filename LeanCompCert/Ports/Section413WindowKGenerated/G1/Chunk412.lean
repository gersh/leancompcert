import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk412

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462426364932317, 362462450509485728⟩, ⟨931356073002410643, 932028240582424797⟩, true⟩

def state01 : KState := ⟨⟨362490817947933260, 362490842104624515⟩, ⟨(-238388879582784289), (-237716211862549253)⟩, true⟩

def words00 : List Nat := [371285072045283922, 371285072046816612, 371285072318901125, 371285072750063991, 371285073020926896, 371285073022290046, 371285073026144978, 371285073288677326, 371285073692348443, 371285073833729304]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496760076768585, 362496784245791146⟩, ⟨(-483249094049788636), (-482575918094745392)⟩, true⟩

def words01 : List Nat := [371285073951463700, 371285074069625290, 371285074775224467, 371285075186940985, 371285075776135274, 371285076365866075, 371285076840329515, 371285076841684697, 371285076919560909, 371285077205251258]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489226725958514, 362489250907060685⟩, ⟨(-172696100370449760), (-172022426430877694)⟩, true⟩

def words02 : List Nat := [371285078077952637, 371285078167513064, 371285078168548369, 371285078154482336, 371285078139890887, 371285078123237916, 371285078086991037, 371285078363678299, 371285078642073569, 371285078744696666]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362509180291628170, 362509204484983933⟩, ⟨(-995375974032880948), (-994701794815278846)⟩, true⟩

def words03 : List Nat := [371285079434348823, 371285080124686533, 371285081401788397, 371285081987317236, 371285082481861611, 371285082976798476, 371285083631697332, 371285084067507111, 371285084653313658, 371285085239698531]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492486730346865, 362492510935935271⟩, ⟨(-306882343094101553), (-306207659340074901)⟩, true⟩

def words04 : List Nat := [371285085770002841, 371285085771361893, 371285086214357498, 371285086730698475, 371285087418986105, 371285087430932662, 371285087441828829, 371285087453191051, 371285087718393446, 371285087899903658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472357383895573, 362472381601678096⟩, ⟨523576533228400610, 524251720053236174⟩, true⟩

def words05 : List Nat := [371285088272556474, 371285088645713598, 371285089018034059, 371285089019389861, 371285088609155635, 371285088273181702, 371285088185991179, 371285088187370884, 371285087960478793, 371285087654030332]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491908698983568, 362491932928895203⟩, ⟨(-283169641331379805), (-282493953997215999)⟩, true⟩

def words06 : List Nat := [371285087347014213, 371285087298486280, 371285087396025484, 371285087739295965, 371285087934076752, 371285087935433195, 371285087462094329, 371285087415892593, 371285087908010128, 371285088075269238]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482475062544567, 362482499304846883⟩, ⟨106289771659144988, 106965970417373602⟩, true⟩

def words07 : List Nat := [371285088241643620, 371285088408515170, 371285089086758682, 371285089473501453, 371285089949208470, 371285090425397163, 371285090900775899, 371285090902132259, 371285090595823870, 371285090534750405]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459797864386350, 362459822118764133⟩, ⟨1042572241755135149, 1043248939052339881⟩, true⟩

def words08 : List Nat := [371285090996536325, 371285090997892752, 371285090741097420, 371285090380185188, 371285090018785368, 371285089721578752, 371285089214520099, 371285088977060806, 371285088739136630, 371285088501400422]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492005257994084, 362492029524641225⟩, ⟨(-287464339182136268), (-286787135222479640)⟩, true⟩

def words09 : List Nat := [371285087890411147, 371285087796724119, 371285087702356058, 371285087689525313, 371285087151354970, 371285086524324055, 371285085896753511, 371285085773439232, 371285085524670395, 371285085694341173]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk412
