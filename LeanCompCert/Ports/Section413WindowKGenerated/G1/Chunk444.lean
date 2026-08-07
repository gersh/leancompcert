import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk444

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482375481065085, 362482403692911602⟩, ⟨139621431804120273, 140467768060102259⟩, true⟩

def state01 : KState := ⟨⟨362451834790669162, 362451863015608887⟩, ⟨1495786829341804936, 1496633747004121636⟩, true⟩

def words00 : List Nat := [371285567451581051, 371285567453049385, 371285566945185398, 371285566382809552, 371285565819906806, 371285565388633955, 371285564704982304, 371285564266628335, 371285563827750375, 371285563392708733]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489246558971463, 362489274797155509⟩, ⟨(-165868458519877854), (-165020952609227780)⟩, true⟩

def words01 : List Nat := [371285562634875821, 371285562323376884, 371285562058444136, 371285562059913124, 371285561514504157, 371285560851439157, 371285560187786510, 371285560031405466, 371285559780828214, 371285559866095668]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464664488670992, 362464692740122653⟩, ⟨926224680750934748, 927072776077016516⟩, true⟩

def words02 : List Nat := [371285559883625232, 371285559885122963, 371285559707822532, 371285559828573741, 371285560103299253, 371285560104768535, 371285559765183986, 371285559381118072, 371285558996508692, 371285558659008024]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464949951889169, 362464978216587806⟩, ⟨913633398520672434, 914482082476962078⟩, true⟩

def words03 : List Nat := [371285558190379990, 371285558182221893, 371285558173559927, 371285558162377343, 371285557669281779, 371285557330452983, 371285557043012598, 371285557044486211, 371285556582618831, 371285556121234003]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476592091595105, 362476620369461230⟩, ⟨396201386848674209, 397050656034706755⟩, true⟩

def words04 : List Nat := [371285555659194752, 371285555567889459, 371285555222173543, 371285555080000227, 371285554937388897, 371285554717411107, 371285553893998501, 371285553391926517, 371285552891107003, 371285552892656612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467946186515209, 362467974477761641⟩, ⟨780609842519867893, 781459706526833075⟩, true⟩

def words05 : List Nat := [371285552692821146, 371285552402907286, 371285552326702139, 371285552328322630, 371285552357950659, 371285552396500335, 371285552397619651, 371285552317518738, 371285551562830139, 371285551169316451]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472086653116916, 362472114957450303⟩, ⟨596588039554020477, 597438485475968099⟩, true⟩

def words06 : List Nat := [371285550832206932, 371285550833688216, 371285550551753957, 371285550270432256, 371285549988514075, 371285549860441898, 371285549527153509, 371285549576440269, 371285549596932775, 371285549598454935]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485842882945872, 362485871200609392⟩, ⟨(-15276809073987043), (-14425770295403313)⟩, true⟩

def words07 : List Nat := [371285549297371387, 371285549208265236, 371285549173095947, 371285549174567486, 371285548649417414, 371285548030414489, 371285547410855406, 371285547232916276, 371285546878560954, 371285546887525258]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474971332744788, 362474999663665027⟩, ⟨468305029855015844, 469156658360888626⟩, true⟩

def words08 : List Nat := [371285546896009660, 371285546897482673, 371285546363730136, 371285546335700773, 371285546306970478, 371285546246920901, 371285545828029495, 371285545406860647, 371285544985102552, 371285544879631782]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463277228570748, 362463305572749640⟩, ⟨988735059264697713, 989587277713818903⟩, true⟩

def words09 : List Nat := [371285544911326604, 371285545180640781, 371285545449573681, 371285545451045184, 371285545046991942, 371285544660179021, 371285544388604402, 371285544390079154, 371285543987201640, 371285543489102760]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk444
