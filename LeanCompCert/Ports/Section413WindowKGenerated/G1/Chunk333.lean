import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk333

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467376277831904, 362467391777520056⟩, ⟨575288207695838548, 575637054394819272⟩, true⟩

def state01 : KState := ⟨⟨362458480143793723, 362458495653067782⟩, ⟨871625564501623392, 871974730461328436⟩, true⟩

def words00 : List Nat := [371284678038489050, 371284678039565271, 371284677220953488, 371284676299242588, 371284675377164558, 371284674731387463, 371284673853182006, 371284673642070589, 371284673430618479, 371284673219277969]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479066147144376, 362479081666176408⟩, ⟨185859544494374270, 186209035540714264⟩, true⟩

def words01 : List Nat := [371284672548188401, 371284672663517281, 371284673150121708, 371284673151198486, 371284672438062695, 371284671574885469, 371284670746620458, 371284670747818472, 371284670339129150, 371284670172645217]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362455897574189951, 362455913102928277⟩, ⟨957819689365927136, 958169503876448116⟩, true⟩

def words02 : List Nat := [371284670005734043, 371284669765426190, 371284668325447342, 371284667640049325, 371284666954174994, 371284666458031616, 371284665031393396, 371284663408925402, 371284661786103687, 371284661062840562]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362440247897877551, 362440263436299189⟩, ⟨1479674238854390438, 1480024376160396906⟩, true⟩

def words03 : List Nat := [371284660237548362, 371284660275186258, 371284660275992373, 371284660231775742, 371284659441916232, 371284658829847016, 371284658217239020, 371284657949679987, 371284656619542718, 371284655289213419]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465453339367101, 362465468887450583⟩, ⟨639146609128140719, 639497068608807495⟩, true⟩

def words04 : List Nat := [371284653958513477, 371284652727017771, 371284651046510667, 371284650265115506, 371284649483431255, 371284648668591949, 371284646655678778, 371284645541814458, 371284644427449747, 371284644211846650]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486684277770700, 362486699835682892⟩, ⟨(-68997451561390807), (-68646664243930017)⟩, true⟩

def words05 : List Nat := [371284643637697820, 371284643063226066, 371284642810849235, 371284642812050828, 371284642813891900, 371284642834155706, 371284642853342130, 371284642854425512, 371284642080609625, 371284642143639970]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481535262601519, 362481550830120903⟩, ⟨102885632387468432, 103236740250894134⟩, true⟩

def words06 : List Nat := [371284643008882659, 371284643130930336, 371284643131749735, 371284643067402373, 371284643210890818, 371284643212078941, 371284643609741853, 371284644179486413, 371284644528142489, 371284644529259378]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362525048903649923, 362525064480916511⟩, ⟨(-1349419808339403170), (-1349068375162950302)⟩, true⟩

def words07 : List Nat := [371284644683702515, 371284644931390543, 371284645810491977, 371284646069889539, 371284646165519676, 371284646261513938, 371284647253772607, 371284647798579177, 371284649010117673, 371284650222051800]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474849819459126, 362474865406482821⟩, ⟨326332222511612402, 326683981428944206⟩, true⟩

def words08 : List Nat := [371284651433759598, 371284651450451286, 371284651689251068, 371284651928595521, 371284652194696684, 371284652195775978, 371284651266926689, 371284650336792289, 371284649406282142, 371284649293318070]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362445693072829434, 362445708669573421⟩, ⟨1300211851509431029, 1300563935037243387⟩, true⟩

def words09 : List Nat := [371284649604069030, 371284650208245706, 371284650811398946, 371284650812478660, 371284650360636768, 371284650182861892, 371284650035489393, 371284650036569007, 371284648874195754, 371284647709544596]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk333
