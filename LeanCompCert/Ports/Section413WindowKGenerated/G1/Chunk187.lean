import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk187

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362409175983711704, 362409180638068687⟩, ⟨1443248548019646182, 1443307417220731250⟩, true⟩

def state01 : KState := ⟨⟨362454968462545254, 362454973122064073⟩, ⟨586904687405445764, 586963653159730986⟩, true⟩

def words00 : List Nat := [371286358726114951, 371286357455381926, 371286354774374492, 371286354384950219, 371286353995370923, 371286353127598125, 371286349066515362, 371286346850709929, 371286344775831091, 371286344776428570]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479677663268433, 362479682328067302⟩, ⟨124409453060362809, 124468517630473505⟩, true⟩

def words01 : List Nat := [371286343100232991, 371286340455185889, 371286338016375549, 371286338017011410, 371286336799427909, 371286336282693147, 371286335765825764, 371286334847348052, 371286331641808585, 371286331287342435]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475007407066459, 362475012077003594⟩, ⟨212046452248421438, 212105613034065126⟩, true⟩

def words02 : List Nat := [371286332925989433, 371286333134560722, 371286333352139292, 371286333569884208, 371286333885202806, 371286333885839085, 371286334012351786, 371286335245741195, 371286336455104624, 371286336455702690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362535629517860510, 362535634193026726⟩, ⟨(-923588234522331608), (-923528975769278304)⟩, true⟩

def words03 : List Nat := [371286338093594799, 371286340336130275, 371286343344870479, 371286344549496821, 371286345295905900, 371286346042422255, 371286348929568087, 371286350400117959, 371286353030389167, 371286355660623478]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362531406588387873, 362531411268770339⟩, ⟨(-844650030516071478), (-844590673983952880)⟩, true⟩

def words04 : List Nat := [371286358288717707, 371286358289296288, 371286358809663897, 371286360491500830, 371286362418668913, 371286362726653206, 371286363014775120, 371286363303052174, 371286366432164575, 371286368835087658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472970440280244, 362472975125888393⟩, ⟨251458721369145334, 251518175909059598⟩, true⟩

def words05 : List Nat := [371286373044801717, 371286377254308277, 371286380856027710, 371286380856606706, 371286380673784253, 371286380644088781, 371286383422020403, 371286383422599544, 371286382992161418, 371286382278122352]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362515963969220241, 362515968660008094⟩, ⟨(-555143327007617094), (-555083775270079108)⟩, true⟩

def words06 : List Nat := [371286383308179831, 371286383809738393, 371286386418885489, 371286389027983561, 371286391195157077, 371286391195740225, 371286391591317749, 371286392355481642, 371286395735846089, 371286397311903567]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362538637823038196, 362538642519095661⟩, ⟨(-980733479207222455), (-980673828532031605)⟩, true⟩

def words07 : List Nat := [371286398887340097, 371286400462802793, 371286404871221498, 371286408250794011, 371286412472158892, 371286416693299708, 371286420300848313, 371286420683574305, 371286423464683460, 371286426245812448]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488519378626895, 362488524079854159⟩, ⟨(-39298651291384048), (-39238903500579456)⟩, true⟩

def words08 : List Nat := [371286430184119012, 371286430349708882, 371286430500467351, 371286430651408851, 371286430972754785, 371286430973393591, 371286431968885036, 371286433881384659, 371286435792745268, 371286435904477619]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362539953399468255, 362539958105944381⟩, ⟨(-1006034665259087030), (-1005974818816450724)⟩, true⟩

def words09 : List Nat := [371286437170342579, 371286438436382871, 371286442529615871, 371286442854508629, 371286442854965204, 371286442486196618, 371286444574295138, 371286445959623907, 371286448806411513, 371286451653159080]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk187
