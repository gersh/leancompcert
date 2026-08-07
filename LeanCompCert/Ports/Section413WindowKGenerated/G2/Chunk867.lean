import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560418732811747, 360560468000009507⟩, ⟨1879944456216955749, 1882829023144130403⟩, true⟩

def state01 : KState := ⟨⟨360581611522063140, 360581660801024363⟩, ⟨42433860903315531, 45319447780935859⟩, true⟩

def words00 : List Nat := [360582184348270256, 360582184210727881, 360582184144417997, 360582184011697011, 360582183878775607, 360582183712692263, 360582183612891663, 360582183594743229, 360582183576478230, 360582183456401839]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598377786761333, 360598427077488342⟩, ⟨(-1411489010777894892), (-1408602403630695452)⟩, true⟩

def words01 : List Nat := [360582183578202883, 360582183706394979, 360582183854898900, 360582183903220251, 360582183904382391, 360582183829424773, 360582183754208003, 360582183778983154, 360582183967298896, 360582184155893450]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584046730000955, 360584096032626809⟩, ⟨(-168773711095047219), (-165886072024391711)⟩, true⟩

def words02 : List Nat := [360582184268911443, 360582184282263517, 360582184283294476, 360582184241725963, 360582184199804994, 360582184123602061, 360582183949367014, 360582183708749425, 360582183467897553, 360582183382340010]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556614002287133, 360556663316659069⟩, ⟨2210662970331974372, 2213551628199470196⟩, true⟩

def words03 : List Nat := [360582183490278149, 360582183598452624, 360582183619527652, 360582183620778733, 360582183597665428, 360582183468708946, 360582183339399969, 360582183206858934, 360582182996574060, 360582182703656988]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589229155712306, 360589278481858477⟩, ⟨(-618505756226704897), (-615616077003375187)⟩, true⟩

def words04 : List Nat := [360582182410463564, 360582182224699525, 360582182149904101, 360582182179645745, 360582182180796678, 360582182097451269, 360582181995697237, 360582181999102763, 360582182041636935, 360582182124732872]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360594524008782334, 360594573346840000⟩, ⟨(-1077890686505761467), (-1074999973903185107)⟩, true⟩

def words05 : List Nat := [360582182125879010, 360582182090036713, 360582182149582916, 360582182326856908, 360582182470328093, 360582182614001975, 360582182654718794, 360582182699343801, 360582182843167879, 360582182987416951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601237571681331, 360601286921487996⟩, ⟨(-1660388129390849079), (-1657496397386259573)⟩, true⟩

def words06 : List Nat := [360582183224760341, 360582183471071508, 360582183650777447, 360582183830615582, 360582183893936821, 360582184024474067, 360582184287304367, 360582184550380920, 360582184737443781, 360582184958880832]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607671375019856, 360607720736628611⟩, ⟨(-2218637445202452911), (-2215744689073175119)⟩, true⟩

def words07 : List Nat := [360582185312683050, 360582185666867785, 360582186079305007, 360582186409108764, 360582186623518495, 360582186838013406, 360582187157679748, 360582187544369192, 360582187839633636, 360582188135148182]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608932653411849, 360608982026904252⟩, ⟨(-2328210427505842426), (-2325316640053412598)⟩, true⟩

def words08 : List Nat := [360582188364063723, 360582188460415790, 360582188689138020, 360582188918221780, 360582189068844825, 360582189223397017, 360582189311447586, 360582189399627908, 360582189576570012, 360582189886704769]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578332775128189, 360578382160384663⟩, ⟨327769663605888847, 330664472122189131⟩, true⟩

def words09 : List Nat := [360582190304144187, 360582190721816068, 360582191037613312, 360582191220865148, 360582191370489525, 360582191520454533, 360582191676619537, 360582191700369969, 360582191701482361, 360582191658911417]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867
