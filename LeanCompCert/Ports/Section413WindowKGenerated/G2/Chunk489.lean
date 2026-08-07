import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550497361380129, 360550512335199466⟩, ⟨1540759182904528501, 1541253961685198475⟩, true⟩

def state01 : KState := ⟨⟨360579743385057102, 360579758365231220⟩, ⟨110495098191095055, 110990187751204451⟩, true⟩

def words00 : List Nat := [360582030177131550, 360582029842776143, 360582029527519992, 360582029003981961, 360582028480355465, 360582027852573140, 360582027724908426, 360582027869884272, 360582027870496409, 360582027639157845]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589597709834129, 360589612696363737⟩, ⟨(-371497484927626413), (-371002084488578765)⟩, true⟩

def words01 : List Nat := [360582027824260054, 360582028055946171, 360582028532793739, 360582028773279415, 360582028773906424, 360582028660915819, 360582028547792864, 360582028687177114, 360582028842753545, 360582028998473494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561981714199414, 360561996707157302⟩, ⟨979373871181172901, 979869586122237821⟩, true⟩

def words02 : List Nat := [360582028999074686, 360582028887332346, 360582028494536080, 360582027954968795, 360582027415239386, 360582026652695550, 360582025758267778, 360582024612214833, 360582023466075182, 360582022654145290]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360514256422204656, 360514271421503645⟩, ⟨3314968274933179242, 3315464300177261482⟩, true⟩

def words03 : List Nat := [360582022245421243, 360582022172637657, 360582022099785803, 360582021815825736, 360582021281760457, 360582020643821324, 360582020005720093, 360582019359245759, 360582018295490119, 360582016911903671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557008735221990, 360557023740887512⟩, ⟨1222423374188862076, 1222919711042119806⟩, true⟩

def words04 : List Nat := [360582015528221109, 360582014478722331, 360582013636999193, 360582012938452864, 360582012239871373, 360582011181565708, 360582009706038325, 360582008646820305, 360582007587448346, 360582006778906759]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360582659056513209, 360582674068613137⟩, ⟨(-33378600839032130), (-32881948990141632)⟩, true⟩

def words05 : List Nat := [360582006269156356, 360582005402722992, 360582004536195317, 360582004085851013, 360582003887082035, 360582003584601867, 360582003282060399, 360582002771772962, 360582002459399679, 360582002473895094]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557612882197619, 360557627900641772⟩, ⟨1192897140352851013, 1193394102847995725⟩, true⟩

def words06 : List Nat := [360582002552175807, 360582002552850405, 360582002214231286, 360582001620192512, 360582001026077721, 360582000138364435, 360581999461648800, 360581998978891918, 360581998496086640, 360581997802680735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561532866646157, 360561547891470295⟩, ⟨1000942067816826236, 1001439342770484638⟩, true⟩

def words07 : List Nat := [360581997305589387, 360581996932861185, 360581996602033662, 360581996602708656, 360581996375880562, 360581995799293490, 360581995222602516, 360581994599550862, 360581994191078914, 360581993774336169]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556773404572968, 360556788435822094⟩, ⟨1233838921112356751, 1234336510793017283⟩, true⟩

def words08 : List Nat := [360581993357513062, 360581992675670544, 360581991817642552, 360581990887887579, 360581989957988509, 360581988821877203, 360581987699937247, 360581986367744158, 360581985035475868, 360581984118834812]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533885864642827, 360533900902258947⟩, ⟨2355360358520483319, 2355858260152055283⟩, true⟩

def words09 : List Nat := [360581983605088514, 360581983506823437, 360581983408498986, 360581982985681569, 360581982713940969, 360581982233243531, 360581981752363553, 360581981395739449, 360581980622768901, 360581979642262051]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489
