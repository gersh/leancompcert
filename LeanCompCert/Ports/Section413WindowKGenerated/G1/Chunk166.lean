import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk166

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362375743572250535, 362375747201299375⟩, ⟨1817443166634180767, 1817483915789222291⟩, true⟩

def state01 : KState := ⟨⟨362455107841492712, 362455111475082540⟩, ⟨499681539343228997, 499722363902000001⟩, true⟩

def words00 : List Nat := [371285227589320312, 371285223349756561, 371285217302524730, 371285214882432930, 371285212462474643, 371285209223872586, 371285202916713353, 371285200235473633, 371285197554289441, 371285197108068814]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494494348561911, 362494497986769211⟩, ⟨(-154779295975374275), (-154738394696503543)⟩, true⟩

def words01 : List Nat := [371285195297267546, 371285192877752097, 371285190829623302, 371285190830189641, 371285190042879372, 371285190181926871, 371285190182306765, 371285190112240918, 371285187613422150, 371285188174200984]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362419787076578200, 362419790719304207⟩, ⟨1087265696847839458, 1087306673251450218⟩, true⟩

def words02 : List Nat := [371285190569936833, 371285190570444589, 371285188148678919, 371285185721616947, 371285183294654278, 371285181021723106, 371285177316667124, 371285175965043740, 371285174613417186, 371285172960630212]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502643522960134, 362502647170292492⟩, ⟨(-290897737666670078), (-290856684637465986)⟩, true⟩

def words03 : List Nat := [371285169029627775, 371285168713100273, 371285171692522294, 371285171693030411, 371285170178405553, 371285168160073872, 371285167184236035, 371285167184795781, 371285167801645127, 371285168852605006]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470553439952540, 362470557091872523⟩, ⟨242921696286262820, 242962825676770264⟩, true⟩

def words04 : List Nat := [371285169788551195, 371285169789059743, 371285166580971364, 371285164082810966, 371285161584705119, 371285160146703667, 371285156538735921, 371285152974678759, 371285149453189371, 371285149453775032]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463918280622713, 362463921937126793⟩, ⟨353716293871773173, 353757499610744595⟩, true⟩

def words05 : List Nat := [371285151307168615, 371285154036802147, 371285156110776697, 371285156111289056, 371285154990257769, 371285154929366035, 371285158409875133, 371285158410384216, 371285157154726132, 371285155880680860]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497910524302801, 362497914185357891⟩, ⟨(-212538164267080089), (-212496882684357663)⟩, true⟩

def words06 : List Nat := [371285156933807755, 371285157469917303, 371285160602110046, 371285163734136690, 371285165576808388, 371285165577320073, 371285164023646224, 371285163955340934, 371285166921322426, 371285167686486537]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503794646241099, 362503798311942125⟩, ⟨(-310503948554444104), (-310462589500458844)⟩, true⟩

def words07 : List Nat := [371285168438266002, 371285169190133565, 371285173537457747, 371285176606584620, 371285179725987817, 371285182845208991, 371285185556070797, 371285185556580902, 371285185446229883, 371285186562676466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362421672513897942, 362421676184145130⟩, ⟨1059806626037309532, 1059848060944900776⟩, true⟩

def words08 : List Nat := [371285189165835362, 371285189166346255, 371285188112578825, 371285186819568626, 371285185526523616, 371285185005293648, 371285182762118441, 371285181233688122, 371285179705253514, 371285178165028588]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362558276901419175, 362558280576268872⟩, ⟨(-1220788077798326873), (-1220746566051546663)⟩, true⟩

def words09 : List Nat := [371285174360810993, 371285174146285148, 371285177304990136, 371285177305501765, 371285177067219706, 371285176015393116, 371285176809322358, 371285177601160604, 371285181978930908, 371285186356398712]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk166
