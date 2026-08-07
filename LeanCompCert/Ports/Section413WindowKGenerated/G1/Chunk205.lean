import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk205

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472278820135650, 362472284458720575⟩, ⟨259159093470662804, 259237268263208830⟩, true⟩

def state01 : KState := ⟨⟨362486597727468698, 362486603371763764⟩, ⟨(-34534113127074084), (-34455821247180318)⟩, true⟩

def words00 : List Nat := [371284929971012723, 371284929971722834, 371284929486401222, 371284929368507411, 371284929250417307, 371284928718982670, 371284925024062318, 371284923699420324, 371284923418813574, 371284923501389469]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362462492674190211, 362462498324305261⟩, ⟨460149375791029016, 460227787067547406⟩, true⟩

def words01 : List Nat := [371284923501871055, 371284923487265909, 371284925557842078, 371284926762181823, 371284928030176850, 371284929298283859, 371284930064530774, 371284930065168694, 371284927671279967, 371284926579035649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454302750949737, 362454308406745821⟩, ⟨628387971628294897, 628466499509899453⟩, true⟩

def words02 : List Nat := [371284926760246571, 371284926760885032, 371284925380994571, 371284924007962248, 371284922634814906, 371284921938256315, 371284920450095739, 371284920488434018, 371284920510299248, 371284920510959650]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472547802074940, 362472553463641935⟩, ⟨253755971449417501, 253834617836906141⟩, true⟩

def words03 : List Nat := [371284919020382099, 371284918439221508, 371284919639794768, 371284919640433213, 371284918267616626, 371284916336696367, 371284914405701010, 371284913683920347, 371284912127801616, 371284911526827763]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362422616756873816, 362422622424195260⟩, ⟨1279401045097543884, 1279479809710986770⟩, true⟩

def words04 : List Nat := [371284910925676471, 371284910039605045, 371284906000626168, 371284904323967779, 371284902647156852, 371284901009043050, 371284896219105506, 371284891430666942, 371284886642436837, 371284884215422073]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362402365805945403, 362402371479034043⟩, ⟨1695930377275350387, 1696009260434251871⟩, true⟩

def words05 : List Nat := [371284881186232447, 371284880517839469, 371284879849283051, 371284879109639751, 371284875658766260, 371284872938812584, 371284870218794117, 371284869426238837, 371284866213482075, 371284862201817811]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501194281490313, 362501199960300153⟩, ⟨(-336445640067005456), (-336366639250781506)⟩, true⟩

def words06 : List Nat := [371284858190252791, 371284855926195719, 371284852677555542, 371284851786448904, 371284850895240649, 371284849660750579, 371284847147193677, 371284846671965917, 371284847667981686, 371284848463569281]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479131787335038, 362479137471970772⟩, ⟨117576930571169782, 117656051255263148⟩, true⟩

def words07 : List Nat := [371284849267101849, 371284850070766144, 371284851869519895, 371284852557586812, 371284853927341908, 371284855297216247, 371284856598174250, 371284856598814012, 371284854758274656, 371284854481264031]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362420104710586343, 362420110400911566⟩, ⟨1332694568190974101, 1332773805994509239⟩, true⟩

def words08 : List Nat := [371284855133392698, 371284855134032826, 371284853371523018, 371284851592043723, 371284849812487774, 371284848280594069, 371284845841324784, 371284843751228628, 371284841661126017, 371284839580415914]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362521948242825174, 362521953938947491⟩, ⟨(-764765023076072345), (-764685665882164843)⟩, true⟩

def words09 : List Nat := [371284836437284306, 371284835144224197, 371284834906036906, 371284834906688261, 371284834004074718, 371284832694565149, 371284832017347618, 371284832018052920, 371284833274829968, 371284835077441634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk205
