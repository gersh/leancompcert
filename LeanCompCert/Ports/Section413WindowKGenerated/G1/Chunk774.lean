import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk774

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484096156443809, 362484185760974580⟩, ⟨74664326163977467, 79347715838562289⟩, true⟩

def state01 : KState := ⟨⟨362472023488912319, 362472113117231982⟩, ⟨1009171892064638660, 1013857123119887408⟩, true⟩

def words00 : List Nat := [371285210965020010, 371285210967702625, 371285210865951905, 371285210765229300, 371285210663509501, 371285210606029925, 371285210500315925, 371285210457692267, 371285210414150078, 371285210354321763]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493945787865366, 362494035440326931⟩, ⟨(-687969753223816279), (-683282653222525811)⟩, true⟩

def words01 : List Nat := [371285210186941923, 371285210180649535, 371285210232882565, 371285210235552962, 371285210075202301, 371285209899394702, 371285209722481119, 371285209713458420, 371285209776575398, 371285209893599009]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475859159711209, 362475948836246634⟩, ⟨712364733664167569, 717053697589023721⟩, true⟩

def words02 : List Nat := [371285210012074139, 371285210014744733, 371285209955531803, 371285210003496961, 371285210083014040, 371285210085684689, 371285209943159880, 371285209769055164, 371285209593890972, 371285209506498333]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476035844942950, 362476125545551749⟩, ⟨698742116457766378, 703432944502474814⟩, true⟩

def words03 : List Nat := [371285209435748728, 371285209485707686, 371285209532576079, 371285209535293763, 371285209443383428, 371285209366190099, 371285209358744911, 371285209361418242, 371285209246367000, 371285209132128486]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476136896297122, 362476226620828607⟩, ⟨690910530781781398, 695603211522030868⟩, true⟩

def words04 : List Nat := [371285209016687681, 371285208906865470, 371285208712496240, 371285208657854056, 371285208602419139, 371285208522446524, 371285208219523690, 371285208084645249, 371285207948306421, 371285207940538382]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473144568611417, 362473234317442216⟩, ⟨922700854280261395, 927395417127295351⟩, true⟩

def words05 : List Nat := [371285207826587791, 371285207680655103, 371285207535115796, 371285207538101709, 371285207477066179, 371285207423974583, 371285207369946135, 371285207316712967, 371285207040600158, 371285206889313212]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469478570456346, 362469568343112869⟩, ⟨1206750185128839690, 1211446593638622540⟩, true⟩

def words06 : List Nat := [371285206736563102, 371285206731331024, 371285206633360657, 371285206524533792, 371285206414658342, 371285206356851755, 371285206214541934, 371285206144566906, 371285206073758093, 371285205965336164]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489678624053980, 362489768420898177⟩, ⟨(-358262431439421947), (-353564148990038871)⟩, true⟩

def words07 : List Nat := [371285205765297413, 371285205733172613, 371285205750700154, 371285205753372631, 371285205584609591, 371285205390955498, 371285205196193018, 371285205168995303, 371285205122180446, 371285205184117676]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484429394604794, 362484519215626718⟩, ⟨48416460944334574, 53116616803447014⟩, true⟩

def words08 : List Nat := [371285205244059849, 371285205246738369, 371285205133749544, 371285205091309284, 371285205052940109, 371285205055622115, 371285204927611747, 371285204789846414, 371285204676638739, 371285204679774395]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468570031917014, 362468659876941780⟩, ⟨1277509989723964802, 1282212005688743882⟩, true⟩

def words09 : List Nat := [371285204830268306, 371285204990667531, 371285205147193730, 371285205149866943, 371285205084448902, 371285205024589686, 371285204969471959, 371285204972145268, 371285204758481259, 371285204547982926]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk774
