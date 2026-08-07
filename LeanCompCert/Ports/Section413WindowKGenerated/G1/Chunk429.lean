import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk429

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503250098127715, 362503276362376917⟩, ⟨(-769510734381943093), (-768749420122302267)⟩, true⟩

def state01 : KState := ⟨⟨362502748199487554, 362502774476336056⟩, ⟨(-747946583542080162), (-747184728706337064)⟩, true⟩

def words00 : List Nat := [371285358176266850, 371285358581583681, 371285358853043388, 371285359124951684, 371285359557449195, 371285359720550640, 371285360361111183, 371285361002207776, 371285361640339064, 371285362047618331]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362516483239184670, 362516509528830170⟩, ⟨(-1337419224966549640), (-1336656820948254146)⟩, true⟩

def words01 : List Nat := [371285362658165003, 371285363269444331, 371285364231996677, 371285364568587800, 371285364826166594, 371285365084160683, 371285365565156992, 371285365817862286, 371285366544445263, 371285367271637928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362512599840408215, 362512626142841301⟩, ⟨(-1170784628989895118), (-1170021676064667226)⟩, true⟩

def words02 : List Nat := [371285367974682183, 371285368193411141, 371285368955532240, 371285369718364019, 371285370485975911, 371285370763099885, 371285370983202118, 371285371203789220, 371285371967531090, 371285372603998399]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496346793068770, 362496373108238324⟩, ⟨(-472948586056412082), (-472185086287881212)⟩, true⟩

def words03 : List Nat := [371285373463332079, 371285374323171165, 371285375079010324, 371285375111731893, 371285375288401259, 371285375465772233, 371285376185970267, 371285376457170009, 371285376714336924, 371285376971998184]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362514601641460314, 362514627969299734⟩, ⟨(-1256825010055567691), (-1256060966178998567)⟩, true⟩

def words04 : List Nat := [371285377612810972, 371285378032778550, 371285378995555505, 371285379958893472, 371285380780402916, 371285380956237574, 371285381585534947, 371285382215535320, 371285383242193653, 371285383924546900]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498784669523514, 362498811010295684⟩, ⟨(-577295435961722358), (-576530836559428434)⟩, true⟩

def words05 : List Nat := [371285384598230254, 371285385272406611, 371285386489105544, 371285387437027059, 371285388393515572, 371285389350481367, 371285390241511797, 371285390517385524, 371285390830763415, 371285391144916400]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498978232136120, 362499004585522569⟩, ⟨(-585579580989636757), (-584814439612907459)⟩, true⟩

def words06 : List Nat := [371285392001271745, 371285392135517365, 371285392266894076, 371285392398731666, 371285392645045996, 371285392765828984, 371285393428839291, 371285394092407254, 371285394753020425, 371285395071207964]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362524223761828364, 362524250128028275⟩, ⟨(-1670543412083760589), (-1669777720047823553)⟩, true⟩

def words07 : List Nat := [371285395843983367, 371285396617440032, 371285397608809137, 371285397878460864, 371285398076241013, 371285398274465117, 371285398748735494, 371285399111709126, 371285400016603392, 371285400922098962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362500491680048860, 362500518059018805⟩, ⟨(-650496076917922791), (-649729835959559527)⟩, true⟩

def words08 : List Nat := [371285401824626779, 371285402005640696, 371285402641536333, 371285403278164981, 371285404074655503, 371285404149865891, 371285404150945715, 371285404102744316, 371285404546447664, 371285404899614289]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482367168046565, 362482393559790039⟩, ⟨128888551876992592, 129655342035096242⟩, true⟩

def words09 : List Nat := [371285405603025858, 371285406306994300, 371285406945851142, 371285407215969831, 371285407646400657, 371285408077495572, 371285408833041553, 371285408867751057, 371285408868818469, 371285408800302484]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk429
