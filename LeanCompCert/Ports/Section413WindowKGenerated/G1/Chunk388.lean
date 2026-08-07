import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk388

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489943262810211, 362489964572440451⟩, ⟨(-186570920931608527), (-186012187239750983)⟩, true⟩

def state01 : KState := ⟨⟨362507368328124428, 362507389649133073⟩, ⟨(-862734402050172861), (-862175226820569287)⟩, true⟩

def words00 : List Nat := [371285170849871969, 371285170871524932, 371285171556477977, 371285172241899994, 371285172896600473, 371285172897869880, 371285173016069077, 371285173365529653, 371285174362407733, 371285174936118192]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499207236949640, 362499228569501462⟩, ⟨(-545921630147553454), (-545362006867211010)⟩, true⟩

def words01 : List Nat := [371285175429178936, 371285175922629407, 371285176929973465, 371285177606123315, 371285178321354268, 371285179037036151, 371285179698040003, 371285179724837833, 371285180087602621, 371285180451038074]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362506753372113891, 362506774715990132⟩, ⟨(-838803271928986871), (-838243208976161883)⟩, true⟩

def words02 : List Nat := [371285181476982529, 371285182061931392, 371285182646197971, 371285183230875947, 371285184014242679, 371285184474755515, 371285185431771278, 371285186389245520, 371285187199627398, 371285187756885907]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362539271235779565, 362539292591139647⟩, ⟨(-2101683829675686992), (-2101123320746736572)⟩, true⟩

def words03 : List Nat := [371285188583260528, 371285189410261442, 371285190899328146, 371285191505767238, 371285192007052760, 371285192508713786, 371285193571361591, 371285194303076213, 371285195696788362, 371285197091004565]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489939235291402, 362489960602136204⟩, ⟨(-185509684864032344), (-184948729811550992)⟩, true⟩

def words04 : List Nat := [371285198347186780, 371285198721022718, 371285199314903912, 371285199909403375, 371285200562874352, 371285200564145084, 371285200335187754, 371285200041973874, 371285200015594339, 371285200139604698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362457491407873521, 362457512786133949⟩, ⟨1075411007819336943, 1075972406428237699⟩, true⟩

def words05 : List Nat := [371285200925193465, 371285201711255698, 371285202488000651, 371285202489271536, 371285202424729124, 371285202467180067, 371285202637735759, 371285202639006717, 371285201927680942, 371285201216561851]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485289827505877, 362485311217145859⟩, ⟨(-4929959080136953), (-4368118204446755)⟩, true⟩

def words06 : List Nat := [371285200504925350, 371285200455726954, 371285200180675253, 371285200212349099, 371285200213332800, 371285200136487463, 371285199177660828, 371285198881172371, 371285198838198965, 371285198842413940]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502059384202336, 362502080785467654⟩, ⟨(-656822437774776552), (-656260144966871350)⟩, true⟩

def words07 : List Nat := [371285198843389852, 371285198715592603, 371285199119539497, 371285199499302744, 371285200069075707, 371285200639293179, 371285201208735219, 371285201229893290, 371285201664903607, 371285202100635298]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471460832143068, 362471482244716003⟩, ⟨533049568086410909, 533612300595119059⟩, true⟩

def words08 : List Nat := [371285203080152394, 371285203179213645, 371285203266017261, 371285203353229494, 371285203354144666, 371285203317373343, 371285203094524892, 371285203240927080, 371285203310527073, 371285203311843674]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488634365954209, 362488655790039345⟩, ⟨(-134870649013390487), (-134307468737976705)⟩, true⟩

def words09 : List Nat := [371285203267895961, 371285203577410730, 371285204172009424, 371285204173281747, 371285203887675497, 371285203494759257, 371285203247062739, 371285203248477168, 371285203154463105, 371285203244635937]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk388
