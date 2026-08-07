import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490831613057321, 362490894152369124⟩, ⟨(-352276969615294434), (-349527126401993970)⟩, true⟩

def state01 : KState := ⟨⟨362478048677903466, 362478111236950655⟩, ⟨480009385052430371, 482760513142075899⟩, true⟩

def words00 : List Nat := [371285525474241330, 371285525520184462, 371285525565465789, 371285525611534600, 371285525702428523, 371285525704894154, 371285525723597548, 371285525771496763, 371285525773165360, 371285525774089990]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502491018128053, 362502553597235627⟩, ⟨(-1111551710197278683), (-1108799275874610343)⟩, true⟩

def words01 : List Nat := [371285525783501717, 371285525907953301, 371285526132759143, 371285526162392910, 371285526164124824, 371285526154423885, 371285526287499975, 371285526315807705, 371285526578787379, 371285526842795821]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489241043738959, 362489303642865189⟩, ⟨(-248713669623351760), (-245959931584503640)⟩, true⟩

def words02 : List Nat := [371285527062227462, 371285527064444969, 371285527108810897, 371285527250688179, 371285527461498441, 371285527463715993, 371285527360555736, 371285527227749963, 371285527194268357, 371285527254792160]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472325055027717, 362472387674080231⟩, ⟨853152011224076176, 855907047163961972⟩, true⟩

def words03 : List Nat := [371285527412054352, 371285527570187425, 371285527727445110, 371285527729665116, 371285527632091202, 371285527546066327, 371285527571269544, 371285527573487709, 371285527373588025, 371285527174343725]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479447768509416, 362479510407442587⟩, ⟨389240507105568415, 391996838171032625⟩, true⟩

def words04 : List Nat := [371285527007909143, 371285527010436941, 371285527134326520, 371285527275766325, 371285527370037259, 371285527372255655, 371285527166528998, 371285527183256815, 371285527240725533, 371285527243024645]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471591287315526, 362471653946505814⟩, ⟨901153505054503064, 903911155971341694⟩, true⟩

def words05 : List Nat := [371285527152351831, 371285527049436637, 371285526961597549, 371285526964042273, 371285526863959413, 371285526824653540, 371285526784567949, 371285526717118895, 371285526335184486, 371285526125081188]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466520961520806, 362466583640506100⟩, ⟨1231544031264982931, 1234302972127704271⟩, true⟩

def words06 : List Nat := [371285525913699679, 371285525852281675, 371285525525008622, 371285525135248609, 371285524744655033, 371285524427059574, 371285523990934946, 371285523791031205, 371285523590379217, 371285523382291089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488306978980506, 362488369677973190⟩, ⟨(-188345762491049939), (-185585517642723353)⟩, true⟩

def words07 : List Nat := [371285523093180437, 371285523040458540, 371285523166509981, 371285523168729317, 371285523036732147, 371285522840471366, 371285522643320649, 371285522544790797, 371285522398458666, 371285522444613120]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489045284610614, 362489108003637403⟩, ⟨(-236481441833958192), (-233719891064214424)⟩, true⟩

def words08 : List Nat := [371285522489817027, 371285522492050524, 371285522475712907, 371285522587108977, 371285522769380127, 371285522771614784, 371285522742634499, 371285522714181920, 371285522790318950, 371285522847848043]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470348058097805, 362470410797160884⟩, ⟨982508594333380158, 985271451371314266⟩, true⟩

def words09 : List Nat := [371285522974091491, 371285523101229326, 371285523231700699, 371285523233922066, 371285523091507825, 371285522945444538, 371285522798245295, 371285522772979123, 371285522551737186, 371285522322488665]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651
