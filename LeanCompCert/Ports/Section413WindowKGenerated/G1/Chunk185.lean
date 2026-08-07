import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk185

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362514438207895404, 362514442758885400⟩, ⟨(-523478005135424502), (-523421058589509430)⟩, true⟩

def state01 : KState := ⟨⟨362514532262158723, 362514536818300859⟩, ⟨(-525333010090328834), (-525275968203174816)⟩, true⟩

def words00 : List Nat := [371286152215966180, 371286152216541152, 371286152827281925, 371286154594296230, 371286157244821967, 371286157245393941, 371286156924419451, 371286156757633368, 371286158861507865, 371286160395190105]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463428941163489, 362463433502446205⟩, ⟨421000585202985582, 421057722268850894⟩, true⟩

def words01 : List Nat := [371286164446517122, 371286168497647940, 371286171683126473, 371286171683697582, 371286170983022006, 371286170098800723, 371286171247328597, 371286171247899993, 371286170027653211, 371286168800624869]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362528242904585780, 362528247470992358⟩, ⟨(-779404114858839401), (-779346882873464731)⟩, true⟩

def words02 : List Nat := [371286169262733034, 371286169889857085, 371286173433011088, 371286176976012894, 371286180410144144, 371286180445554117, 371286182843453724, 371286185241396900, 371286188815090636, 371286191085321134]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362551663903379989, 362551668474989425⟩, ⟨(-1213565020940138495), (-1213507692519430639)⟩, true⟩

def words03 : List Nat := [371286193091017119, 371286195096679868, 371286199446479623, 371286202346581390, 371286205292380658, 371286208238093161, 371286210833969087, 371286211453962289, 371286214984934383, 371286218515843779]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362542488499680611, 362542493076390998⟩, ⟨(-1043329730285527540), (-1043272307266839134)⟩, true⟩

def words04 : List Nat := [371286224956973013, 371286228099391750, 371286230678169748, 371286233256863574, 371286236715383423, 371286239192809659, 371286243501819063, 371286247810589446, 371286251981056648, 371286255013361144]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362574153251070889, 362574157832953651⟩, ⟨(-1630804847728243871), (-1630747328735636325)⟩, true⟩

def words05 : List Nat := [371286259906523570, 371286264799456363, 371286272598449643, 371286276527349536, 371286279995554843, 371286283463559006, 371286287225998568, 371286289556212699, 371286294290883760, 371286299025306669]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506682567142281, 362506687154190312⟩, ⟨(-378399163669541248), (-378341548783300972)⟩, true⟩

def words06 : List Nat := [371286303523633087, 371286304155275335, 371286306872382767, 371286309589502053, 371286312979088006, 371286312979660854, 371286312504263405, 371286312008293971, 371286313349079952, 371286314446808734]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362456438108832997, 362456442701041003⟩, ⟨555013908766249891, 555071619499616131⟩, true⟩

def words07 : List Nat := [371286316716507103, 371286318986181301, 371286320920085358, 371286320920658779, 371286319569948038, 371286319090244368, 371286319990228133, 371286319990811142, 371286318991888244, 371286317384544750]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362516385017422374, 362516389614758041⟩, ⟨(-559042427218284231), (-558984621186687229)⟩, true⟩

def words08 : List Nat := [371286316000357092, 371286316000989615, 371286317194288473, 371286319239784854, 371286320419429900, 371286320420003439, 371286317962345544, 371286318182137948, 371286320511350624, 371286322129351840]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362526658206511010, 362526662809079074⟩, ⟨(-749914924177588289), (-749857020849390387)⟩, true⟩

def words09 : List Nat := [371286323737427389, 371286325345541723, 371286329847174504, 371286332917986624, 371286336862444608, 371286340806692139, 371286344742113164, 371286345746789323, 371286347914769643, 371286350082835895]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk185
