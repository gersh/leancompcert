import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479762493759144, 362479834782362805⟩, ⟨382779477022070635, 386187196891107305⟩, true⟩

def state01 : KState := ⟨⟨362478489836325070, 362478562146503715⟩, ⟨471555539090451434, 474964765002194398⟩, true⟩

def words00 : List Nat := [371285367472747998, 371285367392440223, 371285367100797808, 371285366950367244, 371285366798711550, 371285366670724296, 371285366407261520, 371285366145080618, 371285365881903387, 371285365824558467]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463945117747756, 362464017449420994⟩, ⟨1487033954847009136, 1490444681409580384⟩, true⟩

def words01 : List Nat := [371285365728749162, 371285365720332681, 371285365711145705, 371285365702399780, 371285365448300730, 371285365258118157, 371285365066691961, 371285364975050031, 371285364711563372, 371285364408478708]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475142354406856, 362475214707472851⟩, ⟨705212695926569127, 708624916239050659⟩, true⟩

def words02 : List Nat := [371285364104361340, 371285364005934554, 371285363805182483, 371285363693386518, 371285363580854140, 371285363432717385, 371285363010729490, 371285362794603876, 371285362577248104, 371285362565359706]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469980538840263, 362470052913761203⟩, ⟨1065760246698466532, 1069173993246347874⟩, true⟩

def words03 : List Nat := [371285362421842866, 371285362279097454, 371285362194505224, 371285362197139613, 371285362201563070, 371285362236856680, 371285362271753228, 371285362274143934, 371285362035915728, 371285361819735521]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473934661251977, 362474007057459335⟩, ⟨789586494820078605, 793001728122094143⟩, true⟩

def words04 : List Nat := [371285361602160386, 371285361570263506, 371285361303026372, 371285361039523782, 371285360775129169, 371285360551301678, 371285360253278541, 371285360160769039, 371285360067460374, 371285359981269244]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488398334036027, 362488470751843660⟩, ⟨(-220810912207275053), (-217394170015480965)⟩, true⟩

def words05 : List Nat := [371285359820362665, 371285359807863024, 371285359807877268, 371285359810269165, 371285359582823669, 371285359323438621, 371285359063052126, 371285359008175622, 371285358894423744, 371285358941677538]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475024218009453, 362475096657370671⟩, ⟨713524100249865949, 716942348284805413⟩, true⟩

def words06 : List Nat := [371285358944786327, 371285358947189362, 371285358754694962, 371285358714588741, 371285358673278311, 371285358674715327, 371285358423204136, 371285358135556873, 371285357846966120, 371285357747227331]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477245290375738, 362477317751299871⟩, ⟨558397416673973162, 561817171419507370⟩, true⟩

def words07 : List Nat := [371285357641905505, 371285357684462870, 371285357726579011, 371285357729019020, 371285357649540252, 371285357605265010, 371285357716958200, 371285357719350379, 371285357605649581, 371285357493306447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477540266178202, 362477612748556868⟩, ⟨537779730311847750, 541200984404777148⟩, true⟩

def words08 : List Nat := [371285357379908504, 371285357318536846, 371285357178394114, 371285357145346676, 371285357111594046, 371285357045623222, 371285356732679602, 371285356551709770, 371285356369405273, 371285356359723055]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478344299007640, 362478416803127494⟩, ⟨481600406602587074, 485023180299120508⟩, true⟩

def words09 : List Nat := [371285356250715902, 371285356142979543, 371285356084366719, 371285356087046029, 371285356067575975, 371285356056718940, 371285356045035395, 371285356016478222, 371285355714625102, 371285355618296295]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698
