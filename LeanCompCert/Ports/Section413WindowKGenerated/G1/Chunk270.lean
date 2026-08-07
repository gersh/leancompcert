import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk270

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486525677314296, 362486535689630141⟩, ⟨(-34718227585004993), (-34535476310169989)⟩, true⟩

def state01 : KState := ⟨⟨362467459636493347, 362467469656448652⟩, ⟨480152109869711738, 480335067449925296⟩, true⟩

def words00 : List Nat := [371285257347259153, 371285257348118001, 371285256587245548, 371285255824171828, 371285255060838809, 371285254357090912, 371285253191009327, 371285253223188307, 371285253256724629, 371285253257613033]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362520388413407555, 362520398441122782⟩, ⟨(-949744912487657706), (-949561745272222036)⟩, true⟩

def words01 : List Nat := [371285253311356920, 371285254023865264, 371285254901000876, 371285254901863114, 371285254481690861, 371285253852285958, 371285253961891972, 371285254217158586, 371285255518416358, 371285256819966192]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475902318585027, 362475912354042973⟩, ⟨252401680556972282, 252585057019715050⟩, true⟩

def words02 : List Nat := [371285258118282509, 371285258119141173, 371285258644057858, 371285259489661758, 371285260442585717, 371285260443444275, 371285259572633697, 371285258311851624, 371285257050821858, 371285256973244591]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486531981481861, 362486542024684141⟩, ⟨(-34807764566403302), (-34624178734862674)⟩, true⟩

def words03 : List Nat := [371285257650382101, 371285258673500492, 371285259693662679, 371285259694536407, 371285259875862221, 371285260172321505, 371285261445261078, 371285261495720532, 371285261543720234, 371285261592054621]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473418007234400, 362473428058133640⟩, ⟨320003028444118921, 320186822440656143⟩, true⟩

def words04 : List Nat := [371285262208856296, 371285262209802650, 371285263446843168, 371285264749185395, 371285265808411669, 371285265809270979, 371285265047514891, 371285264766872741, 371285264908350211, 371285264909240504]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470763940478625, 362470773999197248⟩, ⟨391818596433617979, 392002601983521321⟩, true⟩

def words05 : List Nat := [371285264472308388, 371285263965616622, 371285263841325705, 371285263842282057, 371285263573579704, 371285263366594691, 371285263159323471, 371285262856434864, 371285260956337902, 371285260422034777]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477709423002651, 362477719489383024⟩, ⟨203976349573447417, 204160562490817415⟩, true⟩

def words06 : List Nat := [371285260717084228, 371285260717958860, 371285260416484813, 371285260020348527, 371285259636275570, 371285259637227228, 371285259991311482, 371285260851191612, 371285261437605949, 371285261438496095]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362514263639910777, 362514273714078114⟩, ⟨(-785779774346033029), (-785595350596871463)⟩, true⟩

def words07 : List Nat := [371285261250669919, 371285261341897614, 371285262796857226, 371285262797717553, 371285262435200693, 371285261932769671, 371285262290556654, 371285262473158600, 371285263545061875, 371285264617272351]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481133739225492, 362481143821173693⟩, ⟨111391981971319878, 111576616465380034⟩, true⟩

def words08 : List Nat := [371285265442659389, 371285265443525664, 371285265067806069, 371285265086238529, 371285265512839217, 371285265513700722, 371285264486040634, 371285263455737924, 371285262558315603, 371285262559323025]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471716371047777, 362471726460734560⟩, ⟨366744699871443662, 366929544043951032⟩, true⟩

def words09 : List Nat := [371285263618288819, 371285264829544296, 371285265763647714, 371285265764512412, 371285266060428814, 371285266413490127, 371285267294753011, 371285267295616451, 371285266794991938, 371285266296308138]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk270
