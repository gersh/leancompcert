import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk095

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360815858872178559, 360815859360616492⟩, ⟨(-2279677148141561340), (-2279674002511578584)⟩, true⟩

def state01 : KState := ⟨⟨360704697722831273, 360704698212357574⟩, ⟨(-1224259477282364581), (-1224256321307356655)⟩, true⟩

def words00 : List Nat := [360575938537150030, 360575947195934394, 360575952229050234, 360575957261141418, 360575959397711901, 360575963527759969, 360575963527861923, 360575962023549816, 360575964634803036, 360575978170163551]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360487794954313081, 360487795444919124⟩, ⟨840230375189888625, 840233541438653207⟩, true⟩

def words01 : List Nat := [360576002715614945, 360576027255927754, 360576042974434589, 360576053066396192, 360576055682606232, 360576058298296444, 360576066875009055, 360576066875123552, 360576064542543881, 360576055270700496]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360674680207343527, 360674680699030580⟩, ⟨(-939331981659923913), (-939328805114499089)⟩, true⟩

def words02 : List Nat := [360576047726043978, 360576056405950942, 360576072133242242, 360576087857252911, 360576094049633952, 360576098964177161, 360576103407122128, 360576107849166158, 360576115241922110, 360576125583605704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360753602040276617, 360753602533056092⟩, ⟨(-1691892687599510088), (-1691889500637932146)⟩, true⟩

def words03 : List Nat := [360576130140927169, 360576134697303967, 360576150214268431, 360576174631953508, 360576196179788867, 360576217723124048, 360576229387913272, 360576237033236433, 360576255625100866, 360576274213106618]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360729282936626086, 360729283430488242⟩, ⟨(-1460356927912480458), (-1460353730616736656)⟩, true⟩

def words04 : List Nat := [360576288257794914, 360576299561028644, 360576305275636507, 360576310989059464, 360576310989155815, 360576317719648019, 360576335925055579, 360576354126674601, 360576366809362391, 360576382820016382]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360867398678541185, 360867399173487808⟩, ⟨(-2779833260389247102), (-2779830052731580710)⟩, true⟩

def words05 : List Nat := [360576409754552443, 360576436683482757, 360576469287268585, 360576498677169825, 360576518046518901, 360576537411821320, 360576561219353910, 360576591551899401, 360576621971200432, 360576652384163305]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360799764643957585, 360799765140000200⟩, ⟨(-2133278009501024192), (-2133274791360243164)⟩, true⟩

def words06 : List Nat := [360576677225737395, 360576702436727033, 360576734488622571, 360576766533849429, 360576795727260425, 360576814130303902, 360576827050506136, 360576839968020218, 360576852413498583, 360576875704062447]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541996325502661, 360541996822628497⟩, ⟨335198119589493410, 335201348102238988⟩, true⟩

def words07 : List Nat := [360576902187362640, 360576928665151539, 360576949594244724, 360576959750674908, 360576966793028333, 360576973833944642, 360576987389040910, 360576990177464883, 360576990177567593, 360576986524935621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563848661736451, 360563849159951344⟩, ⟨124958653649224335, 124961892600464609⟩, true⟩

def words08 : List Nat := [360576982873041475, 360576974539522987, 360576971690813700, 360576966016050082, 360576960342462518, 360576945120816046, 360576919155278375, 360576904028104387, 360576888904051894, 360576879597135960]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360444584052054263, 360444584551367816⟩, ⟨1269510078848818113, 1269513328341738167⟩, true⟩

def words09 : List Nat := [360576878238627960, 360576869907095800, 360576861577278079, 360576866126162593, 360576866259273037, 360576866392374313, 360576866392478929, 360576858209132096, 360576839299474961, 360576825523070081]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk095
