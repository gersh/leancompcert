import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk490

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459967373056119, 362460002009947485⟩, ⟨1224117006352163216, 1225263655707885744⟩, true⟩

def state01 : KState := ⟨⟨362476054053022210, 362476088704519840⟩, ⟨435819617041327844, 436966982179232674⟩, true⟩

def words00 : List Nat := [371285006881483535, 371285006677949527, 371285006266428561, 371285006269478733, 371285006270764608, 371285006148033749, 371285005519868037, 371285005068059757, 371285004615403310, 371285004578467591]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480809462746682, 362480844129103031⟩, ⟨202746419311368017, 203894512750345789⟩, true⟩

def words01 : List Nat := [371285004397777426, 371285004178449775, 371285004034094966, 371285004035942510, 371285004013710564, 371285004068326703, 371285004123767422, 371285004125400779, 371285003626732083, 371285003543887820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450015140333630, 362450049821259202⟩, ⟨1712445887031379152, 1713594694728891320⟩, true⟩

def words02 : List Nat := [371285003488659072, 371285003490292818, 371285003017234699, 371285002537271727, 371285002056682672, 371285001638925737, 371285001012061091, 371285000600687794, 371285000188760120, 371284999743648125]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482058947735508, 362482093643449851⟩, ⟨141213971865913715, 142363504730031399⟩, true⟩

def words03 : List Nat := [371284999031944289, 371284998735907630, 371284998555743406, 371284998557377425, 371284998121725108, 371284997597398840, 371284997072433344, 371284996962862927, 371284996708635738, 371284996651295081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362461258155428793, 362461292865910433⟩, ⟨1161434318145053257, 1162584575272696983⟩, true⟩

def words04 : List Nat := [371284996593333020, 371284996533655910, 371284996283131689, 371284996366548221, 371284996472837570, 371284996474472393, 371284996076202630, 371284995679865080, 371284995282897842, 371284994895987349]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362457520491158334, 362457555216345734⟩, ⟨1344861654266345901, 1346012632785572563⟩, true⟩

def words05 : List Nat := [371284994413884840, 371284994313239749, 371284994212062475, 371284994122587932, 371284993479383415, 371284992965896474, 371284992451526496, 371284992352052620, 371284991824162058, 371284991266749028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473746661602954, 362473781401436676⟩, ⟨548737765701829761, 549889462843496919⟩, true⟩

def words06 : List Nat := [371284990708635555, 371284990517012250, 371284990195046479, 371284989975474813, 371284989755389219, 371284989464453416, 371284988620019832, 371284988151129365, 371284987681409231, 371284987626479340]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463201293478169, 362463236048216910⟩, ⟨1066289618506024524, 1067442047113488060⟩, true⟩

def words07 : List Nat := [371284987399343041, 371284987088996611, 371284986814336164, 371284986816138329, 371284986645734086, 371284986543427496, 371284986440624379, 371284986220396125, 371284985512284835, 371284985071181733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471703591558855, 362471738360876965⟩, ⟨649031673323026231, 650184817560301705⟩, true⟩

def words08 : List Nat := [371284984629166862, 371284984601672951, 371284984294107498, 371284983988326532, 371284983681916718, 371284983504983388, 371284983122557907, 371284983118742506, 371284983114343497, 371284983111693024]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484727266822713, 362484762050922984⟩, ⟨9589390452023190, 10743260421013728⟩, true⟩

def words09 : List Nat := [371284982843022822, 371284982750136345, 371284982776061727, 371284982777698151, 371284982346307473, 371284981855219620, 371284981363464931, 371284981183693767, 371284980857229500, 371284980854597547]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk490
