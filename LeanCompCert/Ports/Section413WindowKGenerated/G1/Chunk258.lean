import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk258

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464403716629840, 362464412823932032⟩, ⟨546185012042985753, 546343866356950455⟩, true⟩

def state01 : KState := ⟨⟨362482364938721180, 362482374053310602⟩, ⟨82829189391195786, 82988231753137538⟩, true⟩

def words00 : List Nat := [371285588803513453, 371285588804345722, 371285588555953781, 371285588154539882, 371285587752855874, 371285587618406370, 371285587976675862, 371285588836566250, 371285589404334004, 371285589405180155]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362535521140974458, 362535530262938503⟩, ⟨(-1289399455893721673), (-1289240223154814077)⟩, true⟩

def words01 : List Nat := [371285590429032962, 371285591577791860, 371285594053494960, 371285594530622718, 371285594781420140, 371285595032473888, 371285596047481381, 371285596483126105, 371285598417600108, 371285600352278389]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474118139497536, 362474127268856754⟩, ⟨296152130135517426, 296311553854755592⟩, true⟩

def words02 : List Nat := [371285602180640623, 371285602181458033, 371285602066677959, 371285602122175323, 371285602630899256, 371285602631717141, 371285601428847221, 371285600217626081, 371285599006170074, 371285598873729180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362414732642536164, 362414741779259495⟩, ⟨1830587956754044632, 1830747570725959350⟩, true⟩

def words03 : List Nat := [371285598960719781, 371285599492107123, 371285600042913318, 371285600043730993, 371285598598997491, 371285597608550753, 371285596617777490, 371285596248563540, 371285593884473279, 371285591143451677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475561939610608, 362475571083656920⟩, ⟨258500360464900553, 258660163699628859⟩, true⟩

def words04 : List Nat := [371285588402264992, 371285587157836938, 371285585261989191, 371285584567236589, 371285583872272291, 371285582952016437, 371285580038043812, 371285578620183058, 371285577278691218, 371285577279544720]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489381422349017, 362489390573847896⟩, ⟨(-98793768165424485), (-98633772243545539)⟩, true⟩

def words05 : List Nat := [371285576893095743, 371285576215906504, 371285576139357165, 371285576140259250, 371285576497380965, 371285576903063199, 371285577210868115, 371285577211700695, 371285576428519848, 371285576577009277]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464069227014800, 362464078385799384⟩, ⟨555869631957344257, 556029816325501395⟩, true⟩

def words06 : List Nat := [371285577488564431, 371285577489383278, 371285576659468453, 371285575670340387, 371285574680979035, 371285573757424479, 371285572103532799, 371285571943367271, 371285571782945645, 371285571614107289]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362518553696661222, 362518562862870479⟩, ⟨(-853850258307380815), (-853689881826843263)⟩, true⟩

def words07 : List Nat := [371285571072794954, 371285571362701829, 371285573144566948, 371285573412177853, 371285573412819700, 371285573324318703, 371285574458172783, 371285575115257986, 371285576390466671, 371285577665937330]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486382602966065, 362486391776565172⟩, ⟨(-21309407644881619), (-21148839876517501)⟩, true⟩

def words08 : List Nat := [371285578933049439, 371285578933868856, 371285578212995614, 371285577925982273, 371285577688105415, 371285577688939324, 371285576625502840, 371285575554753331, 371285574902711998, 371285574935196492]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362454283745748076, 362454292926733691⟩, ⟨810044138770424644, 810204897812469316⟩, true⟩

def words09 : List Nat := [371285575899260436, 371285576863572996, 371285577532493978, 371285577533319257, 371285576946696942, 371285576812624993, 371285577226081736, 371285577226902732, 371285576176038237, 371285574969120273]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk258
