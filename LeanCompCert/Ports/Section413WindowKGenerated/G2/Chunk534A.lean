import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578677539574029, 360578695524688799⟩, ⟨177907566902816956, 178556480711419108⟩, true⟩

def state01 : KState := ⟨⟨360585087227094633, 360585105219197199⟩, ⟨(-164481539257222498), (-163832252266241612)⟩, true⟩

def words00 : List Nat := [360582039504376456, 360582039505117305, 360582039443325241, 360582039110645094, 360582038777857151, 360582038215712872, 360582037926978661, 360582037958033291, 360582037958694707, 360582037831350759]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615277075572617, 360615295074664714⟩, ⟨(-1777075069164504565), (-1776425408827392237)⟩, true⟩

def words01 : List Nat := [360582038239299687, 360582038647450567, 360582039267780505, 360582039773199585, 360582039979093523, 360582040185036249, 360582040238510428, 360582040512021985, 360582041135132631, 360582041758387831]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583013772729239, 360583031778879957⟩, ⟨(-53538836024853399), (-52888798582017141)⟩, true⟩

def words02 : List Nat := [360582042205909778, 360582042303900594, 360582042608893481, 360582042914113968, 360582043128634500, 360582043129375669, 360582042994362612, 360582042596796284, 360582042199101864, 360582041926573581]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560039526208882, 360560057539344481⟩, ⟨1173994945594000916, 1174645356274243426⟩, true⟩

def words03 : List Nat := [360582041927184926, 360582041795437871, 360582041663621492, 360582041352177813, 360582040691149160, 360582039942203086, 360582039193067486, 360582038793710829, 360582038589050985, 360582038178496320]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557869316689282, 360557887336822851⟩, ⟨1290104406591342168, 1290755191277888592⟩, true⟩

def words04 : List Nat := [360582037767789074, 360582037819464276, 360582038036836615, 360582038254340563, 360582038255035967, 360582038142905383, 360582037681272919, 360582037196843937, 360582036712217820, 360582036171084365]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk534A
