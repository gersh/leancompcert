import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557644789582980, 360557703454242711⟩, ⟨2295776150421596506, 2299511728208512140⟩, true⟩

def state01 : KState := ⟨⟨360582571110618703, 360582629788164565⟩, ⟨(-54911603752421591), (-51174810739418721)⟩, true⟩

def words00 : List Nat := [360582088262805715, 360582088099695639, 360582088010431314, 360582087938419504, 360582087866279086, 360582087698854103, 360582087452788481, 360582087319495930, 360582087185803597, 360582087170540541]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585844077671679, 360585902768258683⟩, ⟨(-363638355115365362), (-359900332129121508)⟩, true⟩

def words01 : List Nat := [360582087171791180, 360582087092593017, 360582087013135206, 360582087071228835, 360582087082041157, 360582087093077714, 360582087094294475, 360582087040518047, 360582087029491794, 360582087071519579]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581743348702581, 360581802052142124⟩, ⟨23145128124556199, 26884363427131653⟩, true⟩

def words02 : List Nat := [360582087225413075, 360582087267509055, 360582087268727614, 360582087238704351, 360582087208488277, 360582087076261685, 360582087043430369, 360582087083997877, 360582087085226563, 360582087055464791]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585983067448374, 360586041783801232⟩, ⟨(-376802238149544156), (-373061784669705530)⟩, true⟩

def words03 : List Nat := [360582087162844513, 360582087273670834, 360582087381982776, 360582087406436463, 360582087407699005, 360582087336871353, 360582087265774709, 360582087300245695, 360582087343286596, 360582087386617932]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595655195525969, 360595713924889064⟩, ⟨(-1289437687502931662), (-1285696006575113056)⟩, true⟩

def words04 : List Nat := [360582087387841620, 360582087342328583, 360582087224675300, 360582087219712773, 360582087214387873, 360582087182882795, 360582087184119783, 360582087100733425, 360582087044610274, 360582087190603523]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596768203727674, 360596826945977399⟩, ⟨(-1394416010504079771), (-1390673113658378965)⟩, true⟩

def words05 : List Nat := [360582087448402893, 360582087706458871, 360582087877908155, 360582088068358879, 360582088219714520, 360582088371443612, 360582088612202526, 360582088835522960, 360582088992930715, 360582089150557063]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596966026452516, 360597024781594729⟩, ⟨(-1412998717914139665), (-1409254604469207243)⟩, true⟩

def words06 : List Nat := [360582089397593272, 360582089701022317, 360582090100224103, 360582090499680581, 360582090802134219, 360582091043265824, 360582091200769505, 360582091358643512, 360582091489891813, 360582091649547075]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594640037775566, 360594698805936974⟩, ⟨(-1193489069874381544), (-1189743727746903624)⟩, true⟩

def words07 : List Nat := [360582091747134372, 360582091844868815, 360582091991671691, 360582092226661380, 360582092425358806, 360582092624274232, 360582092758765817, 360582092781493906, 360582092916165454, 360582093051306838]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584232725080388, 360584291506114607⟩, ⟨(-211243503319104865), (-207496946189971313)⟩, true⟩

def words08 : List Nat := [360582093157574878, 360582093198144985, 360582093199374189, 360582093184004810, 360582093168409342, 360582093105860644, 360582093155995694, 360582093214521405, 360582093215739419, 360582093235663082]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594081454952484, 360594140248892799⟩, ⟨(-1140997390314332889), (-1137249614915718135)⟩, true⟩

def words09 : List Nat := [360582093276990329, 360582093318731868, 360582093357848377, 360582093359215721, 360582093309302507, 360582093158031755, 360582093006502068, 360582092982999345, 360582093111723980, 360582093240758185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk943
