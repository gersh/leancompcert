import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586099673561848, 360586128954312203⟩, ⟨(-219174860708195563), (-217839792264672995)⟩, true⟩

def state01 : KState := ⟨⟨360551823024987376, 360551852314724398⟩, ⟨2094622278693085935, 2095957953782407451⟩, true⟩

def words00 : List Nat := [360582901789691042, 360582901790644200, 360582901615311433, 360582901330388720, 360582901045320183, 360582900639642013, 360582900344067613, 360582899924622265, 360582899505080818, 360582898944168665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584810471416237, 360584839770144135⟩, ⟨(-132561297598883184), (-131225015491206680)⟩, true⟩

def words01 : List Nat := [360582898485064256, 360582898245325966, 360582898005314214, 360582897945735173, 360582897667016499, 360582897182513999, 360582896697843370, 360582896387259003, 360582896270705065, 360582896300475570]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578820095696346, 360578849403519172⟩, ⟨271951247689872869, 273288143930737053⟩, true⟩

def words02 : List Nat := [360582896301325155, 360582896217399511, 360582896451514777, 360582896685905621, 360582896802729809, 360582896824180384, 360582896825039134, 360582896694586632, 360582896563972835, 360582896318133873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554981536018898, 360555010852819044⟩, ⟨1881965533208111159, 1883303035732949315⟩, true⟩

def words03 : List Nat := [360582896417995347, 360582896577961468, 360582896628237298, 360582896629190903, 360582896460456064, 360582896172377269, 360582895883998983, 360582895814721857, 360582895526394471, 360582895114526669]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567402375483770, 360567431701295298⟩, ⟨1042912370669557992, 1044250481867010710⟩, true⟩

def words04 : List Nat := [360582894702451203, 360582894266852978, 360582893941267463, 360582893611036192, 360582893280750736, 360582892767576857, 360582892035335590, 360582891522257413, 360582891008910305, 360582890627747808]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360563591578607925, 360563620913497404⟩, ⟨1300304857493159641, 1301643581951162965⟩, true⟩

def words05 : List Nat := [360582890399756479, 360582889986521582, 360582889573116634, 360582889299787433, 360582889140552137, 360582888878335849, 360582888616038165, 360582888183650109, 360582887680448421, 360582887396356362]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580258365732009, 360580287709603195⟩, ⟨174190595874440756, 175529927180991960⟩, true⟩

def words06 : List Nat := [360582887111959810, 360582886892293429, 360582886724231397, 360582886445807619, 360582886167217873, 360582885833825364, 360582885610320883, 360582885605727512, 360582885601029908, 360582885459006496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610422388266739, 360610451741160515⟩, ⟨(-1864263518244646068), (-1862923577237825612)⟩, true⟩

def words07 : List Nat := [360582885421346953, 360582885369749531, 360582885317869217, 360582885314542010, 360582885315425653, 360582885119235024, 360582884944396262, 360582885134726765, 360582885543409019, 360582885952296222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592760112835865, 360592789474821220⟩, ⟨(-670714122871017430), (-669373567408703268)⟩, true⟩

def words08 : List Nat := [360582886251102619, 360582886331295916, 360582886507248227, 360582886683480679, 360582886708091269, 360582886709045940, 360582886588523358, 360582886330809418, 360582886072920209, 360582886180486047]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555287026028821, 360555316397016958⟩, ⟨1862370077008159565, 1863711241012276207⟩, true⟩

def words09 : List Nat := [360582886504363213, 360582886828432893, 360582887042906096, 360582887043860562, 360582887039659075, 360582886892210230, 360582886744486491, 360582886700404666, 360582886496779160, 360582886089931341]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk675
