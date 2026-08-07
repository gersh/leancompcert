import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk287

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362525995528501932, 362526006899486651⟩, ⟨(-1173292413302926300), (-1173071810226240622)⟩, true⟩

def state01 : KState := ⟨⟨362507445045659140, 362507456424924228⟩, ⟨(-640886575834083252), (-640665735070059998)⟩, true⟩

def words00 : List Nat := [371285136169960513, 371285136186832840, 371285137416525286, 371285138646624896, 371285140242764949, 371285140490158455, 371285140490856337, 371285140482869118, 371285141351236543, 371285142129529778]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498543226473721, 362498554613993732⟩, ⟨(-385086168084848504), (-384865090278778396)⟩, true⟩

def words01 : List Nat := [371285144119812328, 371285146110336405, 371285147923162965, 371285148766890002, 371285149976889312, 371285151187245923, 371285153074618164, 371285153550583465, 371285154017886911, 371285154485506605]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362520877217628530, 362520888613376002⟩, ⟨(-1026687403182720403), (-1026466089044009863)⟩, true⟩

def words02 : List Nat := [371285155076413029, 371285155077423176, 371285156258612839, 371285157455654704, 371285158448210505, 371285158449127991, 371285158483880108, 371285158931496236, 371285160589828624, 371285161834320487]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508865210302964, 362508876614388115⟩, ⟨(-681458592068727470), (-681237038345152534)⟩, true⟩

def words03 : List Nat := [371285162971859409, 371285164109625787, 371285166228036837, 371285167741561840, 371285169296368689, 371285170851419245, 371285172402801562, 371285172403719119, 371285173167252806, 371285173993103360]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477103536849600, 362477114949121399⟩, ⟨231652571956107884, 231874361006610176⟩, true⟩

def words04 : List Nat := [371285175732302218, 371285176466646013, 371285176928585311, 371285177390801273, 371285178218709367, 371285178449076388, 371285179119590536, 371285179790418715, 371285180143334473, 371285180144286847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362557799430457973, 362557810851035880⟩, ⟨(-2088728064027711045), (-2088506036134239331)⟩, true⟩

def words05 : List Nat := [371285180793248864, 371285181723150947, 371285183861774859, 371285184925136905, 371285185790417197, 371285186655928264, 371285188577367523, 371285189894676173, 371285192420367885, 371285194946299111]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362508643676323924, 362508655105203657⟩, ⟨(-674868876822989794), (-674646610127521456)⟩, true⟩

def words06 : List Nat := [371285197472611208, 371285198595452859, 371285200177246245, 371285201759396064, 371285203395599427, 371285203791769126, 371285204081241093, 371285204371015943, 371285205447895077, 371285206264004967]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473307988232528, 362473319425363590⟩, ⟨342115457002446782, 342337961131823836⟩, true⟩

def words07 : List Nat := [371285208287678239, 371285210311574926, 371285212261300830, 371285212602675628, 371285213310271193, 371285214018284806, 371285215229089155, 371285215230008074, 371285214832837668, 371285214420538428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499039180345972, 362499050625707608⟩, ⟨(-398467788436637127), (-398245047389405615)⟩, true⟩

def words08 : List Nat := [371285214357401187, 371285214358428981, 371285215291136703, 371285216284093548, 371285217100128271, 371285217101047951, 371285216576821443, 371285216619846647, 371285217868681618, 371285218350087123]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362527367614883071, 362527379068655510⟩, ⟨(-1214220372835944955), (-1213997389601626995)⟩, true⟩

def words09 : List Nat := [371285218613385673, 371285218876965182, 371285220346217727, 371285221212684989, 371285222322532145, 371285223432643246, 371285224438556428, 371285224916042195, 371285226380353178, 371285227845100716]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk287
