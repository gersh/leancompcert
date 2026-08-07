import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk371

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492790455108226, 362492809866899021⟩, ⟨(-296258556403168902), (-295771858867880060)⟩, true⟩

def state01 : KState := ⟨⟨362459658472084002, 362459677894776809⟩, ⟨933037686708067243, 933524788764667901⟩, true⟩

def words00 : List Nat := [371284837979656663, 371284837980872049, 371284837471491521, 371284837330605663, 371284837189115025, 371284837161767792, 371284836166221846, 371284835081270861, 371284833995898168, 371284833507516359]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362453520077415245, 362453539511015387⟩, ⟨1160925623976888559, 1161413130859836163⟩, true⟩

def words01 : List Nat := [371284832830492451, 371284832404712363, 371284831978536690, 371284831541950731, 371284830701484352, 371284829979853012, 371284829260295931, 371284829261506413, 371284828421808135, 371284827580273465]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478533647863360, 362478553092316200⟩, ⟨232315646405652565, 232803556193883479⟩, true⟩

def words02 : List Nat := [371284826738242052, 371284826196729442, 371284825359579989, 371284825248366156, 371284825136809821, 371284824806575085, 371284823731146128, 371284823295443852, 371284823049484267, 371284823050737797]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486333755633190, 362486353211089633⟩, ⟨(-57326299210045124), (-56837980800814694)⟩, true⟩

def words03 : List Nat := [371284822882782560, 371284822713124092, 371284822997684276, 371284823090992671, 371284823220756831, 371284823350987078, 371284823478851424, 371284823480063315, 371284822838554599, 371284822881243889]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456460040618476, 362456479506871796⟩, ⟨1052440950208640102, 1052929669669668682⟩, true⟩

def words04 : List Nat := [371284823408214416, 371284823409446784, 371284823344684471, 371284823282849746, 371284823220549890, 371284823097139209, 371284822650900040, 371284822559926552, 371284822468576330, 371284822162852138]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362513036085046818, 362513055562267648⟩, ⟨(-1049661024725545759), (-1049171897767255913)⟩, true⟩

def words05 : List Nat := [371284821400770188, 371284821233398362, 371284821513674482, 371284821514891794, 371284821271394566, 371284820917650079, 371284820858199431, 371284820895583975, 371284821656219843, 371284822417363925]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473496667564944, 362473516155745709⟩, ⟨419785051251241793, 420274585535787995⟩, true⟩

def words06 : List Nat := [371284823180761385, 371284823208206181, 371284823535132572, 371284823862643747, 371284824407511356, 371284824408723452, 371284823988983379, 371284823553330468, 371284823117197178, 371284822978063057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362449243231896827, 362449262730970409⟩, ⟨1321559602705515488, 1322049541932460790⟩, true⟩

def words07 : List Nat := [371284823093873587, 371284823514327052, 371284823932494754, 371284823933707022, 371284823387528679, 371284823057521230, 371284822726908653, 371284822636715095, 371284821769437496, 371284820814400546]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467135054874306, 362467154564789545⟩, ⟨656327975422035912, 656818317797502496⟩, true⟩

def words08 : List Nat := [371284819858872462, 371284819626900615, 371284819034873650, 371284818921747488, 371284818808210707, 371284818491230328, 371284817210197863, 371284816472416799, 371284815734048330, 371284815718803998]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473295079807959, 362473314600796191⟩, ⟨427150391124342095, 427641145359117103⟩, true⟩

def words09 : List Nat := [371284815244857118, 371284814524970580, 371284813804623473, 371284813568294815, 371284812972090794, 371284812536753384, 371284812101046341, 371284811668650221, 371284810638022883, 371284810330510146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk371
