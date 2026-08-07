import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk359

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502001388872868, 362502019515905474⟩, ⟨(-610856600197302399), (-610416801023187429)⟩, true⟩

def state01 : KState := ⟨⟨362476261811366689, 362476279948968057⟩, ⟨313197734309969642, 313637912953241558⟩, true⟩

def words00 : List Nat := [371285017211986301, 371285017213154706, 371285016853103104, 371285016654560970, 371285016455424336, 371285016414732217, 371285015633021981, 371285014849526390, 371285014065610496, 371285013948214876]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362442159230652522, 362442177378761321⟩, ⟨1538156284643380621, 1538596840662944509⟩, true⟩

def words01 : List Nat := [371285014237436746, 371285014770325970, 371285015300698924, 371285015301866648, 371285014799577874, 371285014340160270, 371285013880190598, 371285013735280799, 371285012557719705, 371285011366530334]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469629006573018, 362469647165134217⟩, ⟨551392933210653109, 551833864734451039⟩, true⟩

def words02 : List Nat := [371285010174875381, 371285009470833681, 371285008380323114, 371285008064648776, 371285007748618643, 371285007317025183, 371285006375382058, 371285006028415098, 371285005746300131, 371285005747509237]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487871489792615, 362487889658998748⟩, ⟨(-104178714361480965), (-103737400310798065)⟩, true⟩

def words03 : List Nat := [371285005320952266, 371285004653619068, 371285004091202829, 371285004092490139, 371285003893725714, 371285003912875298, 371285003913763934, 371285003784776505, 371285003252437511, 371285003334179996]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466933229783154, 362466951409392407⟩, ⟨648497131341847277, 648938819335000755⟩, true⟩

def words04 : List Nat := [371285004109117300, 371285004110286261, 371285003854332412, 371285003597159477, 371285003339561926, 371285003107379354, 371285002532252585, 371285002576231164, 371285002577106498, 371285002558748040]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488544565540895, 362488562755745078⟩, ⟨(-128442183309293269), (-128000114377037717)⟩, true⟩

def words05 : List Nat := [371285002328233996, 371285002600453398, 371285003533572578, 371285003534741884, 371285003437739011, 371285003145317248, 371285003139507935, 371285003140870308, 371285003240671335, 371285003340979721]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488605006443751, 362488623207196240⟩, ⟨(-130742282162870445), (-130299833859877545)⟩, true⟩

def words06 : List Nat := [371285003439350457, 371285003440520071, 371285002509097097, 371285002350573557, 371285002267206378, 371285002268396577, 371285001715021612, 371285001135670596, 371285000747309044, 371285000849356317]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460670649324500, 362460688860603376⟩, ⟨874284738601110103, 874727565592635557⟩, true⟩

def words07 : List Nat := [371285001465379327, 371285002081834140, 371285002528352466, 371285002529522506, 371285001946892653, 371285001589202758, 371285001643526986, 371285001644697066, 371285001029310403, 371285000354922238]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362457540375912242, 362457558597659096⟩, ⟨987046565507063681, 987489769190631351⟩, true⟩

def words08 : List Nat := [371284999680045893, 371284999395167352, 371284998826113999, 371284998928202747, 371284998929108271, 371284998912096001, 371284998098844172, 371284997465585653, 371284996831773014, 371284996490662448]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473350931059208, 362473369163496633⟩, ⟨417975384199469459, 418418972688395369⟩, true⟩

def words09 : List Nat := [371284995729193351, 371284994959913615, 371284994190837149, 371284994192148710, 371284993911125183, 371284993722482621, 371284993533470623, 371284993327215702, 371284992234119682, 371284991912737978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk359
