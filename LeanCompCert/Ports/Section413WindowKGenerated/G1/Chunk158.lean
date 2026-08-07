import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk158

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362565802931949453, 362565806205234467⟩, ⟨(-1289157866936215408), (-1289122882449899162)⟩, true⟩

def state01 : KState := ⟨⟨362538371115220676, 362538374392845032⟩, ⟨(-855873873484002009), (-855838820413997219)⟩, true⟩

def words00 : List Nat := [371284226014185861, 371284226014666679, 371284228752021666, 371284232124954468, 371284236281392028, 371284237149288363, 371284237310370527, 371284237471601802, 371284241639580964, 371284245063870648]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515195324974331, 362515198606928096⟩, ⟨(-489224614263405109), (-489189492722850523)⟩, true⟩

def words01 : List Nat := [371284251558505613, 371284258052509759, 371284263690853711, 371284263999843433, 371284265484911234, 371284266970031708, 371284272457076482, 371284274433020951, 371284276388132848, 371284278343182262]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503109943094356, 362503113229355936⟩, ⟨(-297637120995708152), (-297601931283374424)⟩, true⟩

def words02 : List Nat := [371284282894823873, 371284285536986676, 371284292177902576, 371284298818181153, 371284304768997758, 371284306213289778, 371284307936838411, 371284309660404825, 371284313359540715, 371284314547574408]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362525814644727948, 362525817935389632⟩, ⟨(-657026222066342068), (-656990962679018472)⟩, true⟩

def words03 : List Nat := [371284315759693467, 371284316971822340, 371284321367297139, 371284324947568266, 371284329702850694, 371284334457712410, 371284339191541021, 371284339192023275, 371284341232588164, 371284343851513677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362443485742840052, 362443489037799993⟩, ⟨647506207112146642, 647541534606307234⟩, true⟩

def words04 : List Nat := [371284347773652585, 371284347774134963, 371284346751566596, 371284345710840189, 371284344806743565, 371284344807275718, 371284343454885451, 371284343482359774, 371284343482724245, 371284343393295660]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362509721291978287, 362509724591291238⟩, ⟨(-402770475876806955), (-402735079364929281)⟩, true⟩

def words05 : List Nat := [371284340816226451, 371284340136803420, 371284342272210592, 371284342272693297, 371284339787755841, 371284336203927791, 371284332620350345, 371284332234116934, 371284331458382994, 371284333059901986]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362445961791888432, 362445965095560307⟩, ⟨608798373460566818, 608833839127520864⟩, true⟩

def words06 : List Nat := [371284334185922245, 371284334186416813, 371284334961996983, 371284336769471965, 371284339394274576, 371284339394757791, 371284336727317430, 371284333588003338, 371284330448899244, 371284328916551330]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362408336592640955, 362408339900670628⟩, ⟨1206260285014242110, 1206295819860947618⟩, true⟩

def words07 : List Nat := [371284327182610534, 371284327866014056, 371284327866379754, 371284327577492921, 371284322002720024, 371284317487081016, 371284312971751582, 371284312424852558, 371284307896840509, 371284303113508220]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501867105794507, 362501870418157268⟩, ⟨(-279456192858285774), (-279420589179816564)⟩, true⟩

def words08 : List Nat := [371284298330560290, 371284297515302825, 371284294736340940, 371284293564031721, 371284292391723271, 371284290522643932, 371284285361360011, 371284284165181643, 371284285736139134, 371284286843229333]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452302898409876, 362452306215169429⟩, ⟨508535807516001327, 508571481082238661⟩, true⟩

def words09 : List Nat := [371284287936183949, 371284289029159877, 371284292944744281, 371284294883792965, 371284296325962984, 371284297768136961, 371284298446329657, 371284298446813614, 371284293854118392, 371284291842910451]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk158
