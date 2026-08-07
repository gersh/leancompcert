import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk409

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475800665089802, 362475824445219833⟩, ⟨379253944548021445, 379911152445035803⟩, true⟩

def state01 : KState := ⟨⟨362481514844828072, 362481538636986608⟩, ⟨145595481997235044, 146253181922539612⟩, true⟩

def words00 : List Nat := [371285113020617368, 371285113022101187, 371285113181900471, 371285113561329668, 371285113818719838, 371285113820063410, 371285113368013127, 371285113355125273, 371285113633931769, 371285113635322530]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469855486316894, 362469879290727122⟩, ⟨622718024197477480, 623376225400165236⟩, true⟩

def words01 : List Nat := [371285113548947182, 371285113459403565, 371285113795412349, 371285113925496615, 371285114066623951, 371285114208229959, 371285114289343718, 371285114290688209, 371285113684439621, 371285113313830743]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477269895710237, 362477293712101167⟩, ⟨319376756719937413, 320035448235633291⟩, true⟩

def words02 : List Nat := [371285113095034593, 371285113096402764, 371285112846611452, 371285112596995980, 371285112346884995, 371285112285235305, 371285112304771929, 371285112613737022, 371285112803019326, 371285112804410858]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502014493518785, 362502038322047213⟩, ⟨(-693569258333570808), (-692910069969109668)⟩, true⟩

def words03 : List Nat := [371285112662599664, 371285112712508118, 371285113357973845, 371285113359318486, 371285113286321098, 371285113122798467, 371285113073589201, 371285113075070476, 371285113306625426, 371285113721525265]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487184246272440, 362487208086967083⟩, ⟨(-86439922536989180), (-85780236027495190)⟩, true⟩

def words04 : List Nat := [371285114136021570, 371285114137375441, 371285114145389563, 371285114274091453, 371285114537024143, 371285114538369403, 371285114088001195, 371285113637301780, 371285113329924832, 371285113382661267]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362449516852584356, 362449540705385430⟩, ⟨1456357633183339493, 1457017815513830469⟩, true⟩

def words05 : List Nat := [371285113932038621, 371285114481946911, 371285114876213980, 371285114877559213, 371285114477712905, 371285114257616487, 371285114062338788, 371285114063684149, 371285113296337970, 371285112429396999]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362464891647031702, 362464915511878906⟩, ⟨826575145404328425, 827235821205083515⟩, true⟩

def words06 : List Nat := [371285111561880891, 371285111290460753, 371285110721117566, 371285110385908835, 371285110050271734, 371285109624730868, 371285108405204323, 371285107691602336, 371285106977312547, 371285106769413812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469010081830288, 362469033958933226⟩, ⟨657825235955203606, 658486413937002506⟩, true⟩

def words07 : List Nat := [371285106277619114, 371285105667806537, 371285105057489147, 371285105042921382, 371285104730724023, 371285104410359183, 371285104089541971, 371285103708405889, 371285102831923821, 371285102441459752]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362456437761243324, 362456461650330693⟩, ⟨1173157654226656523, 1173819323391925813⟩, true⟩

def words08 : List Nat := [371285102185616978, 371285102186964166, 371285101653313536, 371285101101188807, 371285100548580150, 371285100026774019, 371285099329391426, 371285099011757268, 371285098693701515, 371285098374492487]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478965319105382, 362478989220386361⟩, ⟨249715137870097591, 250377306911093505⟩, true⟩

def words09 : List Nat := [371285097676796228, 371285097497554053, 371285097731307962, 371285097732654572, 371285097429132151, 371285097026264257, 371285096622886506, 371285096525797079, 371285096131391749, 371285095983969559]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk409
