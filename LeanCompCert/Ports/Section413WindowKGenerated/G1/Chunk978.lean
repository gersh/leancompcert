import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484519790233311, 362484665455576778⟩, ⟨57106395446204757, 66724633164674155⟩, true⟩

def state01 : KState := ⟨⟨362474241240338462, 362474386936236704⟩, ⟨1062390388054422668, 1072011614191764050⟩, true⟩

def words00 : List Nat := [371285347725303909, 371285347728738000, 371285347623083270, 371285347518767748, 371285347413105618, 371285347336178579, 371285347205636627, 371285347164139791, 371285347121438267, 371285347079516449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484129531192805, 362484275258157043⟩, ⟨95148260226333973, 104772525079788043⟩, true⟩

def words01 : List Nat := [371285346969831496, 371285346893576390, 371285346839633246, 371285346843067289, 371285346730554199, 371285346602923908, 371285346473869212, 371285346423781174, 371285346339957839, 371285346332835839]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472751603995530, 362472897361949324⟩, ⟨1208148205600290139, 1217775502010773275⟩, true⟩

def words02 : List Nat := [371285346324479897, 371285346316791318, 371285346181632039, 371285346101814252, 371285346020305676, 371285345940290232, 371285345737625173, 371285345535883235, 371285345332775801, 371285345235832702]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470635947170473, 362470781736127279⟩, ⟨1415164438957194479, 1424794768550956681⟩, true⟩

def words03 : List Nat := [371285345110928057, 371285345061229666, 371285345010275371, 371285344960002994, 371285344815073647, 371285344681433180, 371285344546047215, 371285344504143102, 371285344378696881, 371285344233761692]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492485580761712, 362492631400454835⟩, ⟨(-722698062260612452), (-713064725272496728)⟩, true⟩

def words04 : List Nat := [371285344087252325, 371285344046716279, 371285343979446686, 371285344000598011, 371285344003274152, 371285343989687927, 371285343924331571, 371285343946923232, 371285344072151372, 371285344150194005]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493130745385168, 362493276596390646⟩, ⟨(-785832979861807940), (-776196578803677486)⟩, true⟩

def words05 : List Nat := [371285344227959646, 371285344306851302, 371285344426758994, 371285344503485897, 371285344610413911, 371285344718732067, 371285344824442221, 371285344827878299, 371285344887839114, 371285344973182181]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477309578483978, 362477455460068309⟩, ⟨762552183771564441, 772191577435896791⟩, true⟩

def words06 : List Nat := [371285345161031645, 371285345222516881, 371285345282941377, 371285345344574777, 371285345408533981, 371285345421763491, 371285345430345549, 371285345440237538, 371285345442818343, 371285345432250141]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499056278655978, 362499202191325265⟩, ⟨(-1365903219507013819), (-1356260783398265969)⟩, true⟩

def words07 : List Nat := [371285345377799177, 371285345405793878, 371285345518796491, 371285345546154963, 371285345554237186, 371285345563325712, 371285345639862544, 371285345680812182, 371285345824708486, 371285345970164895]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489761130596476, 362489907074335609⟩, ⟨(-456074875038670961), (-446429397659410111)⟩, true⟩

def words08 : List Nat := [371285346092206308, 371285346095643464, 371285346187538918, 371285346288646559, 371285346419608682, 371285346444642402, 371285346461938704, 371285346480524410, 371285346549426009, 371285346599954314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482795573276342, 362482941547878048⟩, ⟨225852392135917734, 235500890812924164⟩, true⟩

def words09 : List Nat := [371285346738184875, 371285346877780904, 371285347013176232, 371285347016613706, 371285347012777762, 371285347016730369, 371285347111910751, 371285347115351035, 371285347093520318, 371285347072809743]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk978
