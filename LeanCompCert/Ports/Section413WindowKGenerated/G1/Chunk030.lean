import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk030

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362309412077791387, 362309412178425491⟩, ⟨533660844839679067, 533661049707991119⟩, true⟩

def state01 : KState := ⟨⟨362208064908587375, 362208065009922933⟩, ⟨838972915041316379, 838973122017640357⟩, true⟩

def words00 : List Nat := [371287291217952728, 371287291218031423, 371287236605271208, 371287150424552371, 371287064301162740, 371287009344838712, 371286901629469566, 371286872258894864, 371286842907814930, 371286793621888927]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362705342752492460, 362705342854539939⟩, ⟨(-659936679126317496), (-659936470003423444)⟩, true⟩

def words01 : List Nat := [371286718308816305, 371286735554441537, 371286825319404778, 371286825319484292, 371286821090291578, 371286794650431658, 371286785309579501, 371286785309666438, 371286820844517222, 371286893178934702]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362399793350858455, 362399793453621393⟩, ⟨263588553047522611, 263588764334692539⟩, true⟩

def words02 : List Nat := [371286961844144338, 371286961844223605, 371286918131382459, 371286950774378444, 371286988406940173, 371286988407019700, 371286921923965328, 371286854284329909, 371286786689325011, 371286786445150995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362370841972850833, 362370842076331823⟩, ⟨351694703084054085, 351694916550585715⟩, true⟩

def words03 : List Nat := [371286772582122585, 371286787410427396, 371286800205362017, 371286800205441712, 371286701304141449, 371286633661150785, 371286606388018259, 371286606388099429, 371286569261680860, 371286531193618200]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362538666686996810, 362538666791191893⟩, ⟨(-158246815002164145), (-158246599361068993)⟩, true⟩

def words04 : List Nat := [371286562746130214, 371286591292346691, 371286683556666588, 371286775760417220, 371286838010305530, 371286838010385504, 371286757619864726, 371286730313667681, 371286782660171039, 371286799665868698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362440182305113455, 362440182410038911⟩, ⟨143618342616942079, 143618560489388437⟩, true⟩

def words05 : List Nat := [371286818797559073, 371286837916743287, 371286935536352126, 371286980277901208, 371287041558805225, 371287102799648120, 371287163302717122, 371287163302797878, 371287131923012630, 371287116580133483]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362394940587577985, 362394940693219330⟩, ⟨282937194304208877, 282937414371065681⟩, true⟩

def words06 : List Nat := [371287192129150750, 371287192129231111, 371287141795010513, 371287090916558936, 371287040071276046, 371287020317256530, 371287016276937594, 371287067078289445, 371287102717361084, 371287102717444433]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362762131699718624, 362762131806091423⟩, ⟨(-846599233325063607), (-846599011009026187)⟩, true⟩

def words07 : List Nat := [371287118807253519, 371287164877529284, 371287254166425647, 371287254166506494, 371287239676051022, 371287201317939009, 371287188273579079, 371287188273668940, 371287261997229121, 371287351211800925]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362611271025245264, 362611271132347116⟩, ⟨(-381842635821803338), (-381842411256448396)⟩, true⟩

def words08 : List Nat := [371287440133029161, 371287440133110213, 371287515810722094, 371287605944663432, 371287726900079571, 371287726900160630, 371287708874914003, 371287670317950635, 371287697536379078, 371287737514988188]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507015976909022, 362507016084742462⟩, ⟨(-57836223197971940), (-57835996368252762)⟩, true⟩

def words09 : List Nat := [371287829159292078, 371287920744368388, 371288012096525181, 371288055168698207, 371288129500928846, 371288203785197849, 371288347444347622, 371288353291312909, 371288359311629851, 371288365328093558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk030
