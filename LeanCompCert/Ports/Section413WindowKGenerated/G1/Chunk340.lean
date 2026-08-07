import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk340

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471591383281955, 362471607569307407⟩, ⟨446949839325987301, 447321782280898335⟩, true⟩

def state01 : KState := ⟨⟨362501500675730643, 362501516871607453⟩, ⟨(-570115777297612890), (-569743499345959202)⟩, true⟩

def words00 : List Nat := [371284763746529460, 371284763747753142, 371284763627259691, 371284763898931300, 371284764027971707, 371284764029092156, 371284763592793256, 371284763739063702, 371284764635847700, 371284765129543240]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492217096019827, 362492233301943854⟩, ⟨(-254330288568394981), (-253957668861287389)⟩, true⟩

def words01 : List Nat := [371284765623404344, 371284766117597989, 371284766878359416, 371284767209305778, 371284767803852398, 371284768398800297, 371284768771909562, 371284768773011304, 371284768348502520, 371284768569312207]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459308867460173, 362459325083181889⟩, ⟨865383840029564448, 865756793105770896⟩, true⟩

def words02 : List Nat := [371284769352895032, 371284769353996711, 371284768986557040, 371284768455099368, 371284767923243283, 371284767642632167, 371284766984323672, 371284766678455760, 371284766372253537, 371284766070343387]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362546450620189763, 362546466845890291⟩, ⟨(-2100447580534222355), (-2100074287829719401)⟩, true⟩

def words03 : List Nat := [371284765439357693, 371284765556531777, 371284766536451987, 371284767273911949, 371284767869529094, 371284768465444257, 371284769771500821, 371284770722153972, 371284772535362011, 371284774348965121]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362510927139167751, 362510943374827959⟩, ⟨(-891173762080016692), (-890800130297670252)⟩, true⟩

def words04 : List Nat := [371284776004358894, 371284776510111921, 371284777698126753, 371284778886629291, 371284780110518721, 371284780408620377, 371284780633034488, 371284780857833749, 371284781842577098, 371284782612139707]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481170194125206, 362481186439699070⟩, ⟨122291529442766193, 122665498835540939⟩, true⟩

def words05 : List Nat := [371284783918905600, 371284785226030417, 371284786530930560, 371284786687132951, 371284786870462427, 371284787054342275, 371284788099689122, 371284788100792038, 371284787997490330, 371284787892982557]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475525062446932, 362475541317902461⟩, ⟨314797287216833638, 315171593230158538⟩, true⟩

def words06 : List Nat := [371284788544121998, 371284788982574582, 371284790026737804, 371284791071300700, 371284791978595507, 371284791979698752, 371284791742107626, 371284791746791246, 371284792023928913, 371284792025070943]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478056669536893, 362478072935058548⟩, ⟨228530575471916871, 228905224488719545⟩, true⟩

def words07 : List Nat := [371284791754383837, 371284791407559614, 371284791274371822, 371284791275599454, 371284791066570577, 371284790992424608, 371284790917901000, 371284790759626763, 371284789833365147, 371284789637655048]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461963949094565, 362461980224458987⟩, ⟨777069456006895847, 777444440516778259⟩, true⟩

def words08 : List Nat := [371284790035676660, 371284790036780468, 371284789484914571, 371284788749097736, 371284788012914347, 371284787342836947, 371284786458862173, 371284786316268582, 371284786173307204, 371284785869531348]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480841175082330, 362480857460412055⟩, ⟨133531239906197067, 133906564184113191⟩, true⟩

def words09 : List Nat := [371284785307531348, 371284785415059367, 371284786257417955, 371284786258522402, 371284785954762512, 371284785511104873, 371284785067023835, 371284784974306458, 371284784453047861, 371284784339127132]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk340
