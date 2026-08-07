import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478289718801310, 362478417722541129⟩, ⟨606047533184709778, 613989988139077724⟩, true⟩

def state01 : KState := ⟨⟨362484537362822831, 362484665395376940⟩, ⟨31849575690221071, 39794678819113845⟩, true⟩

def words00 : List Nat := [371285098733374791, 371285098736925657, 371285098713797902, 371285098721254906, 371285098723757594, 371285098691915300, 371285098501296172, 371285098418736628, 371285098366395093, 371285098369795601]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481492321588343, 362481620383407507⟩, ⟨311766571476287651, 319714364508222161⟩, true⟩

def words01 : List Nat := [371285098367486093, 371285098366064831, 371285098465204370, 371285098511612764, 371285098583712051, 371285098657033586, 371285098704833094, 371285098708046130, 371285098597861946, 371285098564048372]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479508691502098, 362479636781930069⟩, ⟨494149458978585732, 502099881881626160⟩, true⟩

def words02 : List Nat := [371285098608825379, 371285098612047570, 371285098595985676, 371285098579812218, 371285098578459606, 371285098582034150, 371285098540956162, 371285098542821329, 371285098543572406, 371285098545031142]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494341827431144, 362494469946926461⟩, ⟨(-869575053952989199), (-861621958745671903)⟩, true⟩

def words03 : List Nat := [371285098487840036, 371285098460231742, 371285098504226067, 371285098507441010, 371285098444916170, 371285098357981607, 371285098283938341, 371285098287566620, 371285098375380250, 371285098480891225]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478058369895040, 362478186518356250⟩, ⟨627595407687747304, 635551166169097112⟩, true⟩

def words04 : List Nat := [371285098582775198, 371285098585989345, 371285098590099170, 371285098654086809, 371285098710378089, 371285098713594898, 371285098636048426, 371285098559336049, 371285098481371129, 371285098439684898]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471157946125916, 362471286123596073⟩, ⟨1262184259391787459, 1270142685391400295⟩, true⟩

def words05 : List Nat := [371285098409731800, 371285098456359891, 371285098484642577, 371285098487861742, 371285098388366535, 371285098315979621, 371285098283960084, 371285098287174785, 371285098174048078, 371285098027525950]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492007914475884, 362492136120715887⟩, ⟨(-655267708291647402), (-647306636471364040)⟩, true⟩

def words06 : List Nat := [371285097879512776, 371285097851104524, 371285097792353210, 371285097810103787, 371285097812591441, 371285097811335950, 371285097725848505, 371285097744997467, 371285097880600275, 371285097960464598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481803654791667, 362481931890350107⟩, ⟨283281645204709244, 291245413587377854⟩, true⟩

def words07 : List Nat := [371285098014692884, 371285098069937824, 371285098172566174, 371285098217564767, 371285098285500753, 371285098354682348, 371285098414641599, 371285098417856947, 371285098320085800, 371285098289715050]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475588920308028, 362475717184486803⟩, ⟨854990203918091648, 862956604949183838⟩, true⟩

def words08 : List Nat := [371285098319941973, 371285098323181275, 371285098302668790, 371285098283072717, 371285098275321536, 371285098278865470, 371285098235261056, 371285098213363115, 371285098190413160, 371285098167256117]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496905271364920, 362497033564636670⟩, ⟨(-1106023213863705509), (-1098054136424235371)⟩, true⟩

def words09 : List Nat := [371285098067459912, 371285098069013009, 371285098126870642, 371285098130142769, 371285098092300306, 371285098036641787, 371285098038681251, 371285098058004135, 371285098189918677, 371285098323319465]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk919
