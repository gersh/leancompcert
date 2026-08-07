import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk058

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362275089976700941, 362275090378710302⟩, ⟨1184337250045438665, 1184338829666102927⟩, true⟩

def state01 : KState := ⟨⟨362404089515566020, 362404089919018413⟩, ⟨435794162533267348, 435795750530931666⟩, true⟩

def words00 : List Nat := [371279251528564098, 371279245884502042, 371279225548086976, 371279217319609668, 371279209093920124, 371279196324148429, 371279144198944717, 371279121574175193, 371279098957109530, 371279097793464357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362358178110985254, 362358178515904902⟩, ⟨703552348759813024, 703553945289800102⟩, true⟩

def words01 : List Nat := [371279084885674041, 371279070474881553, 371279071091990055, 371279076818633427, 371279091524144623, 371279106224662490, 371279115141635491, 371279115141796963, 371279084847601162, 371279064073514834]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362395398314686701, 362395398721047016⟩, ⟨487008646406348431, 487010251328373869⟩, true⟩

def words02 : List Nat := [371279051891284742, 371279051891446451, 371279028725088998, 371279005710510968, 371278982703767695, 371278967754872669, 371278938290649431, 371278938142676708, 371278937994701881, 371278933927106772]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362512543039555666, 362512543447383585⟩, ⟨(-197113015558866824), (-197111402073330148)⟩, true⟩

def words03 : List Nat := [371278919601167700, 371278910566617290, 371278913202270483, 371278913202432498, 371278885860482827, 371278853862253899, 371278821874925498, 371278809116175064, 371278791494789803, 371278797273428213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362419086467445555, 362419086876738379⟩, ⟨348450673517955063, 348452295566008875⟩, true⟩

def words04 : List Nat := [371278797273551557, 371278795373151815, 371278763644259231, 371278761077110152, 371278758510763817, 371278756512818230, 371278723055667170, 371278689447144508, 371278655850046497, 371278651371706928]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362382121983581630, 362382122394339244⟩, ⟨565616931126028224, 565618561750558020⟩, true⟩

def words05 : List Nat := [371278660112131833, 371278679026384843, 371278697786528177, 371278697786690860, 371278677781704007, 371278666566815202, 371278673173519138, 371278673173682040, 371278660807155400, 371278644333204527]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362533346632451977, 362533347044667314⟩, ⟨(-321183120346929343), (-321181481172555725)⟩, true⟩

def words06 : List Nat := [371278640403864317, 371278640404043411, 371278641312804115, 371278644021315630, 371278644021442218, 371278637171783124, 371278606729635773, 371278605263864497, 371278631289613970, 371278640609448007]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523512078316229, 362523512492023103⟩, ⟨(-263360467859983284), (-263358819922823180)⟩, true⟩

def words07 : List Nat := [371278648557406157, 371278656502714347, 371278676160180891, 371278685943668451, 371278702967643302, 371278719985886096, 371278737207200173, 371278737207363669, 371278723576863789, 371278731192937434]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362400233086521903, 362400233501686386⟩, ⟨462668460463998991, 462670116979409619⟩, true⟩

def words08 : List Nat := [371278767656832627, 371278776076915810, 371278781671934202, 371278787265104604, 371278793551532814, 371278793551714583, 371278786507752181, 371278786415946646, 371278786324115513, 371278785304229580]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362685269513553167, 362685269930196557⟩, ⟨(-1217453172980080292), (-1217451507746268116)⟩, true⟩

def words09 : List Nat := [371278780601705378, 371278789230539013, 371278821198248858, 371278829766290216, 371278833306556591, 371278836845674579, 371278869096456052, 371278887236607016, 371278922216836525, 371278957185281074]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk058
