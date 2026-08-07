import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk163

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460587299735056, 362460590793147819⟩, ⟨398437127573068609, 398475645432459029⟩, true⟩

def state01 : KState := ⟨⟨362509115559023166, 362509119056893542⟩, ⟨(-392667925844823124), (-392629335303965658)⟩, true⟩

def words00 : List Nat := [371285037920199380, 371285039495144875, 371285041646367912, 371285043797528049, 371285045397629237, 371285045398126794, 371285042946427724, 371285043041464292, 371285046135750702, 371285047612144357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496219011552641, 362496222513954926⟩, ⟨(-182237294399060836), (-182198629920238364)⟩, true⟩

def words01 : List Nat := [371285049064849981, 371285050517549116, 371285053849321979, 371285055316785558, 371285057464156022, 371285059611446929, 371285060772488925, 371285060772986751, 371285058381595777, 371285059066254403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460898286475143, 362460901793311009⟩, ⟨394396749681551282, 394435486539368868⟩, true⟩

def words02 : List Nat := [371285062460872042, 371285062461369740, 371285060856957232, 371285059230094636, 371285057603233627, 371285057148055809, 371285055166600282, 371285055510417944, 371285055833611884, 371285055834127872]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362518103144286564, 362518106655622261⟩, ⟨(-540146411442887938), (-540107601079639974)⟩, true⟩

def words03 : List Nat := [371285054399946238, 371285054445034596, 371285058240956840, 371285058241454961, 371285057046375588, 371285054720727840, 371285052395157948, 371285052036412490, 371285052334314989, 371285054357655207]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481129690417033, 362481133206243834⟩, ⟨63912295870699824, 63951179641800606⟩, true⟩

def words04 : List Nat := [371285056313239869, 371285056313738319, 371285053282824331, 371285053227529355, 371285053363099981, 371285053363601849, 371285050248891780, 371285047115393444, 371285044592809376, 371285044593377890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362442006444248713, 362442009964577335⟩, ⟨704196583184320740, 704235540582741264⟩, true⟩

def words05 : List Nat := [371285047473800654, 371285050593274005, 371285053440936180, 371285053877389151, 371285055410123663, 371285056942911309, 371285060347988536, 371285060348487547, 371285058777545758, 371285056146764545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362539241074342357, 362539244599138186⟩, ⟨(-886855034840217849), (-886816004335651847)⟩, true⟩

def words06 : List Nat := [371285054622250415, 371285054622805344, 371285056885678318, 371285059885368584, 371285062342449427, 371285062342957313, 371285063765933107, 371285065693529687, 371285071354618177, 371285074664232826]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507689280311323, 362507692809660897⟩, ⟨(-370140599306624030), (-370101494234839616)⟩, true⟩

def words07 : List Nat := [371285077455727055, 371285080247039520, 371285084559357001, 371285087017761723, 371285090458271404, 371285093898556160, 371285097201912798, 371285097202413366, 371285098090212485, 371285099470167897]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467974361796700, 362467977895591798⟩, ⟨280683290887714501, 280722468800426195⟩, true⟩

def words08 : List Nat := [371285104578930264, 371285104725539173, 371285104725912914, 371285104688468243, 371285105409355619, 371285105409905708, 371285104750230727, 371285105181176524, 371285105562478081, 371285105562998780]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362539764048248133, 362539767586564155⟩, ⟨(-896245819166573755), (-896206567132910923)⟩, true⟩

def words09 : List Nat := [371285106356232304, 371285108194446643, 371285112062858903, 371285112867593246, 371285113142876119, 371285113418276375, 371285116388462391, 371285117511435162, 371285120844097260, 371285124176581050]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk163
