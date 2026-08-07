import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588753879418565, 360588803738581981⟩, ⟨(-580793954202847499), (-577857915735999397)⟩, true⟩

def state01 : KState := ⟨⟨360582057091316343, 360582106962450952⟩, ⟨3088430459637633, 6025512868794083⟩, true⟩

def words00 : List Nat := [360582177015004604, 360582177016260114, 360582176940982693, 360582176872713636, 360582176804106176, 360582176685395030, 360582176570025794, 360582176372635818, 360582176175001749, 360582176054445779]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553594518398817, 360553644401368442⟩, ⟨2485529965509383783, 2488468080110135841⟩, true⟩

def words01 : List Nat := [360582176185185696, 360582176316955517, 360582176347771969, 360582176349027458, 360582176248376528, 360582176115021044, 360582175981302589, 360582175887073549, 360582175661354510, 360582175335559111]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571398877370005, 360571448772188190⟩, ⟨932579886865725114, 935519034956653446⟩, true⟩

def words02 : List Nat := [360582175009463151, 360582174815022692, 360582174688119068, 360582174691054908, 360582174692214261, 360582174583340582, 360582174342898573, 360582174046697439, 360582173750123537, 360582173511784163]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571358154050957, 360571408060812102⟩, ⟨936149333276912796, 939089523210437502⟩, true⟩

def words03 : List Nat := [360582173389956384, 360582173202505831, 360582173014817466, 360582172953780410, 360582172954831405, 360582172927692264, 360582172900428250, 360582172804630755, 360582172620220403, 360582172498262933]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556995670371553, 360557045588978335⟩, ⟨2189121104586773885, 2192062327991386411⟩, true⟩

def words04 : List Nat := [360582172375915516, 360582172175302107, 360582171869918394, 360582171481099657, 360582171092081479, 360582170670412167, 360582170336962360, 360582170087721031, 360582169838323206, 360582169512508323]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583194620420335, 360583244550874038⟩, ⟨(-96885280731811832), (-93943023623396014)⟩, true⟩

def words05 : List Nat := [360582169225573556, 360582169070211545, 360582168914474766, 360582168890167178, 360582168734541113, 360582168456311291, 360582168177841065, 360582168030922042, 360582167962092340, 360582167975730235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560035657005023, 360560085599440999⟩, ⟨1924055452523698529, 1926998755264214287⟩, true⟩

def words06 : List Nat := [360582167976853533, 360582167877555822, 360582167824044945, 360582167791337233, 360582167758283551, 360582167668646718, 360582167447654214, 360582167146808186, 360582166845751254, 360582166483539363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561579167166645, 360561629121426078⟩, ⟨1789381663977195341, 1792325998611044389⟩, true⟩

def words07 : List Nat := [360582166231539716, 360582166091435036, 360582165951206977, 360582165745533305, 360582165519769734, 360582165260302799, 360582165000448610, 360582164871957247, 360582164712863727, 360582164478880376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586302232093756, 360586352198232617⟩, ⟨(-368602613022749649), (-365657241495897605)⟩, true⟩

def words08 : List Nat := [360582164244617252, 360582164141853980, 360582164123772338, 360582164065015743, 360582164006172396, 360582163811083910, 360582163558935681, 360582163414979809, 360582163270658558, 360582163252734274]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578204780769991, 360578254758883742⟩, ⟨338269268321735217, 341215685195686869⟩, true⟩

def words09 : List Nat := [360582163253865721, 360582163220461275, 360582163283226403, 360582163447062470, 360582163503918363, 360582163560979595, 360582163562118665, 360582163518661175, 360582163343846958, 360582163300524014]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872
