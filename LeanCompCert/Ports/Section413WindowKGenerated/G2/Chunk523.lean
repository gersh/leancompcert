import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571338774047401, 360571355996636860⟩, ⟨558259564330031468, 558868177128476090⟩, true⟩

def state01 : KState := ⟨⟨360598751879037795, 360598769108459712⟩, ⟨(-875481906070629058), (-874872935900570076)⟩, true⟩

def words00 : List Nat := [360582041769576413, 360582042168470860, 360582042858745503, 360582043549145054, 360582043881350255, 360582043882074572, 360582043977932107, 360582044107069241, 360582044333557814, 360582044654025644]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620408615715493, 360620425852043405⟩, ⟨(-2008533216129769877), (-2007923884673160959)⟩, true⟩

def words01 : List Nat := [360582044678613747, 360582044703271954, 360582045092557322, 360582045666315735, 360582046148427381, 360582046630644646, 360582046929405473, 360582047367008404, 360582048101127870, 360582048835459755]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597429402231741, 360597446645382632⟩, ⟨(-806143132591299450), (-805533444123456864)⟩, true⟩

def words02 : List Nat := [360582049934170359, 360582050668607317, 360582051189135745, 360582051709723454, 360582051883659171, 360582052336101608, 360582052720087088, 360582053104193188, 360582053305360195, 360582053600263612]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360623992159727039, 360624009409726573⟩, ⟨(-2196325158972110227), (-2195715112081850613)⟩, true⟩

def words03 : List Nat := [360582054124836219, 360582054649615233, 360582055418281894, 360582055921438884, 360582056113946848, 360582056306497757, 360582056798546455, 360582057611210235, 360582058413330933, 360582059215575108]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599756304337003, 360599773561235969⟩, ⟨(-927863479436554438), (-927253071395583210)⟩, true⟩

def words04 : List Nat := [360582059811229952, 360582060042889483, 360582060397031097, 360582060751377683, 360582060889874924, 360582061038088276, 360582061038734018, 360582061004287918, 360582060989799087, 360582061328969239]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550766487591851, 360550783751327771⟩, ⟨1637030775631118160, 1637641541620375656⟩, true⟩

def words05 : List Nat := [360582061776575357, 360582062224300511, 360582062390864957, 360582062391589922, 360582062194203039, 360582061829072569, 360582061463743658, 360582061310977750, 360582060924330908, 360582060327752912]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586391456576915, 360586408727147882⟩, ⟨(-228408832181317402), (-227797708274013438)⟩, true⟩

def words06 : List Nat := [360582059731013303, 360582059498548559, 360582059758554241, 360582060070992352, 360582060071660957, 360582060072114067, 360582059708716291, 360582059335338474, 360582058961762239, 360582059035366667]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581863817135824, 360581881094620915⟩, ⟨8718712593598280, 9330198625902956⟩, true⟩

def words07 : List Nat := [360582059036024011, 360582058816179356, 360582058653846705, 360582059037160814, 360582059314185300, 360582059591316888, 360582059591967856, 360582059589023997, 360582059222398391, 360582059219833323]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593219597767137, 360593236882090511⟩, ⟨(-586259301280089055), (-585647457023739849)⟩, true⟩

def words08 : List Nat := [360582059217029513, 360582059202741011, 360582059134195521, 360582058841301238, 360582058548299766, 360582058164261663, 360582058126145179, 360582058289378582, 360582058290030855, 360582058483949156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641908808247065, 360641926099414820⟩, ⟨(-3137367523599864024), (-3136755320732982074)⟩, true⟩

def words09 : List Nat := [360582059061553248, 360582059639348713, 360582060259116254, 360582060963229104, 360582061323681536, 360582061684165301, 360582062322706554, 360582063212892558, 360582064355900775, 360582065499030611]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523
