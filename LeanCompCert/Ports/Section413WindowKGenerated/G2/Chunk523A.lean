import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk523A
