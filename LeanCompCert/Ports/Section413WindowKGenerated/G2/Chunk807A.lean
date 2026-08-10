import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592532166413340, 360592574613825224⟩, ⟨(-844835246832319863), (-842521758029191221)⟩, true⟩

def state01 : KState := ⟨⟨360582214235844734, 360582256694144942⟩, ⟨(-12147851109651655), (-9833483564674397)⟩, true⟩

def words00 : List Nat := [360582134856339248, 360582134986966232, 360582134992720078, 360582134998576033, 360582134999542487, 360582135010648413, 360582135011590565, 360582134985608426, 360582134959501078, 360582134858415430]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592498106617409, 360592540575816786⟩, ⟨(-842219722673354133), (-839904475401869573)⟩, true⟩

def words01 : List Nat := [360582134959278881, 360582135060493526, 360582135314630365, 360582135415803946, 360582135416869158, 360582135386480755, 360582135355889563, 360582135285274223, 360582135415114158, 360582135545212584]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572420411157315, 360572462891367934⟩, ⟨778483743604642819, 780799879754404801⟩, true⟩

def words02 : List Nat := [360582135597893372, 360582135599048420, 360582135513038797, 360582135528911007, 360582135529878784, 360582135505292119, 360582135363523220, 360582135130133119, 360582134896534279, 360582134635202375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556649603129961, 360556692094230288⟩, ⟨2051688268088046882, 2054005283418827172⟩, true⟩

def words03 : List Nat := [360582134516352494, 360582134344163761, 360582134171856213, 360582133893059735, 360582133526230412, 360582133097675556, 360582132668791032, 360582132393363377, 360582132156482768, 360582131842600598]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590354880696580, 360590397382695365⟩, ⟨(-669889338515725515), (-667571443189216079)⟩, true⟩

def words04 : List Nat := [360582131528456194, 360582131339915571, 360582131227831450, 360582131161450935, 360582131095000926, 360582130884026787, 360582130570716120, 360582130410925403, 360582130250787487, 360582130346458177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk807A
