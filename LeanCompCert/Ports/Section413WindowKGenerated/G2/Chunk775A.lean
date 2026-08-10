import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555337090900745, 360555376115015147⟩, ⟨2074559837364909823, 2076602504278206253⟩, true⟩

def state01 : KState := ⟨⟨360591025371160609, 360591064405718637⟩, ⟨(-691533881438495095), (-689490405091918213)⟩, true⟩

def words00 : List Nat := [360582170641198577, 360582170370487423, 360582170182809649, 360582169986073253, 360582169789236878, 360582169450323530, 360582169169368123, 360582169025374366, 360582168901990298, 360582169017901529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584078095980628, 360584117141091906⟩, ⟨(-153004529821605985), (-150960235441968271)⟩, true⟩

def words01 : List Nat := [360582169018904531, 360582169006501188, 360582169146526031, 360582169383688043, 360582169538891014, 360582169694269850, 360582169710971227, 360582169742345151, 360582169768365482, 360582169794754244]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588159344951162, 360588198400471256⟩, ⟨(-469413984882142544), (-467368883557771606)⟩, true⟩

def words02 : List Nat := [360582169986894817, 360582170051594341, 360582170052580315, 360582170034127250, 360582170015511609, 360582169882775735, 360582169991593997, 360582170129717280, 360582170166595774, 360582170245493792]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572381214838259, 360572420280822004⟩, ⟨753957011372642312, 756002923995446818⟩, true⟩

def words03 : List Nat := [360582170336909627, 360582170428673806, 360582170597571473, 360582170600751082, 360582170601781425, 360582170464769153, 360582170327551045, 360582170248759627, 360582170249678465, 360582170125082972]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585458016434556, 360585497092957782⟩, ⟨(-260221685714483070), (-258174955809357964)⟩, true⟩

def words04 : List Nat := [360582170000331301, 360582169792601852, 360582169454883878, 360582169283541546, 360582169111902355, 360582168848517687, 360582168644868599, 360582168358263767, 360582168071454476, 360582167993967320]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk775A
