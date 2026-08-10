import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk995A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586186016405543, 360586251600910074⟩, ⟨(-383794288030073650), (-379388005301123034)⟩, true⟩

def state01 : KState := ⟨⟨360585904626148488, 360585970224427704⟩, ⟨(-355872385406395646), (-351464732028723256)⟩, true⟩

def words00 : List Nat := [360582438695746097, 360582438664673405, 360582438660099111, 360582438681055120, 360582438682286945, 360582438634482757, 360582438570925440, 360582438443328700, 360582438315457093, 360582438306026435]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561937198352276, 360562002810271776⟩, ⟨2029299751865232899, 2033708762657189315⟩, true⟩

def words01 : List Nat := [360582438425536378, 360582438545346749, 360582438614323445, 360582438615770498, 360582438583974223, 360582438497245813, 360582438410102138, 360582438317716884, 360582438190586682, 360582437986745422]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600433757818256, 360600499383402540⟩, ⟨(-1802097734650066545), (-1797687363873682873)⟩, true⟩

def words02 : List Nat := [360582437782581410, 360582437626597255, 360582437551524310, 360582437565298242, 360582437566634307, 360582437494852554, 360582437454718671, 360582437486126079, 360582437617974278, 360582437800942064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581311572600235, 360581377211990814⟩, ⟨101235658172198174, 105647403156277680⟩, true⟩

def words03 : List Nat := [360582437933084901, 360582438065371210, 360582438171706231, 360582438336660740, 360582438441468740, 360582438546507703, 360582438600850793, 360582438602298222, 360582438577227999, 360582438568261221]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569221157559025, 360569286810574091⟩, ⟨1304713865070671922, 1309126966303273104⟩, true⟩

def words04 : List Nat := [360582438558777605, 360582438520644835, 360582438410638345, 360582438250272347, 360582438089671639, 360582437887438053, 360582437744434425, 360582437599186934, 360582437453797002, 360582437257247153]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk995A
