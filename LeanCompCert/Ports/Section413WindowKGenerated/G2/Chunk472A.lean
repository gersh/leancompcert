import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556036581594200, 360556050491868010⟩, ⟨1266237973516184378, 1266681643338472712⟩, true⟩

def state01 : KState := ⟨⟨360556327894780452, 360556341811181964⟩, ⟨1252408108250758117, 1252852067331822439⟩, true⟩

def words00 : List Nat := [360582886399342129, 360582885590578538, 360582885007034589, 360582884556939950, 360582884106819241, 360582883277471741, 360582882000428261, 360582881170869869, 360582880341145649, 360582879664758152]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360533219748310911, 360533233670888008⟩, ⟨2343501481428110227, 2343945732088699251⟩, true⟩

def words01 : List Nat := [360582879103224270, 360582878318350135, 360582877533380195, 360582877017363014, 360582876795075324, 360582876208614743, 360582875622105048, 360582874812388217, 360582873555196435, 360582872504689125]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360551899317141345, 360551913245836546⟩, ⟨1461407071359485763, 1461851610947792425⟩, true⟩

def words02 : List Nat := [360582871454011245, 360582870850399756, 360582870261203764, 360582869324399289, 360582868387529262, 360582867334994448, 360582866591379002, 360582866183154480, 360582865774889109, 360582865005543254]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617891095704991, 360617905030522778⟩, ⟨(-1655748746622402724), (-1655303917833858878)⟩, true⟩

def words03 : List Nat := [360582864350740863, 360582864028184197, 360582863727588194, 360582863877482395, 360582863878081092, 360582863625353690, 360582863565658335, 360582863984472390, 360582864726763744, 360582865469170693]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586473843727591, 360586487784745239⟩, ⟨(-171603796477548474), (-171158674779373390)⟩, true⟩

def words04 : List Nat := [360582865937177122, 360582866504375945, 360582866870414924, 360582867236618794, 360582867305126515, 360582867305775880, 360582866927418834, 360582866326337776, 360582865725158113, 360582865455592854]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk472A
