import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547351516151654, 360547354568694220⟩, ⟨751700827314210014, 751747915620455240⟩, true⟩

def state01 : KState := ⟨⟨360594960766016084, 360594963821340084⟩, ⟨(-334070513145901796), (-334023361408666966)⟩, true⟩

def words00 : List Nat := [360580324717637318, 360580324717934092, 360580324386639536, 360580322601362232, 360580320816193504, 360580318540198447, 360580318840859035, 360580319950109708, 360580320096290443, 360580320738555083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360703586689896441, 360703589748014833⟩, ⟨(-2812406465915597320), (-2812359250424717952)⟩, true⟩

def words01 : List Nat := [360580323297679186, 360580325856665074, 360580328351907725, 360580331711108078, 360580333426488871, 360580335141739020, 360580338772777226, 360580343362853632, 360580348763899034, 360580354164542386]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360629905279458869, 360629908340390943⟩, ⟨(-1130988672202694074), (-1130941392489479416)⟩, true⟩

def words02 : List Nat := [360580358603219236, 360580361135302705, 360580364663244217, 360580368190965546, 360580370403049444, 360580371351980390, 360580371352248377, 360580370823747951, 360580370828337560, 360580372998422152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578846492280737, 360578849555997126⟩, ⟨35034348921448591, 35081692214543121⟩, true⟩

def words03 : List Nat := [360580375506011895, 360580378013437739, 360580379236190381, 360580380629927758, 360580381535408669, 360580382440890360, 360580384403745907, 360580385598695757, 360580385598959758, 360580385532013525]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564470367332129, 360564473433846791⟩, ⟨363390666785122677, 363438074004523265⟩, true⟩

def words04 : List Nat := [360580385465011796, 360580384701305971, 360580386111614874, 360580387521856674, 360580387522129553, 360580387295680319, 360580385167065044, 360580382603643354, 360580380040353466, 360580378820017668]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228A
