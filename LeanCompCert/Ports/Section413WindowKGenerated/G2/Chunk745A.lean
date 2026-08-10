import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554963076745381, 360554999025968463⟩, ⟨2032673719472885119, 2034482662245847531⟩, true⟩

def state01 : KState := ⟨⟨360558163391547238, 360558199350787049⟩, ⟨1794142576110460248, 1795952265180445150⟩, true⟩

def words00 : List Nat := [360582307152399836, 360582306727273448, 360582306391588101, 360582305996418642, 360582305601177303, 360582305052491059, 360582304323635639, 360582303775004280, 360582303226056297, 360582302857231560]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561941145723093, 360561977115069791⟩, ⟨1512616716593363534, 1514427158775168572⟩, true⟩

def words01 : List Nat := [360582302534698344, 360582302088002338, 360582301641115372, 360582301342026467, 360582301177190223, 360582300888546126, 360582300599789441, 360582300200206258, 360582299812201944, 360582299540710897]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575568317747270, 360575604297093161⟩, ⟨497070725367776080, 498881912738776202⟩, true⟩

def words02 : List Nat := [360582299268860785, 360582299177052252, 360582299090579346, 360582298914191800, 360582298737642351, 360582298439586160, 360582298231987081, 360582298204384562, 360582298176694699, 360582298003154328]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603058599855262, 360603094589203792⟩, ⟨(-1551935864655905316), (-1550123931738297214)⟩, true⟩

def words03 : List Nat := [360582298004162504, 360582298095290497, 360582298320523930, 360582298410946746, 360582298411924786, 360582298349028506, 360582298301422829, 360582298441180911, 360582298721031465, 360582299001114844]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584492744533365, 360584528743998008⟩, ⟨(-168048539967053461), (-166235852946425971)⟩, true⟩

def words04 : List Nat := [360582299191053790, 360582299395779485, 360582299542525270, 360582299689562197, 360582299729238126, 360582299730298778, 360582299590248762, 360582299309276685, 360582299028109091, 360582298916726122]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745A
