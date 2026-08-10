import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk674A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587261450585041, 360587290641146613⟩, ⟨(-296133553472727553), (-294804568256713911)⟩, true⟩

def state01 : KState := ⟨⟨360563462958310090, 360563492157955485⟩, ⟨1307842778077739102, 1309172375587028894⟩, true⟩

def words00 : List Nat := [360582916751878205, 360582916706618876, 360582916508725137, 360582916306253421, 360582916103541283, 360582915720480636, 360582915117557099, 360582914404796065, 360582913691867548, 360582913198981847]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537313651773172, 360537342860376554⟩, ⟨3070790328683877887, 3072120530096175149⟩, true⟩

def words01 : List Nat := [360582912911652381, 360582912844185862, 360582912776616756, 360582912567338051, 360582912234229638, 360582911803257561, 360582911372032267, 360582910936178957, 360582910437226842, 360582909762335857]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586245598484815, 360586274816070832⟩, ⟨(-228456672109045162), (-227125865043326154)⟩, true⟩

def words02 : List Nat := [360582909087249292, 360582908632080634, 360582908326991934, 360582908198188791, 360582908069300645, 360582907754584850, 360582907220058530, 360582906905413878, 360582906590489577, 360582906545319348]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588756135056901, 360588785361715250⟩, ⟨(-397769484744992325), (-396438065886990957)⟩, true⟩

def words03 : List Nat := [360582906546188221, 360582906417116647, 360582906377401480, 360582906578673860, 360582906724436610, 360582906870351701, 360582906877543352, 360582906890931811, 360582906978869567, 360582907067118685]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579042682804917, 360579071918426204⟩, ⟨257255260827631260, 258587284190875928⟩, true⟩

def words04 : List Nat := [360582907188897197, 360582907189849312, 360582907092162312, 360582906884742459, 360582906677183486, 360582906279117572, 360582905992327339, 360582905925167115, 360582905857905041, 360582905680979071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk674A
