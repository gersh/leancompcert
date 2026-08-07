import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607993443136223, 360608037769515317⟩, ⟨(-2117154708767663662), (-2114687984305980246)⟩, true⟩

def state01 : KState := ⟨⟨360586058101962943, 360586102439589089⟩, ⟨(-309691872619819134), (-307224221346499958)⟩, true⟩

def words00 : List Nat := [360582374586465084, 360582374634351149, 360582374746976746, 360582374859980781, 360582374935694514, 360582374936875549, 360582374865801737, 360582374701758690, 360582374537494697, 360582374487964349]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569221029598191, 360569265378362471⟩, ⟨1077900628604916747, 1080369197826360387⟩, true⟩

def words01 : List Nat := [360582374501968620, 360582374516190106, 360582374517252328, 360582374457533071, 360582374287325515, 360582374057053741, 360582373826437130, 360582373707354786, 360582373631272072, 360582373473458642]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583039559864760, 360583083919771028⟩, ⟨(-61076916869290767), (-58607429269845213)⟩, true⟩

def words02 : List Nat := [360582373315375284, 360582373384272041, 360582373442112739, 360582373500171755, 360582373501281614, 360582373415509751, 360582373182734424, 360582373067017089, 360582372950956346, 360582372932044690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564501973601459, 360564546344786497⟩, ⟨1467078831989012809, 1469549249352831021⟩, true⟩

def words03 : List Nat := [360582372933108679, 360582372846929593, 360582372760511105, 360582372646336093, 360582372644051788, 360582372605037069, 360582372565893819, 360582372453068161, 360582372241961260, 360582372027093058]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562814041178960, 360562858423492811⟩, ⟨1606171344530263279, 1608642679408682861⟩, true⟩

def words04 : List Nat := [360582371811826761, 360582371661767445, 360582371364861546, 360582370994305455, 360582370623572311, 360582370157683964, 360582369812972463, 360582369549005355, 360582369284925610, 360582368947196980]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567971704471326, 360568016097958370⟩, ⟨1180853913840205740, 1183326170002814552⟩, true⟩

def words05 : List Nat := [360582368711520909, 360582368562891556, 360582368413935412, 360582368261072928, 360582367961442448, 360582367522970019, 360582367084273741, 360582366792958355, 360582366575978443, 360582366403197308]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556736398563142, 360556780803292593⟩, ⟨2107273223335208749, 2109746406602755401⟩, true⟩

def words06 : List Nat := [360582366230224965, 360582365983648142, 360582365590190671, 360582365344075668, 360582365097653203, 360582364814564097, 360582364384738886, 360582363804026870, 360582363223102153, 360582362789549448]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566331314842132, 360566375730705278⟩, ⟨1315970241612325403, 1318444343130047767⟩, true⟩

def words07 : List Nat := [360582362480311221, 360582362318274341, 360582362156107164, 360582361900072776, 360582361689031389, 360582361439373367, 360582361189360900, 360582361044297505, 360582360941997757, 360582360749414421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581749202996560, 360581793630033105⟩, ⟨44227768747937493, 46702791902052851⟩, true⟩

def words08 : List Nat := [360582360556584280, 360582360359993410, 360582360295075122, 360582360336784280, 360582360337891410, 360582360253685117, 360582360022643247, 360582359938886962, 360582359854769309, 360582359793106230]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592368016067625, 360592412454360730⟩, ⟨(-831809607598045529), (-829333655835576119)⟩, true⟩

def words09 : List Nat := [360582359787296990, 360582359700374056, 360582359672016157, 360582359806131250, 360582359839522135, 360582359873087955, 360582359874141416, 360582359826062558, 360582359923839428, 360582360047046449]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824
