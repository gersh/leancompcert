import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680A

def state06 : KState := ⟨⟨360612172788973922, 360612202577054969⟩, ⟨(-2000859204485202196), (-1999489748974069604)⟩, true⟩

def words05 : List Nat := [360582822442505444, 360582822552848030, 360582822878549995, 360582823211310297, 360582823355150148, 360582823499056841, 360582823587547722, 360582823804670708, 360582824237108260, 360582824669751608]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590401827161803, 360590431624415527⟩, ⟨(-519162544300890016), (-517792464452114428)⟩, true⟩

def words06 : List Nat := [360582824938850330, 360582824992450503, 360582825162475668, 360582825332777311, 360582825448300298, 360582825449262239, 360582825349274774, 360582825140130763, 360582824930778347, 360582824971590505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557853963869021, 360557883770174907⟩, ⟨1696642290685176312, 1698012986759544984⟩, true⟩

def words07 : List Nat := [360582825299640414, 360582825627865130, 360582825848027074, 360582825917484485, 360582825918304569, 360582825838331751, 360582825771816698, 360582825772778750, 360582825571888055, 360582825206525665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581498534547601, 360581528349946454⟩, ⟨86821696505376462, 88193011673791164⟩, true⟩

def words08 : List Nat := [360582824840957789, 360582824539342261, 360582824429627658, 360582824458912105, 360582824459810142, 360582824279146279, 360582823959443981, 360582823855447788, 360582823751186125, 360582823591709912]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589111593073345, 360589141417630065⟩, ⟨(-431598591932220696), (-430226653159710550)⟩, true⟩

def words09 : List Nat := [360582823573544943, 360582823447590782, 360582823363406851, 360582823558617908, 360582823699150885, 360582823839855560, 360582823872583340, 360582823873545808, 360582823844531870, 360582823938398340]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680B
