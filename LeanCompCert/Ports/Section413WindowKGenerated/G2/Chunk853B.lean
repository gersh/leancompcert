import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853A

def state06 : KState := ⟨⟨360555381850188360, 360555429548798356⟩, ⟨2299682433524644415, 2302432052010570219⟩, true⟩

def words05 : List Nat := [360582404834616054, 360582404772492950, 360582404710238612, 360582404561026894, 360582404274404099, 360582403929753608, 360582403584741032, 360582403286577297, 360582403060002460, 360582402745283954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583499413658672, 360583547123827008⟩, ⟨(-100541808350744160), (-97791203185927388)⟩, true⟩

def words06 : List Nat := [360582402430285856, 360582402252783188, 360582402211438697, 360582402260059320, 360582402261221160, 360582402180206841, 360582401961774056, 360582401804081797, 360582401646032956, 360582401638788929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568556650167275, 360568604372039079⟩, ⟨1175231983705010123, 1177983588051251935⟩, true⟩

def words07 : List Nat := [360582401639894577, 360582401544420309, 360582401448691971, 360582401538538237, 360582401598005405, 360582401657673005, 360582401658766111, 360582401639167363, 360582401482201370, 360582401322004543]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584339338365069, 360584387071788782⟩, ⟨(-172364868027439906), (-169612277320570934)⟩, true⟩

def words08 : List Nat := [360582401161403636, 360582401138113920, 360582401093985827, 360582400970659864, 360582400847130739, 360582400689396485, 360582400698633945, 360582400756630756, 360582400757723944, 360582400770219290]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572167959506236, 360572215704530785⟩, ⟨866969489332376287, 869723070691688889⟩, true⟩

def words09 : List Nat := [360582400841074486, 360582400912298456, 360582400913314597, 360582400914464872, 360582400778429974, 360582400525950158, 360582400273245163, 360582400061686105, 360582399933387690, 360582399815428815]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk853B
