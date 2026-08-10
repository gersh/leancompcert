import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339A

def state06 : KState := ⟨⟨360619547622727207, 360619554631945107⟩, ⟨(-1292932115040153901), (-1292771177112846251)⟩, true⟩

def words05 : List Nat := [360581472754076351, 360581474497462381, 360581476617977231, 360581479175051587, 360581481511944695, 360581483848776322, 360581485377760742, 360581486043141188, 360581487164492261, 360581488285927239]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360643990721416207, 360643997734913671⟩, ⟨(-2123212888739639911), (-2123051805457183197)⟩, true⟩

def words06 : List Nat := [360581490273238728, 360581491397071446, 360581492084704026, 360581492772353529, 360581493240385162, 360581494405592106, 360581496436348041, 360581498467074295, 360581499889124963, 360581501729336645]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360645735669076122, 360645742686868428⟩, ⟨(-2182653957799628948), (-2182492728600145474)⟩, true⟩

def words07 : List Nat := [360581503270854991, 360581504812409700, 360581506934653843, 360581508193837039, 360581508699461844, 360581509205088408, 360581510289780069, 360581512051559371, 360581513942177804, 360581515832785260]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360611950493487047, 360611957515607947⟩, ⟨(-1034698087835068017), (-1034536711528504527)⟩, true⟩

def words08 : List Nat := [360581517216208353, 360581518351290947, 360581519766614478, 360581521181991381, 360581521999775028, 360581522000229829, 360581521955495646, 360581521475429144, 360581521012834708, 360581521908784715]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567422747169405, 360567429773578240⟩, ⟨479121667093805190, 479283189169030612⟩, true⟩

def words09 : List Nat := [360581523182194875, 360581524455624140, 360581525287694809, 360581525736290291, 360581525736672873, 360581525705796483, 360581526507521312, 360581526751697645, 360581526752109933, 360581526337965565]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339B
