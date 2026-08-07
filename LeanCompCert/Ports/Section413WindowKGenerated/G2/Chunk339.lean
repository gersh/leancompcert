import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614826710235258, 360614833693672366⟩, ⟨(-1133220622290541617), (-1133060559105805161)⟩, true⟩

def state01 : KState := ⟨⟨360614432302078550, 360614439289790721⟩, ⟨(-1119908624174704165), (-1119748416043655759)⟩, true⟩

def words00 : List Nat := [360581411741965494, 360581412713017128, 360581413248648793, 360581413784296820, 360581414099019082, 360581414852656563, 360581416104323161, 360581417356010482, 360581418103357190, 360581419077586904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360649190195683327, 360649197187677434⟩, ⟨(-2298764295406969666), (-2298603942054219506)⟩, true⟩

def words01 : List Nat := [360581420920354770, 360581422763151710, 360581424735076656, 360581426219736550, 360581426866810772, 360581427513873351, 360581428409156040, 360581429742574587, 360581431740802719, 360581433739015714]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360613723831008037, 360613730827334561⟩, ⟨(-1095587513120881134), (-1095427012791866894)⟩, true⟩

def words02 : List Nat := [360581435302847412, 360581436889008250, 360581439342995913, 360581441796974982, 360581443686464641, 360581444710490767, 360581445209387300, 360581445708303864, 360581445916323539, 360581446868335656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597427667590168, 360597434668190340⟩, ⟨(-542435294229356710), (-542274648873748558)⟩, true⟩

def words03 : List Nat := [360581448687871481, 360581450507388079, 360581451889457786, 360581453084641557, 360581453707189566, 360581454329826990, 360581455819768908, 360581456746663654, 360581457217841984, 360581457689053787]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360655467392261920, 360655474397156325⟩, ⟨(-2512649766832992208), (-2512488975710330540)⟩, true⟩

def words04 : List Nat := [360581459027464495, 360581460803167149, 360581462211012141, 360581463618852970, 360581464315416397, 360581464891223006, 360581466111009000, 360581467330861455, 360581468830382668, 360581471010637215]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk339
