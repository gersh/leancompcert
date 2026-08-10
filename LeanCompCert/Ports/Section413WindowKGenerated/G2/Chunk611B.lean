import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611A

def state06 : KState := ⟨⟨360612306347006795, 360612330197247313⟩, ⟨(-1825946580634902405), (-1824961162163080051)⟩, true⟩

def words05 : List Nat := [360582487556360810, 360582488028049512, 360582488766777824, 360582489239299099, 360582489479195874, 360582489719143586, 360582490081978448, 360582490578223980, 360582491066822838, 360582491555593922]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360618905183581871, 360618929041975538⟩, ⟨(-2229756196019726257), (-2228770278860871515)⟩, true⟩

def words06 : List Nat := [360582491832618407, 360582491932609665, 360582492191259968, 360582492450161576, 360582492561992497, 360582492796826716, 360582492897277538, 360582492997818839, 360582493365358968, 360582493961972582]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589388694283660, 360589412560758116⟩, ⟨(-424113778732469442), (-423127367232346744)⟩, true⟩

def words07 : List Nat := [360582494521001795, 360582495080172599, 360582495430592215, 360582495592752717, 360582495687863986, 360582495783198561, 360582496091915949, 360582496340006891, 360582496453817258, 360582496567766300]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601958710322879, 360601982584880526⟩, ⟨(-1193183538961994799), (-1192196632892112169)⟩, true⟩

def words08 : List Nat := [360582496899565387, 360582497445826657, 360582497969575517, 360582498493469485, 360582498791551719, 360582498823627264, 360582498848233315, 360582498873078077, 360582499063271901, 360582499382564955]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592107481352751, 360592131364082452⟩, ⟨(-590346812985423950), (-589359406827757680)⟩, true⟩

def words09 : List Nat := [360582499530872905, 360582499679259001, 360582499868113000, 360582500262749619, 360582500588764148, 360582500914908126, 360582501106898589, 360582501149373876, 360582501307424758, 360582501465766612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611B
