import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360639081418957608, 360639105220579876⟩, ⟨(-3460603380186723918), (-3459620933743626478)⟩, true⟩

def state01 : KState := ⟨⟨360601539683546701, 360601563493335028⟩, ⟨(-1166799997733689446), (-1165817052306728276)⟩, true⟩

def words00 : List Nat := [360582484646348103, 360582485227524117, 360582485682656720, 360582486138014662, 360582486395415721, 360582486396271614, 360582486386984339, 360582486243231947, 360582486139161322, 360582486452339026]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547850112136782, 360547873929979332⟩, ⟨2114513319014829521, 2115496756677134401⟩, true⟩

def words01 : List Nat := [360582486888240945, 360582487324291772, 360582487591194787, 360582487592050806, 360582487592228354, 360582487434828620, 360582487277188546, 360582487112238783, 360582486680556374, 360582486115134390]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585277341619570, 360585301167540924⟩, ⟨(-173202874761768329), (-172218943282970271)⟩, true⟩

def words02 : List Nat := [360582485549536773, 360582485251829056, 360582485119654885, 360582485103350757, 360582485086965720, 360582484836146872, 360582484507179650, 360582484219094398, 360582483930757624, 360582483956252332]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595277834898493, 360595301668984899⟩, ⟨(-784636141781835824), (-783651711133838202)⟩, true⟩

def words03 : List Nat := [360582483957028587, 360582483759852787, 360582483577606994, 360582483766447397, 360582483886617068, 360582484006922744, 360582484007692538, 360582484125136263, 360582484335474228, 360582484546086454]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594901728736183, 360594925570881166⟩, ⟨(-761610777831733514), (-760625854442113160)⟩, true⟩

def words04 : List Nat := [360582485023823813, 360582485385049860, 360582485589783859, 360582485794604854, 360582485818074810, 360582486007116308, 360582486377251188, 360582486747538005, 360582486880632216, 360582487084929308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611
