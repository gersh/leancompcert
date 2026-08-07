import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk510

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566332720851340, 360566349064335798⟩, ⟨795181124205172719, 795744328670476743⟩, true⟩

def state01 : KState := ⟨⟨360571643256776731, 360571659606902275⟩, ⟨524398916701693600, 524962459897020500⟩, true⟩

def words00 : List Nat := [360581951666605598, 360581951755295991, 360581951755930373, 360581951651883820, 360581951547726097, 360581951303596247, 360581951260872341, 360581951269018914, 360581951269657932, 360581950970554442]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609234721215331, 360609251077997900⟩, ⟨(-1393383896982249657), (-1392820014179016205)⟩, true⟩

def words01 : List Nat := [360581950776744231, 360581950784898758, 360581951095261036, 360581951227801248, 360581951228452725, 360581951046307594, 360581950864023951, 360581951050939145, 360581951586594129, 360581952122387877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567947471785933, 360567963835299101⟩, ⟨713135591412933945, 713699817643040527⟩, true⟩

def words02 : List Nat := [360581952464649073, 360581952547505038, 360581952548085417, 360581952516930266, 360581952485593103, 360581952228533231, 360581951748904254, 360581951053926739, 360581950358845243, 360581949722378134]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550713642329862, 360550730012483783⟩, ⟨1592796997229416217, 1593361562370487909⟩, true⟩

def words03 : List Nat := [360581949557896762, 360581949667612693, 360581949668241028, 360581949585803984, 360581949582159569, 360581949400480038, 360581949218611566, 360581948908559168, 360581948522345238, 360581947911433049]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595232737737416, 360595249114541315⟩, ⟨(-679659335470164597), (-679094430880676135)⟩, true⟩

def words04 : List Nat := [360581947300379722, 360581946932743738, 360581947016336760, 360581947250011794, 360581947250662696, 360581947138397656, 360581946643263044, 360581946531212255, 360581946578435318, 360581946839740025]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600078510454843, 360600094893991399⟩, ⟨(-927165981793984023), (-926600733470483301)⟩, true⟩

def words05 : List Nat := [360581946840388661, 360581946721287944, 360581946649205155, 360581946936832906, 360581947128608941, 360581947320492618, 360581947321128512, 360581947272353429, 360581947601107572, 360581947957318195]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611492863532412, 360611509253714153⟩, ⟨(-1510001067394346345), (-1509435479733626371)⟩, true⟩

def words06 : List Nat := [360581948695916077, 360581949401315909, 360581949914740826, 360581950428226065, 360581950675374576, 360581951112810920, 360581951838692923, 360581952564683558, 360581953046213524, 360581953625672141]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360612205878202135, 360612222275056366⟩, ⟨(-1546393405391621585), (-1545827476933076775)⟩, true⟩

def words07 : List Nat := [360581954587445895, 360581955549404011, 360581956569379572, 360581957207100179, 360581957502359449, 360581957797655448, 360581958206708946, 360581958809758690, 360581959402811477, 360581959995991096]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608345310681892, 360608361714263200⟩, ⟨(-1349384127800824764), (-1348817855691134478)⟩, true⟩

def words08 : List Nat := [360581960397339309, 360581960416514802, 360581960612490284, 360581960808677735, 360581960809270452, 360581960880790457, 360581960881419688, 360581960799573740, 360581960894199924, 360581961411750211]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567340789216898, 360567357199456341⟩, ⟨745780039793998786, 746346652101361280⟩, true⟩

def words09 : List Nat := [360581962096074214, 360581962780505682, 360581963166358540, 360581963306895727, 360581963307490948, 360581963194911571, 360581963187242156, 360581963187949294, 360581963094171319, 360581962809086505]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk510
