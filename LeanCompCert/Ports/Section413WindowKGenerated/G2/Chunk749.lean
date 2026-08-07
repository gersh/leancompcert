import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590302667682310, 360590339019344990⟩, ⟨(-605358658062130913), (-603519653004140717)⟩, true⟩

def state01 : KState := ⟨⟨360600716888185959, 360600753249998709⟩, ⟨(-1385538443847672205), (-1383698678500291313)⟩, true⟩

def words00 : List Nat := [360582281473957233, 360582281475026242, 360582281574149068, 360582281713467120, 360582281778834793, 360582281863886962, 360582281864863884, 360582281784227159, 360582281767283195, 360582282015086610]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584599820066856, 360584636191914929⟩, ⟨(-178063523731825845), (-176223006586668647)⟩, true⟩

def words01 : List Nat := [360582282345305827, 360582282675719168, 360582282916821662, 360582283163441427, 360582283364925905, 360582283566698579, 360582283846844169, 360582284009410891, 360582284041764191, 360582284074263181]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599258176391195, 360599294558314210⟩, ⟨(-1276412694947108540), (-1274571422937788730)⟩, true⟩

def words02 : List Nat := [360582284075146740, 360582284030928312, 360582284231879820, 360582284433030172, 360582284467050051, 360582284468116547, 360582284324053545, 360582284289053398, 360582284395419777, 360582284623535043]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599378007239591, 360599414399319611⟩, ⟨(-1285383722767499109), (-1283541689643918271)⟩, true⟩

def words03 : List Nat := [360582284762376627, 360582284901343099, 360582285217964394, 360582285648989292, 360582285957853520, 360582286266873992, 360582286486672574, 360582286577418433, 360582286806834683, 360582287036599019]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609091868489830, 360609128270626198⟩, ⟨(-2013346548352444756), (-2011503761556299150)⟩, true⟩

def words04 : List Nat := [360582287443840084, 360582287904286194, 360582288229163172, 360582288554132342, 360582288781499339, 360582289098773372, 360582289556462608, 360582290014344345, 360582290327405071, 360582290686583874]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360639778689588729, 360639815101800253⟩, ⟨(-4313519417648939226), (-4311675875670077546)⟩, true⟩

def words05 : List Nat := [360582291190813672, 360582291695355161, 360582292260045112, 360582292799161846, 360582293189464324, 360582293579855748, 360582294052830318, 360582294643641271, 360582295411852728, 360582296180285465]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360617385711719881, 360617422134115083⟩, ⟨(-2634960899413765914), (-2633116594019007092)⟩, true⟩

def words06 : List Nat := [360582296858974060, 360582297437479148, 360582298011686682, 360582298586176956, 360582299011968472, 360582299260165082, 360582299419268624, 360582299578484172, 360582299862699709, 360582300332431512]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579699944026891, 360579736376468944⟩, ⟨190573334783238510, 192418393441551660⟩, true⟩

def words07 : List Nat := [360582300800150055, 360582301268056122, 360582301626035778, 360582301908541288, 360582302145640427, 360582302383023065, 360582302616039011, 360582302671543998, 360582302672504908, 360582302639384943]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581980453436373, 360582016895952293⟩, ⟨19651726406980138, 21497540454571700⟩, true⟩

def words08 : List Nat := [360582302701615188, 360582302887895615, 360582303218042908, 360582303548409529, 360582303727162141, 360582303728334381, 360582303729205753, 360582303672983083, 360582303616439024, 360582303568047967]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586980938397462, 360587017391095317⟩, ⟨(-355415863147775415), (-353569285507084485)⟩, true⟩

def words09 : List Nat := [360582303565193119, 360582303425157984, 360582303284923682, 360582303272398707, 360582303273292617, 360582303256071921, 360582303238748932, 360582303108661777, 360582303132735904, 360582303196811147]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk749
