import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464504382964284, 362464579058991197⟩, ⟨1463899958244143344, 1467475637129132298⟩, true⟩

def state01 : KState := ⟨⟨362473450929690436, 362473525627493979⟩, ⟨829585804996464373, 833163027954455597⟩, true⟩

def words00 : List Nat := [371285276591521869, 371285276500867452, 371285276333618880, 371285276247144252, 371285276159895841, 371285276033986997, 371285275735557794, 371285275513912055, 371285275291036053, 371285275211867897]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476389418833057, 362476464138796836⟩, ⟨621226915349966403, 624805709802129839⟩, true⟩

def words01 : List Nat := [371285275048006416, 371285274884547655, 371285274752426499, 371285274755104423, 371285274700384758, 371285274685406806, 371285274669675229, 371285274588189780, 371285274267150992, 371285274145985248]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469961622256950, 362470036363878281⟩, ⟨1077145125174358307, 1080725455689820677⟩, true⟩

def words02 : List Nat := [371285274097637535, 371285274100067431, 371285273911336679, 371285273715597663, 371285273518904649, 371285273385530856, 371285273151660603, 371285273065872039, 371285272979220485, 371285272871078194]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486793508606919, 362486868272180279⟩, ⟨(-116835178445966183), (-113253290759095889)⟩, true⟩

def words03 : List Nat := [371285272657948153, 371285272529130062, 371285272441251904, 371285272443684526, 371285272271635543, 371285272068513043, 371285271864385554, 371285271859719345, 371285271803575232, 371285271828787050]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479069257739780, 362479144043237180⟩, ⟨431097540018899448, 434680983107634668⟩, true⟩

def words04 : List Nat := [371285271840082746, 371285271842513756, 371285271614338576, 371285271556986996, 371285271498429393, 371285271449239489, 371285271193473149, 371285270938173951, 371285270681914847, 371285270625099163]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477877822671677, 362477952630110558⟩, ⟨515696796901176900, 519281796847964524⟩, true⟩

def words05 : List Nat := [371285270652335297, 371285270766975823, 371285270862317374, 371285270864760011, 371285270770083338, 371285270700410235, 371285270755160731, 371285270757598512, 371285270681389378, 371285270581024425]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491309715246852, 362491384544429427⟩, ⟨(-437493558981640422), (-433907015989831050)⟩, true⟩

def words06 : List Nat := [371285270479558550, 371285270481895007, 371285270433626416, 371285270486029455, 371285270521317531, 371285270523792865, 371285270419208126, 371285270412186135, 371285270592129847, 371285270680795129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486889206329464, 362486964057693349⟩, ⟨(-123759139339657521), (-120171022030562351)⟩, true⟩

def words07 : List Nat := [371285270746947314, 371285270813913665, 371285270962948895, 371285271013911846, 371285271072905276, 371285271132856657, 371285271174495548, 371285271176931064, 371285271028126907, 371285271055030235]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474969746200824, 362475044619185523⟩, ⟨722369187848028716, 725958839917239548⟩, true⟩

def words08 : List Nat := [371285271278679719, 371285271281111782, 371285271240613672, 371285271160650464, 371285271079730708, 371285271060102844, 371285270940209044, 371285270904279144, 371285270867551179, 371285270831890373]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507067052329450, 362507141947337575⟩, ⟨(-1556381446533871761), (-1552790230914610965)⟩, true⟩

def words09 : List Nat := [371285270743526258, 371285270800541917, 371285270954264998, 371285270999595091, 371285271012638154, 371285271026416158, 371285271237284427, 371285271349949210, 371285271659636077, 371285271970422960]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709
