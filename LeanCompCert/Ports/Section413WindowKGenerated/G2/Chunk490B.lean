import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490A

def state06 : KState := ⟨⟨360523089765699183, 360523104841665311⟩, ⟨2886027393734753814, 2886527175664797558⟩, true⟩

def words05 : List Nat := [360581949232861344, 360581948812248121, 360581948391578278, 360581947751454132, 360581946695934541, 360581945537215005, 360581944378331733, 360581943633898426, 360581942713230413, 360581941514630350]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560792919116113, 360560808001468846⟩, ⟨1036056800107359224, 1036556895394661370⟩, true⟩

def words06 : List Nat := [360581940315921464, 360581939414467115, 360581938865901577, 360581938185289050, 360581937504651452, 360581936467300825, 360581935014774818, 360581933887399052, 360581932759863319, 360581932046616486]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360531126947969646, 360531142036758023⟩, ⟨2491935656852332922, 2492436067968637262⟩, true⟩

def words07 : List Nat := [360581931616743560, 360581930869256409, 360581930121670635, 360581929624445930, 360581929336868122, 360581928806599129, 360581928276295458, 360581927377818324, 360581926201678404, 360581925167727230]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565725777330171, 360565740872485307⟩, ⟨793703787982799989, 794204511611580049⟩, true⟩

def words08 : List Nat := [360581924133593927, 360581923513509308, 360581923032338476, 360581922344231883, 360581921656031290, 360581920864824674, 360581920309101244, 360581920079095665, 360581919849022218, 360581919412139241]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569879410982508, 360569894512529011⟩, ⟨589647228584931620, 590148265997751156⟩, true⟩

def words09 : List Nat := [360581919083133295, 360581918745871170, 360581918408428188, 360581918134788514, 360581917446496855, 360581916407800138, 360581915369013409, 360581914555144868, 360581914069578643, 360581913825482123]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk490B
