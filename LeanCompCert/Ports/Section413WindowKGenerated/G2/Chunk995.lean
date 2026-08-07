import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk995

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586186016405543, 360586251600910074⟩, ⟨(-383794288030073650), (-379388005301123034)⟩, true⟩

def state01 : KState := ⟨⟨360585904626148488, 360585970224427704⟩, ⟨(-355872385406395646), (-351464732028723256)⟩, true⟩

def words00 : List Nat := [360582438695746097, 360582438664673405, 360582438660099111, 360582438681055120, 360582438682286945, 360582438634482757, 360582438570925440, 360582438443328700, 360582438315457093, 360582438306026435]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561937198352276, 360562002810271776⟩, ⟨2029299751865232899, 2033708762657189315⟩, true⟩

def words01 : List Nat := [360582438425536378, 360582438545346749, 360582438614323445, 360582438615770498, 360582438583974223, 360582438497245813, 360582438410102138, 360582438317716884, 360582438190586682, 360582437986745422]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600433757818256, 360600499383402540⟩, ⟨(-1802097734650066545), (-1797687363873682873)⟩, true⟩

def words02 : List Nat := [360582437782581410, 360582437626597255, 360582437551524310, 360582437565298242, 360582437566634307, 360582437494852554, 360582437454718671, 360582437486126079, 360582437617974278, 360582437800942064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581311572600235, 360581377211990814⟩, ⟨101235658172198174, 105647403156277680⟩, true⟩

def words03 : List Nat := [360582437933084901, 360582438065371210, 360582438171706231, 360582438336660740, 360582438441468740, 360582438546507703, 360582438600850793, 360582438602298222, 360582438577227999, 360582438568261221]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569221157559025, 360569286810574091⟩, ⟨1304713865070671922, 1309126966303273104⟩, true⟩

def words04 : List Nat := [360582438558777605, 360582438520644835, 360582438410638345, 360582438250272347, 360582438089671639, 360582437887438053, 360582437744434425, 360582437599186934, 360582437453797002, 360582437257247153]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603845262083773, 360603910928754282⟩, ⟨(-2142295298998836331), (-2137880838298096829)⟩, true⟩

def words05 : List Nat := [360582437126319457, 360582437096666661, 360582437118119469, 360582437215220789, 360582437226402609, 360582437237697034, 360582437303064140, 360582437419535442, 360582437636389506, 360582437853571248]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588502848298319, 360588568528771791⟩, ⟨(-614798429074319118), (-610382594082228940)⟩, true⟩

def words06 : List Nat := [360582437975689051, 360582438026788866, 360582438178427888, 360582438330489281, 360582438456637222, 360582438482439861, 360582438483750398, 360582438425372075, 360582438366694682, 360582438404598265]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570363202385104, 360570428896488326⟩, ⟨1191509648266104614, 1195926840440793058⟩, true⟩

def words07 : List Nat := [360582438568133481, 360582438731954316, 360582438845112521, 360582438857857086, 360582438859091199, 360582438800488076, 360582438782020092, 360582438783467999, 360582438724769952, 360582438605671303]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591674659841713, 360591740367625667⟩, ⟨(-930756862595494198), (-926338308026988824)⟩, true⟩

def words08 : List Nat := [360582438486239115, 360582438526362822, 360582438598575704, 360582438671056871, 360582438672404628, 360582438660533594, 360582438733710056, 360582438807310967, 360582438846814919, 360582438941713417]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589605272052234, 360589670993624273⟩, ⟨(-724682059910009876), (-720262132118013530)⟩, true⟩

def words09 : List Nat := [360582438979052995, 360582439016550329, 360582439052621254, 360582439165775484, 360582439253017882, 360582439340520354, 360582439377367039, 360582439378818407, 360582439444458712, 360582439518718218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk995
