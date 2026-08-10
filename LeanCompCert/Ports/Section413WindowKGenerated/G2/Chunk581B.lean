import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581A

def state06 : KState := ⟨⟨360599303693820981, 360599325175678465⟩, ⟨(-1011820628556516944), (-1010976539503955796)⟩, true⟩

def words05 : List Nat := [360581940400023172, 360581940762733074, 360581941420978229, 360581941784395755, 360581941897692317, 360581942011063162, 360581942026929988, 360581942197521278, 360581942497061141, 360581942796773289]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590519638503151, 360590541128102024⟩, ⟨(-501061841921916020), (-500217302592177258)⟩, true⟩

def words06 : List Nat := [360581942947149761, 360581943013281593, 360581943068541311, 360581943124026193, 360581943124705728, 360581943104596858, 360581942869984258, 360581942446944467, 360581942023758249, 360581942044321581]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569245575126150, 360569267072370811⟩, ⟨736697734409066639, 737542718532718067⟩, true⟩

def words07 : List Nat := [360581942488412316, 360581942932643395, 360581943227667187, 360581943586148610, 360581943775317720, 360581943964699902, 360581944145583245, 360581944200324312, 360581944201053296, 360581943983999081]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619101970474456, 360619123475384354⟩, ⟨(-2164243584386037985), (-2163398154261289411)⟩, true⟩

def words08 : List Nat := [360581943766768366, 360581943912174289, 360581944284860021, 360581944657702639, 360581944776352413, 360581944777165031, 360581944800233829, 360581944901017260, 360581945296941519, 360581945936688314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360631576211439046, 360631597724089740⟩, ⟨(-2890251318225594603), (-2889405437625707593)⟩, true⟩

def words09 : List Nat := [360581946297827296, 360581946659028101, 360581947315410966, 360581948157977088, 360581948887934392, 360581949617999176, 360581950169351814, 360581950727923959, 360581951581622052, 360581952435561610]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581B
