import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617613369143115, 360617639410289010⟩, ⟨(-2228995324077014857), (-2227872995855076709)⟩, true⟩

def state01 : KState := ⟨⟨360623702699459967, 360623728749151765⟩, ⟨(-2617635699880542208), (-2616512826387926962)⟩, true⟩

def words00 : List Nat := [360582720693414393, 360582721097083967, 360582721746105827, 360582722395375197, 360582722876123856, 360582723189107789, 360582723378358560, 360582723567701308, 360582724002367711, 360582724645997326]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584693146128954, 360584719204280818⟩, ⟨(-128210089425244134), (-127086676052489614)⟩, true⟩

def words01 : List Nat := [360582725326788360, 360582726007741153, 360582726548224192, 360582726844346637, 360582727078275992, 360582727312435782, 360582727617757448, 360582727841399292, 360582727873423160, 360582727905553871]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630330459939166, 360630356526566455⟩, ⟨(-3040994141681103366), (-3039870187366386822)⟩, true⟩

def words02 : List Nat := [360582728043707658, 360582728371868714, 360582728945128811, 360582729518542812, 360582729845729534, 360582730252211404, 360582730846904566, 360582731441852521, 360582732051445794, 360582732798481882]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608346665723141, 360608372740907103⟩, ⟨(-1637711659627013052), (-1636587159096983940)⟩, true⟩

def words03 : List Nat := [360582733421853666, 360582734045304033, 360582734540495629, 360582735158131557, 360582735629953516, 360582736101905133, 360582736416596032, 360582736573798124, 360582736976093037, 360582737378693213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601788260648742, 360601814344282457⟩, ⟨(-1218979324079841972), (-1217854284074014770)⟩, true⟩

def words04 : List Nat := [360582738026225081, 360582738490414056, 360582738802450895, 360582739114578187, 360582739355151084, 360582739720008907, 360582740076500728, 360582740433141749, 360582740666232633, 360582740965884719]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360645360414590801, 360645386506700981⟩, ⟨(-4001292279761835407), (-4000166698492717737)⟩, true⟩

def words05 : List Nat := [360582741437712475, 360582741909791379, 360582742626759170, 360582743350061335, 360582743824883630, 360582744299750838, 360582745019573616, 360582745895285858, 360582746876918716, 360582747858723457]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360632899928428984, 360632926029102387⟩, ⟨(-3205583535015127374), (-3204457406855660250)⟩, true⟩

def words06 : List Nat := [360582748652576546, 360582749307469704, 360582750207275928, 360582751107326603, 360582751907059240, 360582752668697229, 360582753281320193, 360582753894037452, 360582754470118932, 360582755256657058]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599027077527002, 360599053186649376⟩, ⟨(-1041923642960664518), (-1040796975122925408)⟩, true⟩

def words07 : List Nat := [360582756158301110, 360582757060087922, 360582757813042542, 360582758371660718, 360582758750032058, 360582759128615485, 360582759544322683, 360582759927743646, 360582760183604368, 360582760439586511]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360629906746885594, 360629932864502808⟩, ⟨(-3014588756382492179), (-3013461545853376885)⟩, true⟩

def words08 : List Nat := [360582760888374418, 360582761536131369, 360582762378902570, 360582763221819405, 360582763857781684, 360582764411828061, 360582765096573472, 360582765781567007, 360582766459662229, 360582767198824491]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610519924403017, 360610546050583704⟩, ⟨(-1775805285015382281), (-1774677527325234913)⟩, true⟩

def words09 : List Nat := [360582767791844244, 360582768384935361, 360582769177277615, 360582770124620427, 360582770937360413, 360582771750233890, 360582772393235520, 360582772882924443, 360582773318291101, 360582773753947889]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638
