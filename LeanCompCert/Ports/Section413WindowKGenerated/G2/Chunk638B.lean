import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638B
