import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921A

def state06 : KState := ⟨⟨360587546761263138, 360587602693468313⟩, ⟨(-522504506122127952), (-519023686838267666)⟩, true⟩

def words05 : List Nat := [360581970853335096, 360581970789295187, 360581970777216285, 360581970889778423, 360581970920423309, 360581970951265595, 360581970952461776, 360581970894579949, 360581970924498307, 360581970987140927]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590260472054427, 360590316416830349⟩, ⟨(-772591742147848013), (-769109764282748241)⟩, true⟩

def words06 : List Nat := [360581971104839678, 360581971266011083, 360581971360519700, 360581971455170870, 360581971520203689, 360581971644444308, 360581971781610472, 360581971919028628, 360581971945830293, 360581972037749264]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623254216167386, 360623310173519430⟩, ⟨(-3813824596463342405), (-3810341459394178483)⟩, true⟩

def words07 : List Nat := [360581972212889345, 360581972388417050, 360581972681080425, 360581972934341627, 360581973086991247, 360581973239763056, 360581973509776167, 360581973842177384, 360581974291685375, 360581974741495541]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603015376518590, 360603071346572405⟩, ⟨(-1948244635194181301), (-1944760327212458757)⟩, true⟩

def words08 : List Nat := [360581975132088142, 360581975405419769, 360581975629108563, 360581975853162247, 360581976030411051, 360581976090480562, 360581976091765696, 360581976093188054, 360581976211852116, 360581976442219351]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564944046976310, 360565000029580360⟩, ⟨1561755547426755646, 1565241012476603172⟩, true⟩

def words09 : List Nat := [360581976608782132, 360581976775586384, 360581976877038756, 360581976908661764, 360581976910683857, 360581976913080484, 360581976914176939, 360581976913829852, 360581976795977629, 360581976613229781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921B
