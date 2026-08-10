import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442A

def state06 : KState := ⟨⟨360541123871138572, 360541136037893837⟩, ⟨1864153895442046142, 1864517804426734786⟩, true⟩

def words05 : List Nat := [360583267368210265, 360583267121871733, 360583266875483453, 360583266216842809, 360583265736428310, 360583265040829794, 360583264345085572, 360583264159545482, 360583263464557801, 360583262513366651]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587928605593397, 360587940778067952⟩, ⟨(-207750148148565025), (-207385986000120389)⟩, true⟩

def words06 : List Nat := [360583261562090024, 360583260598461243, 360583259889186604, 360583259689968066, 360583259490709990, 360583258833358134, 360583257666668251, 360583257010043859, 360583256353258195, 360583256312255115]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597255684016657, 360597267862254184⟩, ⟨(-620748995895507320), (-620384578592523204)⟩, true⟩

def words07 : List Nat := [360583256312799046, 360583256161092307, 360583256366708346, 360583257036190018, 360583257191264689, 360583257346417514, 360583257346956469, 360583257246007985, 360583257369718990, 360583257686815678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619100448111804, 360619112632054084⟩, ⟨(-1588106073164240125), (-1587741403226927573)⟩, true⟩

def words08 : List Nat := [360583258513264596, 360583259357988549, 360583259888995329, 360583260420043801, 360583260647234714, 360583261295555412, 360583262304727777, 360583263313970389, 360583263875427690, 360583264685445814]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360638045785982852, 360638057975636007⟩, ⟨(-2427345776929978912), (-2426980854029528896)⟩, true⟩

def words09 : List Nat := [360583265642094473, 360583266598874976, 360583268064747007, 360583269021947604, 360583269547725686, 360583270073537903, 360583270677250694, 360583271616948081, 360583272854150282, 360583274091434081]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442B
