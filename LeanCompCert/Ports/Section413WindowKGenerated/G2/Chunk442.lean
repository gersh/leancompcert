import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569165427526954, 360569177559979834⟩, ⟨622215682126216659, 622578073917619275⟩, true⟩

def state01 : KState := ⟨⟨360633743651848883, 360633755789997285⟩, ⟨(-2232374251336664471), (-2232011607774304585)⟩, true⟩

def words00 : List Nat := [360583262911244045, 360583263399841810, 360583264399530689, 360583265399290255, 360583265910175498, 360583266332691673, 360583267266280148, 360583268200009582, 360583269211498789, 360583270354070156]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580388131641664, 360580400275550263⟩, ⟨126800255012104509, 127163153261232729⟩, true⟩

def words01 : List Nat := [360583271239483378, 360583272124932987, 360583272934060303, 360583274000861097, 360583274813423055, 360583275626046578, 360583276084412237, 360583276085016521, 360583276033088679, 360583275968749296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581594453171411, 360581606602767772⟩, ⟨73430722585896492, 73793872375890646⟩, true⟩

def words02 : List Nat := [360583276350068836, 360583276350673157, 360583276286873194, 360583275966300215, 360583275645644317, 360583275048486490, 360583275023671894, 360583275182241506, 360583275182780649, 360583275014985179]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576319191316239, 360576331346625509⟩, ⟨306717516851323384, 307080919351248682⟩, true⟩

def words03 : List Nat := [360583275018195464, 360583275059299583, 360583275059796902, 360583274955206552, 360583274683943474, 360583273975884590, 360583273267742400, 360583272857780814, 360583272753329747, 360583272597062925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575935741450115, 360575947902510628⟩, ⟨323529997970165534, 323893654933806296⟩, true⟩

def words04 : List Nat := [360583272440705174, 360583272027857142, 360583271543566950, 360583271461726681, 360583271379724005, 360583271167952570, 360583270446552929, 360583269305310964, 360583268164004850, 360583267533130602]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442
