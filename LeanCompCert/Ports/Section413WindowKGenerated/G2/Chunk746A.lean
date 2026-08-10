import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603152111679530, 360603188161275607⟩, ⟨(-1560087307885858313), (-1558270882313427791)⟩, true⟩

def state01 : KState := ⟨⟨360616052894321030, 360616088954030394⟩, ⟨(-2522662130789791615), (-2520844950715938305)⟩, true⟩

def words00 : List Nat := [360582300278822805, 360582300440117698, 360582300727579193, 360582301015344293, 360582301221815714, 360582301455440547, 360582301575366293, 360582301695400051, 360582301994616155, 360582302448679763]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580084055382310, 360580120125108182⟩, ⟨161229224659674975, 163047152114180433⟩, true⟩

def words01 : List Nat := [360582303081751420, 360582303715010899, 360582304163825500, 360582304433272663, 360582304657223025, 360582304881448714, 360582305122930144, 360582305185172998, 360582305186128026, 360582305157969536]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600655341862407, 360600691421604720⟩, ⟨(-1373874180650069051), (-1372055505718617935)⟩, true⟩

def words02 : List Nat := [360582305230218376, 360582305422516749, 360582305793827892, 360582306165339814, 360582306388866642, 360582306433070903, 360582306470363289, 360582306507962991, 360582306648886320, 360582306896330791]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589827344701327, 360589863434554033⟩, ⟨(-565735290129680198), (-563915860609243896)⟩, true⟩

def words03 : List Nat := [360582307053831367, 360582307211445728, 360582307422232195, 360582307770229487, 360582307950226845, 360582308130385425, 360582308220046190, 360582308221108437, 360582308290515569, 360582308392946750]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577288265529616, 360577324365402704⟩, ⟨370181300141583347, 372001477631785983⟩, true⟩

def words04 : List Nat := [360582308491029105, 360582308492091239, 360582308410908732, 360582308233060931, 360582308055044800, 360582307832116491, 360582307764857642, 360582307758735171, 360582307752477493, 360582307640387725]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746A
