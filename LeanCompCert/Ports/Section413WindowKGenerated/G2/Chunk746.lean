import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746

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

def state06 : KState := ⟨⟨360588750699023097, 360588786808918334⟩, ⟨(-485552387010910389), (-483731461317367707)⟩, true⟩

def words05 : List Nat := [360582307587053626, 360582307600783271, 360582307793359900, 360582307854347161, 360582307855354403, 360582307750173973, 360582307644798892, 360582307595322464, 360582307682968448, 360582307770848695]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583779607407070, 360583815727432055⟩, ⟨(-114432457570195323), (-112610775540037097)⟩, true⟩

def words06 : List Nat := [360582307771795740, 360582307745563775, 360582307852303251, 360582307981187614, 360582308042956978, 360582308044020028, 360582308004888983, 360582307876171096, 360582307747261105, 360582307634925727]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552349959429541, 360552386089458932⟩, ⟨2232651799928501745, 2234474229037818335⟩, true⟩

def words07 : List Nat := [360582307791481539, 360582307948241605, 360582308014627780, 360582308015690390, 360582307902845506, 360582307696240818, 360582307489309404, 360582307404376026, 360582307140181164, 360582306740624409]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565071434883236, 360565107574963516⟩, ⟨1282446475115020815, 1284269654872878661⟩, true⟩

def words08 : List Nat := [360582306340841212, 360582305916947324, 360582305583480803, 360582305205402109, 360582304827255757, 360582304294806508, 360582303627278658, 360582303139064652, 360582302650553790, 360582302241650796]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578042974251826, 360578079124455717⟩, ⟨313496222002932310, 315320157942385668⟩, true⟩

def words09 : List Nat := [360582302012396545, 360582301676005556, 360582301339419999, 360582301151461724, 360582301073865205, 360582300951335970, 360582300828710721, 360582300567701994, 360582300333125197, 360582300277841827]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746
