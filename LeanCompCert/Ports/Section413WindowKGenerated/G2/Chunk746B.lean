import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk746B
