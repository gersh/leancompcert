import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422A

def state06 : KState := ⟨⟨360611512487986626, 360611523537939996⟩, ⟨(-1224733860837317914), (-1224418273939293174)⟩, true⟩

def words05 : List Nat := [360582546922360340, 360582547551885553, 360582548199968410, 360582548542572454, 360582548543108093, 360582548406952449, 360582548693287419, 360582549394702120, 360582550080791506, 360582550766970561]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628332137675479, 360628343193104600⟩, ⟨(-1935761320750736153), (-1935445502420116745)⟩, true⟩

def words06 : List Nat := [360582551172518366, 360582551778644013, 360582552545642613, 360582553312777011, 360582553855498023, 360582554412658484, 360582554660545103, 360582554908482798, 360582555506089192, 360582556589938834]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571966962209347, 360571978023066230⟩, ⟨447179178606530698, 447495226395246102⟩, true⟩

def words07 : List Nat := [360582558001324267, 360582559412752866, 360582560279601172, 360582560895002602, 360582561205347890, 360582561515832068, 360582562216020748, 360582562359948559, 360582562360462580, 360582562110729316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601868821130550, 360601879887416106⟩, ⟨(-817067590886863553), (-816751313546790359)⟩, true⟩

def words08 : List Nat := [360582562169172686, 360582562819252675, 360582564027720705, 360582565236245995, 360582565971509828, 360582566150603602, 360582566306448195, 360582566462445789, 360582566779382550, 360582567236650062]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597981536911301, 360597992608682772⟩, ⟨(-652645942972519059), (-652329433607309305)⟩, true⟩

def words09 : List Nat := [360582567317930540, 360582567399265052, 360582568038834154, 360582569127612881, 360582569850664605, 360582570573774378, 360582570936464442, 360582570937040198, 360582571108407008, 360582571473636147]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk422B
