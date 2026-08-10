import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512A

def state06 : KState := ⟨⟨360612827174104095, 360612843691467244⟩, ⟨(-1584036915315829052), (-1583464820418133278)⟩, true⟩

def words05 : List Nat := [360581951076321855, 360581951055773691, 360581951314462536, 360581951615219844, 360581951615881178, 360581951534335774, 360581951750117827, 360581952240448213, 360581952843666360, 360581953447023747]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607549900991227, 360607566425105337⟩, ⟨(-1313632384251701564), (-1313059943265543720)⟩, true⟩

def words06 : List Nat := [360581953758619268, 360581953976130693, 360581954573126535, 360581955170314181, 360581955672281282, 360581955794783842, 360581955795416186, 360581955676926568, 360581955736891839, 360581956237216169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552823202154377, 360552839732941390⟩, ⟨1492502231218598283, 1493075014357962663⟩, true⟩

def words07 : List Nat := [360581956660950493, 360581957084805938, 360581957308634302, 360581957311439334, 360581957312043619, 360581957056893556, 360581956803519335, 360581956804228354, 360581956427430859, 360581955860366468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586189865784160, 360586206403276497⟩, ⟨(-218618362762056085), (-218045235741781363)⟩, true⟩

def words08 : List Nat := [360581955293164823, 360581954892698944, 360581955224688091, 360581955580744733, 360581955610017715, 360581955610726880, 360581955289169444, 360581955318517601, 360581955319102499, 360581955263003510]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580164992806275, 360580181537057691⟩, ⟨90381277755516216, 90954751481364682⟩, true⟩

def words09 : List Nat := [360581955263641450, 360581955105617920, 360581954947468625, 360581954964040568, 360581954986534952, 360581955009156450, 360581955009788292, 360581954842259362, 360581954567904953, 360581954534162591]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512B
