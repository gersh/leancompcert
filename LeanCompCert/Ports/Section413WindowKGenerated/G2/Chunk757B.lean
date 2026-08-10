import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757A

def state06 : KState := ⟨⟨360563406504660141, 360563443729467259⟩, ⟨1419643561994966671, 1421548341715381345⟩, true⟩

def words05 : List Nat := [360582207444101015, 360582207652527739, 360582207754448149, 360582207863626474, 360582207910570108, 360582207957798616, 360582207972171732, 360582207973250853, 360582207813696009, 360582207567135097]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582041065534972, 360582078300550478⟩, ⟨7780027976280039, 9685581132296465⟩, true⟩

def words06 : List Nat := [360582207320351596, 360582207036607413, 360582206872096858, 360582206850734904, 360582206829283512, 360582206659761725, 360582206381702755, 360582206278019580, 360582206173995630, 360582206129257517]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563830316620558, 360563867561919318⟩, ⟨1387763714717906449, 1389670047086806815⟩, true⟩

def words07 : List Nat := [360582206128541248, 360582206039905215, 360582206035344928, 360582206217531250, 360582206277211297, 360582206337049416, 360582206338016812, 360582206265657814, 360582206019182064, 360582205778428778]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587504682050019, 360587541937531041⟩, ⟨(-406409858950395267), (-404502754919106459)⟩, true⟩

def words08 : List Nat := [360582205537311978, 360582205470387008, 360582205408566171, 360582205259751513, 360582205110766230, 360582204871960235, 360582204808417470, 360582204864257960, 360582204865246765, 360582204855886531]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360612309071128776, 360612346336788258⟩, ⟨(-2286510920398138171), (-2284603044889677237)⟩, true⟩

def words09 : List Nat := [360582205003570526, 360582205151565504, 360582205473149856, 360582205621086542, 360582205622083213, 360582205621979114, 360582205794340411, 360582206055308403, 360582206453810513, 360582206852548081]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757B
