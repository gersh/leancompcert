import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385A

def state06 : KState := ⟨⟨360544713537239201, 360544722668582457⟩, ⟨1443993191874043605, 1444231189124996761⟩, true⟩

def words05 : List Nat := [360582181972651947, 360582182057319251, 360582182057783392, 360582181751271833, 360582181076469314, 360582179961393996, 360582178846206727, 360582178401870207, 360582177767737777, 360582176796931135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360629529952046038, 360629539088311574⟩, ⟨(-1827072304809601682), (-1826834117731139452)⟩, true⟩

def words06 : List Nat := [360582175826056994, 360582175560047552, 360582175563773001, 360582175567590985, 360582175568075794, 360582174993821106, 360582174316908379, 360582174310569889, 360582174967519402, 360582176196041964]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593694794222289, 360593703935449618⟩, ⟨(-444731362446388647), (-444492983966844151)⟩, true⟩

def words07 : List Nat := [360582176912472200, 360582177628919343, 360582178568542383, 360582179846586815, 360582180946043685, 360582182045528108, 360582182508438477, 360582182508959902, 360582182602974408, 360582182902195767]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605212724447985, 360605221870585587⟩, ⟨(-889241688750260762), (-889003120808032846)⟩, true⟩

def words08 : List Nat := [360582183590706381, 360582183825462800, 360582183825932018, 360582183711076755, 360582183596130861, 360582183435671256, 360582184002096330, 360582184568595221, 360582184732941277, 360582185330438713]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613414457064085, 360613423608132466⟩, ⟨(-1205844817410330160), (-1205606059164911896)⟩, true⟩

def words09 : List Nat := [360582185691684196, 360582186053061520, 360582187083661771, 360582187813866726, 360582187999105435, 360582188184375021, 360582188569806898, 360582189480397451, 360582190289996891, 360582191099669864]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385B
