import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360648072012996787, 360648074558261771⟩, ⟨(-1400853952396610613), (-1400817955680410295)⟩, true⟩

def state01 : KState := ⟨⟨360599758827467112, 360599761375293413⟩, ⟨(-390917147691840551), (-390881097431642099)⟩, true⟩

def words00 : List Nat := [360581055050043331, 360581057203386524, 360581061632137076, 360581066060543669, 360581069368675075, 360581070397232361, 360581070397474383, 360581069860204292, 360581069322938226, 360581068768654245]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360449235856287320, 360449238406645979⟩, ⟨2757438669024161848, 2757474772248920740⟩, true⟩

def words01 : List Nat := [360581069999525102, 360581071230328194, 360581071324000233, 360581071324269260, 360581069140174770, 360581065881061827, 360581062622175398, 360581060032095146, 360581055164924315, 360581048864210459]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360546200995173949, 360546203548076884⟩, ⟨728325345179565480, 728361501642930290⟩, true⟩

def words02 : List Nat := [360581042564038334, 360581038536646070, 360581036236839009, 360581033553653675, 360581030870706574, 360581026301578436, 360581019456531979, 360581013356580570, 360581007257133640, 360581003428709609]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360533223824335690, 360533226379799499⟩, ⟨999838928063803319, 999875138139271905⟩, true⟩

def words03 : List Nat := [360581001766349375, 360580998969029297, 360580996171926508, 360580993549938222, 360580992080548224, 360580989561149977, 360580987041966988, 360580982738151950, 360580978188945965, 360580975908841490]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360543697285948605, 360543699843948462⟩, ⟨780358837590338823, 780395100783457441⟩, true⟩

def words04 : List Nat := [360580973628866179, 360580972755715630, 360580970658060289, 360580967115100695, 360580963572428571, 360580958838931370, 360580955263507337, 360580953955503201, 360580952647594467, 360580950206754355]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209A
