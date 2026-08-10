import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535A

def state06 : KState := ⟨⟨360538035209531026, 360538053306962687⟩, ⟨2352283827283847504, 2352938747798742668⟩, true⟩

def words05 : List Nat := [360581986241008687, 360581986552311666, 360581986688752766, 360581986689495939, 360581986477937233, 360581986178971333, 360581985879809338, 360581985568531624, 360581985021640001, 360581984202179244]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559918166756945, 360559936271202919⟩, ⟨1180095220529448126, 1180750516766342368⟩, true⟩

def words06 : List Nat := [360581983382578362, 360581982717228670, 360581982242112619, 360581981953921979, 360581981665671271, 360581981080642950, 360581980147678239, 360581979160996978, 360581978174125703, 360581977535282933]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566186382834586, 360566204494363516⟩, ⟨844178155123601755, 844833830829120185⟩, true⟩

def words07 : List Nat := [360581977124516358, 360581976444918958, 360581975765207284, 360581975172286766, 360581974754816566, 360581974248202262, 360581973741531403, 360581973061110558, 360581972496478112, 360581972203038939]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556463648774840, 360556481767302792⟩, ⟨1365071659904093092, 1365727710652141558⟩, true⟩

def words08 : List Nat := [360581971909366104, 360581971667534637, 360581971180061491, 360581970488431660, 360581969796715117, 360581968864989881, 360581968166558510, 360581967674737061, 360581967182852739, 360581966516521903]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579411035132188, 360579429160690531⟩, ⟨135289719869074791, 135946147410074421⟩, true⟩

def words09 : List Nat := [360581966041581572, 360581965914423397, 360581966006556049, 360581966007299812, 360581965971710864, 360581965640237144, 360581965323914771, 360581965515343636, 360581965515960053, 360581965469410869]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535B
