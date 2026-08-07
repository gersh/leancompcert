import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk270

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583789541413060, 360583793886415271⟩, ⟨(-32279532423895428), (-32200179384290142)⟩, true⟩

def state01 : KState := ⟨⟨360578227032041091, 360578231380384199⟩, ⟨117723018621183923, 117802461881899271⟩, true⟩

def words00 : List Nat := [360582601331636239, 360582601198927587, 360582600484835400, 360582599080953397, 360582597677119530, 360582595376182255, 360582594130940028, 360582593922226577, 360582593713492862, 360582592819180271]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360637770904249551, 360637775255949259⟩, ⟨(-1490983239094277517), (-1490903705155297289)⟩, true⟩

def words01 : List Nat := [360582593864723466, 360582595071749939, 360582595624578430, 360582595790408519, 360582595790735921, 360582594798132778, 360582594180542040, 360582595429789166, 360582597472261162, 360582599514668208]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590915668712860, 360590920023793922⟩, ⟨(-224991950987547341), (-224912325668251209)⟩, true⟩

def words02 : List Nat := [360582600867603514, 360582601410571434, 360582602884335957, 360582604358095069, 360582604986537882, 360582604986893065, 360582604251739869, 360582602224791126, 360582600197924340, 360582599490862538]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592680143911460, 360592684502337559⟩, ⟨(-272523836470270290), (-272444120717279278)⟩, true⟩

def words03 : List Nat := [360582601165086326, 360582602839254359, 360582603824985286, 360582604860376337, 360582605542734193, 360582606225138917, 360582607472240882, 360582608532839176, 360582608905787810, 360582609278761609]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587029179389247, 360587033541173266⟩, ⟨(-119591232475189123), (-119511425907316117)⟩, true⟩

def words04 : List Nat := [360582609615573154, 360582610640228981, 360582613029307134, 360582615418276480, 360582616621257902, 360582616621613313, 360582616463328138, 360582616031199234, 360582615598993101, 360582615537184234]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360558622683617223, 360558627048785925⟩, ⟨648869442899782609, 648949341039822257⟩, true⟩

def words05 : List Nat := [360582615537501073, 360582614868325048, 360582614199132004, 360582614371853331, 360582614372156146, 360582613883768311, 360582613395377410, 360582612051772174, 360582609802398406, 360582608916525756]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605677639601476, 360605682008121927⟩, ⟨(-624600205057316772), (-624520216201845130)⟩, true⟩

def words06 : List Nat := [360582608507562865, 360582609032736282, 360582609033056389, 360582608682133470, 360582608331177702, 360582607823558963, 360582609381700381, 360582610939794662, 360582611441953989, 360582612294546447]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630822903575930, 360630827275454181⟩, ⟨(-1305584459935378816), (-1305504380167214902)⟩, true⟩

def words07 : List Nat := [360582612762558050, 360582613230640367, 360582615060757996, 360582615532687206, 360582615533016358, 360582614878027927, 360582614929636140, 360582616322391987, 360582618102997090, 360582619883549628]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600852872107038, 360600857247381976⟩, ⟨(-494223016800162785), (-494142845033854521)⟩, true⟩

def words08 : List Nat := [360582620617191568, 360582621162451281, 360582621302503608, 360582621442644779, 360582621442942803, 360582621231561876, 360582620310335719, 360582618703673148, 360582617097061302, 360582617136458280]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572094763901853, 360572099142529225⟩, ⟨285193538376938702, 285273800977665772⟩, true⟩

def words09 : List Nat := [360582619170314481, 360582621204090148, 360582622187983694, 360582623435082590, 360582624331320351, 360582625227585965, 360582625945330152, 360582626238817034, 360582626239137273, 360582625851052387]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk270
