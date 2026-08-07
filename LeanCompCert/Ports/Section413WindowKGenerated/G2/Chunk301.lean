import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk301

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568505421938094, 360568510872753428⟩, ⟨445750217301413419, 445861174984345637⟩, true⟩

def state01 : KState := ⟨⟨360590700477157117, 360590705931740564⟩, ⟨(-222306718640533112), (-222195647518855032)⟩, true⟩

def words00 : List Nat := [360583323201426383, 360583324052059364, 360583326001861098, 360583327951609738, 360583328908257777, 360583328908657166, 360583328768067371, 360583327635107202, 360583326502103570, 360583326713264962]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360638158572614992, 360638164031000607⟩, ⟨(-1651592680461228661), (-1651481494837285423)⟩, true⟩

def words01 : List Nat := [360583326713620942, 360583326409063036, 360583326898182847, 360583328568757517, 360583329703862557, 360583330838956633, 360583331424255831, 360583332146864781, 360583333967635758, 360583335788417782]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596266260912922, 360596271723066498⟩, ⟨(-389835660831619881), (-389724361697717489)⟩, true⟩

def words02 : List Nat := [360583337114031445, 360583337343632529, 360583337343991930, 360583337012737436, 360583336681439211, 360583336027379671, 360583336551982086, 360583337178155459, 360583337178513998, 360583337390926917]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360704072806003191, 360704078271929677⟩, ⟨(-3638689358942823469), (-3638577946112909803)⟩, true⟩

def words03 : List Nat := [360583338408263543, 360583339425653972, 360583341540114437, 360583343919581322, 360583345179759792, 360583346439879365, 360583348796879913, 360583351706071166, 360583355711920984, 360583359717597940]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360659502675264812, 360659508145004303⟩, ⟨(-2295199241176636185), (-2295087713404166217)⟩, true⟩

def words04 : List Nat := [360583362973380653, 360583366260619894, 360583370232353363, 360583374203940080, 360583377896154898, 360583380493898623, 360583382391325748, 360583384288668986, 360583385832324885, 360583388357487997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360585763746149939, 360585769219656868⟩, ⟨(-71607213717499996), (-71495572337848380)⟩, true⟩

def words05 : List Nat := [360583391051525900, 360583393745459389, 360583395662775302, 360583396486149729, 360583396740735364, 360583396995417140, 360583397973309358, 360583398597429747, 360583398676391314, 360583398755403765]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360652412904133169, 360652418381419431⟩, ⟨(-2082151767166138320), (-2082040011782755074)⟩, true⟩

def words06 : List Nat := [360583399929661387, 360583401940499791, 360583403639397776, 360583405338253768, 360583406094755323, 360583406095155513, 360583406175626231, 360583406593202499, 360583408105500016, 360583410393226042]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597428511750543, 360597433992847247⟩, ⟨(-423056633060844675), (-422944762697865823)⟩, true⟩

def words07 : List Nat := [360583412077119669, 360583413760946155, 360583415053707222, 360583416997357089, 360583418210622459, 360583419423872090, 360583419805913630, 360583419806314040, 360583419918080404, 360583420382870843]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614894543027556, 360614900027894083⟩, ⟨(-950313653944067239), (-950201669788912983)⟩, true⟩

def words08 : List Nat := [360583421941613806, 360583422408179414, 360583422408536162, 360583422327365836, 360583422246126026, 360583422265173228, 360583423737664736, 360583425210135193, 360583425974157812, 360583427017070033]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360625825848694958, 360625831337348823⟩, ⟨(-1280516605831665909), (-1280404507318281059)⟩, true⟩

def words09 : List Nat := [360583427633143236, 360583428249287809, 360583429718120076, 360583430552935131, 360583430553310300, 360583430264288414, 360583430778852639, 360583432432428180, 360583433836691507, 360583435240950748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk301
