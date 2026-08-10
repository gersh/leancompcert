import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk751A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk751B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk751A

def state06 : KState := ⟨⟨362457711716689444, 362457796018057510⟩, ⟨2058594747196018549, 2062873579606485865⟩, true⟩

def words05 : List Nat := [371285244023376481, 371285243989633084, 371285243954924600, 371285243903128081, 371285243642921772, 371285243437990548, 371285243231757307, 371285243138607045, 371285242808986800, 371285242446737746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479829525378852, 362479913849913076⟩, ⟨396124854301827662, 400405427994748590⟩, true⟩

def words06 : List Nat := [371285242083323453, 371285241897813812, 371285241622747955, 371285241440152603, 371285241256769247, 371285241045507917, 371285240735556726, 371285240603804612, 371285240512500898, 371285240515178405]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475069726925856, 362475154075023449⟩, ⟨753966694816659323, 758249039888005793⟩, true⟩

def words07 : List Nat := [371285240446251259, 371285240378335905, 371285240312747576, 371285240315625501, 371285240273002621, 371285240261463913, 371285240249047105, 371285240236446670, 371285239987272985, 371285239856346780]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459754089230367, 362459838460343836⟩, ⟨1905508037255388318, 1909792112781216860⟩, true⟩

def words08 : List Nat := [371285239766508215, 371285239769095353, 371285239577867383, 371285239381208797, 371285239183541187, 371285238992635490, 371285238712704672, 371285238481578268, 371285238249607995, 371285238009655995]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485625550927188, 362485709945464920⟩, ⟨(-39897429037290629), (-35611592127193201)⟩, true⟩

def words09 : List Nat := [371285237673615426, 371285237451138926, 371285237227289064, 371285237180986520, 371285237010435287, 371285236807165787, 371285236602854720, 371285236530923852, 371285236384108874, 371285236393356209]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk751B
