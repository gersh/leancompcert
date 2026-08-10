import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602301459275687, 360602344125496589⟩, ⟨(-1636000003654319787), (-1633668835086160815)⟩, true⟩

def state01 : KState := ⟨⟨360601651884455354, 360601694561708953⟩, ⟨(-1583572751246916527), (-1581240690080634733)⟩, true⟩

def words00 : List Nat := [360582150851477918, 360582150943360528, 360582151086735430, 360582151230444230, 360582151273261623, 360582151320348677, 360582151321380574, 360582151282429700, 360582151355700496, 360582151598575626]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587757290404690, 360587799978583099⟩, ⟨(-459224165928837210), (-456891220781834500)⟩, true⟩

def words01 : List Nat := [360582151993591325, 360582152388824633, 360582152666511297, 360582152872762828, 360582153040709437, 360582153208967583, 360582153529399349, 360582153697682738, 360582153768502101, 360582153839499526]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602694797924895, 360602737497029310⟩, ⟨(-1668022286699516485), (-1665688457364355223)⟩, true⟩

def words02 : List Nat := [360582153978231536, 360582154193701505, 360582154561330101, 360582154929171490, 360582155166985606, 360582155309412043, 360582155373352784, 360582155437621206, 360582155654024193, 360582155909536701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360616680263762097, 360616722973901549⟩, ⟨(-2799948811587141239), (-2797614089134157513)⟩, true⟩

def words03 : List Nat := [360582156078246039, 360582156247077227, 360582156568161994, 360582157023184940, 360582157439769572, 360582157856533080, 360582158151399693, 360582158496057639, 360582158924033245, 360582159352385456]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600221779522610, 360600264500580808⟩, ⟨(-1467778600165204375), (-1465442993893952521)⟩, true⟩

def words04 : List Nat := [360582159742699075, 360582159980946078, 360582160142791687, 360582160304759635, 360582160428468795, 360582160629659010, 360582160939515867, 360582161249607629, 360582161435835975, 360582161660666614]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk809A
