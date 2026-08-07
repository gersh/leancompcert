import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589924072154272, 360589954353844454⟩, ⟨(-489286889585528254), (-487883705618735222)⟩, true⟩

def state01 : KState := ⟨⟨360554621410308776, 360554651701231353⟩, ⟨1932572671264734164, 1933976488620129266⟩, true⟩

def words00 : List Nat := [360582842451014294, 360582842422759920, 360582842182113684, 360582842069579128, 360582841956790911, 360582841790743683, 360582841412430458, 360582840836341829, 360582840260086929, 360582839669291696]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566329209588512, 360566359509646926⟩, ⟨1129313818260059168, 1130718262470929380⟩, true⟩

def words01 : List Nat := [360582839259238610, 360582839061419961, 360582838863498629, 360582838559556214, 360582838382993072, 360582838153322118, 360582837923363483, 360582837836333851, 360582837718211914, 360582837479079613]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560329339326948, 360560359648557663⟩, ⟨1541104818390302445, 1542509892048708123⟩, true⟩

def words02 : List Nat := [360582837239747645, 360582836996176125, 360582836886842415, 360582836915448183, 360582836916352625, 360582836756857670, 360582836385114294, 360582836076050780, 360582835766697837, 360582835386457251]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556269263748260, 360556299582218913⟩, ⟨1819779335119536263, 1821185042959385353⟩, true⟩

def words03 : List Nat := [360582835059835140, 360582834627248003, 360582834194486261, 360582833973910442, 360582833891765280, 360582833629361823, 360582833366860224, 360582832981405109, 360582832383776477, 360582831998345944]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564434430849824, 360564464758465346⟩, ⟨1259309788050834756, 1260716123640716788⟩, true⟩

def words04 : List Nat := [360582831612591911, 360582831389685436, 360582831173378488, 360582830823112432, 360582830472698317, 360582830069283921, 360582829811511818, 360582829647132723, 360582829482667838, 360582829159392378]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573343633015312, 360573373969788941⟩, ⟨647541557680997722, 648948522021504160⟩, true⟩

def words05 : List Nat := [360582828892678830, 360582828628068222, 360582828363174418, 360582828160873942, 360582827746594793, 360582827140578725, 360582826534377664, 360582826079290693, 360582825730709149, 360582825594053746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573318085476583, 360573348431521898⟩, ⟨649135831627199492, 650543432605824914⟩, true⟩

def words06 : List Nat := [360582825457271236, 360582825213217114, 360582824937920449, 360582824568745023, 360582824199323884, 360582823741988196, 360582823320113331, 360582822777891009, 360582822235498571, 360582821905129090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360532429771532150, 360532460126718975⟩, ⟨3457199266251861799, 3458607495023406075⟩, true⟩

def words07 : List Nat := [360582821767960023, 360582821766550653, 360582821765039916, 360582821601720017, 360582821226458405, 360582820734192396, 360582820241669349, 360582819744895325, 360582819150959153, 360582818418725723]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573924278943369, 360573954643292380⟩, ⟨607163085185344264, 608571943261623308⟩, true⟩

def words08 : List Nat := [360582817686290831, 360582817126093726, 360582816672313441, 360582816430317591, 360582816188231709, 360582815770317212, 360582815209917731, 360582814861370356, 360582814512536987, 360582814330921753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576529211944494, 360576559585555999⟩, ⟨428161117517720282, 429570611880311968⟩, true⟩

def words09 : List Nat := [360582814202823372, 360582813910002984, 360582813617000661, 360582813481348968, 360582813457917733, 360582813296305849, 360582813134602476, 360582812824509054, 360582812522799305, 360582812432890502]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk686
