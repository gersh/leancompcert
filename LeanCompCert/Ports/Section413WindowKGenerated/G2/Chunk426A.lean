import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk426A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609211362401615, 360609222598295347⟩, ⟨(-1132540227398363752), (-1132216751013421294)⟩, true⟩

def state01 : KState := ⟨⟨360612063552141918, 360612074793509406⟩, ⟨(-1254073665871312285), (-1253749956276848045)⟩, true⟩

def words00 : List Nat := [360582645941538316, 360582646774269191, 360582647188633018, 360582647603037346, 360582647875161032, 360582648436528886, 360582649415971144, 360582650395478519, 360582650949766645, 360582651640889734]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360657778035456574, 360657789282303769⟩, ⟨(-3202106120302146110), (-3201782177190053796)⟩, true⟩

def words01 : List Nat := [360582652882484619, 360582654124191512, 360582655709093109, 360582657512495085, 360582658842975715, 360582660173444283, 360582661740543687, 360582663581961222, 360582665345119254, 360582667108324040]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612732123224725, 360612743375609450⟩, ⟨(-1282244079070686716), (-1281919899922403242)⟩, true⟩

def words02 : List Nat := [360582668594441009, 360582669701383435, 360582670792991443, 360582671884716467, 360582672585716718, 360582672739398301, 360582672739918122, 360582672550121297, 360582672535152887, 360582673241202038]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550895845823233, 360550907103676310⟩, ⟨1354296370576499802, 1354620782867877888⟩, true⟩

def words03 : List Nat := [360582674358187284, 360582675475231330, 360582676314038524, 360582676605642006, 360582676755369633, 360582676905251246, 360582677040015121, 360582677040596030, 360582676628221934, 360582675883762330]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603860831620866, 360603872094952978⟩, ⟨(-904318112288312670), (-903993466343120912)⟩, true⟩

def words04 : List Nat := [360582675139203174, 360582675117152755, 360582675839885527, 360582676562705571, 360582676821781825, 360582676822362842, 360582676534346563, 360582676329272660, 360582676467941975, 360582676965498965]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk426A
