import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605428835387083, 360605492382961424⟩, ⟨(-2264215569442159718), (-2260010437518156904)⟩, true⟩

def state01 : KState := ⟨⟨360596461432156154, 360596524993298236⟩, ⟨(-1385454582182152545), (-1381248120554046143)⟩, true⟩

def words00 : List Nat := [360582431471786065, 360582431611308311, 360582431800117772, 360582431989339979, 360582432117130467, 360582432141365257, 360582432142661670, 360582432081363401, 360582432061123141, 360582432206564563]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592659828890989, 360592723403421677⟩, ⟨(-1012783330826288370), (-1008575556912081656)⟩, true⟩

def words01 : List Nat := [360582432455548376, 360582432704800196, 360582432887051548, 360582433071590333, 360582433229543239, 360582433387870638, 360582433649812594, 360582433808264831, 360582433914519410, 360582434020973915]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604366285336302, 360604429873325632⟩, ⟨(-2160360117698443756), (-2156151024503640336)⟩, true⟩

def words02 : List Nat := [360582434043971126, 360582434142292854, 360582434320931408, 360582434499839214, 360582434590067488, 360582434631965630, 360582434747896345, 360582434864285128, 360582435063889739, 360582435289729590]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583938419593485, 360584002021136024⟩, ⟨(-157690012356073591), (-153479590472381091)⟩, true⟩

def words03 : List Nat := [360582435449651743, 360582435609735288, 360582435800393215, 360582436043324195, 360582436215199504, 360582436387282934, 360582436506968779, 360582436523086044, 360582436540208374, 360582436557804639]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599866206629540, 360599929821603936⟩, ⟨(-1719315695025100156), (-1715103956217508390)⟩, true⟩

def words04 : List Nat := [360582436678905336, 360582436828563918, 360582436899879873, 360582436971341341, 360582437016268558, 360582437128820778, 360582437344901585, 360582437561251055, 360582437683908324, 360582437863783848]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980A
