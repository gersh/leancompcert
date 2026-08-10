import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471A

def state06 : KState := ⟨⟨360591552966168410, 360591566851942703⟩, ⟨(-409713096058172407), (-409270582122283019)⟩, true⟩

def words05 : List Nat := [360582886329610241, 360582886299622104, 360582886552380241, 360582887118665701, 360582887572021633, 360582888025464107, 360582888130206144, 360582888325204991, 360582888509761018, 360582888694521905]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606029278181834, 360606043170056296⟩, ⟨(-1092544758037334452), (-1092101956386500668)⟩, true⟩

def words06 : List Nat := [360582889327273537, 360582889511713804, 360582889512291137, 360582889454336203, 360582889396274940, 360582889397824780, 360582889906834406, 360582890415951012, 360582890700519711, 360582891192010749]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586359888851466, 360586373786853731⟩, ⟨(-164654458371730042), (-164211367642065174)⟩, true⟩

def words07 : List Nat := [360582891970845840, 360582892749837752, 360582893381262619, 360582893700320538, 360582893700920712, 360582893552351935, 360582893403668920, 360582893182670905, 360582893256971429, 360582893331423748]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573605195912718, 360573619100085003⟩, ⟨436986206487305378, 437429588348198602⟩, true⟩

def words08 : List Nat := [360582893332001217, 360582893182432885, 360582892769467397, 360582892602346895, 360582892435061844, 360582892155456519, 360582891427835639, 360582890349306468, 360582889270698621, 360582888639994904]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556036581594200, 360556050491868010⟩, ⟨1266237973516184378, 1266681643338472712⟩, true⟩

def words09 : List Nat := [360582888511428930, 360582888579411837, 360582888579989407, 360582888424191441, 360582888282981305, 360582888029679702, 360582887878994047, 360582887879642601, 360582887535271752, 360582886967362470]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471B
