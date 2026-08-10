import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924A

def state06 : KState := ⟨⟨360591300838350381, 360591357149597436⟩, ⟨(-869498865112969899), (-865983056451223565)⟩, true⟩

def words05 : List Nat := [360581990070526429, 360581990172515974, 360581990353527694, 360581990607310394, 360581990767733499, 360581990928393149, 360581991030739425, 360581991032076822, 360581991118905792, 360581991221731080]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360600314552018826, 360600370875880059⟩, ⟨(-1702994121615670071), (-1699477146584475395)⟩, true⟩

def words06 : List Nat := [360581991440954741, 360581991573469336, 360581991592985134, 360581991612621412, 360581991613740608, 360581991680191219, 360581991873985178, 360581992068031362, 360581992187907153, 360581992388066751]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599595298364853, 360599651634840610⟩, ⟨(-1636506683029605643), (-1632988541470551831)⟩, true⟩

def words07 : List Nat := [360581992677807244, 360581992967934345, 360581993264923222, 360581993445502788, 360581993523162528, 360581993600910614, 360581993617758458, 360581993693363344, 360581993885382500, 360581994077704869]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596759574800364, 360596815924013814⟩, ⟨(-1374341706586813634), (-1370822386982148576)⟩, true⟩

def words08 : List Nat := [360581994198638178, 360581994285388662, 360581994427181981, 360581994569403393, 360581994662574168, 360581994666544249, 360581994667736054, 360581994612999608, 360581994618703567, 360581994780475717]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569511015436892, 360569567377267072⟩, ⟨1146006761397226850, 1149527247986286202⟩, true⟩

def words09 : List Nat := [360581994918363646, 360581995056488941, 360581995122309739, 360581995123647721, 360581995101521304, 360581995013814875, 360581994925719202, 360581994877453860, 360581994831830209, 360581994698866924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk924B
