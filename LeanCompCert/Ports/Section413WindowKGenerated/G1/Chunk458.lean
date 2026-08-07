import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk458

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497854624003510, 362497884718483808⟩, ⟨(-567200379229205940), (-566269128662539772)⟩, true⟩

def state01 : KState := ⟨⟨362475850222096322, 362475880330298547⟩, ⟨440632504865876240, 441564383967207926⟩, true⟩

def words00 : List Nat := [371285521210098928, 371285521211616899, 371285520752930835, 371285520715717565, 371285520783660060, 371285520785179021, 371285520342878105, 371285519900921574, 371285519458321682, 371285519369459587]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 45800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 45800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362456937190419814, 362456967312265816⟩, ⟨1307206365515257208, 1308138869707309332⟩, true⟩

def words01 : List Nat := [371285519352208055, 371285519545967250, 371285519739044048, 371285519740562395, 371285519299013543, 371285518732511919, 371285518165233815, 371285518074242262, 371285517450683467, 371285516829282563]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 45810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 45800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488038661065393, 362488068796528589⟩, ⟨(-117902930662391277), (-116969802461256023)⟩, true⟩

def words02 : List Nat := [371285516207247082, 371285516061633957, 371285515899175648, 371285516056947530, 371285516170324789, 371285516171853716, 371285516018673081, 371285516181210245, 371285516540920721, 371285516598181155]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 45820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 45800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498547655987066, 362498577805302141⟩, ⟨(-599556520756303174), (-598622757653662388)⟩, true⟩

def words03 : List Nat := [371285516654866808, 371285516712079737, 371285517244174272, 371285517539223275, 371285517923171110, 371285518307697307, 371285518606485796, 371285518608013346, 371285518842718889, 371285519129495469]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 45830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 45800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481694636918673, 362481724799784777⟩, ⟨173094916681260606, 174029301032500100⟩, true⟩

def words04 : List Nat := [371285519890757999, 371285520018614008, 371285520019770770, 371285520004383128, 371285520081268906, 371285520082960080, 371285520129582680, 371285520311990245, 371285520420887999, 371285520422489957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 45840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 45800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496429338031944, 362496459514598658⟩, ⟨(-502519385268670798), (-501584372672208162)⟩, true⟩

def words05 : List Nat := [371285520569638867, 371285520800323963, 371285521505327235, 371285521630165587, 371285521677302496, 371285521724919891, 371285521969842600, 371285521977846618, 371285522217383622, 371285522457563875]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 45850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 45800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362504377858584455, 362504408048875819⟩, ⟨(-867160600780928430), (-866224958705089026)⟩, true⟩

def words06 : List Nat := [371285522697190271, 371285522698712322, 371285522634968426, 371285522841924294, 371285523192313580, 371285523200926304, 371285523209218997, 371285523218009920, 371285523700963146, 371285524114392048]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 45860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 45800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489133646837333, 362489163850836231⟩, ⟨(-167804260666994254), (-166867989757116262)⟩, true⟩

def words07 : List Nat := [371285524725049001, 371285525336299371, 371285525949665686, 371285525951186149, 371285526044302679, 371285526158898698, 371285526584316345, 371285526715741060, 371285526796153714, 371285526877148711]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 45870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 45800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495671789702031, 362495702007314532⟩, ⟨(-467833083914797322), (-466896188343965926)⟩, true⟩

def words08 : List Nat := [371285527087501036, 371285527089191949, 371285527336872946, 371285527611987908, 371285527776971953, 371285527778492983, 371285527316234942, 371285527323626100, 371285527758873935, 371285527982160494]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 45880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 45800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493160531591558, 362493190763073655⟩, ⟨(-352502190598578845), (-351564658484172557)⟩, true⟩

def words09 : List Nat := [371285528204164849, 371285528426687387, 371285529122792412, 371285529582369414, 371285530134191273, 371285530686583771, 371285531238391724, 371285531239913581, 371285531400429815, 371285531569189335]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 45890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 45800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 45800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk458
