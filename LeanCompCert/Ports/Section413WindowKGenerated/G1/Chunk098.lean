import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk098

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362635173007536916, 362635174214217845⟩, ⟨(-1495057085602144491), (-1495049079022731063)⟩, true⟩

def state01 : KState := ⟨⟨362538828625618764, 362538829834885741⟩, ⟨(-550469897746677231), (-550461865810807957)⟩, true⟩

def words00 : List Nat := [371282647323271524, 371282652817492253, 371282668732026119, 371282684643458642, 371282702105445379, 371282705722515641, 371282707577431213, 371282709432064718, 371282717513882640, 371282723233539211]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362540960851379760, 362540962063223599⟩, ⟨(-570875755810367098), (-570867698581877400)⟩, true⟩

def words01 : List Nat := [371282739358219530, 371282755479728686, 371282771475691974, 371282779033156369, 371282788276023600, 371282797517150012, 371282817153238002, 371282822975348866, 371282828896042928, 371282834815633550]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362539168224949889, 362539169439369308⟩, ⟨(-553419004985596906), (-553410922452137780)⟩, true⟩

def words02 : List Nat := [371282843004132055, 371282846085708971, 371282851983612606, 371282857880433760, 371282861966900629, 371282861967188533, 371282857226815859, 371282859065277128, 371282871278090381, 371282877004982966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362575833804067652, 362575835021103923⟩, ⟨(-913876345694332677), (-913868237423770405)⟩, true⟩

def words03 : List Nat := [371282882342110838, 371282887678251773, 371282903384414705, 371282915426408564, 371282928150242970, 371282940871593834, 371282953713443030, 371282953713730584, 371282962232388977, 371282971670080270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362512462348510808, 362512463568113981⟩, ⟨(-289600599223799023), (-289592465681565753)⟩, true⟩

def words04 : List Nat := [371282987775341102, 371282997787719795, 371283006833940882, 371283015878418059, 371283025351909367, 371283029661160892, 371283041810469479, 371283053957429545, 371283063317492918, 371283066302284973]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362745660107283165, 362745661329487792⟩, ⟨(-2587785006073971504), (-2587776846894397188)⟩, true⟩

def words05 : List Nat := [371283079621049204, 371283092937254696, 371283114006411396, 371283125436594892, 371283135649205817, 371283145859842990, 371283166391720967, 371283182695549574, 371283209316296690, 371283235931770077]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362587079652974081, 362587080877783310⟩, ⟨(-1023800300105296257), (-1023792115231045869)⟩, true⟩

def words06 : List Nat := [371283262277036649, 371283274919521238, 371283291587040649, 371283308251331259, 371283327906480058, 371283333873691635, 371283337487630651, 371283341100928843, 371283353206199706, 371283363714858476]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503824598113096, 362503825825524599⟩, ⟨(-201113515790762864), (-201105305218717342)⟩, true⟩

def words07 : List Nat := [371283384511185510, 371283405303420005, 371283426235665498, 371283433502684069, 371283443670197487, 371283453835790374, 371283465904439254, 371283468976591983, 371283471037218285, 371283473097539708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362564650002561421, 362564651232561421⟩, ⟨(-801964181390288290), (-801955945230764120)⟩, true⟩

def words08 : List Nat := [371283482532628298, 371283487162952940, 371283502060309443, 371283516954771275, 371283530476026229, 371283530476315516, 371283540513011467, 371283550660453678, 371283563674604290, 371283571873019336]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362583780195251426, 362583781427891954⟩, ⟨(-991303591821009583), (-991295329533484987)⟩, true⟩

def words09 : List Nat := [371283577670539392, 371283583466976219, 371283595884055636, 371283604123574765, 371283615342096657, 371283626558464179, 371283637626761657, 371283640470719067, 371283650586164714, 371283660699729801]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk098
