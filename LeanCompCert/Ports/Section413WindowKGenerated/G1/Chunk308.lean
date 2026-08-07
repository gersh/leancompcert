import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk308

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472302230384773, 362472315404242956⟩, ⟨405405070318370237, 405679333315727875⟩, true⟩

def state01 : KState := ⟨⟨362447811896614104, 362447825079382837⟩, ⟨1159718576852328583, 1159993114340755145⟩, true⟩

def words00 : List Nat := [371285486384279784, 371285485961885529, 371285484136986927, 371285483363071682, 371285482588726989, 371285481985394534, 371285480157363030, 371285478078017674, 371285475998397344, 371285474969494514]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362452381305670407, 362452394497343642⟩, ⟨1018994304979115624, 1019269116860356812⟩, true⟩

def words01 : List Nat := [371285473748208652, 371285473077845547, 371285472407201769, 371285471741087501, 371285470382605118, 371285469346831679, 371285468323202730, 371285468324195017, 371285467247362645, 371285466175372856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451732463229432, 362451745663776086⟩, ⟨1038982312868744293, 1039257398274900573⟩, true⟩

def words02 : List Nat := [371285465103035195, 371285464105678327, 371285462750111710, 371285462089493447, 371285461428609914, 371285460572534136, 371285458316181340, 371285456845879987, 371285455375153069, 371285454953373067]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362449449543178031, 362449462752757157⟩, ⟨1109359526423456843, 1109634890346559135⟩, true⟩

def words03 : List Nat := [371285453860757440, 371285452707783637, 371285451554473770, 371285450952554730, 371285449825657668, 371285448739420984, 371285447652926750, 371285446511544564, 371285444297303573, 371285443131821573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362451662518552621, 362451675736972178⟩, ⟨1041213434658266839, 1041489071266045067⟩, true⟩

def words04 : List Nat := [371285441965853366, 371285441848281773, 371285440858167111, 371285439753763425, 371285438649055140, 371285437839345563, 371285436563274680, 371285436254226965, 371285435944868047, 371285435512377885]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362503581352007335, 362503594579374604⟩, ⟨(-560728738821080729), (-560452826131054985)⟩, true⟩

def words05 : List Nat := [371285434418766488, 371285434373065739, 371285435327235678, 371285435328227166, 371285434931637008, 371285434106429789, 371285433304787861, 371285433305880588, 371285433436788820, 371285434026374668]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500114319513745, 362500127555851811⟩, ⟨(-453861683620453338), (-453585494046729682)⟩, true⟩

def words06 : List Nat := [371285434590675748, 371285434591672172, 371285434158300819, 371285434161739890, 371285434485354133, 371285434486354286, 371285434136492755, 371285433791807327, 371285434147044394, 371285434624166841]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362456096498306323, 362456109743579805⟩, ⟨905398007889877659, 905674473344986005⟩, true⟩

def words07 : List Nat := [371285436146704954, 371285437669558495, 371285439080542487, 371285439283716317, 371285439646941921, 371285440010617612, 371285440466987692, 371285440467980009, 371285439528822595, 371285438580151858]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469269018951305, 362469282273112462⟩, ⟨498744246632772339, 499020986583321679⟩, true⟩

def words08 : List Nat := [371285437726839828, 371285437727932790, 371285437752355446, 371285438207551372, 371285438482454055, 371285438483446640, 371285437363428386, 371285437132899637, 371285437046658983, 371285437047686218]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474800624900746, 362474813888101022⟩, ⟨327894789234511477, 328171808450017725⟩, true⟩

def words09 : List Nat := [371285436525481100, 371285435785696784, 371285435349450753, 371285435350546600, 371285435345187252, 371285435419892001, 371285435482704364, 371285435483714503, 371285434677472579, 371285434334976428]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk308
