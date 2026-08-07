import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485887903269573, 362485944032705668⟩, ⟨(-37211942180502133), (-34868904953260511)⟩, true⟩

def state01 : KState := ⟨⟨362476304487726814, 362476360635857037⟩, ⟨555114849526438468, 557459042149801610⟩, true⟩

def words00 : List Nat := [371285380016559243, 371285380018665686, 371285379965551695, 371285379863731559, 371285379761131546, 371285379719196790, 371285379561282903, 371285379578927208, 371285379580505100, 371285379549336245]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502411985455942, 362502468152502224⟩, ⟨(-1058701893701500490), (-1056356531780042974)⟩, true⟩

def words01 : List Nat := [371285379497808293, 371285379593282006, 371285379949597303, 371285380013491413, 371285380052077989, 371285380091326972, 371285380237692784, 371285380254524441, 371285380532360778, 371285380811116934]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488560363473057, 362488616549468885⟩, ⟨(-202360721626826956), (-200014188153386876)⟩, true⟩

def words02 : List Nat := [371285381090082206, 371285381092179454, 371285381195007832, 371285381370392028, 371285381625024432, 371285381627126285, 371285381612290465, 371285381568078524, 371285381641858049, 371285381696593251]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478131145563889, 362478187350463635⟩, ⟨442523257901621604, 444870960302752012⟩, true⟩

def words03 : List Nat := [371285381775002337, 371285381854246299, 371285381931818857, 371285381933917260, 371285381709203004, 371285381547079324, 371285381481041923, 371285381483176807, 371285381367392440, 371285381253443952]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495527653984081, 362495583877657420⟩, ⟨(-633331852422533144), (-630982988966171324)⟩, true⟩

def words04 : List Nat := [371285381150558611, 371285381152885675, 371285381255454050, 371285381439132620, 371285381603837539, 371285381605941504, 371285381615952815, 371285381715704674, 371285382048660713, 371285382215776995]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487045714941043, 362487101957725260⟩, ⟨(-108638673304286429), (-106288627742526683)⟩, true⟩

def words05 : List Nat := [371285382376876088, 371285382538698846, 371285382832455165, 371285383034410853, 371285383291598920, 371285383549611283, 371285383791370538, 371285383793468949, 371285383742610176, 371285383772960344]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480011389666175, 362480067651144617⟩, ⟨326565081146815074, 328916283229462814⟩, true⟩

def words06 : List Nat := [371285384063712075, 371285384065810576, 371285384008377345, 371285383919292680, 371285383829367226, 371285383818980904, 371285383781589828, 371285383850419081, 371285383897283799, 371285383899459301]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497717733045698, 362497774013544626⟩, ⟨(-769026433161142029), (-766674054188433305)⟩, true⟩

def words07 : List Nat := [371285383990501219, 371285384168577744, 371285384453421826, 371285384455520695, 371285384392370487, 371285384251009513, 371285384177715745, 371285384180028522, 371285384320510807, 371285384523164891]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489558881266230, 362489615180687720⟩, ⟨(-264181251646091015), (-261827701648068189)⟩, true⟩

def words08 : List Nat := [371285384723911092, 371285384726010161, 371285384619124562, 371285384662249178, 371285384783003731, 371285384785119116, 371285384729236660, 371285384619793893, 371285384645062817, 371285384715811598]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474481859532052, 362474538177821121⟩, ⟨669106043127075922, 671460760938300708⟩, true⟩

def words09 : List Nat := [371285384998694692, 371285385282403302, 371285385544426435, 371285385590402660, 371285385714439119, 371285385839527807, 371285386022087517, 371285386024187150, 371285385858979358, 371285385686075375]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk618
