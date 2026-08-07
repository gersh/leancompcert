import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360497866780907689, 360497869861451519⟩, ⟨1891399887717742524, 1891447615853673186⟩, true⟩

def state01 : KState := ⟨⟨360642563456567039, 360642566539911992⟩, ⟨(-1422840929259758873), (-1422793136964255697)⟩, true⟩

def words00 : List Nat := [360580462220796309, 360580460517049977, 360580461172323622, 360580462030245330, 360580462030521459, 360580461271061969, 360580460608894066, 360580461228654820, 360580462954403153, 360580465665355480]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604142871214321, 360604145957391099⟩, ⟨(-542450167003853078), (-542402309817136414)⟩, true⟩

def words01 : List Nat := [360580466916338511, 360580468167240255, 360580469688444680, 360580472494552144, 360580474812674506, 360580477130643673, 360580478492646712, 360580479902017354, 360580480934809465, 360580481967608056]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606326014877877, 360606329103848854⟩, ⟨(-592501227949683578), (-592453306705560716)⟩, true⟩

def words02 : List Nat := [360580484899014581, 360580486607117124, 360580487362873106, 360580488118594814, 360580488118848118, 360580487810665360, 360580489401445460, 360580490992143463, 360580491628325318, 360580492755381471]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580331623204033, 360580334714986541⟩, ⟨3602595433015962, 3650581158956322⟩, true⟩

def words03 : List Nat := [360580494732197710, 360580496708938060, 360580498263697109, 360580498263994343, 360580497931045178, 360580495727360751, 360580493523811688, 360580493857428335, 360580493857673347, 360580493851044037]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608047692573636, 360608050787190741⟩, ⟨(-632780115885520415), (-632732065120236123)⟩, true⟩

def words04 : List Nat := [360580493844374699, 360580492876140332, 360580490021560195, 360580489062548124, 360580488103542506, 360580486059831776, 360580485138296473, 360580483264087237, 360580481389984724, 360580481963822686]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360544615629423609, 360544618726846736⟩, ⟨823440475031644518, 823488590209574872⟩, true⟩

def words05 : List Nat := [360580484382270569, 360580486800565026, 360580487767243933, 360580487900761045, 360580487901010279, 360580487549794434, 360580487198524090, 360580487119838051, 360580486516516004, 360580484954643321]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599591574115377, 360599594674346308⟩, ⟨(-438831517544211753), (-438783337884994941)⟩, true⟩

def words06 : List Nat := [360580483722847039, 360580485240912589, 360580488650521234, 360580492059889710, 360580493850976651, 360580493851274400, 360580493759532816, 360580492818668767, 360580492221365805, 360580493053263857]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566113811286415, 360566116914353855⟩, ⟨330488896403419835, 330537141231378311⟩, true⟩

def words07 : List Nat := [360580493053531266, 360580492559522667, 360580493461530811, 360580496362363760, 360580498753515103, 360580501144506493, 360580502126420389, 360580502126718349, 360580501227571745, 360580500601961835]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360536846015573274, 360536849121451889⟩, ⟨1002850183940132541, 1002898493382748647⟩, true⟩

def words08 : List Nat := [360580499976312476, 360580498996585209, 360580496136286876, 360580492106789237, 360580488077591641, 360580483564709958, 360580480022662301, 360580477873294599, 360580475724076461, 360580472370402857]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574644832236507, 360574647940926372⟩, ⟨133656486396936330, 133704860484258870⟩, true⟩

def words09 : List Nat := [360580470473238767, 360580469955845912, 360580470807537378, 360580470807835544, 360580470298133973, 360580468021291590, 360580465744591824, 360580463123313758, 360580461448181916, 360580461195730036]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229
