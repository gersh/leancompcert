import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk229A
