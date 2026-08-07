import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk168

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483477873134512, 362483481594136374⟩, ⟨29099384304167212, 29141669107034248⟩, true⟩

def state01 : KState := ⟨⟨362446569871935968, 362446573597506904⟩, ⟨649491650423332073, 649534012010952757⟩, true⟩

def words00 : List Nat := [371285218982338545, 371285218982852767, 371285217961012342, 371285216932602533, 371285215923735885, 371285215924301486, 371285214180545356, 371285213912174694, 371285213643656685, 371285213336472458]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362512230875715961, 362512234605926168⟩, ⟨(-454494853930482341), (-454452414332778703)⟩, true⟩

def words01 : List Nat := [371285212274958811, 371285213512042224, 371285215871260999, 371285215871783889, 371285215297936983, 371285214078113112, 371285214521666614, 371285214522232617, 371285216031374139, 371285217638187462]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362506697751797686, 362506701486658438⟩, ⟨(-361633090247809877), (-361590572404531435)⟩, true⟩

def words02 : List Nat := [371285218503826832, 371285218504343593, 371285217084001207, 371285218139611040, 371285220310907239, 371285220311421859, 371285218559602077, 371285216731260523, 371285216603565878, 371285217880669220]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475038425617458, 362475042165109633⟩, ⟨171666392480465473, 171708988294391973⟩, true⟩

def words03 : List Nat := [371285222686066855, 371285227491109066, 371285232382442041, 371285233672278026, 371285234727994436, 371285235783825750, 371285239871295456, 371285239871810401, 371285239265797922, 371285238660851581]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468105893602465, 362468109637713444⟩, ⟨288760670256297014, 288803343874114358⟩, true⟩

def words04 : List Nat := [371285239228810393, 371285239229386952, 371285242595965070, 371285246040788508, 371285248982092329, 371285248982607551, 371285247662401938, 371285248090646891, 371285249301504549, 371285249302038318]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458322915585692, 362458326664380365⟩, ⟨453757322027885842, 453800074590109480⟩, true⟩

def words05 : List Nat := [371285248285293478, 371285246913500505, 371285246720389577, 371285246720957010, 371285246891286187, 371285247498248186, 371285248110654005, 371285248111169467, 371285244041683154, 371285242445791404]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362410407879500843, 362410411632895120⟩, ⟨1261786054087991863, 1261828884223298281⟩, true⟩

def words06 : List Nat := [371285241549370760, 371285241549886390, 371285237570723117, 371285232511695817, 371285227453062970, 371285223440315137, 371285217680855234, 371285214739117909, 371285211797560523, 371285208840021576]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362535568616389019, 362535572374449756⟩, ⟨(-850217881029422509), (-850174972147444089)⟩, true⟩

def words07 : List Nat := [371285204406894103, 371285203483054638, 371285204497651466, 371285204498173461, 371285204447597299, 371285203839805039, 371285204093634007, 371285204094202742, 371285206557978277, 371285209542144357]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490698720478916, 362490702483196255⟩, ⟨(-92771282301199004), (-92728294791742854)⟩, true⟩

def words08 : List Nat := [371285212060568985, 371285212061086116, 371285213160855257, 371285215462837578, 371285217888770104, 371285217889286623, 371285215649359740, 371285213383135119, 371285212352661667, 371285212678282885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452444891232909, 362452448658607592⟩, ⟨553520205837207593, 553563272032137789⟩, true⟩

def words09 : List Nat := [371285213805968167, 371285214933718056, 371285216067045911, 371285216067562756, 371285212538855849, 371285209931201490, 371285207618894676, 371285207619421951, 371285205819519739, 371285203881804760]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk168
