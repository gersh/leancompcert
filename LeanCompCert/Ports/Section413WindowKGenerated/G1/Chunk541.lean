import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472808668666897, 362472851229079772⟩, ⟨653860540545953758, 655416007726125550⟩, true⟩

def state01 : KState := ⟨⟨362484760471258169, 362484803047941926⟩, ⟨7254988209329953, 8811335728112205⟩, true⟩

def words00 : List Nat := [371284966022135490, 371284966024137318, 371284966053512118, 371284966116870388, 371284966124406818, 371284966126232155, 371284965806419954, 371284965776571051, 371284965887199059, 371284965889112285]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474479378875419, 362474521972128448⟩, ⟨563681395174007633, 565238639336770827⟩, true⟩

def words01 : List Nat := [371284965887465299, 371284965845334300, 371284966049212927, 371284966161615741, 371284966351721501, 371284966542498763, 371284966665700413, 371284966667517670, 371284966335767792, 371284966145065196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471357716608802, 362471400326036663⟩, ⟨732672601570177864, 734230721199839560⟩, true⟩

def words02 : List Nat := [371284966101301332, 371284966103118680, 371284965797712087, 371284965493144634, 371284965187877541, 371284964983202744, 371284964631207496, 371284964599869735, 371284964567891341, 371284964536662931]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488217099707747, 362488259725558883⟩, ⟨(-180086875978624262), (-178527867272680742)⟩, true⟩

def words03 : List Nat := [371284964287348636, 371284964021058964, 371284963826184591, 371284963828002355, 371284963447237019, 371284963010951172, 371284962573926890, 371284962418692571, 371284962201050604, 371284962263981286]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476640725523856, 362476683367783759⟩, ⟨446679515888468821, 448239413045047583⟩, true⟩

def words04 : List Nat := [371284962326529467, 371284962328362582, 371284962245791520, 371284962332876186, 371284962387431607, 371284962389249810, 371284961989548092, 371284961590801181, 371284961191346753, 371284961103943410]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362466319962113859, 362466362620776047⟩, ⟨1005677671332618842, 1007238456758748296⟩, true⟩

def words05 : List Nat := [371284961139939706, 371284961329582380, 371284961445547819, 371284961447366135, 371284961109058245, 371284960875996214, 371284960693916781, 371284960695743871, 371284960422523307, 371284960081203646]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494716290629080, 362494758965568238⟩, ⟨(-532359899917196516), (-530798232848466578)⟩, true⟩

def words06 : List Nat := [371284959739064627, 371284959657160349, 371284959559605278, 371284959682339628, 371284959717951686, 371284959719802763, 371284959669006834, 371284959815316764, 371284960214694457, 371284960397462638]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481664776007715, 362481707467542886⟩, ⟨174728802392664650, 176291368548904560⟩, true⟩

def words07 : List Nat := [371284960581466963, 371284960766043885, 371284961057545467, 371284961179398707, 371284961321004792, 371284961463316796, 371284961605398104, 371284961607217393, 371284961334250281, 371284961276486203]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469492461726405, 362469535169451940⟩, ⟨834339030405133706, 835902473840308880⟩, true⟩

def words08 : List Nat := [371284961497716744, 371284961499535989, 371284961327253598, 371284961156067058, 371284960984165577, 371284960917366882, 371284960728677989, 371284960682603095, 371284960635938512, 371284960570334766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499362475804974, 362499405199996234⟩, ⟨(-784432469903796677), (-782868134107518257)⟩, true⟩

def words09 : List Nat := [371284960290460160, 371284960296200204, 371284960640887934, 371284960725831639, 371284960754995022, 371284960784712054, 371284960911043300, 371284960913067070, 371284961136418711, 371284961404972019]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541
