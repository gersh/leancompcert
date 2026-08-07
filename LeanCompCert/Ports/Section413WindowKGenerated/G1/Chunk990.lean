import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487123214556928, 362487272615873875⟩, ⟨(-200084992195597205), (-190099129364293171)⟩, true⟩

def state01 : KState := ⟨⟨362479954829800213, 362480104262133545⟩, ⟨509614572608507859, 519603506216867455⟩, true⟩

def words00 : List Nat := [371285352505977725, 371285352509456904, 371285352450059427, 371285352384138642, 371285352316916058, 371285352281848490, 371285352217070110, 371285352234120978, 371285352248696713, 371285352252298346]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494498888185848, 362494648351878493⟩, ⟨(-930480814178979468), (-920488775522188116)⟩, true⟩

def words01 : List Nat := [371285352201668783, 371285352205106071, 371285352308125365, 371285352311607092, 371285352300772381, 371285352254420549, 371285352258504081, 371285352263320013, 371285352359559811, 371285352457315500]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487381748961332, 362487531244084617⟩, ⟨(-225691452633986061), (-215696301553018621)⟩, true⟩

def words02 : List Nat := [371285352552724827, 371285352592234550, 371285352732565840, 371285352874747681, 371285353021060489, 371285353047218237, 371285353072605851, 371285353099121414, 371285353149621008, 371285353175585329]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484674936217942, 362484824462716482⟩, ⟨42412979787904409, 52411238119208479⟩, true⟩

def words03 : List Nat := [371285353289632790, 371285353405126666, 371285353500194573, 371285353503691222, 371285353524297285, 371285353548321366, 371285353655839485, 371285353659324485, 371285353656729076, 371285353655346927]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488673744231495, 362488823301911652⟩, ⟨(-353622025993116979), (-343620679273882261)⟩, true⟩

def words04 : List Nat := [371285353749011972, 371285353808036034, 371285353907740126, 371285354008812611, 371285354098744248, 371285354102224478, 371285354055935581, 371285354057814504, 371285354134391848, 371285354173086362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484806798945984, 362484956388277435⟩, ⟨29447826729765529, 39452308671194273⟩, true⟩

def words05 : List Nat := [371285354207367207, 371285354242792285, 371285354378797026, 371285354465384204, 371285354555644183, 371285354647267641, 371285354717355694, 371285354720836235, 371285354654797843, 371285354655072017]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479753569229370, 362479903189540431⟩, ⟨530039452411093568, 540047003352749304⟩, true⟩

def words06 : List Nat := [371285354701273510, 371285354704754336, 371285354619406754, 371285354535074312, 371285354449307180, 371285354395679528, 371285354325640585, 371285354339368878, 371285354351812433, 371285354355416607]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487040162311229, 362487189814180717⟩, ⟨(-191905868057751312), (-181895190468290228)⟩, true⟩

def words07 : List Nat := [371285354302795182, 371285354294163697, 371285354338184416, 371285354341665763, 371285354263108401, 371285354168763189, 371285354073034905, 371285354031074587, 371285353968588814, 371285353991061570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483698378820381, 362483848062113536⟩, ⟨139173301864763045, 149187093069954977⟩, true⟩

def words08 : List Nat := [371285354007224783, 371285354010706519, 371285353902056049, 371285353897080909, 371285353890462258, 371285353883678235, 371285353795211352, 371285353707869236, 371285353629732204, 371285353633746092]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471802640409706, 362471952355045774⟩, ⟨1318034744880372636, 1328051642017072260⟩, true⟩

def words09 : List Nat := [371285353703166304, 371285353789231218, 371285353848065237, 371285353851547340, 371285353774474743, 371285353729876254, 371285353712965025, 371285353716447202, 371285353612950042, 371285353481604978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990
