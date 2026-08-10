import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk990A
