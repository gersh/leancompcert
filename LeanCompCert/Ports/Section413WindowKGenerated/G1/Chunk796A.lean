import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466217630690752, 362466312605915806⟩, ⟨1498504450614435598, 1503609469790428932⟩, true⟩

def state01 : KState := ⟨⟨362476830934663571, 362476925934485218⟩, ⟨653661402225703307, 658768379416441221⟩, true⟩

def words00 : List Nat := [371285201936681498, 371285201860119547, 371285201703546562, 371285201659854569, 371285201615302800, 371285201537747560, 371285201272365290, 371285201089515971, 371285200905217332, 371285200879585287]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487841492947761, 362487936517844664⟩, ⟨(-222970995013172689), (-217862021453893187)⟩, true⟩

def words01 : List Nat := [371285200777741045, 371285200623049731, 371285200467253180, 371285200470312072, 371285200393624467, 371285200366474049, 371285200338355230, 371285200310902666, 371285200241904289, 371285200279648034]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482490271858314, 362482585321237614⟩, ⟨203154848585299339, 208265771560489223⟩, true⟩

def words02 : List Nat := [371285200473498337, 371285200485397594, 371285200494438818, 371285200504414038, 371285200515729321, 371285200518765804, 371285200563540912, 371285200666763017, 371285200736843806, 371285200739692474]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501860410197457, 362501955484529050⟩, ⟨(-1339350137796912130), (-1334237227749833324)⟩, true⟩

def words03 : List Nat := [371285200833458758, 371285200961620715, 371285201245808765, 371285201359443736, 371285201447180328, 371285201535748119, 371285201753684196, 371285201913677319, 371285202125944065, 371285202339443607]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492890347541305, 362492985446706318⟩, ⟨(-624968434320677264), (-619853546414055924)⟩, true⟩

def words04 : List Nat := [371285202551688742, 371285202554554415, 371285202699465046, 371285202845769341, 371285203002499553, 371285203029200839, 371285203057630592, 371285203087035065, 371285203227002164, 371285203327882775]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796A
