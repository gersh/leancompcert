import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592389583329255, 360592421258202962⟩, ⟨(-693671979233669444), (-692172174036902402)⟩, true⟩

def state01 : KState := ⟨⟨360558858896615401, 360558890580952328⟩, ⟨1656877596862323320, 1658378065476989296⟩, true⟩

def words00 : List Nat := [360582547370521106, 360582547371514132, 360582547207820219, 360582547076722141, 360582546945377682, 360582546672906294, 360582546197171629, 360582545620085468, 360582545042826867, 360582544525688842]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360545722807394086, 360545754501090542⟩, ⟨2578013670657855674, 2579514795516669158⟩, true⟩

def words01 : List Nat := [360582544189113404, 360582544055632631, 360582543922030260, 360582543687105102, 360582543422489772, 360582543059442456, 360582542696114188, 360582542535835487, 360582542172383997, 360582541648773324]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586025858695974, 360586057561772887⟩, ⟨(-248179071203494831), (-246677288541779435)⟩, true⟩

def words02 : List Nat := [360582541124952650, 360582540804277039, 360582540657949537, 360582540686792519, 360582540687718493, 360582540496886263, 360582540311604343, 360582540222241030, 360582540132580398, 360582540183031079]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564651344065377, 360564683056612458⟩, ⟨1250885590114692176, 1252388036966008142⟩, true⟩

def words03 : List Nat := [360582540183916341, 360582540109136735, 360582540034183381, 360582539900652929, 360582539869322192, 360582539717970144, 360582539566515798, 360582539313131995, 360582538856611147, 360582538603190246]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561482627744990, 360561514349648994⟩, ⟨1473181031852002093, 1474684135043709801⟩, true⟩

def words04 : List Nat := [360582538349427101, 360582538298595734, 360582538181247780, 360582537941592211, 360582537701781526, 360582537411230268, 360582537225361029, 360582536932086055, 360582536638704411, 360582536219001007]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701A
