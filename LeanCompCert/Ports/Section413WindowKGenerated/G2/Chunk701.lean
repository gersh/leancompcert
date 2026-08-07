import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701

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

def state06 : KState := ⟨⟨360585361476966643, 360585393208245603⟩, ⟨(-202109085927727909), (-200605325035818469)⟩, true⟩

def words05 : List Nat := [360582535920139727, 360582535616686126, 360582535312949754, 360582535096912999, 360582534886446538, 360582534503226158, 360582534119826522, 360582533939395432, 360582533952299105, 360582533994080529]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561589281434086, 360561621022189240⟩, ⟨1465767030780943301, 1467271456570250727⟩, true⟩

def words06 : List Nat := [360582533994985854, 360582533870148343, 360582533542310421, 360582533417404505, 360582533292228659, 360582533116240368, 360582532737348592, 360582532234502623, 360582531731468591, 360582531260988874]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360539681965698232, 360539713715813461⟩, ⟨3003177788270095073, 3004682870901863109⟩, true⟩

def words07 : List Nat := [360582530963803134, 360582530805147986, 360582530646399320, 360582530360606511, 360582530015475125, 360582529529370294, 360582529042984371, 360582528759336755, 360582528272848130, 360582527663817193]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564482974817300, 360564514734324062⟩, ⟨1262635297473595889, 1264141039250553487⟩, true⟩

def words08 : List Nat := [360582527054570602, 360582526648183581, 360582526402854634, 360582526360239117, 360582526317546945, 360582526101974387, 360582525799145375, 360582525556364850, 360582525313314116, 360582525007001802]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552462394242466, 360552494163228577⟩, ⟨2106392902679386348, 2107899309857089588⟩, true⟩

def words09 : List Nat := [360582524751312622, 360582524341305458, 360582523931121415, 360582523590664229, 360582523352232067, 360582523026921763, 360582522701493687, 360582522274896749, 360582521645513975, 360582521218924547]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk701
