import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk119

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360489569490794324, 360489570274282159⟩, ⟨1097078979176610036, 1097085296121996554⟩, true⟩

def state01 : KState := ⟨⟨360507011199075431, 360507011983950601⟩, ⟨888929005792199872, 888935339253929640⟩, true⟩

def words00 : List Nat := [360581754569523627, 360581743294742588, 360581731250128915, 360581726210084803, 360581721170849092, 360581714337644330, 360581700494460261, 360581681231808476, 360581661972363353, 360581649711847657]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360438859970717768, 360438860756966617⟩, ⟨1701344729075418671, 1701351078904545983⟩, true⟩

def words01 : List Nat := [360581643445680251, 360581641329719753, 360581639214099766, 360581631388702099, 360581627054873676, 360581620935866756, 360581614817843353, 360581610933956395, 360581603527090377, 360581591552176730]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566924846910176, 360566925634539057⟩, ⟨173860046239217063, 173866412525160849⟩, true⟩

def words02 : List Nat := [360581579579241997, 360581564290154423, 360581552623194225, 360581547937184230, 360581543251949190, 360581532493316103, 360581517879022223, 360581510242687208, 360581502607587478, 360581499516561284]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559178493538561, 360559179282559753⟩, ⟨266219676907160970, 266226059810041182⟩, true⟩

def words03 : List Nat := [360581498295177714, 360581492100155140, 360581486682376387, 360581492690318323, 360581492690443756, 360581492304175115, 360581491917955525, 360581486972417718, 360581478139903174, 360581476272493593]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628454639294400, 360628455429695568⟩, ⟨(-560993474208553232), (-560987074821679044)⟩, true⟩

def words04 : List Nat := [360581479500818231, 360581484953772408, 360581486894227693, 360581488834372820, 360581489001700609, 360581494412067801, 360581501752614776, 360581509091960532, 360581510904454278, 360581514832689320]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360705419915102245, 360705420706886766⟩, ⟨(-1481585947969267587), (-1481579532044408613)⟩, true⟩

def words05 : List Nat := [360581516461925484, 360581518090932375, 360581526668970390, 360581531525574117, 360581531525709198, 360581530371732918, 360581529217920111, 360581532460771836, 360581542819439601, 360581553176409013]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360626733171460431, 360626733964644343⟩, ⟨(-541095546063148382), (-541089113394767220)⟩, true⟩

def words06 : List Nat := [360581559935793977, 360581559935940590, 360581559757847990, 360581559393317661, 360581559028809870, 360581556898510626, 360581551118690115, 360581541832865001, 360581532548562399, 360581533971878930]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360400069865052343, 360400070659617199⟩, ⟨2173814319909102093, 2173820769114395895⟩, true⟩

def words07 : List Nat := [360581544676232653, 360581555378826230, 360581561579054409, 360581561579201165, 360581560855859585, 360581558239363234, 360581555623263447, 360581549844352890, 360581539961503483, 360581524813967316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360631865495286370, 360631866291238300⟩, ⟨(-604281726008920087), (-604275260179634629)⟩, true⟩

def words08 : List Nat := [360581509668926907, 360581501446594123, 360581496797104091, 360581495153803001, 360581493510762641, 360581485156385645, 360581474967804005, 360581471693557395, 360581468419813013, 360581472224006240]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602317443334463, 360602318240687312⟩, ⟨(-249913415443900068), (-249906932810502878)⟩, true⟩

def words09 : List Nat := [360581472224139506, 360581470966019396, 360581472856146351, 360581479560973962, 360581484510118206, 360581489458461254, 360581490026152714, 360581490927056399, 360581492662785594, 360581494398273305]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk119
