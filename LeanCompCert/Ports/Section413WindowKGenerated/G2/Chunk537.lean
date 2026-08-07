import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk537

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586346117273837, 360586364313320708⟩, ⟨(-237208382672418382), (-236548173424375848)⟩, true⟩

def state01 : KState := ⟨⟨360595800444833759, 360595818647897478⟩, ⟨(-744976418146786893), (-744315832059266625)⟩, true⟩

def words00 : List Nat := [360581959750729723, 360581960047607626, 360581960086028705, 360581960124531153, 360581960125155662, 360581960014775042, 360581960267024540, 360581960519407870, 360581960597748295, 360581960856531478]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612395148445308, 360612413358555206⟩, ⟨(-1636541681742495196), (-1635880717169611528)⟩, true⟩

def words01 : List Nat := [360581961106506755, 360581961356688494, 360581961513625870, 360581961514371359, 360581961416160900, 360581961023066586, 360581960629840599, 360581960803758721, 360581961371236946, 360581961938865148]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573619663281230, 360573637880493820⟩, ⟨446531148550864776, 447192494714481766⟩, true⟩

def words02 : List Nat := [360581962296954103, 360581962309251517, 360581962531353268, 360581962753670948, 360581962754306354, 360581962731324636, 360581962362434665, 360581961819830967, 360581961277106355, 360581960837774939]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360529034826409641, 360529053050649454⟩, ⟨2842439862517233617, 2843101586289070079⟩, true⟩

def words03 : List Nat := [360581960874392773, 360581961066061383, 360581961083893459, 360581961084639216, 360581960866442568, 360581960422069614, 360581959977496747, 360581959503296628, 360581958790332178, 360581957806628038]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596316464224489, 360596334695501889⟩, ⟨(-773617474148033459), (-772955372142061941)⟩, true⟩

def words04 : List Nat := [360581956822791666, 360581956079917279, 360581955570820354, 360581955328296842, 360581955085724141, 360581954548710182, 360581954202525039, 360581954101961386, 360581954129665555, 360581954397979200]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570098504010360, 360570116742402983⟩, ⟨635691208207426178, 636353692691679672⟩, true⟩

def words05 : List Nat := [360581954398646254, 360581954393207235, 360581954387636178, 360581954603052886, 360581954642378599, 360581954681821764, 360581954682497599, 360581954463007421, 360581953897970852, 360581953678650969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559078268619701, 360559096514034546⟩, ⟨1228145118504701172, 1228807980539226310⟩, true⟩

def words06 : List Nat := [360581953459077442, 360581953436560195, 360581953068576267, 360581952527228353, 360581951985778855, 360581951357475279, 360581950956378232, 360581950546849697, 360581950137246119, 360581949554401651]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605207665635383, 360605225918087419⟩, ⟨(-1252471264134580323), (-1251808023674774395)⟩, true⟩

def words07 : List Nat := [360581949129999758, 360581948820249821, 360581948544944274, 360581948707252770, 360581948707947922, 360581948570980842, 360581948641334924, 360581949023800080, 360581949457224368, 360581949890797582]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578969354811394, 360578987614383128⟩, ⟨158598281687125418, 159261905078547390⟩, true⟩

def words08 : List Nat := [360581950050792772, 360581950051539155, 360581950025492687, 360581950185535255, 360581950191258210, 360581950192004657, 360581949852615496, 360581949340137108, 360581948827521124, 360581948423178045]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552401439310726, 360552419705903512⟩, ⟨1587923562515538945, 1588587563604671997⟩, true⟩

def words09 : List Nat := [360581948658687221, 360581948949371774, 360581949031153220, 360581949031903277, 360581949015099805, 360581948705638503, 360581948395970654, 360581948246162027, 360581947903862173, 360581947355784640]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk537
