import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk097

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590960445567371, 360590960955858220⟩, ⟨(-137187723797241114), (-137184368372287006)⟩, true⟩

def state01 : KState := ⟨⟨360699301042391627, 360699301553786367⟩, ⟨(-1187948187719659756), (-1187944821581559326)⟩, true⟩

def words00 : List Nat := [360576828142937115, 360576846482087621, 360576870640710995, 360576894794377898, 360576910010200576, 360576921028116810, 360576935192463185, 360576949353925356, 360576959141556203, 360576971740010077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622526950864012, 360622527463372737⟩, ⟨(-442386376085752256), (-442382999125283104)⟩, true⟩

def words01 : List Nat := [360576977454707195, 360576983168238983, 360576990264556839, 360577002607587762, 360577009368057708, 360577016127157087, 360577016127261392, 360577015989881392, 360577014809007433, 360577019491031900]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360634001239645235, 360634001753258584⟩, ⟨(-554285820857878064), (-554282433154936408)⟩, true⟩

def words02 : List Nat := [360577034715361645, 360577039515903106, 360577039516009178, 360577036309285640, 360577033103201127, 360577027025167728, 360577031671765530, 360577037171897952, 360577037172003425, 360577041273024802]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360740249797483460, 360740250312202583⟩, ⟨(-1588732276058976761), (-1588728877591217905)⟩, true⟩

def words03 : List Nat := [360577052501142702, 360577063726987262, 360577085467182867, 360577101947134607, 360577107378135874, 360577112808030246, 360577113472156198, 360577119715663017, 360577136464279305, 360577153209483025]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360756845198811386, 360756845714648642⟩, ⟨(-1751554617021703492), (-1751551207657783138)⟩, true⟩

def words04 : List Nat := [360577162503677374, 360577162503794783, 360577170833979450, 360577180248078728, 360577186854863292, 360577192135001687, 360577192135107574, 360577191072526366, 360577199436805933, 360577217860309828]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596494987763636, 360596495504708274⟩, ⟨(-187575013912746697), (-187571593746188069)⟩, true⟩

def words05 : List Nat := [360577235744569058, 360577253625181697, 360577266142220109, 360577268303861775, 360577268303960201, 360577267675884920, 360577267819231086, 360577275134183166, 360577277103588153, 360577279072606421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360832234943628714, 360832235461682906⟩, ⟨(-2489854815352223198), (-2489851384350846894)⟩, true⟩

def words06 : List Nat := [360577286737094181, 360577299585981612, 360577315274783514, 360577330960394053, 360577337319709494, 360577339764052469, 360577352649267603, 360577365531879701, 360577388851085267, 360577414933144287]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589325442643545, 360589325961819935⟩, ⟨(-114837457178347384), (-114834015207498130)⟩, true⟩

def words07 : List Nat := [360577435681795893, 360577456426216189, 360577482121702876, 360577513144919972, 360577535857285538, 360577558565024235, 360577575954552787, 360577583041534485, 360577584242339699, 360577585442935619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360719959283285280, 360719959803570993⟩, ⟨(-1393336063445420875), (-1393332610619728315)⟩, true⟩

def words08 : List Nat := [360577597055487332, 360577603030923615, 360577603743886043, 360577604456714651, 360577604456813553, 360577603034295006, 360577616874961445, 360577630712822475, 360577637779891648, 360577652316019188]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360858708824610169, 360858709346010353⟩, ⟨(-2752584873776226790), (-2752581410034282798)⟩, true⟩

def words09 : List Nat := [360577677247546102, 360577702174016943, 360577726574501881, 360577745455123664, 360577755587089071, 360577765716995548, 360577781713057259, 360577805027999342, 360577833691800951, 360577862349781981]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk097
