import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk782

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618559385442673, 360618599145867067⟩, ⟨(-2844887566391792651), (-2842787577389043349)⟩, true⟩

def state01 : KState := ⟨⟨360616596263506021, 360616636034577102⟩, ⟨(-2691468656701697257), (-2689367835077726985)⟩, true⟩

def words00 : List Nat := [360582247211672821, 360582247482481878, 360582247916353859, 360582248350566868, 360582248743575485, 360582248973659079, 360582249116042544, 360582249258549607, 360582249537500837, 360582249978458683]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589726927368257, 360589766708959519⟩, ⟨(-589901791742992070), (-587800147281633856)⟩, true⟩

def words01 : List Nat := [360582250415221062, 360582250852170317, 360582251183282498, 360582251351434194, 360582251478561897, 360582251605982278, 360582251728424214, 360582251906719894, 360582252003798132, 360582252101024545]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592017903458791, 360592057695591284⟩, ⟨(-769188127902593362), (-767085658854423520)⟩, true⟩

def words02 : List Nat := [360582252142382868, 360582252265720895, 360582252381711521, 360582252497909764, 360582252498959409, 360582252455476477, 360582252248749791, 360582252170839877, 360582252176617480, 360582252303114460]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585373613120109, 360585413415904592⟩, ⟨(-249312696219048751), (-247209393812938709)⟩, true⟩

def words03 : List Nat := [360582252340175638, 360582252377384614, 360582252577517042, 360582252909248069, 360582253199842553, 360582253490611693, 360582253698770938, 360582253744060122, 360582253785363583, 360582253827021361]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597170293475447, 360597210106786386⟩, ⟨(-1172320841690968014), (-1170216715644469180)⟩, true⟩

def words04 : List Nat := [360582254031436052, 360582254246258698, 360582254336525078, 360582254426905004, 360582254476305485, 360582254659773549, 360582254886784459, 360582255113999156, 360582255259421982, 360582255451693871]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360616242017642444, 360616281841515555⟩, ⟨(-2664855444220089400), (-2662750491631999474)⟩, true⟩

def words05 : List Nat := [360582255699092184, 360582255946809595, 360582256188594240, 360582256406077844, 360582256467255500, 360582256528508043, 360582256719594835, 360582256992553586, 360582257428223871, 360582257864162442]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587524632694397, 360587564467203587⟩, ⟨(-417356942451898151), (-415251157430337013)⟩, true⟩

def words06 : List Nat := [360582258199700873, 360582258407633644, 360582258730436618, 360582259053570641, 360582259267341182, 360582259318427830, 360582259319441104, 360582259244733617, 360582259169812882, 360582259166933624]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571792608817561, 360571832453852173⟩, ⟨814121348170330656, 816227957068471836⟩, true⟩

def words07 : List Nat := [360582259324341565, 360582259481958687, 360582259527366575, 360582259577178074, 360582259578115533, 360582259547104042, 360582259646487381, 360582259647605130, 360582259616517632, 360582259484473896]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586364596547020, 360586404452148837⟩, ⟨(-326668359457775765), (-324560923305731653)⟩, true⟩

def words08 : List Nat := [360582259352193727, 360582259182877907, 360582259169463014, 360582259244903720, 360582259245937772, 360582259163733356, 360582259033154734, 360582258924258101, 360582258826731642, 360582258880840440]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576185788837307, 360576225655094999⟩, ⟨470303853891756298, 472412124343742588⟩, true⟩

def words09 : List Nat := [360582258881846063, 360582258853651515, 360582258907161242, 360582259071789127, 360582259123294162, 360582259174963777, 360582259175960140, 360582259146040758, 360582259091323369, 360582259015559160]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk782
