import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578113000465711, 360578178311531839⟩, ⟨417553494068823075, 421932597027897365⟩, true⟩

def state01 : KState := ⟨⟨360584853606531265, 360584918931209709⟩, ⟨(-251782827087575064), (-247402372358068178)⟩, true⟩

def words00 : List Nat := [360582427384191850, 360582427464651953, 360582427487218096, 360582427509941397, 360582427511149433, 360582427556303370, 360582427635639673, 360582427715256527, 360582427716621076, 360582427743200747]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605976422395407, 360606041760700172⟩, ⟨(-2349599814517959457), (-2345218006489907285)⟩, true⟩

def words01 : List Nat := [360582427838995276, 360582427935211728, 360582428075468962, 360582428233782120, 360582428305372128, 360582428377085845, 360582428549821611, 360582428773533931, 360582429012455429, 360582429251699157]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591352750300843, 360591418102372234⟩, ⟨(-897208694026641164), (-892825518633756270)⟩, true⟩

def words02 : List Nat := [360582429439975377, 360582429559290523, 360582429674757767, 360582429790642495, 360582429854226108, 360582429855670075, 360582429818275351, 360582429729601464, 360582429640652526, 360582429714873531]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557529183951518, 360557594549605530⟩, ⟨2462701943765612375, 2467086468390314231⟩, true⟩

def words03 : List Nat := [360582429841182546, 360582429967766000, 360582430030828437, 360582430032272591, 360582429994193804, 360582429930844655, 360582429867094587, 360582429770296507, 360582429572304186, 360582429323799111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580340504059531, 360580405883344381⟩, ⟨196471348304470913, 200857227084236201⟩, true⟩

def words04 : List Nat := [360582429074979134, 360582428839183230, 360582428654009786, 360582428530233616, 360582428406323009, 360582428187571497, 360582427938415708, 360582427790949595, 360582427643057711, 360582427596752376]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360582708979846868, 360582774372922890⟩, ⟨(-38870103685789517), (-34482854686458943)⟩, true⟩

def words05 : List Nat := [360582427577727539, 360582427478800181, 360582427379588128, 360582427395797967, 360582427397007497, 360582427396162254, 360582427395158940, 360582427343638111, 360582427321590761, 360582427326750987]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576944078193711, 360577009484858134⟩, ⟨533915653984313861, 538304253197041377⟩, true⟩

def words06 : List Nat := [360582427403504011, 360582427404948592, 360582427380831644, 360582427280344282, 360582427179647638, 360582426985771789, 360582426842007997, 360582426799737627, 360582426757322647, 360582426655565562]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598114742464800, 360598180162785692⟩, ⟨(-1569903165717995635), (-1565513209395077401)⟩, true⟩

def words07 : List Nat := [360582426648912374, 360582426697233435, 360582426810210941, 360582426907956819, 360582426918105524, 360582426928364608, 360582427039541494, 360582427202138880, 360582427361839375, 360582427521844315]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595610231961287, 360595675666042114⟩, ⟨(-1321066845141636654), (-1316675521289715696)⟩, true⟩

def words08 : List Nat := [360582427623380612, 360582427738031819, 360582427850921097, 360582427964230776, 360582427990464358, 360582428045644845, 360582428048622222, 360582428051744018, 360582428099031874, 360582428233967885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584013711171899, 360584079158883843⟩, ⟨(-168400203258189923), (-164007524541852173)⟩, true⟩

def words09 : List Nat := [360582428469587365, 360582428705479334, 360582428863315193, 360582428920341892, 360582428938149914, 360582428956366852, 360582429075292623, 360582429164373170, 360582429182263518, 360582429200387029]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993
