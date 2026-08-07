import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk963

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360600183719905068, 360600244998956388⟩, ⟨(-1733673937148900466), (-1729689198205623294)⟩, true⟩

def state01 : KState := ⟨⟨360589134005732018, 360589195297936815⟩, ⟨(-669573860117272764), (-665587854429231966)⟩, true⟩

def words00 : List Nat := [360582283915802096, 360582284027913040, 360582284079507256, 360582284131259421, 360582284132439486, 360582284113656484, 360582284236679043, 360582284359967015, 360582284406090512, 360582284479292743]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582197782215320, 360582259087624012⟩, ⟨(-1567514403842725), 2419763017797463⟩, true⟩

def words01 : List Nat := [360582284553815864, 360582284628744852, 360582284700706048, 360582284702103129, 360582284666748261, 360582284540438083, 360582284413859315, 360582284284126861, 360582284208536924, 360582284209748367]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578942417816374, 360579003736528343⟩, ⟨311933936290979948, 315922495148099770⟩, true⟩

def words02 : List Nat := [360582284210732143, 360582284144914153, 360582284045833909, 360582284051177782, 360582284052348289, 360582284030383945, 360582283900882322, 360582283672095729, 360582283443045917, 360582283322276793]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587240796980705, 360587302128843384⟩, ⟨(-487461017437894757), (-483471191706081257)⟩, true⟩

def words03 : List Nat := [360582283363114707, 360582283438264050, 360582283453892627, 360582283474540264, 360582283475709473, 360582283468999943, 360582283561385595, 360582283689256947, 360582283742595935, 360582283796132430]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582710937205298, 360582772282277853⟩, ⟨(-51024699023651269), (-47033600589060169)⟩, true⟩

def words04 : List Nat := [360582283846800386, 360582283951548376, 360582284087570425, 360582284223852293, 360582284268135821, 360582284269533527, 360582284237989079, 360582284210200943, 360582284181984101, 360582284133731507]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580072133769846, 360580133492145636⟩, ⟨203250143857178115, 207242524123303947⟩, true⟩

def words05 : List Nat := [360582284134976387, 360582284087218441, 360582284097792759, 360582284224651618, 360582284278028731, 360582284331623069, 360582284332868031, 360582284332239437, 360582284223986122, 360582284203271864]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587673455096911, 360587734826644549⟩, ⟨(-529241224248810422), (-525247574677251322)⟩, true⟩

def words06 : List Nat := [360582284247271621, 360582284316315625, 360582284319852507, 360582284323528565, 360582284324698134, 360582284329492093, 360582284416899373, 360582284504574952, 360582284505847908, 360582284560748406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595301216619335, 360595362601352431⟩, ⟨(-1264426332582947266), (-1260431412261607642)⟩, true⟩

def words07 : List Nat := [360582284634804020, 360582284709275564, 360582284819715462, 360582284823096219, 360582284824386896, 360582284735242177, 360582284662930814, 360582284735211755, 360582284872033164, 360582285009168686]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590628667802468, 360590690065886328⟩, ⟨(-814138969559093850), (-810142762429865464)⟩, true⟩

def words08 : List Nat := [360582285092404040, 360582285213892221, 360582285329314900, 360582285445125805, 360582285509973902, 360582285511371987, 360582285468996374, 360582285357933922, 360582285246605734, 360582285310645384]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556730504397874, 360556791915637473⟩, ⟨2453518732849259027, 2457516208126242511⟩, true⟩

def words09 : List Nat := [360582285463138587, 360582285615896298, 360582285676743222, 360582285678141442, 360582285631620256, 360582285526628803, 360582285421247613, 360582285294891669, 360582285085363435, 360582284822360775]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk963
