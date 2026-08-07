import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk732

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487366916349316, 362487446714506904⟩, ⟨(-160575357784065493), (-156630594823375657)⟩, true⟩

def state01 : KState := ⟨⟨362481490227976865, 362481570048529602⟩, ⟨269663481853757378, 273609884256643466⟩, true⟩

def words00 : List Nat := [371285307175476708, 371285307178732270, 371285307180621021, 371285307182318671, 371285307190638257, 371285307193485338, 371285307221138339, 371285307305692747, 371285307375310815, 371285307377914340]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490783784415286, 362490863627709322⟩, ⟨(-410750811232609993), (-406802743823943129)⟩, true⟩

def words01 : List Nat := [371285307447008343, 371285307568424360, 371285307766651868, 371285307769167124, 371285307719078653, 371285307642953455, 371285307653565859, 371285307656337521, 371285307728329823, 371285307807059182]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475953308420658, 362476033174395175⟩, ⟨675193107591939808, 679142835780427598⟩, true⟩

def words02 : List Nat := [371285307885309147, 371285307887826643, 371285307765897579, 371285307779215265, 371285307811913692, 371285307814436686, 371285307701631714, 371285307530298555, 371285307357977871, 371285307281124391]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479803934895267, 362479883823531765⟩, ⟨393235216144623796, 397186603987111692⟩, true⟩

def words03 : List Nat := [371285307189832161, 371285307226241670, 371285307258667349, 371285307261227348, 371285307138267662, 371285307047513224, 371285307047964383, 371285307050497783, 371285306977797412, 371285306906600951]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487201681238216, 362487281592441794⟩, ⟨(-148573889158076784), (-144620848390768956)⟩, true⟩

def words04 : List Nat := [371285306838292098, 371285306841104274, 371285306897553330, 371285307020729570, 371285307124337687, 371285307126854900, 371285307054351351, 371285307101701529, 371285307243780367, 371285307273341840]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482717381060013, 362482797315170522⟩, ⟨179929795644798808, 183884514458243930⟩, true⟩

def words05 : List Nat := [371285307302804454, 371285307333074104, 371285307452750746, 371285307499697852, 371285307528798699, 371285307558842785, 371285307588576973, 371285307591093864, 371285307372424453, 371285307341302904]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481718237988304, 362481798194534649⟩, ⟨253171534568846064, 257127897149494792⟩, true⟩

def words06 : List Nat := [371285307433099774, 371285307435660656, 371285307406746408, 371285307379300962, 371285307377321007, 371285307380094667, 371285307390696742, 371285307469209799, 371285307512205006, 371285307514817842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499999444249435, 362500079423570235⟩, ⟨(-1086411288786730344), (-1082453257408611152)⟩, true⟩

def words07 : List Nat := [371285307516872852, 371285307568139076, 371285307775434529, 371285307777951909, 371285307737378849, 371285307666773737, 371285307707757649, 371285307748294939, 371285307951580859, 371285308156019184]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483498516196186, 362483578518247288⟩, ⟨122810881020199467, 126770578192836125⟩, true⟩

def words08 : List Nat := [371285308357966115, 371285308393595594, 371285308454976252, 371285308517600284, 371285308635718510, 371285308638236237, 371285308508464874, 371285308359848289, 371285308227130314, 371285308230052348]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471669448909838, 362471749473597357⟩, ⟨989898617576124433, 993859973888006147⟩, true⟩

def words09 : List Nat := [371285308370477905, 371285308535502124, 371285308661919997, 371285308664450205, 371285308613098902, 371285308604010350, 371285308633111571, 371285308635630304, 371285308454866023, 371285308272695420]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk732
