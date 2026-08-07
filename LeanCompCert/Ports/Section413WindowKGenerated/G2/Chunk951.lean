import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584084528812118, 360584144232242687⟩, ⟨(-193095447699256794), (-189261497747198208)⟩, true⟩

def state01 : KState := ⟨⟨360597218971647956, 360597278688073086⟩, ⟨(-1442225593043191808), (-1438390407242970938)⟩, true⟩

def words00 : List Nat := [360582154254350423, 360582154389758622, 360582154469835794, 360582154550050461, 360582154571121922, 360582154678456265, 360582154895921361, 360582155113654274, 360582155246342873, 360582155406778147]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360616592951864720, 360616652681294376⟩, ⟨(-3284981082946528893), (-3281144660222086493)⟩, true⟩

def words01 : List Nat := [360582155677438513, 360582155948512500, 360582156307372332, 360582156618178436, 360582156820776217, 360582157023498523, 360582157242583764, 360582157523627290, 360582157887390334, 360582158251460564]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597903261403990, 360597963003993740⟩, ⟨(-1507243570324713162), (-1503405895749783172)⟩, true⟩

def words02 : List Nat := [360582158544546471, 360582158748004701, 360582158928931656, 360582159110240369, 360582159261539294, 360582159302913087, 360582159304141658, 360582159274094534, 360582159303274659, 360582159471015534]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576110724754577, 360576170480319954⟩, ⟨566078232828677368, 569917141840838974⟩, true⟩

def words03 : List Nat := [360582159748742504, 360582160026731899, 360582160238629945, 360582160417918619, 360582160552356553, 360582160687157237, 360582160818819145, 360582160840605056, 360582160841854084, 360582160780318282]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593041312917972, 360593101081497843⟩, ⟨(-1044740491852276259), (-1040900344577330355)⟩, true⟩

def words04 : List Nat := [360582160740466237, 360582160832448176, 360582161034487180, 360582161236810556, 360582161345578199, 360582161367022878, 360582161416298790, 360582161465989202, 360582161507336007, 360582161623745667]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598511405578810, 360598571187299547⟩, ⟨(-1565271476809290392), (-1561430079116181400)⟩, true⟩

def words05 : List Nat := [360582161651325088, 360582161679034470, 360582161816921257, 360582162010176608, 360582162174950557, 360582162339946287, 360582162438111410, 360582162541394475, 360582162714941652, 360582162888951315]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587618422194354, 360587678216889816⟩, ⟨(-528715088237435827), (-524872455803829089)⟩, true⟩

def words06 : List Nat := [360582163042641516, 360582163086522255, 360582163087750714, 360582163076136941, 360582163064317662, 360582162977845892, 360582163033876541, 360582163100442016, 360582163111375412, 360582163170753874]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598372580500575, 360598432388236918⟩, ⟨(-1552263714974093440), (-1548419841377897258)⟩, true⟩

def words07 : List Nat := [360582163278325295, 360582163386334418, 360582163526573742, 360582163615973430, 360582163617260498, 360582163611112753, 360582163707555314, 360582163882734014, 360582164054791866, 360582164227139873]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595109699074937, 360595169519944804⟩, ⟨(-1241826244464369233), (-1237981120754366895)⟩, true⟩

def words08 : List Nat := [360582164343828899, 360582164350642532, 360582164351768058, 360582164324459964, 360582164296772221, 360582164241256985, 360582164232455306, 360582164168362940, 360582164148888031, 360582164287089237]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579764338916875, 360579824172797439⟩, ⟨219045915218144208, 222892277482533526⟩, true⟩

def words09 : List Nat := [360582164535173532, 360582164783517534, 360582164946236777, 360582165091982409, 360582165195272952, 360582165298927335, 360582165454394484, 360582165500133280, 360582165501368029, 360582165478233180]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951
