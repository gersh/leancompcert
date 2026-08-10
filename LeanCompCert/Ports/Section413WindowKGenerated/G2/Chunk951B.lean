import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951B
