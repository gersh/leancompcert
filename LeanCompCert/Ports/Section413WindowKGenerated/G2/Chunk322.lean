import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360506963502978367, 360506969776667167⟩, ⟨2411236009477221351, 2411372609933300661⟩, true⟩

def state01 : KState := ⟨⟨360524049392633215, 360524055670368430⟩, ⟨1861064816879832665, 1861201547650977421⟩, true⟩

def words00 : List Nat := [360581854799528463, 360581852761199951, 360581851201864691, 360581850602911467, 360581850003962797, 360581848636601696, 360581846306496213, 360581843684068391, 360581841061675101, 360581839015529901]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360500573509774000, 360500579791598683⟩, ⟨2617498648577690770, 2617635511090537734⟩, true⟩

def words01 : List Nat := [360581837222015053, 360581834939388656, 360581832656822049, 360581831334157545, 360581830839084493, 360581829756509840, 360581828673955617, 360581827110832976, 360581824879751285, 360581822358671636]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360460284613266496, 360460290899138785⟩, ⟨3915626630917882855, 3915763623864792725⟩, true⟩

def words02 : List Nat := [360581819837608135, 360581817291815288, 360581813784505853, 360581809677771744, 360581805571221993, 360581801209695341, 360581797474327828, 360581793568295867, 360581789662455650, 360581785271582620]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360534775280679044, 360534781570601510⟩, ⟨1514358192859322711, 1514495316363392171⟩, true⟩

def words03 : List Nat := [360581781502441814, 360581778467365778, 360581775432351252, 360581773356140236, 360581770675236941, 360581767080550413, 360581763486004852, 360581760850135057, 360581758688438830, 360581757231779035]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360505740141891408, 360505746435908879⟩, ⟨2450509702040593908, 2450646957587611882⟩, true⟩

def words04 : List Nat := [360581755775148027, 360581753578734199, 360581751548647587, 360581749939707505, 360581748330753754, 360581746480474635, 360581744204651153, 360581741444779731, 360581738685003962, 360581735488857333]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360467355911681206, 360467362209744035⟩, ⟨3688723679458431124, 3688861065489516988⟩, true⟩

def words05 : List Nat := [360581733133028307, 360581731734905363, 360581730336821274, 360581728320382031, 360581725344211010, 360581722127177345, 360581718910205051, 360581716650684629, 360581713586139564, 360581710041904281]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360528881190113632, 360528887492240409⟩, ⟨1703571061477319183, 1703708578631060319⟩, true⟩

def words06 : List Nat := [360581706497791752, 360581703910973429, 360581701894980829, 360581699353780597, 360581696812708106, 360581693440570755, 360581690330470866, 360581687774351248, 360581685218264963, 360581682923868270]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360496395094773110, 360496401400992638⟩, ⟨2752171393313361430, 2752309042560453060⟩, true⟩

def words07 : List Nat := [360581681288249290, 360581679088991819, 360581676889788575, 360581675304874829, 360581674495085990, 360581673431690371, 360581672368320825, 360581670485034130, 360581667643030530, 360581665002063285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360464230853202113, 360464237163469067⟩, ⟨3790483829109724805, 3790621609028635437⟩, true⟩

def words08 : List Nat := [360581662361118312, 360581660141393816, 360581656963130114, 360581653101854768, 360581649240743589, 360581644730646804, 360581640708535228, 360581637404927291, 360581634101477260, 360581630214228703]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360521402735412054, 360521409049749676⟩, ⟨1943875242304442223, 1944013153684610059⟩, true⟩

def words09 : List Nat := [360581626579110124, 360581622907080188, 360581619235144384, 360581616161608778, 360581612468916831, 360581607959554309, 360581603450386012, 360581599896396350, 360581597078456966, 360581595215498426]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322
