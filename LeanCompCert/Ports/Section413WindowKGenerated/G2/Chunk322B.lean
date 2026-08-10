import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322B
