import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668456515133022, 360668472592855208⟩, ⟨(-4375837921092751172), (-4375288217412281984)⟩, true⟩

def state01 : KState := ⟨⟨360611513092108381, 360611529176488911⟩, ⟨(-1494360832041322412), (-1493810791415353786)⟩, true⟩

def words00 : List Nat := [360582007628640964, 360582008712787323, 360582009787171311, 360582010861707923, 360582011747883359, 360582012244744261, 360582012544902550, 360582012845119453, 360582013056503822, 360582013640510264]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360538016003603732, 360538032094560425⟩, ⟨2225746939286388706, 2226297312765500900⟩, true⟩

def words01 : List Nat := [360582014153268350, 360582014666135989, 360582014983265063, 360582014983964170, 360582014911759252, 360582014675661221, 360582014439368409, 360582014189178346, 360582013549668848, 360582012681537223]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591135207263796, 360591151304822131⟩, ⟨(-463441562704119818), (-462890855019039964)⟩, true⟩

def words02 : List Nat := [360582011813281632, 360582011235430498, 360582011006223810, 360582010771825863, 360582010537377982, 360582009971454284, 360582009278589558, 360582008975438737, 360582008684010803, 360582008865308414]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582132194772314, 360582148298999093⟩, ⟨(-7655053019274237), (-7104007677463451)⟩, true⟩

def words03 : List Nat := [360582008865942211, 360582008748469627, 360582008630871600, 360582008787874191, 360582008788463869, 360582008689123389, 360582008589710511, 360582008294904277, 360582008013689643, 360582008017257472]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576982861149637, 360576998971961609⟩, ⟨253064089724109618, 253615468573687476⟩, true⟩

def words04 : List Nat := [360582008307051842, 360582008307751470, 360582008208734586, 360582007830459963, 360582007452091668, 360582006802340092, 360582006405518807, 360582006397978821, 360582006390359498, 360582006187530685]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360615974851677434, 360615990969104073⟩, ⟨(-1722031907884401236), (-1721480193970401012)⟩, true⟩

def words05 : List Nat := [360582006379456744, 360582006670454970, 360582007194346554, 360582007744621714, 360582007910833267, 360582008077088553, 360582008561763860, 360582009243054761, 360582009914410666, 360582010585890746]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623791127864580, 360623807251960239⟩, ⟨(-2118228114556555751), (-2117676062757316799)⟩, true⟩

def words06 : List Nat := [360582011008283466, 360582011162241527, 360582011527529953, 360582011893008652, 360582012160599421, 360582012662659346, 360582012969577118, 360582013276559358, 360582013762645610, 360582014588252057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579987357299455, 360580003487997769⟩, ⟨101680667632285329, 102233054021067777⟩, true⟩

def words07 : List Nat := [360582015802274131, 360582017016382305, 360582017909337794, 360582018692043972, 360582019371825037, 360582020051764321, 360582020596599349, 360582020753230405, 360582020753860562, 360582020714793765]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605254891128962, 360605271028432389⟩, ⟨(-1178962437168057499), (-1178409715998458361)⟩, true⟩

def words08 : List Nat := [360582020893652770, 360582021308583603, 360582022111800546, 360582022915119835, 360582023410015352, 360582023516749126, 360582023517327958, 360582023455274107, 360582023647237579, 360582024106572524]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592151776232555, 360592167920208652⟩, ⟨(-514623357045982415), (-514070297607514627)⟩, true⟩

def words09 : List Nat := [360582024334663187, 360582024562824263, 360582025088587175, 360582025976230540, 360582026766144717, 360582027556141990, 360582028104691243, 360582028265240037, 360582028465803492, 360582028666592205]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk506
