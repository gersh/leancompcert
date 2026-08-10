import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429A

def state06 : KState := ⟨⟨360618671671242858, 360618683105765948⟩, ⟨(-1534948679429842443), (-1534616705627695581)⟩, true⟩

def words05 : List Nat := [360582947932492906, 360582949423936857, 360582951457423437, 360582953761783255, 360582955673390423, 360582957585000680, 360582959110508725, 360582960282722890, 360582961114743857, 360582961946909597]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360632595345746347, 360632606785784979⟩, ⟨(-2133228603669287440), (-2132896392892058286)⟩, true⟩

def words06 : List Nat := [360582963320903006, 360582964156069773, 360582964717847878, 360582965279664550, 360582965552061331, 360582966304340158, 360582967598325221, 360582968892362387, 360582969913107692, 360582971068838852]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360648930558653101, 360648942004229929⟩, ⟨(-2835344809218770291), (-2835012360438521919)⟩, true⟩

def words07 : List Nat := [360582972609926942, 360582974151114832, 360582975667268373, 360582976644872857, 360582977161319984, 360582977677784737, 360582978274933568, 360582979268770474, 360582980803975185, 360582982339251485]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624513830719365, 360624525281870544⟩, ⟨(-1786008757624921011), (-1785676069230612997)⟩, true⟩

def words08 : List Nat := [360582983601439178, 360582984325232150, 360582985412999546, 360582986500894402, 360582987448727756, 360582987858262449, 360582987858794346, 360582987815996832, 360582988270985397, 360582989237832708]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576764702925731, 360576776159595900⟩, ⟨267105492154392689, 267438417837709741⟩, true⟩

def words09 : List Nat := [360582990358245708, 360582991478716527, 360582992223018336, 360582993153011527, 360582993943208498, 360582994733523824, 360582995536409336, 360582995801194501, 360582995801720302, 360582995657685150]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk429B
