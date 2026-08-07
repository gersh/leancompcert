import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk106

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552856180456855, 360552856795262453⟩, ⟨315698461692791143, 315702878695639191⟩, true⟩

def state01 : KState := ⟨⟨360755518413085870, 360755519029106501⟩, ⟨(-1833422854926090497), (-1833418425037936191)⟩, true⟩

def words00 : List Nat := [360582643326108900, 360582654910963194, 360582670354728741, 360582685795606883, 360582692530664822, 360582692530793591, 360582697280029332, 360582704077586713, 360582718046406166, 360582734331619183]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360613158171487377, 360613158788736469⟩, ⟨(-321663033252972054), (-321658590324737274)⟩, true⟩

def words01 : List Nat := [360582745792643445, 360582757251522947, 360582777547764380, 360582803929215842, 360582824368822578, 360582844804599246, 360582860753652742, 360582867933380575, 360582870785733112, 360582873637590180]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590578252037324, 360590578870501613⟩, ⟨(-82317816427017699), (-82313360587311563)⟩, true⟩

def words02 : List Nat := [360582874126138613, 360582874126267653, 360582869468738185, 360582860337185285, 360582851207330716, 360582836957475313, 360582834006229062, 360582836940451031, 360582836940567042, 360582836103067947]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360712767961638336, 360712768581322743⟩, ⟨(-1382033843114296268), (-1382029374298621344)⟩, true⟩

def words03 : List Nat := [360582845645986550, 360582855187147642, 360582862842239852, 360582868231091417, 360582868231210337, 360582866107531649, 360582863984228396, 360582866393442369, 360582878602399219, 360582890809092819]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614284619452432, 360614285240366706⟩, ⟨(-334189278275699529), (-334184796368106995)⟩, true⟩

def words04 : List Nat := [360582898548186188, 360582903746316875, 360582913263186743, 360582922778305971, 360582929986353922, 360582929986483195, 360582928483675548, 360582919828977154, 360582911175878976, 360582909332342286]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360559820116957913, 360559820739090286⟩, ⟨246768326714355671, 246772821600828253⟩, true⟩

def words05 : List Nat := [360582921056511504, 360582932778504215, 360582938828069199, 360582945225099859, 360582949327184088, 360582953428533769, 360582966299191713, 360582972331071171, 360582972331187758, 360582970159503122]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360742051001549430, 360742051624905147⟩, ⟨(-1697077421958440852), (-1697072914024983280)⟩, true⟩

def words06 : List Nat := [360582967988198064, 360582967367639856, 360582978006520971, 360582988643431738, 360582991720425907, 360582991720555442, 360582989279167062, 360582992435758278, 360583000742481205, 360583015647581093]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360672371518758080, 360672372143346915⟩, ⟨(-953359589132568852), (-953355068035594128)⟩, true⟩

def words07 : List Nat := [360583026115651870, 360583036581775490, 360583049367497259, 360583066805162385, 360583077762743172, 360583088718290857, 360583095248607607, 360583098328314404, 360583106687390894, 360583115044944557]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360729685421524604, 360729686047336016⟩, ⟨(-1565858112593280966), (-1565853578432873390)⟩, true⟩

def words08 : List Nat := [360583124552753216, 360583134905886710, 360583140819289826, 360583146731599206, 360583150381174241, 360583159862298016, 360583178054985903, 360583196244294470, 360583207695617826, 360583221396841874]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360757226887680182, 360757227514717784⟩, ⟨(-1860441909921870534), (-1860437362647488770)⟩, true⟩

def words09 : List Nat := [360583243805040714, 360583266209088315, 360583288870568324, 360583302896176843, 360583309014642811, 360583315131977052, 360583324693507912, 360583338612463533, 360583354863868547, 360583371112264977]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk106
