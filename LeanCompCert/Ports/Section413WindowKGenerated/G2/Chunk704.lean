import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586086027042437, 360586117984485838⟩, ⟨(-258045984808807132), (-256526329083340296)⟩, true⟩

def state01 : KState := ⟨⟨360587433203758873, 360587465170689250⟩, ⟨(-353052898792326497), (-351532575135373627)⟩, true⟩

def words00 : List Nat := [360582474197231862, 360582474136689681, 360582473874489261, 360582473707498149, 360582473540247527, 360582473322563356, 360582473155615898, 360582472887562611, 360582472619321301, 360582472590337667]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564756169877460, 360564788146215089⟩, ⟨1243758798923141758, 1245279784991215036⟩, true⟩

def words01 : List Nat := [360582472621357172, 360582472652561795, 360582472653466410, 360582472532021614, 360582472439561207, 360582472296803990, 360582472154369463, 360582472155367099, 360582472005841193, 360582471755771909]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593817564821493, 360593849550569287⟩, ⟨(-802877101321314207), (-801355452542438973)⟩, true⟩

def words02 : List Nat := [360582471505469656, 360582471314910282, 360582471472118531, 360582471651884382, 360582471659227739, 360582471660226828, 360582471575301262, 360582471486353038, 360582471508182869, 360582471670764337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586069710944350, 360586101706196723⟩, ⟨(-257209431659834314), (-255687113427843648)⟩, true⟩

def words03 : List Nat := [360582471691156753, 360582471711655798, 360582471712469746, 360582471810949419, 360582471893956033, 360582471977122993, 360582471978012381, 360582471945453778, 360582471848252385, 360582471900920991]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561556281642460, 360561588286307258⟩, ⟨1469561313975147584, 1471084295265222972⟩, true⟩

def words04 : List Nat := [360582471901742666, 360582471883203021, 360582471663327378, 360582471341249939, 360582471019012392, 360582470619045220, 360582470336584850, 360582470113782266, 360582469890857973, 360582469539611236]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360591589449632653, 360591621463716813⟩, ⟨(-646470804641462198), (-644947159711193422)⟩, true⟩

def words05 : List Nat := [360582469244024255, 360582469149764600, 360582469097273985, 360582469098272091, 360582468940097400, 360582468567409569, 360582468194541273, 360582468022958540, 360582468082608849, 360582468213554153]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587735357031994, 360587767380642758⟩, ⟨(-374945953178234281), (-373421636957643691)⟩, true⟩

def words06 : List Nat := [360582468243340449, 360582468282256688, 360582468442530895, 360582468603092841, 360582468643233958, 360582468654416596, 360582468655306427, 360582468559972119, 360582468464463430, 360582468440128822]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547880338790278, 360547912371802911⟩, ⟨2433905486803995768, 2435430465620818732⟩, true⟩

def words07 : List Nat := [360582468604904285, 360582468769865883, 360582468804891029, 360582468805889560, 360582468687059818, 360582468517591228, 360582468347821259, 360582468137241306, 360582467776856530, 360582467287603434]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593617628621207, 360593649671077992⟩, ⟨(-789940480476264656), (-788414835990288666)⟩, true⟩

def words08 : List Nat := [360582466798138103, 360582466509837102, 360582466360108777, 360582466206245858, 360582466052310265, 360582465707344970, 360582465303395745, 360582465100586401, 360582464897472020, 360582465054091565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566219499370570, 360566251551336543⟩, ⟨1141588566032055456, 1143114880866780984⟩, true⟩

def words09 : List Nat := [360582465113074638, 360582465172164819, 360582465391960956, 360582465726988668, 360582465953092996, 360582466179352576, 360582466247942336, 360582466248941300, 360582466175663385, 360582465946809831]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704
