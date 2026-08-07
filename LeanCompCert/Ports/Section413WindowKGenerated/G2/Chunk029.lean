import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk029

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361326150778362977, 361326150818368468⟩, ⟨(-2164347135010175454), (-2164347056177852666)⟩, true⟩

def state01 : KState := ⟨⟨360976569925567749, 360976569965865876⟩, ⟨(-1151933587080753714), (-1151933507398302246)⟩, true⟩

def words00 : List Nat := [360580277140254623, 360580357897550663, 360580556027376840, 360580754020805986, 360580868886449072, 360580869090086735, 360580869090114526, 360580779145813534, 360580716526862419, 360580852512276628]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360306587174653280, 360306587215242887⟩, ⟨802482212498437512, 802482293030571222⟩, true⟩

def words01 : List Nat := [360581033592491622, 360581214548387519, 360581334724008349, 360581411159264978, 360581411159291042, 360581404614401985, 360581507984088391, 360581507984119361, 360581504067910587, 360581409918335549]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361234214646315774, 361234214687198623⟩, ⟨(-1911449203623427845), (-1911449122233587507)⟩, true⟩

def words02 : List Nat := [360581315833217617, 360581265925811526, 360581317271743811, 360581368582573730, 360581368582602699, 360581353390974319, 360581502492900156, 360581651493024140, 360581842973093567, 360582065549623193]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361124091250886979, 361124091292066939⟩, ⟨(-1589400480121906148), (-1589400397860032608)⟩, true⟩

def words03 : List Nat := [360582228098284519, 360582390536108088, 360582544333424456, 360582762593559098, 360582947121771906, 360583131524332194, 360583225528282769, 360583294967453001, 360583478911806431, 360583662731080869]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360631415205829965, 360631415247304618⟩, ⟨(-139589520998886338), (-139589437869103216)⟩, true⟩

def words04 : List Nat := [360583875216385294, 360583975769717565, 360584017564096155, 360584059330094710, 360584059330121008, 360584072852134207, 360584100526000866, 360584128181104962, 360584128181132887, 360584112828507904]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361408555188326003, 361408555230097377⟩, ⟨(-2436647054043065944), (-2436646970036462680)⟩, true⟩

def words05 : List Nat := [360584152157798260, 360584191460460985, 360584344072055659, 360584505220696986, 360584571298032406, 360584637330678265, 360584816473338234, 360585085486870277, 360585363686133554, 360585641697494722]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361155141928211141, 361155141970283657⟩, ⟨(-1688851758372072277), (-1688851673472644805)⟩, true⟩

def words06 : List Nat := [360585829543948677, 360585906970175934, 360586097047787878, 360586286997194861, 360586443635701961, 360586490019182413, 360586490019210583, 360586457566948827, 360586505043152078, 360586696438990273]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360253936669046750, 360253936711416971⟩, ⟨994445573737765086, 994445659522924034⟩, true⟩

def words07 : List Nat := [360586999946323093, 360587303249486101, 360587548112108386, 360587683100163881, 360587716780666410, 360587750438549541, 360587807686021901, 360587807686053597, 360587755328209642, 360587643308572315]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360387488183788873, 360387488226459383⟩, ⟨595998728857474292, 595998815538983596⟩, true⟩

def words08 : List Nat := [360587531364083885, 360587429468839161, 360587446098753378, 360587472785005009, 360587472785034236, 360587407054078707, 360587232138808735, 360587100580293156, 360586969109797033, 360586818933997505]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360219058782059532, 360219058825033369⟩, ⟨1100287598942182366, 1100287686532179862⟩, true⟩

def words09 : List Nat := [360586752290526179, 360586628233583511, 360586504259532625, 360586426418691309, 360586405448407145, 360586352538864594, 360586299664626647, 360586175883960016, 360585943682126892, 360585821387210763]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk029
