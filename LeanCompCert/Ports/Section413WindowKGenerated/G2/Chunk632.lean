import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608441591962688, 360608467126320784⟩, ⟨(-1629153259449892766), (-1628063112469843578)⟩, true⟩

def state01 : KState := ⟨⟨360606412754013029, 360606438296841296⟩, ⟨(-1501108240064238788), (-1500017557729059618)⟩, true⟩

def words00 : List Nat := [360582707324132127, 360582707357321719, 360582707384009979, 360582707410946784, 360582707411689966, 360582707488083257, 360582707488882509, 360582707474722263, 360582707595640614, 360582707972091980]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560845492735537, 360560871043921503⟩, ⟨1379544306515763970, 1380635517183584806⟩, true⟩

def words01 : List Nat := [360582708598178093, 360582709224414483, 360582709701771739, 360582709929888606, 360582710052308363, 360582710174968415, 360582710175703988, 360582710165743847, 360582709976188780, 360582709631665629]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586672145080781, 360586697704646934⟩, ⟨(-253322183022305092), (-252230442517704206)⟩, true⟩

def words02 : List Nat := [360582709286951364, 360582709152529066, 360582709250656569, 360582709348964590, 360582709349792333, 360582709239489855, 360582708950683597, 360582708779938118, 360582708609270376, 360582708673277548]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582352972320632, 360582378540362033⟩, ⟨19783866819638429, 20876143256145675⟩, true⟩

def words03 : List Nat := [360582708674082795, 360582708546457603, 360582708436176754, 360582708581546058, 360582708663656049, 360582708745908385, 360582708746700029, 360582708697391482, 360582708654357470, 360582708650154193]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593379978592824, 360593405554997219⟩, ⟨(-677673360741919903), (-676580555388589669)⟩, true⟩

def words04 : List Nat := [360582708890146204, 360582708954388481, 360582708955187500, 360582708895386179, 360582708835458363, 360582708561467841, 360582708546649982, 360582708664603370, 360582708665395856, 360582708798339007]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360592777962228037, 360592803547030615⟩, ⟨(-639594370215507144), (-638501033635288434)⟩, true⟩

def words05 : List Nat := [360582709076166862, 360582709354271278, 360582709789536955, 360582709975988283, 360582709976807925, 360582709951642919, 360582709933866091, 360582710103597970, 360582710263884289, 360582710424354159]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593775073667990, 360593800666937750⟩, ⟨(-702847324214305954), (-701753451959425932)⟩, true⟩

def words06 : List Nat := [360582710425159733, 360582710383252357, 360582710172920578, 360582710109712254, 360582710046270514, 360582709920085660, 360582709800136229, 360582709554605033, 360582709308911439, 360582709433166205]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568291304694456, 360568316906350253⟩, ⟨909633377254183554, 910727780135387788⟩, true⟩

def words07 : List Nat := [360582709594657239, 360582709756315403, 360582709757122448, 360582709709266609, 360582709579130887, 360582709384269961, 360582709242735401, 360582709243625344, 360582709164775385, 360582708938274011]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575986055348807, 360576011665392398⟩, ⟨422733087560438533, 423828021264043939⟩, true⟩

def words08 : List Nat := [360582708733524538, 360582708894656776, 360582709085342433, 360582709276191674, 360582709277011662, 360582709256508136, 360582708987149822, 360582708711750200, 360582708436090057, 360582708268667229]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577750852128877, 360577776470641695⟩, ⟨311029347481027363, 312124817242655657⟩, true⟩

def words09 : List Nat := [360582708163655197, 360582707879841951, 360582707595867452, 360582707659498378, 360582707745967151, 360582707832579907, 360582707833383414, 360582707755730712, 360582707429313507, 360582707352430679]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632
