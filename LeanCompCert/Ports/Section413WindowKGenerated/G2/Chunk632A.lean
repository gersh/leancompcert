import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk632A
