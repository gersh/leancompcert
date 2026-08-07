import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517215336703441, 360517217933106992⟩, ⟨1338611439758650837, 1338648510391577019⟩, true⟩

def state01 : KState := ⟨⟨360585647883998737, 360585650482963112⟩, ⟨(-105395322194577546), (-105358197515383388)⟩, true⟩

def words00 : List Nat := [360580657984053862, 360580657576946654, 360580659407025038, 360580661236981795, 360580661237238702, 360580660835647005, 360580659478189811, 360580659915656032, 360580659915877808, 360580659805235133]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360524650306037688, 360524652907594706⟩, ⟨1182750772241086291, 1182787951663611833⟩, true⟩

def words01 : List Nat := [360580659805477380, 360580658684472101, 360580657828800651, 360580659883705418, 360580660722141894, 360580661560543151, 360580661560785331, 360580661284890504, 360580658776484516, 360580656125003021]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360545123543244281, 360545126147359385⟩, ⟨750254575955297067, 750291809417666271⟩, true⟩

def words02 : List Nat := [360580653473681123, 360580653051982513, 360580651305068822, 360580648420266181, 360580645535693727, 360580641443974564, 360580639073009108, 360580637924521959, 360580636776113248, 360580634515055442]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537360950792963, 360537363557479225⟩, ⟨913877972660530921, 913915260464368235⟩, true⟩

def words03 : List Nat := [360580632834885382, 360580630352858212, 360580627870987715, 360580625331955716, 360580620564098322, 360580613852434908, 360580607141354971, 360580601436775738, 360580597166184059, 360580595121361173]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567261427225860, 360567264036505199⟩, ⟨281334419286280592, 281371761920091252⟩, true⟩

def words04 : List Nat := [360580593076690491, 360580589667681126, 360580586421335555, 360580585400044763, 360580584378778903, 360580582796796635, 360580579804823765, 360580575016966604, 360580570229509577, 360580567665910405]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360529723051026494, 360529725662869000⟩, ⟨1075530650074168845, 1075568046932053099⟩, true⟩

def words05 : List Nat := [360580567072182037, 360580567107484769, 360580567107728957, 360580565427950590, 360580563830408354, 360580561673791947, 360580559582406588, 360580559582679073, 360580558312850593, 360580555910833653]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360638930579812148, 360638933194231697⟩, ⟨(-1236038532818878034), (-1236001081418203596)⟩, true⟩

def words06 : List Nat := [360580553508985766, 360580551052333737, 360580550623623843, 360580551519603447, 360580551519855259, 360580550330477110, 360580548265940257, 360580547649862173, 360580548636489872, 360580551394533138]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594689197221866, 360594691814234701⟩, ⟨(-299228640770099753), (-299191134456404381)⟩, true⟩

def words07 : List Nat := [360580553043859083, 360580554693059134, 360580557666394508, 360580561768934326, 360580563840281057, 360580565911470945, 360580566580476839, 360580566580749545, 360580565698038654, 360580566365273066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360666694644239666, 360666697263825814⟩, ⟨(-1824658514707835739), (-1824620953878688911)⟩, true⟩

def words08 : List Nat := [360580568441179237, 360580571634957575, 360580573370244525, 360580575105397181, 360580575649427805, 360580577916362820, 360580582398405535, 360580586880077275, 360580589620603134, 360580593684293056]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360671270303782811, 360671272925943260⟩, ⟨(-1921405305835476961), (-1921367690444045347)⟩, true⟩

def words09 : List Nat := [360580599962454293, 360580606240102622, 360580614731788690, 360580621006371983, 360580625325119377, 360580629643482857, 360580633308331697, 360580638098774917, 360580642374224386, 360580646649331589]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk211
