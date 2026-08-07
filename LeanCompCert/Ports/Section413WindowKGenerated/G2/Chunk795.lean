import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576509523175859, 360576550669579931⟩, ⟨448543507501604608, 450752783537838666⟩, true⟩

def state01 : KState := ⟨⟨360580016488187371, 360580057645294559⟩, ⟨169713161096316746, 171923288083789510⟩, true⟩

def words00 : List Nat := [360582220500636495, 360582220501773003, 360582220437517836, 360582220294287650, 360582220150875895, 360582219968403386, 360582219951060157, 360582219995261799, 360582219996277328, 360582219930391828]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582209367143253, 360582250534990149⟩, ⟨(-4699386398681047), (-2488405445035655)⟩, true⟩

def words01 : List Nat := [360582219950361991, 360582219997857974, 360582219998793522, 360582219997360428, 360582219875546542, 360582219630166547, 360582219384575109, 360582219263816456, 360582219240967829, 360582219242558653]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576392668749858, 360576433847420394⟩, ⟨457751218359204140, 459963060061209454⟩, true⟩

def words02 : List Nat := [360582219243576415, 360582219144764614, 360582218887959794, 360582218767406529, 360582218646544091, 360582218484418770, 360582218269972987, 360582217930309649, 360582217590437392, 360582217363830066]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582899037978915, 360582940227345859⟩, ⟨(-59648784833552359), (-57436092392294645)⟩, true⟩

def words03 : List Nat := [360582217377132912, 360582217463371800, 360582217469990410, 360582217598554852, 360582217687540388, 360582217776825030, 360582218023573019, 360582218112828061, 360582218122919737, 360582218133175654]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587561759028295, 360587602959147224⟩, ⟨(-430621370243875043), (-428407822538060397)⟩, true⟩

def words04 : List Nat := [360582218134117271, 360582218070007695, 360582218131608840, 360582218193423927, 360582218194472733, 360582218121221628, 360582217953919670, 360582217773020549, 360582217591770514, 360582217636240686]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571751564063406, 360571792775021556⟩, ⟨827143754444176956, 829358164463135030⟩, true⟩

def words05 : List Nat := [360582217637263463, 360582217626670633, 360582217615854947, 360582217692966387, 360582217693934825, 360582217663703673, 360582217633350899, 360582217503339179, 360582217215493492, 360582217085786553]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584873066730196, 360584914288404877⟩, ⟨(-216850192602178362), (-214634929921537262)⟩, true⟩

def words06 : List Nat := [360582216982391520, 360582217014503042, 360582217015523337, 360582216928508883, 360582216841311271, 360582216715052850, 360582216779718325, 360582216877839362, 360582216878881172, 360582216886965640]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603074632892423, 360603115865309034⟩, ⟨(-1665268760587455566), (-1663052643119129596)⟩, true⟩

def words07 : List Nat := [360582217030188738, 360582217173744470, 360582217363897207, 360582217530370697, 360582217563237601, 360582217596211929, 360582217622517003, 360582217728738315, 360582217992263430, 360582218256041507]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586577793047687, 360586619036309121⟩, ⟨(-352527488423808192), (-350310507870397214)⟩, true⟩

def words08 : List Nat := [360582218421902086, 360582218430351567, 360582218434659057, 360582218439284263, 360582218440242933, 360582218340337992, 360582218193899998, 360582217942594941, 360582217691078302, 360582217652888001]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548510724678062, 360548551978654923⟩, ⟨2677477447643234533, 2679695281089976829⟩, true⟩

def words09 : List Nat := [360582217710409444, 360582217768145073, 360582217769159303, 360582217733158481, 360582217644695728, 360582217517232542, 360582217389433194, 360582217230493820, 360582216913983426, 360582216492236456]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk795
