import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615364004518474, 360615384081884153⟩, ⟨(-1892511861672344416), (-1891748159271279412)⟩, true⟩

def state01 : KState := ⟨⟨360575031662015859, 360575051746858579⟩, ⟨378234145771203908, 378998269166936750⟩, true⟩

def words00 : List Nat := [360581783820141321, 360581783857663130, 360581783876543903, 360581783895662400, 360581783896318606, 360581783835508637, 360581783571382125, 360581783136373060, 360581782701219943, 360581782314593741]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558623460079113, 360558643552302505⟩, ⟨1302337969371780500, 1303102508410666586⟩, true⟩

def words01 : List Nat := [360581782391006400, 360581782587087264, 360581782624825453, 360581782625610104, 360581782485542779, 360581782130534455, 360581781775302838, 360581781688145002, 360581781435829986, 360581781025818320]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561020114621515, 360561040214256241⟩, ⟨1167445293054890854, 1168210249536245910⟩, true⟩

def words02 : List Nat := [360581780615639813, 360581780309932291, 360581780453152612, 360581780648376832, 360581780649100857, 360581780575655547, 360581780187734388, 360581779802911429, 360581779417886222, 360581778901448435]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564069004253935, 360564089111361487⟩, ⟨995666580385879220, 996431957848584100⟩, true⟩

def words03 : List Nat := [360581778534000861, 360581777921693288, 360581777309257206, 360581777011649313, 360581776921282909, 360581776675034520, 360581776428695664, 360581776003449931, 360581775472620554, 360581775159601611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582102310044554, 360582122424552475⟩, ⟨(-20435763434376955), (-19669968998548281)⟩, true⟩

def words04 : List Nat := [360581774846325213, 360581774795087072, 360581774795798205, 360581774580874404, 360581774365830343, 360581774005697185, 360581773803324280, 360581773707644432, 360581773611889411, 360581773362974180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590204527754799, 360590224649668046⟩, ⟨(-477101591947990516), (-476335380185968010)⟩, true⟩

def words05 : List Nat := [360581773550874445, 360581773738997914, 360581773888503305, 360581773904660849, 360581773905389857, 360581773633616923, 360581773361714370, 360581773005769636, 360581772992003497, 360581773142771683]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579169917124808, 360579190046508948⟩, ⟨144692349025044413, 145458981884142733⟩, true⟩

def words06 : List Nat := [360581773143470895, 360581773136592988, 360581772815620151, 360581772741087937, 360581772666329438, 360581772511982237, 360581772043638642, 360581771417370726, 360581770790970979, 360581770479041930]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548559385952570, 360548579522739984⟩, ⟨1870319025999975884, 1871086076218455638⟩, true⟩

def words07 : List Nat := [360581770433911759, 360581770380758647, 360581770327522369, 360581770039957190, 360581769537577326, 360581768785284740, 360581768032778954, 360581767594556700, 360581767164067413, 360581766576238006]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580344599308063, 360580364743502981⟩, ⟨78145511743935991, 78912979634150807⟩, true⟩

def words08 : List Nat := [360581765988254605, 360581765493901014, 360581765157037115, 360581765134353978, 360581765111629795, 360581764792891158, 360581764446226322, 360581764354610206, 360581764262768808, 360581764157931677]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569069640477395, 360569089792161831⟩, ⟨714076060750439401, 714843951010578951⟩, true⟩

def words09 : List Nat := [360581764133814987, 360581763952414149, 360581763902573918, 360581764237476505, 360581764492568586, 360581764747780930, 360581764765777106, 360581764766562573, 360581764554133243, 360581764330300317]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563
