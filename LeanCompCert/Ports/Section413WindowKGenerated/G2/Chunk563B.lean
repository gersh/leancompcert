import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk563B
