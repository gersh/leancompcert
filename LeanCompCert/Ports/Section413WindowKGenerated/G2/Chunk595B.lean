import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595A

def state06 : KState := ⟨⟨360562506306325218, 360562528877528359⟩, ⟨1163421229320268647, 1164329440383036633⟩, true⟩

def words05 : List Nat := [360582078981464289, 360582079047564054, 360582079048316206, 360582078935601867, 360582078780436008, 360582078506110939, 360582078238441412, 360582078239274326, 360582078053791215, 360582077726426664]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360614118326999312, 360614140906078836⟩, ⟨(-1910927381750386686), (-1910018701533410454)⟩, true⟩

def words06 : List Nat := [360582077398884248, 360582077447605044, 360582077465555572, 360582077483653395, 360582077484428048, 360582077238033521, 360582077114028920, 360582077193647094, 360582077472238208, 360582078011356011]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594976760365314, 360594999347378002⟩, ⟨(-770518703691219350), (-769609550855456420)⟩, true⟩

def words07 : List Nat := [360582078409316939, 360582078807348989, 360582079369196787, 360582080071024560, 360582080701166045, 360582081331427334, 360582081747175039, 360582081882360268, 360582082099845528, 360582082317605836]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594156693547307, 360594179288399308⟩, ⟨(-721659562695875224), (-720749942753312336)⟩, true⟩

def words08 : List Nat := [360582082817001127, 360582083141788621, 360582083324555256, 360582083507423474, 360582083525411497, 360582083683273735, 360582083882587572, 360582084082049996, 360582084138304330, 360582084342136394]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615039564429323, 360615062167159949⟩, ⟨(-1966298594687492240), (-1965388505221005118)⟩, true⟩

def words09 : List Nat := [360582084537161599, 360582084732417542, 360582085056891973, 360582085174211534, 360582085174980402, 360582085037520910, 360582084957527837, 360582085295117720, 360582085849094574, 360582086403242884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk595B
