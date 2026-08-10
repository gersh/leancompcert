import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604A

def state06 : KState := ⟨⟨362484412131815929, 362484465760338110⟩, ⟨44681463672460221, 46871613125896165⟩, true⟩

def words05 : List Nat := [371285240352609380, 371285240596549971, 371285240837187982, 371285240839235129, 371285240747618804, 371285240734853961, 371285240979679213, 371285241019292700, 371285241020849594, 371285241010307113]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489435595151494, 362489489241992527⟩, ⟨(-258994827587441317), (-256803570480091583)⟩, true⟩

def words06 : List Nat := [371285241220646767, 371285241308023692, 371285241574975591, 371285241842771736, 371285242060564583, 371285242062648368, 371285242127264084, 371285242201804935, 371285242446909947, 371285242519257992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487004986970663, 362487058652544761⟩, ⟨(-112019932390345431), (-109827542407369181)⟩, true⟩

def words07 : List Nat := [371285242591777741, 371285242664990354, 371285242816359209, 371285242832399432, 371285242860015480, 371285242888404245, 371285242909547951, 371285242911609717, 371285242718318686, 371285242750982165]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472097000467441, 362472150684256657⟩, ⟨789724924697839745, 791918416427710733⟩, true⟩

def words08 : List Nat := [371285243009420447, 371285243011468492, 371285242905537107, 371285242799396231, 371285242692493129, 371285242668502523, 371285242531761877, 371285242507699345, 371285242482960660, 371285242408780177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511229540797168, 362511283243078811⟩, ⟨(-1577580848074852582), (-1575386237646006930)⟩, true⟩

def words09 : List Nat := [371285242223575402, 371285242255833404, 371285242560609408, 371285242686508517, 371285242753738784, 371285242821635440, 371285243162185781, 371285243367033399, 371285243798834288, 371285244231531134]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604B
