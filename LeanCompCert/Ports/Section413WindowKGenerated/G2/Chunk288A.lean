import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360669522748634778, 360669527719840551⟩, ⟨(-2500203981581323259), (-2500107150924109241)⟩, true⟩

def state01 : KState := ⟨⟨360658959577016937, 360658964551803166⟩, ⟨(-2196028572652054184), (-2195931638859380694)⟩, true⟩

def words00 : List Nat := [360582725338919241, 360582728022930221, 360582730104289392, 360582732185546318, 360582733424700733, 360582735267810572, 360582738312806264, 360582741357665011, 360582743390740746, 360582746036692293]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360688965419848222, 360688970398231234⟩, ⟨(-3060592973258889167), (-3060495935825160793)⟩, true⟩

def words01 : List Nat := [360582749468864855, 360582752900917578, 360582757534239882, 360582760971295638, 360582763286316621, 360582765601205775, 360582769117188964, 360582773238152975, 360582776923309190, 360582780608292469]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360668319107973212, 360668324089979043⟩, ⟨(-2465887778004614137), (-2465790636143151843)⟩, true⟩

def words02 : List Nat := [360582783527155728, 360582785250335474, 360582786782828793, 360582788315326115, 360582789531983777, 360582791255591860, 360582792366938658, 360582793478246744, 360582795451454518, 360582798418439966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603987503446165, 360603992489044935⟩, ⟨(-610826646162933233), (-610729400698966949)⟩, true⟩

def words03 : List Nat := [360582801558726029, 360582804698866071, 360582806902108284, 360582808755224410, 360582810086119262, 360582811417026627, 360582813947637724, 360582815283800113, 360582816018439403, 360582816753089214]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360637057249739752, 360637062238934833⟩, ⟨(-1564493997761597693), (-1564396648562392903)⟩, true⟩

def words04 : List Nat := [360582818371847231, 360582821034294403, 360582824895792345, 360582828757095349, 360582831597223534, 360582833243435415, 360582834378898164, 360582835514386853, 360582837051414786, 360582838931300353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk288A
