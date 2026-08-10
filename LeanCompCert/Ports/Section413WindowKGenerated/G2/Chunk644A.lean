import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604260120780886, 360604286673928880⟩, ⟨(-1377181003570011532), (-1376025855793105470)⟩, true⟩

def state01 : KState := ⟨⟨360590468871050556, 360590495432825054⟩, ⟨(-489026019551749859), (-487870316184660283)⟩, true⟩

def words00 : List Nat := [360582920355974660, 360582920495784242, 360582920876260556, 360582921257000054, 360582921479171204, 360582921480077561, 360582921462245219, 360582921259430199, 360582921056448539, 360582921100549750]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576698793852253, 360576725364161580⟩, ⟨398033387217595443, 399189640355758491⟩, true⟩

def words01 : List Nat := [360582921361398862, 360582921622413100, 360582921712034875, 360582921874907712, 360582921904717921, 360582921934770584, 360582922104838746, 360582922131076094, 360582922131883899, 360582922036629071]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581365917832503, 360581392496716753⟩, ⟨97326508428369222, 98483314004529970⟩, true⟩

def words02 : List Nat := [360582921941184696, 360582921859754961, 360582921994442564, 360582922129298512, 360582922130135610, 360582922058504179, 360582921746796552, 360582921472719503, 360582921198364397, 360582921028673987]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597128081560702, 360597154669077552⟩, ⟨(-918359638799959943), (-917202276982102913)⟩, true⟩

def words03 : List Nat := [360582921005765824, 360582920862594861, 360582920815790540, 360582921033494828, 360582921079636372, 360582921125910990, 360582921126719161, 360582921035367871, 360582921237292333, 360582921459211441]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594053109475259, 360594079705547073⟩, ⟨(-720172327422731568), (-719014414280904676)⟩, true⟩

def words04 : List Nat := [360582921751601000, 360582922050407965, 360582922228030204, 360582922405745876, 360582922522495138, 360582922789407151, 360582923112634394, 360582923436025421, 360582923546123461, 360582923720158470]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk644A
