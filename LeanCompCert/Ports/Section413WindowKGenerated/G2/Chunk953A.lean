import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360612140806908738, 360612200771390121⟩, ⟨(-2866140118287645392), (-2862281316305032782)⟩, true⟩

def state01 : KState := ⟨⟨360601173439765520, 360601233417410691⟩, ⟨(-1820981223854836966), (-1817121167298887286)⟩, true⟩

def words00 : List Nat := [360582166916494080, 360582167140225300, 360582167396244365, 360582167652672351, 360582167832440618, 360582167902652560, 360582167917387804, 360582167932273797, 360582168037922037, 360582168239547707]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579720785993138, 360579780776665504⟩, ⟨223846746865256444, 227708045107229638⟩, true⟩

def words01 : List Nat := [360582168550785897, 360582168862309509, 360582169118338345, 360582169264769011, 360582169340606348, 360582169416808639, 360582169602676614, 360582169679066491, 360582169680333905, 360582169656702299]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606837926541509, 360606897930253662⟩, ⟨(-2361095245047642481), (-2357232703788038737)⟩, true⟩

def words02 : List Nat := [360582169702983100, 360582169829518424, 360582169959278197, 360582170089296906, 360582170121964752, 360582170212676097, 360582170413146889, 360582170614033864, 360582170847067286, 360582171107879114]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360594640107662771, 360594700124545777⟩, ⟨(-1198239872092388936), (-1194376075190572154)⟩, true⟩

def words03 : List Nat := [360582171303559430, 360582171499386245, 360582171692252007, 360582171940261107, 360582172129551646, 360582172319066012, 360582172423359375, 360582172446107878, 360582172578624682, 360582172711625936]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593531776247616, 360593591806138946⟩, ⟨(-1092532580787499541), (-1088667543607099131)⟩, true⟩

def words04 : List Nat := [360582172921189002, 360582173147966082, 360582173309108458, 360582173470398712, 360582173603443848, 360582173792561495, 360582173955577159, 360582174118844225, 360582174211170935, 360582174332346253]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk953A
