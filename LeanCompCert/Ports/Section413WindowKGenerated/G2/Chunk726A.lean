import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583202968074931, 360583237037313136⟩, ⟨(-63319868571152727), (-61649206749803143)⟩, true⟩

def state01 : KState := ⟨⟨360581953351701937, 360581987430638802⟩, ⟨27390898039754096, 29062264033682284⟩, true⟩

def words00 : List Nat := [360582388040380729, 360582388082623145, 360582388083551229, 360582388030316058, 360582387976900454, 360582387821337802, 360582387765213562, 360582387770395844, 360582387771314550, 360582387682174868]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593344833711580, 360593378922399397⟩, ⟨(-799937799796741690), (-798265725740161892)⟩, true⟩

def words01 : List Nat := [360582387677518150, 360582387512048670, 360582387368953870, 360582387369985059, 360582387204306042, 360582386870474349, 360582386536453503, 360582386401656600, 360582386553860918, 360582386706294687]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587470420375542, 360587504518887069⟩, ⟨(-373381241152403827), (-371708453650296349)⟩, true⟩

def words02 : List Nat := [360582386762707092, 360582386792187082, 360582387010702404, 360582387229517519, 360582387315236062, 360582387316267408, 360582387212772055, 360582386993493816, 360582386774024172, 360582386753006794]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545679783973202, 360545713892211662⟩, ⟨2662118454208564991, 2663791948227009709⟩, true⟩

def words03 : List Nat := [360582386805957402, 360582386859117604, 360582386860043806, 360582386762333136, 360582386577268105, 360582386323617994, 360582386069674028, 360582385899796427, 360582385540646497, 360582385036873378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590488887685229, 360590523005662485⟩, ⟨(-593073576664955325), (-591399375171306819)⟩, true⟩

def words04 : List Nat := [360582384532882704, 360582384094496308, 360582383751291479, 360582383597441469, 360582383443504635, 360582383122300647, 360582382806235583, 360582382679609760, 360582382614019640, 360582382727136776]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726A
