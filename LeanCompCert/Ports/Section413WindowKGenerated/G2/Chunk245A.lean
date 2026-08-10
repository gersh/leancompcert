import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360636421620601263, 360636425167918105⟩, ⟨(-1298737393379668663), (-1298678598176190059)⟩, true⟩

def state01 : KState := ⟨⟨360580103809832168, 360580107360190316⟩, ⟨80956602671294257, 81015472401957095⟩, true⟩

def words00 : List Nat := [360583421362621133, 360583421362940703, 360583421903481420, 360583422775690611, 360583422775959742, 360583422538000191, 360583420648096435, 360583417465599397, 360583414283299092, 360583412765021078]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622668419261122, 360622671972630137⟩, ⟨(-962414885983036239), (-962355942440917009)⟩, true⟩

def words01 : List Nat := [360583413709283748, 360583414788373268, 360583415026305077, 360583416109474310, 360583416759473548, 360583417409507559, 360583419721749595, 360583422575934254, 360583424176930539, 360583425777840328]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360682261690421424, 360682265246812613⟩, ⟨(-2424096583194146064), (-2424037565533563110)⟩, true⟩

def words02 : List Nat := [360583426941975301, 360583429223424194, 360583432717817072, 360583436211986011, 360583438340365571, 360583438818581654, 360583440957909044, 360583443097161352, 360583445940913443, 360583449969590586]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360653583273709267, 360653586833144763⟩, ⟨(-1720448364558068644), (-1720389272205433762)⟩, true⟩

def words03 : List Nat := [360583452585736805, 360583455201702496, 360583459477712899, 360583464848101905, 360583469084191247, 360583473319982831, 360583476716202180, 360583478463304380, 360583481320465314, 360583484177498888]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360647094130782786, 360647097693238889⟩, ⟨(-1561298206950261682), (-1561239040456928844)⟩, true⟩

def words04 : List Nat := [360583486478335703, 360583488822342091, 360583490223511690, 360583491624600667, 360583492593518676, 360583494388816961, 360583497842306132, 360583501295576548, 360583503434640094, 360583506025263779]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245A
