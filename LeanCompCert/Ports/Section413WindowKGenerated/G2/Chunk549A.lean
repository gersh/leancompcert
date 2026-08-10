import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk549A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582478701734552, 360582497754219004⟩, ⟨(-40492131852586785), (-39785416019004801)⟩, true⟩

def state01 : KState := ⟨⟨360570548084548479, 360570567144226974⟩, ⟨614371595568676819, 615078706390675607⟩, true⟩

def words00 : List Nat := [360581773079235858, 360581772841292609, 360581772369529493, 360581771732188954, 360581771094747186, 360581770321936870, 360581769715540325, 360581769440320950, 360581769165020765, 360581768723290727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605807847347128, 360605826914228376⟩, ⟨(-1322000387962329979), (-1321292881601003573)⟩, true⟩

def words01 : List Nat := [360581768524359617, 360581768529656842, 360581768783157937, 360581768783921313, 360581768706906713, 360581768316456311, 360581767925873913, 360581767973626800, 360581768412316504, 360581768851163228]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574605237130982, 360574624311292363⟩, ⟨391765353272763746, 392473259494673578⟩, true⟩

def words02 : List Nat := [360581769124333174, 360581769406082512, 360581769738098961, 360581770070324357, 360581770223709202, 360581770224473415, 360581770204339937, 360581769948845716, 360581769693226920, 360581769282337233]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573497190053065, 360573516271403798⟩, ⟨452695100873813505, 453403402043100253⟩, true⟩

def words03 : List Nat := [360581769274694857, 360581769397266645, 360581769397946895, 360581769355119427, 360581769290268406, 360581769142372572, 360581769105451248, 360581769121313998, 360581769121994315, 360581768972569490]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604048206149448, 360604067294718026⟩, ⟨(-1225982678924852039), (-1225273981172373195)⟩, true⟩

def words04 : List Nat := [360581769003291092, 360581769350787594, 360581769617912138, 360581769885164448, 360581769885880996, 360581769802719693, 360581769481255754, 360581769315800806, 360581769314273668, 360581769720858181]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk549A
