import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245

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

def state06 : KState := ⟨⟨360692244229798874, 360692247795277341⟩, ⟨(-2669961848687403237), (-2669902607979863987)⟩, true⟩

def words05 : List Nat := [360583510273629251, 360583514521747842, 360583519767877701, 360583523367082862, 360583525574757208, 360583527782282298, 360583530468050578, 360583533978652408, 360583538405370131, 360583542831799476]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593862477202891, 360593866045741069⟩, ⟨(-253697868142426943), (-253638552274404053)⟩, true⟩

def words06 : List Nat := [360583546430534526, 360583548383455323, 360583549167459327, 360583549951487031, 360583549951756038, 360583549777464503, 360583548543863256, 360583546292140020, 360583544040538847, 360583543366473868]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360535126224053452, 360535129795605487⟩, ⟨1190066006851089364, 1190125396785596384⟩, true⟩

def words07 : List Nat := [360583545441953883, 360583547517326093, 360583548755322914, 360583549747723361, 360583550302393833, 360583550857103342, 360583551355457270, 360583551355777812, 360583550210945179, 360583548241365683]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582519920118792, 360582523494698031⟩, ⟨24894242699604346, 24953707057807440⟩, true⟩

def words08 : List Nat := [360583546271874343, 360583545671703143, 360583545742775186, 360583545813906667, 360583545814204246, 360583544189450549, 360583541870432446, 360583540306692364, 360583538742982827, 360583538285550321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597109031219236, 360597112608858267⟩, ⟨(-333969305288727817), (-333909765675303691)⟩, true⟩

def words09 : List Nat := [360583538244574310, 360583536931231327, 360583535956298953, 360583537117150649, 360583537847883282, 360583538578612408, 360583538578901179, 360583538488727990, 360583539040781872, 360583539592896506]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk245
