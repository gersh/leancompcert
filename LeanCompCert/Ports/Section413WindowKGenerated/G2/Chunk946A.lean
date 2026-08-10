import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583853883419247, 360583912936500211⟩, ⟨(-174466827102265135), (-170694562925967721)⟩, true⟩

def state01 : KState := ⟨⟨360593849542372856, 360593908608378898⟩, ⟨(-1120119516636202573), (-1116346029683783561)⟩, true⟩

def words00 : List Nat := [360582108578926092, 360582108640510997, 360582108813386546, 360582108986521497, 360582109045042582, 360582109046413120, 360582109025111891, 360582109058335602, 360582109156271027, 360582109282405346]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581571710413784, 360581630789487275⟩, ⟨41581217697744016, 45355941024596762⟩, true⟩

def words01 : List Nat := [360582109311420411, 360582109340600762, 360582109481160939, 360582109693910093, 360582109861000320, 360582110028310740, 360582110139848985, 360582110141219754, 360582110141337561, 360582110137838835]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594432543768521, 360594491635753682⟩, ⟨(-1175325422050143932), (-1171549476956760824)⟩, true⟩

def words02 : List Nat := [360582110240468620, 360582110410662461, 360582110524590711, 360582110638666279, 360582110722117253, 360582110891707478, 360582111051880877, 360582111212308079, 360582111316497052, 360582111448743540]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590160276125550, 360590219381067844⟩, ⟨(-771034884413072414), (-767257713121608320)⟩, true⟩

def words03 : List Nat := [360582111671560372, 360582111894775276, 360582112059862480, 360582112113905740, 360582112115183082, 360582112074538959, 360582112075375574, 360582112174146487, 360582112260923675, 360582112348036477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578277237711857, 360578336355701156⟩, ⟨353527807577870656, 357306213702500350⟩, true⟩

def words04 : List Nat := [360582112378855000, 360582112380226204, 360582112330180781, 360582112294824736, 360582112259082917, 360582112163747387, 360582112004654186, 360582111759833239, 360582111514754583, 360582111381730766]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk946A
