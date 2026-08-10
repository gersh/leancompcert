import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk220A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360496604858999930, 360496607692100831⟩, ⟨1832410012898001262, 1832452185160334236⟩, true⟩

def state01 : KState := ⟨⟨360546793554566925, 360546796390353657⟩, ⟨727996549152807937, 728038780516767773⟩, true⟩

def words00 : List Nat := [360579897187592475, 360579893297752158, 360579890681110391, 360579890124260867, 360579889567442290, 360579887201299192, 360579882780349621, 360579879663082787, 360579876546012161, 360579874026905987]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360499632344428258, 360499635182922620⟩, ⟨1766226514695575121, 1766268805667997229⟩, true⟩

def words01 : List Nat := [360579872524384098, 360579869136895114, 360579865749659664, 360579864420157372, 360579864140421817, 360579861804144143, 360579859468047671, 360579855830707901, 360579850851142341, 360579847208611449]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360554660759296725, 360554663600475671⟩, ⟨554290853059086000, 554333203159666334⟩, true⟩

def words02 : List Nat := [360579843566318227, 360579840409754477, 360579838794123624, 360579836151275600, 360579833508621533, 360579830309623649, 360579828148608001, 360579828042581725, 360579827936538355, 360579826251549646]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360662284577579709, 360662287421448245⟩, ⟨(-1817366153403434435), (-1817323744037779701)⟩, true⟩

def words03 : List Nat := [360579826021891391, 360579826934384731, 360579828134968009, 360579828430256290, 360579828430520096, 360579827031101349, 360579826285388141, 360579827974302819, 360579831715887694, 360579835457198085]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585422669186717, 360585425515776517⟩, ⟨(-123370571935465449), (-123328102580589773)⟩, true⟩

def words04 : List Nat := [360579837971872672, 360579839143031743, 360579839653213324, 360579840163429672, 360579840163668375, 360579840149732150, 360579838821403535, 360579836458599450, 360579834095954604, 360579832658192708]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk220A
