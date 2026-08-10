import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607528829366024, 360607545575636256⟩, ⟨(-1323014382994687157), (-1322430515370140241)⟩, true⟩

def state01 : KState := ⟨⟨360607921558289504, 360607938311280846⟩, ⟨(-1343416755180436211), (-1342832540712519835)⟩, true⟩

def words00 : List Nat := [360581918128387145, 360581918308149224, 360581918308785301, 360581918268337529, 360581918227760928, 360581918202586595, 360581918686452634, 360581919170436710, 360581919466501977, 360581919971378258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360629693998383720, 360629710758124568⟩, ⟨(-2467316409326652749), (-2466731846485155507)⟩, true⟩

def words01 : List Nat := [360581920373189024, 360581920775192053, 360581921551562802, 360581922046259728, 360581922197560070, 360581922348903335, 360581922765726926, 360581923472154306, 360581924398483321, 360581925324938750]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580211029898479, 360580227796437699⟩, ⟨87067733244011251, 87652647051726427⟩, true⟩

def words02 : List Nat := [360581926063538875, 360581926550776095, 360581926828948979, 360581927107320729, 360581927107929603, 360581927091765561, 360581926803798214, 360581926328291574, 360581925852668089, 360581925504108661]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561720572602186, 360561737345875335⟩, ⟨1041955879856944927, 1042541141371770411⟩, true⟩

def words03 : List Nat := [360581925813214863, 360581926155338599, 360581926308956661, 360581926408053881, 360581926408652509, 360581926305960597, 360581926473814401, 360581926474528836, 360581926371673378, 360581925981455734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360615570794140034, 360615587574158908⟩, ⟨(-1739079940574533428), (-1738494330677744740)⟩, true⟩

def words04 : List Nat := [360581925591091380, 360581925654127686, 360581926043029045, 360581926432052028, 360581926454003621, 360581926681110852, 360581927282129385, 360581927883334250, 360581928438264893, 360581929090670152]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk516A
